//! Built-in lowering for the experimental `join impl` item.
//!
//! The parser presents `join impl Name[<...>] { ... }` to macro expansion as a
//! private `core::join_impl! { [visibility] Name[<...>] { ... } }` invocation.
//! Keeping the first lowering in this pipeline gives the extension ordinary
//! Rust hygiene, `NodeId` assignment, name resolution, and HIR lowering
//! instead of hiding it in an opaque AST placeholder.

use rustc_ast::token::{self, Delimiter};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_ast_pretty::pprust;
use rustc_errors::PResult;
use rustc_expand::base::{DummyResult, ExpandResult, ExtCtxt, MacEager, MacroExpanderResult};
use rustc_parse::exp;
use rustc_parse::parser::{AllowConstBlockItems, FollowedByType, ForceCollect, Parser};
use rustc_span::{FileName, Ident, Span, kw, sym};
use smallvec::SmallVec;

#[derive(Debug)]
struct Argument {
    name: Ident,
    ty: String,
}

#[derive(Debug)]
struct Channel {
    name: Ident,
    arguments: Vec<Argument>,
    reply: Option<String>,
}

#[derive(Debug)]
struct Pattern {
    channel: Ident,
    bindings: Vec<Ident>,
}

#[derive(Debug)]
struct Rule {
    patterns: Vec<Pattern>,
    body: String,
    is_async: bool,
}

#[derive(Debug)]
struct Definition {
    visibility: String,
    struct_attributes: String,
    impl_attributes: String,
    name: Ident,
    generic_params: String,
    generic_args: String,
    generic_where: String,
    channels: Vec<Channel>,
    rules: Vec<Rule>,
}

/// Expand one parsed `join impl` item.
pub(crate) fn expand_join_impl<'cx>(
    cx: &'cx mut ExtCtxt<'_>,
    span: Span,
    tts: TokenStream,
) -> MacroExpanderResult<'cx> {
    // The AST feature gate emits the user-facing diagnostic. Avoid a second,
    // misleading lowering error when expansion is still attempted during
    // recovery after that gate has fired.
    if !cx.ecfg.features.joins() {
        return ExpandResult::Ready(MacEager::items(SmallVec::new()));
    }
    let mut parser = cx.new_parser_from_tts(tts);
    let attributes = match parser.parse_outer_attributes_for_macro() {
        Ok(attributes) => attributes,
        Err(error) => return ExpandResult::Ready(DummyResult::any(span, error.emit())),
    };
    let struct_attributes =
        attributes.iter().map(pprust::attribute_to_string).collect::<Vec<_>>().join("\n");
    let impl_attributes = attributes
        .iter()
        // Item-level configuration and lint policy apply to the generated
        // implementation as well as its storage struct. Do not blindly copy
        // derives/representation attributes to an `impl`, where rustc would
        // reject them as ill-formed.
        .filter(|attribute| {
            attribute.has_name(sym::cfg)
                || attribute.has_name(sym::allow)
                || attribute.has_name(sym::warn)
                || attribute.has_name(sym::deny)
                || attribute.has_name(sym::forbid)
                || attribute.has_name(sym::expect)
        })
        .map(pprust::attribute_to_string)
        .collect::<Vec<_>>()
        .join("\n");
    let visibility = match parser.parse_visibility(FollowedByType::No) {
        Ok(visibility) => pprust::vis_to_string(&visibility).trim().to_string(),
        Err(error) => return ExpandResult::Ready(DummyResult::any(span, error.emit())),
    };
    let name = match parser.parse_ident() {
        Ok(name) => name,
        Err(error) => return ExpandResult::Ready(DummyResult::any(span, error.emit())),
    };
    let mut generic_tokens = Vec::new();
    while parser.token.kind.open_delim() != Some(Delimiter::Brace) && parser.token != token::Eof {
        generic_tokens.push(parser.parse_token_tree());
    }
    let generic_text = pprust::tts_to_string(&TokenStream::new(generic_tokens));
    let (generic_params, generic_args, generic_where) = match split_generic_syntax(&generic_text) {
        Ok(generics) => generics,
        Err(message) => {
            let guar = cx.dcx().span_err(span, message);
            return ExpandResult::Ready(DummyResult::any(span, guar));
        }
    };
    if parser.token.kind.open_delim() != Some(Delimiter::Brace) {
        let guar = cx.dcx().span_err(span, "expected a brace-delimited join body");
        return ExpandResult::Ready(DummyResult::any(span, guar));
    }
    let body = parser.parse_token_tree();
    let TokenTree::Delimited(_, _, Delimiter::Brace, body_tokens) = body else {
        let guar = cx.dcx().span_err(span, "expected a brace-delimited join body");
        return ExpandResult::Ready(DummyResult::any(span, guar));
    };
    if parser.token != token::Eof {
        let guar = cx.dcx().span_err(parser.token.span, "unexpected tokens after join body");
        return ExpandResult::Ready(DummyResult::any(span, guar));
    }

    let definition = match parse_definition(
        parser.psess,
        visibility,
        struct_attributes,
        impl_attributes,
        name,
        generic_params,
        generic_args,
        generic_where,
        body_tokens,
    ) {
        Ok(definition) => definition,
        Err(error) => return ExpandResult::Ready(DummyResult::any(span, error.emit())),
    };
    // The isolated unary representation is a semantic lowering, not an
    // optional CFA rewrite.  All modes therefore construct the same
    // caller-owned future; `-Zjoin-cfa` only controls whether optional proofs
    // are collected or consumed later in MIR. Shared/multi-input definitions
    // continue through the compatibility matcher.
    let direct_unary = true;
    let generated = match generate_endpoint(&definition, direct_unary) {
        Ok(generated) => generated,
        Err(message) => {
            let guar = cx.dcx().span_err(span, message);
            return ExpandResult::Ready(DummyResult::any(span, guar));
        }
    };

    // Parse the generated endpoint through rustc's own parser. Macro
    // expansion assigns fresh node ids and applies normal expansion hygiene to
    // every generated item before name resolution and HIR lowering.
    let tokens = match rustc_parse::source_str_to_stream(
        cx.psess(),
        FileName::macro_expansion_source_code(&generated),
        generated,
        Some(span),
    ) {
        Ok(tokens) => tokens,
        Err(errors) => {
            let guar = errors
                .into_iter()
                .map(|error| error.emit())
                .next()
                .unwrap_or_else(|| cx.dcx().span_err(span, "failed to lower join item"));
            return ExpandResult::Ready(DummyResult::any(span, guar));
        }
    };
    let mut generated_parser = cx.new_parser_from_tts(tokens);
    let mut items = SmallVec::new();
    loop {
        match generated_parser.parse_item(ForceCollect::No, AllowConstBlockItems::Yes) {
            Ok(Some(item)) => items.push(item),
            Ok(None) => break,
            Err(error) => return ExpandResult::Ready(DummyResult::any(span, error.emit())),
        }
    }
    ExpandResult::Ready(MacEager::items(items))
}

fn parse_definition<'a>(
    psess: &'a rustc_session::parse::ParseSess,
    visibility: String,
    struct_attributes: String,
    impl_attributes: String,
    name: Ident,
    generic_params: String,
    generic_args: String,
    generic_where: String,
    body: TokenStream,
) -> PResult<'a, Definition> {
    let mut parser = Parser::new(psess, body, Some("join impl body"));
    let mut channels = Vec::new();
    let mut rules = Vec::new();
    while parser.token != token::Eof {
        if parser.token.is_ident_named(sym::channel) {
            parser.bump();
            channels.push(parse_channel(&mut parser)?);
        } else {
            // `async when` opts a reaction into Rust's ordinary Future
            // lowering. The matcher still claims inputs atomically; the
            // generated reaction evaluates the async body through the
            // runtime's compatibility executor after releasing the queue
            // lock. Keeping the modifier on the rule (rather than inventing
            // a second body language) lets all expressions use normal Rust
            // `.await` and `?` semantics.
            let is_async = parser.token.is_keyword(kw::Async);
            if is_async {
                parser.bump();
            }
            if parser.token.is_ident_named(sym::when) {
                parser.bump();
                rules.push(parse_rule(&mut parser, is_async)?);
            } else {
                return parser.unexpected_any();
            }
        }
    }
    Ok(Definition {
        visibility,
        struct_attributes,
        impl_attributes,
        name,
        generic_params,
        generic_args,
        generic_where,
        channels,
        rules,
    })
}

fn split_generic_syntax(text: &str) -> Result<(String, String, String), String> {
    let text = text.trim();
    if text.is_empty() {
        return Ok((String::new(), String::new(), String::new()));
    }
    if !text.starts_with('<') {
        return Err("expected generic parameters before the join body".into());
    }
    let generic_end = matching_delimiter(text, 0, '<', '>')
        .ok_or_else(|| "unclosed generic parameter list".to_string())?;
    let suffix = text[generic_end + 1..].trim();
    let generic_where = if suffix.is_empty() {
        String::new()
    } else if suffix.starts_with("where ") {
        suffix.to_string()
    } else {
        return Err("expected a `where` clause after generic parameters".into());
    };
    let inner = &text[1..generic_end];
    let parameters = split_top_level_with_angles(inner, ',')
        .into_iter()
        .map(str::trim)
        .filter(|parameter| !parameter.is_empty())
        .collect::<Vec<_>>();
    if parameters.is_empty() {
        return Err("join generic parameter lists cannot be empty".into());
    }
    let mut arguments = Vec::with_capacity(parameters.len());
    for parameter in &parameters {
        let mut argument = parameter.split_once(':').map_or(*parameter, |(name, _)| name).trim();
        if let Some((name, _)) = argument.split_once('=') {
            argument = name.trim();
        }
        if let Some(const_name) = argument.strip_prefix("const ") {
            argument = const_name.split_whitespace().next().unwrap_or(const_name);
        }
        if argument.is_empty()
            || argument.chars().any(|character| {
                !(character.is_ascii_alphanumeric() || character == '_' || character == '\'')
            })
        {
            return Err(
                "native join lowering currently accepts only named generic parameters".into()
            );
        }
        arguments.push(argument);
    }
    Ok((
        format!("<{}>", parameters.join(", ")),
        format!("<{}>", arguments.join(", ")),
        generic_where,
    ))
}

fn parse_channel<'a>(parser: &mut Parser<'a>) -> PResult<'a, Channel> {
    let name = parser.parse_ident()?;
    let arguments_tokens = take_group(parser, Delimiter::Parenthesis)?;
    let arguments = parse_arguments(parser.psess, arguments_tokens)?;
    let reply = if parser.eat(exp!(RArrow)) {
        Some(pprust::ty_to_string(&*parser.parse_ty()?))
    } else {
        None
    };
    parser.expect(exp!(Semi))?;
    Ok(Channel { name, arguments, reply })
}

fn parse_arguments<'a>(
    psess: &'a rustc_session::parse::ParseSess,
    tokens: TokenStream,
) -> PResult<'a, Vec<Argument>> {
    let mut parser = Parser::new(psess, tokens, Some("join channel arguments"));
    let mut arguments = Vec::new();
    while parser.token != token::Eof {
        let name = parser.parse_ident()?;
        parser.expect(exp!(Colon))?;
        let ty = pprust::ty_to_string(&*parser.parse_ty()?);
        arguments.push(Argument { name, ty });
        if !parser.eat(exp!(Comma)) {
            break;
        }
    }
    if parser.token != token::Eof {
        return parser.unexpected_any();
    }
    Ok(arguments)
}

fn parse_rule<'a>(parser: &mut Parser<'a>, is_async: bool) -> PResult<'a, Rule> {
    let first = parse_pattern(parser)?;
    let mut patterns = vec![first];
    while parser.eat(exp!(And)) {
        patterns.push(parse_pattern(parser)?);
    }
    let body = take_group(parser, Delimiter::Brace)?;
    Ok(Rule { patterns, body: pprust::tts_to_string(&body), is_async })
}

fn parse_pattern<'a>(parser: &mut Parser<'a>) -> PResult<'a, Pattern> {
    let channel = parser.parse_ident()?;
    let arguments = take_group(parser, Delimiter::Parenthesis)?;
    let mut argument_parser = Parser::new(parser.psess, arguments, Some("join pattern"));
    let mut bindings = Vec::new();
    while argument_parser.token != token::Eof {
        bindings.push(argument_parser.parse_ident()?);
        if !argument_parser.eat(exp!(Comma)) {
            break;
        }
    }
    if argument_parser.token != token::Eof {
        return argument_parser.unexpected_any();
    }
    Ok(Pattern { channel, bindings })
}

fn take_group<'a>(parser: &mut Parser<'a>, delimiter: Delimiter) -> PResult<'a, TokenStream> {
    if parser.token.kind.open_delim() != Some(delimiter) {
        return parser.unexpected_any();
    }
    match parser.parse_token_tree() {
        TokenTree::Delimited(_, _, found, tokens) if found == delimiter => Ok(tokens),
        _ => parser.unexpected_any(),
    }
}

fn generate_endpoint(definition: &Definition, direct_unary: bool) -> Result<String, String> {
    if definition.channels.is_empty() {
        return Err("a join definition must declare at least one channel".into());
    }
    for (index, channel) in definition.channels.iter().enumerate() {
        if definition.channels[..index]
            .iter()
            .any(|previous| previous.name.name == channel.name.name)
        {
            return Err(format!("channel `{}` is declared more than once", channel.name.name));
        }
    }
    // Keep the specialized matchers for the common one/two-channel shape.
    // Definitions with additional channels or rules use the shared dynamic
    // matcher below, so every invocation still enters one atomic queue state.
    if definition.rules.len() == 1
        && definition.rules[0].patterns.len() <= 2
        && definition.channels.len() == definition.rules[0].patterns.len()
    {
        resolve_rule(definition, &definition.rules[0], 0)?;
        return generate_restricted_endpoint(definition, direct_unary);
    }
    generate_dynamic_endpoint(definition)
}

fn generate_restricted_endpoint(
    definition: &Definition,
    direct_unary: bool,
) -> Result<String, String> {
    if definition.rules.len() != 1 {
        return Err("the native join lowering currently requires exactly one rule".into());
    }
    let rule = &definition.rules[0];
    if rule.patterns.is_empty() || rule.patterns.len() > 2 {
        return Err(
            "the native join lowering currently supports one or two channels per rule".into()
        );
    }
    let resolved = resolve_rule(definition, rule, 0)?;
    let (body, aliases) = rewrite_body(definition, &rule.body, rule.is_async);
    let channels = resolved.iter().map(|(_, channel, _)| *channel).collect::<Vec<_>>();
    let expected_replies = channels.iter().filter(|channel| channel.reply.is_some()).count();
    let (prefix, replies) = split_reaction_body(&body, expected_replies).ok_or_else(|| {
        "join rule must contain `return { channel: expression, ... }`".to_string()
    })?;
    if replies.len() != expected_replies {
        return Err(format!(
            "join rule must return exactly one expression for each result-bearing channel (expected {expected_replies})"
        ));
    }
    for (target, _) in &replies {
        let declaration = definition
            .channels
            .iter()
            .find(|channel| channel.name.name.as_str() == target)
            .ok_or_else(|| format!("reply target `{target}` refers to an unknown channel"))?;
        if declaration.reply.is_none() {
            return Err(format!("one-way channel `{target}` cannot receive a reply"));
        }
    }

    let direct_shape = direct_unary
        && channels.len() == 1
        && channels[0].reply.is_some()
        && aliases.is_empty();
    let prefix = rewrite_early_return_maps(
        definition,
        &resolved,
        &prefix,
        if direct_shape { EarlyReturnMode::DirectUnary } else { EarlyReturnMode::UnaryOrPair },
        0,
    )?;
    let queue_bound = if channels.len() == 1 {
        if direct_shape { 0 } else { 1 }
    } else {
        u32::MAX
    };
    let endpoint_attribute = join_endpoint_attribute(definition, direct_shape, queue_bound);

    if channels.len() == 1 {
        return generate_unary_endpoint(
            definition,
            rule,
            channels[0],
            &aliases,
            &prefix,
            &replies,
            &endpoint_attribute,
            direct_shape,
        );
    }

    let left = channels[0];
    let right = channels[1];
    let left_expression = reply_expression(&replies, left)?;
    let right_expression = reply_expression(&replies, right)?;
    let left_type = channel_input_type(left);
    let right_type = channel_input_type(right);
    let left_binding = "__join_left_value";
    let right_binding = "__join_right_value";
    let left_unpack = pattern_unpack(&rule.patterns[0], left_binding);
    let right_unpack = pattern_unpack(&rule.patterns[1], right_binding);
    let left_reply = left.reply.as_deref().unwrap_or("()");
    let right_reply = right.reply.as_deref().unwrap_or("()");
    let scope_bounds = scoped_constructor_bounds(&[
        left_type.as_str(),
        right_type.as_str(),
        left_reply,
        right_reply,
    ]);
    let visibility = visibility_prefix(&definition.visibility);
    let struct_attributes = attributes_prefix(&definition.struct_attributes);
    let impl_attributes = attributes_prefix(&definition.impl_attributes);
    let left_method = channel_method(&visibility, left, "submit_left", left_reply, &scope_bounds);
    let right_method =
        channel_method(&visibility, right, "submit_right", right_reply, &scope_bounds);
    let left_result = if left.reply.is_some() { left_expression.to_string() } else { "()".into() };
    let right_result =
        if right.reply.is_some() { right_expression.to_string() } else { "()".into() };
    let reaction = reaction_result_body(
        &aliases,
        &prefix,
        &format!("({left_result}, {right_result})"),
        &format!("({left_reply}, {right_reply})"),
        rule.is_async,
    );
    let dispatch = if rule.is_async {
        format!(
            "self.matcher.__join_dispatch_future_at(::joins_runtime::source_location(file!(), line!(), column!()), move |{left_binding}, {right_binding}| {{\n{left_unpack}\n{right_unpack}\nlet __join_result = {reaction};\nasync move {{ match __join_result.await {{ Ok((left, right)) => (Ok(left), Ok(right)), Err(error) => (Err(error.clone()), Err(error)) }} }}\n}})"
        )
    } else {
        format!(
            "self.matcher.__join_dispatch_once_at(::joins_runtime::source_location(file!(), line!(), column!()), move |{left_binding}, {right_binding}| {{\n{left_unpack}\n{right_unpack}\nlet __join_result = {reaction};\nmatch __join_result {{ Ok((left, right)) => (Ok(left), Ok(right)), Err(error) => (Err(error.clone()), Err(error)) }}\n}})"
        )
    };
    Ok(format!(
        r#"{struct_attributes}{visibility}struct {struct_name} {{
    matcher: ::joins_runtime::PairMatcher<{left_type}, {right_type}, {left_reply}, {right_reply}>,
}}

impl {impl_generics}Clone for {impl_name} {{
    fn clone(&self) -> Self {{
        Self {{ matcher: self.matcher.clone() }}
    }}
}}

{impl_attributes}{endpoint_attribute}
impl {impl_generics}{impl_name} {{

    {visibility}fn new() -> Self {{
        Self {{ matcher: ::joins_runtime::PairMatcher::new() }}
    }}

    {visibility}fn new_in_scope(scope: ::joins_runtime::QueryScope) -> Self
{scope_bounds}{{
        Self {{ matcher: ::joins_runtime::PairMatcher::new_in_scope(scope) }}
    }}

    {left_method}

    {right_method}

    fn __join_dispatch_once(&self) -> bool
{scope_bounds}{{
        let __join_endpoint = self.clone();
        {dispatch}
    }}
}}
"#,
        visibility = visibility,
        struct_attributes = struct_attributes,
        impl_attributes = impl_attributes,
        struct_name = struct_name(definition),
        impl_generics = impl_generics(definition),
        impl_name = impl_name(definition),
        left_type = left_type,
        right_type = right_type,
        left_reply = left_reply,
        right_reply = right_reply,
        scope_bounds = scope_bounds,
        left_method = left_method,
        right_method = right_method,
        dispatch = dispatch,
        endpoint_attribute = endpoint_attribute,
    ))
}

fn generate_unary_endpoint(
    definition: &Definition,
    rule: &Rule,
    channel: &Channel,
    aliases: &str,
    prefix: &str,
    replies: &[(String, String)],
    endpoint_attribute: &str,
    direct_unary: bool,
) -> Result<String, String> {
    let expression = reply_expression(replies, channel)?;
    let input_type = channel_input_type(channel);
    let output_type = channel.reply.as_deref().unwrap_or("()");
    let scope_bounds = scoped_constructor_bounds(&[input_type.as_str(), output_type]);
    let binding = "__join_input_value";
    let unpack = pattern_unpack(&rule.patterns[0], binding);
    let visibility = visibility_prefix(&definition.visibility);
    let struct_attributes = attributes_prefix(&definition.struct_attributes);
    let impl_attributes = attributes_prefix(&definition.impl_attributes);
    let result = if channel.reply.is_some() { expression.to_string() } else { "()".into() };
    let use_direct_unary = direct_unary && channel.reply.is_some() && aliases.is_empty();
    let reaction = if use_direct_unary {
        reaction_value_body(aliases, prefix, &result, rule.is_async)
    } else {
        reaction_result_body(aliases, prefix, &result, output_type, rule.is_async)
    };
    // A closed unary endpoint with no nested channel aliases has the exact
    // ordinary-future shape: capture the argument now and evaluate the body
    // only when the returned future is first polled. Returning an opaque
    // future keeps the capture inline, like an ordinary `async fn`, instead
    // of allocating the compatibility `Reply` thunk. The MIR pass still
    // records and checks the body, while shared/multi-input rules retain the
    // compatibility matcher.
    // An `async when` body is already an ordinary coroutine; await that inner
    // body from the generated outer future so the isolated case has the same
    // construction and first-poll contract as an `async fn`.
    let direct_reaction = if rule.is_async {
        format!("({reaction}).await")
    } else {
        reaction.clone()
    };
    let scoped_constructor = if use_direct_unary {
        String::new()
    } else {
        format!(
            "    {visibility}fn new_in_scope(scope: ::joins_runtime::QueryScope) -> Self\n{scope_bounds}{{\n        Self {{ matcher: ::joins_runtime::UnaryMatcher::new_bounded_in_scope(scope) }}\n    }}\n\n",
            visibility = visibility,
            scope_bounds = scope_bounds,
        )
    };
    let dispatch_bounds = if use_direct_unary { String::new() } else { scope_bounds.clone() };
    let dispatch = if use_direct_unary {
        // The direct method never submits to the matcher. Keep the private
        // compatibility hook type-correct without constructing a second
        // reaction closure (and, importantly, without reintroducing a
        // JoinError conversion into the public future).
        "false".to_string()
    } else if rule.is_async {
        format!(
            "self.matcher.__join_dispatch_future_at(::joins_runtime::source_location(file!(), line!(), column!()), move |{binding}| {{\n{unpack}\n{reaction}\n}})"
        )
    } else {
        format!(
            "self.matcher.__join_dispatch_once_at(::joins_runtime::source_location(file!(), line!(), column!()), move |{binding}| {{\n{unpack}\n{reaction}\n}})"
        )
    };
    let storage = if use_direct_unary {
        direct_struct_decl(definition, &visibility)
    } else {
        format!(
            "{visibility}struct {struct_name} {{\n    matcher: ::joins_runtime::UnaryMatcher<{input_type}, {output_type}>,\n}}",
            visibility = visibility,
            struct_name = struct_name(definition),
            input_type = input_type,
            output_type = output_type,
        )
    };
    let clone_impl = if use_direct_unary {
        format!(
            "impl {impl_generics}Clone for {impl_name} {{\n    fn clone(&self) -> Self {{ {clone_value} }}\n}}",
            impl_generics = impl_generics(definition),
            impl_name = impl_name(definition),
            clone_value = direct_struct_value(definition),
        )
    } else {
        format!(
            "impl {impl_generics}Clone for {impl_name} {{\n    fn clone(&self) -> Self {{\n        Self {{ matcher: self.matcher.clone() }}\n    }}\n}}",
            impl_generics = impl_generics(definition),
            impl_name = impl_name(definition),
        )
    };
    let constructor = if use_direct_unary {
        format!(
            "    {visibility}fn new() -> Self {{ {value} }}",
            visibility = visibility,
            value = direct_struct_value(definition),
        )
    } else {
        format!(
            "    {visibility}fn new() -> Self {{\n        Self {{ matcher: ::joins_runtime::UnaryMatcher::new_bounded() }}\n    }}",
            visibility = visibility,
        )
    };
    let dispatch_method = if use_direct_unary {
        String::new()
    } else {
        format!(
            "    fn __join_dispatch_once(&self) -> bool\n{dispatch_bounds}{{\n        let __join_endpoint = self.clone();\n        {dispatch}\n    }}",
            dispatch_bounds = dispatch_bounds,
            dispatch = dispatch,
        )
    };
    let method = if use_direct_unary {
        format!(
            "{visibility}fn {channel}(&self{argument}) -> impl ::core::future::Future<Output = {output_type}>{future_captures} {{ let __join_input_value = {value}; async move {{ {unpack} {direct_reaction} }} }}",
            channel = channel.name.name,
            argument = channel_method_argument(channel),
            value = channel_submit_value(channel),
            unpack = unpack,
            direct_reaction = direct_reaction,
            future_captures = opaque_future_captures(definition),
        )
    } else if channel.reply.is_some() {
        format!(
            "{visibility}fn {channel}(&self{argument}) -> ::joins_runtime::Reply<{output_type}>\n{scope_bounds}{{ let reply = self.matcher.submit_at({value}, ::joins_runtime::source_location(file!(), line!(), column!())); let _ = self.__join_dispatch_once(); reply }}",
            channel = channel.name.name,
            argument = channel_method_argument(channel),
            value = channel_submit_value(channel),
            scope_bounds = scope_bounds,
        )
    } else {
        format!(
            "{visibility}fn {channel}(&self{argument})\n{scope_bounds}{{ let _ = self.matcher.submit_at({value}, ::joins_runtime::source_location(file!(), line!(), column!())); let _ = self.__join_dispatch_once(); }}",
            channel = channel.name.name,
            argument = channel_method_argument(channel),
            value = channel_submit_value(channel),
            scope_bounds = scope_bounds,
        )
    };
    Ok(format!(
        r#"{struct_attributes}{storage}

{clone_impl}

{impl_attributes}{endpoint_attribute}
impl {impl_generics}{impl_name} {{

{constructor}

{scoped_constructor}

{method}

{dispatch_method}
}}
"#,
        struct_attributes = struct_attributes,
        storage = storage,
        clone_impl = clone_impl,
        impl_attributes = impl_attributes,
        constructor = constructor,
        impl_generics = impl_generics(definition),
        impl_name = impl_name(definition),
        scoped_constructor = scoped_constructor,
        method = method,
        dispatch_method = dispatch_method,
        endpoint_attribute = endpoint_attribute,
    ))
}

/// Build the result-producing part of a reaction. Synchronous rules use the
/// explicit `Result` closure that the first compiler slice has always used.
/// `async when` rules instead let Rust lower an ordinary async block. The
/// matcher has already released its queue lock before handing that future to
/// the runtime executor. The synchronous form remains a direct Result closure.
fn reaction_result_body(
    aliases: &str,
    prefix: &str,
    value: &str,
    result_type: &str,
    is_async: bool,
) -> String {
    if is_async {
        format!(
            "async move {{\n{aliases}{prefix}\nOk::<{result_type}, ::joins_runtime::JoinError>({value})\n}}"
        )
    } else {
        format!(
            "(|| -> ::core::result::Result<{result_type}, ::joins_runtime::JoinError> {{\n{aliases}{prefix}\nOk({value})\n}})()"
        )
    }
}

/// Build the body for an isolated unary reaction whose declared output is
/// already the public future output.  Unlike the shared matcher path this
/// does not add a transport `Result` or translate panics/errors: the generated
/// async block has exactly the same output and unwind behaviour as an ordinary
/// `async fn` with the equivalent body.
fn reaction_value_body(aliases: &str, prefix: &str, value: &str, is_async: bool) -> String {
    if is_async {
        format!(
            "async move {{\n{aliases}{prefix}\n{value}\n}}"
        )
    } else {
        format!("{{\n{aliases}{prefix}\n{value}\n}}")
    }
}

fn generate_dynamic_endpoint(definition: &Definition) -> Result<String, String> {
    let dispatch_bounds = endpoint_dispatch_bounds(definition);
    let mut method_definitions = Vec::with_capacity(definition.channels.len());
    for (index, channel) in definition.channels.iter().enumerate() {
        method_definitions.push(dynamic_channel_method(
            &visibility_prefix(&definition.visibility),
            index,
            channel,
            &dispatch_bounds,
        ));
    }

    let mut rule_definitions = Vec::with_capacity(definition.rules.len());
    let mut direct_method_definitions = Vec::new();
    for (rule_index, rule) in definition.rules.iter().enumerate() {
        let resolved = resolve_rule(definition, rule, rule_index)?;
        // Each rule owns a distinct endpoint clone below. Generate aliases
        // against that per-rule capture so re-emission cannot move the shared
        // outer endpoint into the first closure.
        let (body, aliases) = rewrite_body_with_endpoint(
            definition,
            &rule.body,
            rule.is_async,
            "__join_rule_endpoint",
        );
        let expected_replies =
            resolved.iter().filter(|(_, channel, _)| channel.reply.is_some()).count();
        let (prefix, replies) = split_reaction_body(&body, expected_replies).ok_or_else(|| {
            format!("join rule {rule_index} must contain `return {{ channel: expression, ... }}`")
        })?;
        validate_replies(definition, &resolved, &replies, rule_index)?;
        let prefix = rewrite_early_return_maps(
            definition,
            &resolved,
            &prefix,
            EarlyReturnMode::Dynamic,
            rule_index,
        )?;
        let pattern =
            resolved.iter().map(|(index, _, _)| index.to_string()).collect::<Vec<_>>().join(", ");
        let body = dynamic_rule_body(&resolved, &aliases, &prefix, &replies, rule.is_async)?;
        // A dynamic endpoint may still contain one private, synchronous,
        // unary result rule (for example because the declaration also has an
        // unrelated one-way channel).  Emit a hidden ready-reply adapter for
        // the compiler's proof-driven forwarding rewrite.  It is never used
        // by ordinary source calls and does not change registration or
        // matching semantics until a MIR certificate retargets one call.
        if definition.rules.len() == 1
            && !rule.is_async
            && resolved.len() == 1
            && resolved[0].1.reply.is_some()
            && aliases.is_empty()
        {
            let channel = resolved[0].1;
            let input_type = channel_input_type(channel);
            let output_type = channel.reply.as_deref().unwrap_or("()");
            let binding = "__join_direct_input";
            let unpack = pattern_unpack(&rule.patterns[0], binding);
            let expression = reply_expression(&replies, channel)?;
            let reaction = reaction_result_body("", &prefix, expression, output_type, false);
            let fallback_bindings = channel.arguments.iter().enumerate()
                .map(|(index, _)| format!("__join_fallback_{index}"))
                .collect::<Vec<_>>();
            let fallback_pattern = match fallback_bindings.as_slice() {
                [] => "()".to_string(),
                [binding] => binding.clone(),
                bindings => format!("({})", bindings.join(", ")),
            };
            let fallback_args = fallback_bindings.join(", ");
            direct_method_definitions.push(format!(
                "    #[doc(hidden)]\n    #[join_direct_adapter(channel = {channel_index}, rule = {rule_index})]\n    fn __join_direct_{name}(&self{argument}) -> ::joins_runtime::Reply<{output_type}>\n{scope_bounds}{{\n        ::joins_runtime::__join_sync_inline({value}, |{binding}: {input_type}| {{\n        let __join_direct_result = ::std::panic::catch_unwind(::std::panic::AssertUnwindSafe(|| {{\n            {unpack}\n            {reaction}\n        }}))\n            .unwrap_or_else(|_| Err(::joins_runtime::JoinError::Panic));\n        ::joins_runtime::Reply::ready(__join_direct_result)\n        }}, |{fallback_pattern}| self.{name}({fallback_args}))\n    }}",
                name = channel.name.name,
                channel_index = resolved[0].0,
                rule_index = rule_index,
                argument = channel_method_argument(channel),
                output_type = output_type,
                scope_bounds = dispatch_bounds,
                binding = binding,
                input_type = input_type,
                value = channel_submit_value(channel),
                unpack = unpack,
                reaction = reaction,
            ));
        }
        // Each rule is a separate `move` closure. Clone the endpoint for that
        // closure instead of moving one shared capture into the first rule;
        // this is required when a reaction re-emits state (for example a
        // reusable lock or once-cell protocol) and multiple rules share the
        // same dynamic matcher.
        let dispatch = if rule.is_async {
            format!(
                "{{ let __join_rule_endpoint = __join_endpoint.clone(); let _ = __join_rule_endpoint; self.matcher.__join_dispatch_future_at(&[{pattern}], ::joins_runtime::source_location(file!(), line!(), column!()), move |inputs| {{\n{body}\n}}) }}"
            )
        } else {
            format!(
                "{{ let __join_rule_endpoint = __join_endpoint.clone(); let _ = __join_rule_endpoint; self.matcher.__join_dispatch_once_at(&[{pattern}], ::joins_runtime::source_location(file!(), line!(), column!()), move |inputs| {{\n{body}\n}}) }}"
            )
        };
        rule_definitions.push(format!("if {dispatch} {{ return true; }}"));
    }
    if rule_definitions.is_empty() {
        return Err("a join definition must declare at least one rule".into());
    }
    let visibility = visibility_prefix(&definition.visibility);
    let struct_attributes = attributes_prefix(&definition.struct_attributes);
    let impl_attributes = attributes_prefix(&definition.impl_attributes);
    let methods = method_definitions.join("\n\n    ");
    let direct_methods = direct_method_definitions.join("\n\n");
    let rules = rule_definitions.join("\n        ");
    let endpoint_attribute = join_endpoint_attribute(definition, false, u32::MAX);
    Ok(format!(
        r#"{struct_attributes}{visibility}struct {struct_name} {{
    matcher: ::joins_runtime::DynamicMatcher,
}}

impl {impl_generics}Clone for {impl_name} {{
    fn clone(&self) -> Self {{
        Self {{ matcher: self.matcher.clone() }}
    }}
}}

{impl_attributes}{endpoint_attribute}
impl {impl_generics}{impl_name} {{

    {visibility}fn new() -> Self {{
        Self {{ matcher: ::joins_runtime::DynamicMatcher::new({channel_count}) }}
    }}

    {visibility}fn new_in_scope(scope: ::joins_runtime::QueryScope) -> Self {{
        Self {{ matcher: ::joins_runtime::DynamicMatcher::new_in_scope(scope, {channel_count}) }}
    }}

    {methods}

{direct_methods}

    fn __join_dispatch_once(&self) -> bool
{dispatch_bounds}{{
        let __join_endpoint = self.clone();
        {rules}
        false
    }}
}}
"#,
        visibility = visibility,
        struct_attributes = struct_attributes,
        impl_attributes = impl_attributes,
        struct_name = struct_name(definition),
        impl_generics = impl_generics(definition),
        impl_name = impl_name(definition),
        channel_count = definition.channels.len(),
        methods = methods,
        direct_methods = direct_methods,
        rules = rules,
        dispatch_bounds = dispatch_bounds,
        endpoint_attribute = endpoint_attribute,
    ))
}

/// Emit the compact, parsed contract consumed by rustc's join descriptor
/// query. Only shape is encoded here; names, method identities, and resolved
/// types come from the generated HIR after normal name and type resolution.
fn join_endpoint_attribute(definition: &Definition, direct_unary: bool, queue_bound: u32) -> String {
    let arity = definition.rules.iter().map(|rule| rule.patterns.len()).max().unwrap_or(0);
    let async_rule = definition.rules.iter().any(|rule| rule.is_async);
    format!(
        "#[join_endpoint(channels = {}, rules = {}, arity = {}, async_rule = {}, direct_unary = {}, queue_bound = {})]",
        definition.channels.len(),
        definition.rules.len(),
        arity,
        u32::from(async_rule),
        u32::from(direct_unary),
        queue_bound,
    )
}

fn resolve_rule<'a>(
    definition: &'a Definition,
    rule: &'a Rule,
    rule_index: usize,
) -> Result<Vec<(usize, &'a Channel, &'a Pattern)>, String> {
    if rule.patterns.is_empty() {
        return Err(format!("join rule {rule_index} must match at least one channel"));
    }
    let mut resolved = Vec::with_capacity(rule.patterns.len());
    for (pattern_index, pattern) in rule.patterns.iter().enumerate() {
        let Some((channel_index, channel)) = definition
            .channels
            .iter()
            .enumerate()
            .find(|(_, channel)| channel.name.name == pattern.channel.name)
        else {
            return Err(format!(
                "join rule {rule_index} pattern {pattern_index} refers to unknown channel `{}`",
                pattern.channel.name
            ));
        };
        if resolved.iter().any(|(index, _, _)| *index == channel_index) {
            return Err(format!(
                "join rule {rule_index} cannot match channel `{}` twice",
                channel.name.name
            ));
        }
        if channel.arguments.len() != pattern.bindings.len() {
            return Err(format!(
                "join rule {rule_index} pattern for `{}` binds {} argument(s), but the channel declares {}",
                channel.name.name,
                pattern.bindings.len(),
                channel.arguments.len(),
            ));
        }
        resolved.push((channel_index, channel, pattern));
    }
    Ok(resolved)
}

fn validate_replies(
    definition: &Definition,
    resolved: &[(usize, &Channel, &Pattern)],
    replies: &[(String, String)],
    rule_index: usize,
) -> Result<(), String> {
    let expected = resolved.iter().filter(|(_, channel, _)| channel.reply.is_some()).count();
    if replies.len() != expected {
        return Err(format!(
            "join rule {rule_index} must return exactly one expression for each result-bearing channel (expected {expected})"
        ));
    }
    for (target, _) in replies {
        let Some((_, channel, _)) =
            resolved.iter().find(|(_, channel, _)| channel.name.name.as_str() == target)
        else {
            return Err(format!(
                "join rule {rule_index} reply target `{target}` is not one of its matched channels"
            ));
        };
        if channel.reply.is_none() {
            return Err(format!("one-way channel `{target}` cannot receive a reply"));
        }
        if replies.iter().filter(|(name, _)| name == target).count() > 1 {
            return Err(format!("join rule {rule_index} replies to `{target}` more than once"));
        }
    }
    // Make an unknown target diagnostic deterministic even when the expected
    // count happened to be zero.
    for (target, _) in replies {
        if !definition.channels.iter().any(|channel| channel.name.name.as_str() == target) {
            return Err(format!("join rule {rule_index} reply target `{target}` is unknown"));
        }
    }
    Ok(())
}

fn dynamic_rule_body(
    resolved: &[(usize, &Channel, &Pattern)],
    aliases: &str,
    prefix: &str,
    replies: &[(String, String)],
    is_async: bool,
) -> Result<String, String> {
    let mut extraction = String::new();
    for (index, (_, channel, pattern)) in resolved.iter().enumerate() {
        let input_type = channel_input_type(channel);
        let value = format!("__join_input_value_{index}");
        if is_async {
            extraction.push_str(&format!(
                "let {value}: {input_type} = inputs.with_mut(|inputs| inputs[{index}].take::<{input_type}>())?;\n{}",
                pattern_unpack(pattern, &value),
            ));
        } else {
            extraction.push_str(&format!(
                "let {value}: {input_type} = inputs[{index}].take::<{input_type}>()?;\n{}",
                pattern_unpack(pattern, &value),
            ));
        }
    }
    let mut outputs = Vec::with_capacity(resolved.len());
    for (_, channel, _) in resolved {
        if let Some(reply_type) = channel.reply.as_deref() {
            let expression = reply_expression(replies, channel)?;
            outputs.push(format!("Ok(::joins_runtime::erase_reply::<{reply_type}>({expression}))"));
        } else {
            outputs.push("Ok(::joins_runtime::erase_reply::<()>(()))".to_string());
        }
    }
    let body = format!("{aliases}{extraction}{prefix}\nOk(vec![{}])", outputs.join(",\n"));
    if is_async {
        Ok(format!("async move {{\n{body}\n}}"))
    } else {
        Ok(format!("let inputs = inputs;\n{body}"))
    }
}

fn dynamic_channel_method(
    visibility: &str,
    index: usize,
    channel: &Channel,
    dispatch_bounds: &str,
) -> String {
    let argument = channel_method_argument(channel);
    let value = channel_submit_value(channel);
    let input_type = channel_input_type(channel);
    let output_type = channel.reply.as_deref().unwrap_or("()");
    if channel.reply.is_some() {
        format!(
            "{visibility}fn {name}(&self{argument}) -> ::joins_runtime::Reply<{output_type}>\n{dispatch_bounds}{{ let reply = self.matcher.submit_at::<{input_type}, {output_type}>({index}, {value}, ::joins_runtime::source_location(file!(), line!(), column!())); let _ = self.__join_dispatch_once(); reply }}",
            name = channel.name.name,
            dispatch_bounds = dispatch_bounds,
        )
    } else {
        format!(
            "{visibility}fn {name}(&self{argument})\n{dispatch_bounds}{{ let _ = self.matcher.submit_at::<{input_type}, ()>({index}, {value}, ::joins_runtime::source_location(file!(), line!(), column!())); let _ = self.__join_dispatch_once(); }}",
            name = channel.name.name,
            dispatch_bounds = dispatch_bounds,
        )
    }
}

fn reply_expression<'a>(
    replies: &'a [(String, String)],
    channel: &Channel,
) -> Result<&'a str, String> {
    if channel.reply.is_none() {
        return Ok("");
    }
    replies
        .iter()
        .find(|(target, _)| target == channel.name.name.as_str())
        .map(|(_, expression)| expression.as_str())
        .ok_or_else(|| format!("missing reply expression for `{}`", channel.name.name))
}

fn reply_value_expression<'a>(
    replies: &'a [(String, String)],
    channel: &Channel,
) -> Result<&'a str, String> {
    if channel.reply.is_none() {
        return Ok("()");
    }
    reply_expression(replies, channel)
}

fn split_reaction_body(
    body: &str,
    expected_replies: usize,
) -> Option<(&str, Vec<(String, String)>)> {
    if let Some(result) = split_return_map(body) {
        return Some(result);
    }
    // A rule containing only one-way channels has no result slots to name. In
    // that case the body itself is the reaction and an explicit return map is
    // optional; the generated closure supplies the unit completions.
    (expected_replies == 0 && find_keyword(body, "return").is_none())
        .then_some((body.trim(), Vec::new()))
}

fn visibility_prefix(visibility: &str) -> String {
    if visibility.is_empty() { String::new() } else { format!("{visibility} ") }
}

fn attributes_prefix(attributes: &str) -> String {
    if attributes.is_empty() { String::new() } else { format!("{attributes}\n") }
}

fn struct_name(definition: &Definition) -> String {
    format!("{}{}{}", definition.name.name, definition.generic_params, where_suffix(definition),)
}

/// Declare the zero-sized storage used by an isolated unary endpoint. Generic
/// parameters still need a non-recursive witness in the type definition so
/// lifetimes and type parameters are checked normally without adding runtime
/// state or a queue.
fn direct_struct_decl(definition: &Definition, visibility: &str) -> String {
    if definition.generic_params.is_empty() {
        return format!("{visibility}struct {};", definition.name.name);
    }
    format!(
        "{visibility}struct {}(::core::marker::PhantomData<fn() -> {}>){where_suffix};",
        format!("{}{}", definition.name.name, definition.generic_params),
        direct_phantom_type(definition),
        where_suffix = where_suffix(definition),
    )
}

fn direct_struct_value(definition: &Definition) -> String {
    if definition.generic_params.is_empty() {
        "Self".to_string()
    } else {
        "Self(::core::marker::PhantomData)".to_string()
    }
}

fn direct_phantom_type(definition: &Definition) -> String {
    let Some(end) = matching_delimiter(&definition.generic_params, 0, '<', '>') else {
        return "()".to_string();
    };
    let inner = &definition.generic_params[1..end];
    let components = split_top_level_with_angles(inner, ',')
        .into_iter()
        .filter_map(|parameter| {
            let parameter = parameter.trim();
            if parameter.is_empty() {
                return None;
            }
            if let Some(parameter) = parameter.strip_prefix("const ") {
                let name = parameter.split(|character: char| character == ':' || character == '=' || character.is_whitespace()).next()?;
                return Some(format!("[(); {name}]"));
            }
            let name = parameter
                .split(|character: char| character == ':' || character == '=')
                .next()?
                .trim();
            if name.is_empty() {
                None
            } else if name.starts_with('\'') {
                Some(format!("&{name} ()"))
            } else {
                Some(name.to_string())
            }
        })
        .collect::<Vec<_>>();
    match components.as_slice() {
        [] => "()".to_string(),
        [component] => format!("({component},)"),
        components => format!("({})", components.join(", ")),
    }
}

/// `impl Trait` return types do not automatically expose lifetimes which are
/// captured only by an argument. Preserve every declared generic parameter in
/// the precise-capture bound so a borrowed unary input has the same lifetime
/// contract as an ordinary `async fn`.
fn opaque_future_captures(definition: &Definition) -> String {
    if definition.generic_args.is_empty() {
        String::new()
    } else {
        format!(" + use{}", definition.generic_args)
    }
}

fn impl_name(definition: &Definition) -> String {
    format!("{}{}{}", definition.name.name, definition.generic_args, where_suffix(definition),)
}

fn where_suffix(definition: &Definition) -> String {
    if definition.generic_where.is_empty() {
        String::new()
    } else {
        format!(" {}", definition.generic_where)
    }
}

/// `new_in_scope` installs a cancellation hook that must own `Send + 'static`
/// queue values. Keep that requirement on the optional constructor rather
/// than making every unscoped endpoint generic over `Send` unnecessarily.
fn scoped_constructor_bounds(types: &[&str]) -> String {
    let mut unique = Vec::new();
    for ty in types {
        if !unique.iter().any(|seen| seen == ty) {
            unique.push(*ty);
        }
    }
    if unique.is_empty() {
        return String::new();
    }
    let mut bounds = String::from("    where\n");
    for ty in unique {
        bounds.push_str(&format!("        {ty}: ::core::marker::Send + 'static,\n"));
    }
    bounds.push_str("    ");
    bounds
}

fn endpoint_dispatch_bounds(definition: &Definition) -> String {
    let mut types = Vec::with_capacity(definition.channels.len() * 2);
    for channel in &definition.channels {
        types.push(channel_input_type(channel));
        types.push(channel.reply.clone().unwrap_or_else(|| "()".into()));
    }
    let references = types.iter().map(String::as_str).collect::<Vec<_>>();
    scoped_constructor_bounds(&references)
}

fn impl_generics(definition: &Definition) -> String {
    if definition.generic_params.is_empty() {
        String::new()
    } else {
        format!("{} ", definition.generic_params)
    }
}

fn channel_method(
    visibility: &str,
    channel: &Channel,
    submit: &str,
    reply_type: &str,
    dispatch_bounds: &str,
) -> String {
    if channel.reply.is_some() {
        format!(
            "{visibility}fn {name}(&self{argument}) -> ::joins_runtime::Reply<{reply_type}>\n{dispatch_bounds}{{ let reply = self.matcher.{submit}_at({value}, ::joins_runtime::source_location(file!(), line!(), column!())); let _ = self.__join_dispatch_once(); reply }}",
            name = channel.name.name,
            argument = channel_method_argument(channel),
            value = channel_submit_value(channel),
            dispatch_bounds = dispatch_bounds,
        )
    } else {
        format!(
            "{visibility}fn {name}(&self{argument})\n{dispatch_bounds}{{ let _ = self.matcher.{submit}_at({value}, ::joins_runtime::source_location(file!(), line!(), column!())); let _ = self.__join_dispatch_once(); }}",
            name = channel.name.name,
            argument = channel_method_argument(channel),
            value = channel_submit_value(channel),
            dispatch_bounds = dispatch_bounds,
        )
    }
}

fn channel_input_type(channel: &Channel) -> String {
    match channel.arguments.as_slice() {
        [] => "()".to_string(),
        [argument] => argument.ty.clone(),
        arguments => format!(
            "({})",
            arguments.iter().map(|argument| argument.ty.as_str()).collect::<Vec<_>>().join(", ")
        ),
    }
}

fn channel_method_argument(channel: &Channel) -> String {
    if channel.arguments.is_empty() {
        String::new()
    } else {
        format!(
            ", {}",
            channel
                .arguments
                .iter()
                .map(|argument| format!("{}: {}", argument.name.name, argument.ty))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn channel_submit_value(channel: &Channel) -> String {
    match channel.arguments.as_slice() {
        [] => "()".to_string(),
        [argument] => argument.name.name.to_string(),
        arguments => format!(
            "({})",
            arguments
                .iter()
                .map(|argument| argument.name.name.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn pattern_unpack(pattern: &Pattern, value: &str) -> String {
    let pattern = match pattern.bindings.as_slice() {
        [] => "()".to_string(),
        [binding] => binding.name.to_string(),
        bindings => format!(
            "({})",
            bindings.iter().map(|binding| binding.name.to_string()).collect::<Vec<_>>().join(", ")
        ),
    };
    format!("let {pattern} = {value};")
}

/// Rewrite bare channel submissions in a reaction body to local closures
/// which call the generated endpoint methods. This keeps the user-facing
/// spelling (`fib(input - 1)`) while leaving ordinary Rust calls and explicit
/// receivers (`self.fib(...)`) untouched.
fn rewrite_body(definition: &Definition, body: &str, is_async: bool) -> (String, String) {
    rewrite_body_with_endpoint(definition, body, is_async, "__join_endpoint")
}

fn rewrite_body_with_endpoint(
    definition: &Definition,
    body: &str,
    is_async: bool,
    endpoint_binding: &str,
) -> (String, String) {
    let (rewritten, used_channels) = rewrite_channel_calls(definition, body);
    let demand_bindings = collect_demand_bindings(&rewritten);
    let aliases = used_channels
        .iter()
        .map(|&index| channel_alias_name(&definition.channels[index]))
        .collect::<Vec<_>>();
    let rewritten = rewrite_demands(&rewritten, &demand_bindings, &aliases, is_async);
    (rewritten, channel_aliases(definition, &used_channels, endpoint_binding))
}

fn rewrite_channel_calls(definition: &Definition, body: &str) -> (String, Vec<usize>) {
    let bytes = body.as_bytes();
    let mut at = 0;
    let mut rewritten = String::with_capacity(body.len());
    let mut used = Vec::new();
    while at < bytes.len() {
        if bytes.get(at..at + 2) == Some(b"//") {
            let end = body[at..].find('\n').map_or(bytes.len(), |offset| at + offset);
            rewritten.push_str(&body[at..end]);
            at = end;
            continue;
        }
        if bytes.get(at..at + 2) == Some(b"/*") {
            let end = find_comment_end(bytes, at).unwrap_or(bytes.len());
            rewritten.push_str(&body[at..end]);
            at = end;
            continue;
        }
        if matches!(bytes[at], b'"' | b'\'') && is_literal_quote(bytes, at) {
            let end = skip_quoted(bytes, at, bytes[at]);
            rewritten.push_str(&body[at..end]);
            at = end;
            continue;
        }
        if bytes[at] == b'r' && raw_string_start(bytes, at).is_some() {
            let end = skip_raw_string(bytes, at);
            rewritten.push_str(&body[at..end]);
            at = end;
            continue;
        }
        if is_identifier_start(bytes[at]) {
            let start = at;
            at += 1;
            while at < bytes.len() && is_identifier_byte(bytes[at]) {
                at += 1;
            }
            let name = &body[start..at];
            let channel = definition
                .channels
                .iter()
                .enumerate()
                .find(|(_, channel)| channel.name.name.as_str() == name);
            let call = next_nontrivia(body, at)
                .and_then(|next| bytes.get(next).copied().map(|byte| byte == b'('))
                .unwrap_or(false);
            let receiver = has_explicit_receiver(bytes, start);
            if let Some((index, _)) = channel
                && call
                && !receiver
            {
                let alias = channel_alias_name(&definition.channels[index]);
                rewritten.push_str(&alias);
                if !used.contains(&index) {
                    used.push(index);
                }
            } else {
                rewritten.push_str(name);
            }
            continue;
        }
        let character = body[at..].chars().next().expect("byte offset is in body");
        rewritten.push(character);
        at += character.len_utf8();
    }
    (rewritten, used)
}

fn collect_demand_bindings(body: &str) -> Vec<String> {
    let mut bindings = Vec::new();
    let mut search_from = 0;
    while search_from < body.len() {
        let Some(relative) = find_keyword(&body[search_from..], "let") else {
            break;
        };
        let let_at = search_from + relative;
        let mut at = let_at + "let".len();
        at = next_nontrivia(body, at).unwrap_or(body.len());
        if body[at..].starts_with("mut")
            && body.as_bytes().get(at + 3).is_none_or(|byte| !is_identifier_byte(*byte))
        {
            at = next_nontrivia(body, at + 3).unwrap_or(body.len());
        }
        let Some(name_end) = identifier_end(body.as_bytes(), at) else {
            search_from = let_at + "let".len();
            continue;
        };
        let name = &body[at..name_end];
        let Some(equal) = find_let_assignment(body, name_end) else {
            break;
        };
        let Some(value) = next_nontrivia(body, equal + 1) else {
            break;
        };
        let channel_call = identifier_end(body.as_bytes(), value)
            .filter(|&end| body[value..end].starts_with("__join_channel_"))
            .and_then(|end| next_nontrivia(body, end))
            .is_some_and(|open| body.as_bytes().get(open) == Some(&b'('));
        if channel_call {
            bindings.push(name.to_string());
        }
        search_from = name_end;
    }
    bindings
}

fn rewrite_demands(body: &str, bindings: &[String], aliases: &[String], is_async: bool) -> String {
    if bindings.is_empty() && aliases.is_empty() {
        return body.to_string();
    }
    let bytes = body.as_bytes();
    let mut at = 0;
    let mut rewritten = String::with_capacity(body.len());
    while at < bytes.len() {
        if bytes.get(at..at + 2) == Some(b"//") {
            let end = body[at..].find('\n').map_or(bytes.len(), |offset| at + offset);
            rewritten.push_str(&body[at..end]);
            at = end;
            continue;
        }
        if bytes.get(at..at + 2) == Some(b"/*") {
            let end = find_comment_end(bytes, at).unwrap_or(bytes.len());
            rewritten.push_str(&body[at..end]);
            at = end;
            continue;
        }
        if matches!(bytes[at], b'"' | b'\'') && is_literal_quote(bytes, at) {
            let end = skip_quoted(bytes, at, bytes[at]);
            rewritten.push_str(&body[at..end]);
            at = end;
            continue;
        }
        if bytes[at] == b'r' && raw_string_start(bytes, at).is_some() {
            let end = skip_raw_string(bytes, at);
            rewritten.push_str(&body[at..end]);
            at = end;
            continue;
        }
        if is_identifier_start(bytes[at]) {
            let start = at;
            let Some(end) = identifier_end(bytes, at) else {
                rewritten.push(body[at..].chars().next().expect("identifier byte"));
                at += 1;
                continue;
            };
            let name = &body[start..end];
            // A channel call may be demanded directly without introducing a
            // temporary (`fib(input - 1)?`). The first scan has already
            // rewritten the channel name to its local submission closure;
            // recognize that alias here and wrap the complete call in the
            // same synchronous or async demand bridge used for named locals.
            if aliases.iter().any(|alias| alias == name)
                && let Some(open) = next_nontrivia(body, end)
                && bytes.get(open) == Some(&b'(')
                && let Some(close) = matching_delimiter(body, open, '(', ')')
                && let Some(question) = next_nontrivia(body, close + 1)
                && bytes.get(question) == Some(&b'?')
            {
                let call = rewrite_demands(&body[start..=close], bindings, aliases, is_async);
                if is_async {
                    rewritten.push_str(&call);
                    rewritten.push_str(".await?");
                } else {
                    rewritten.push_str("::joins_runtime::blocking_wait_at(");
                    rewritten.push_str(&call);
                    rewritten.push_str(
                        ", ::joins_runtime::source_location(file!(), line!(), column!()))?",
                    );
                }
                at = question + 1;
                continue;
            }
            let question = next_nontrivia(body, end)
                .and_then(|next| bytes.get(next).copied().map(|byte| byte == b'?'))
                .unwrap_or(false);
            if question && bindings.iter().any(|binding| binding == name) {
                if is_async {
                    // A channel reply is already a Future. In an async
                    // reaction, preserve Rust's normal async lowering and
                    // let `?` propagate the Future's `JoinError`.
                    rewritten.push_str(name);
                    rewritten.push_str(".await");
                } else {
                    rewritten.push_str("::joins_runtime::blocking_wait_at(");
                    rewritten.push_str(name);
                    rewritten.push_str(
                        ", ::joins_runtime::source_location(file!(), line!(), column!()))",
                    );
                }
            } else {
                rewritten.push_str(name);
            }
            at = end;
            continue;
        }
        let character = body[at..].chars().next().expect("byte offset is in body");
        rewritten.push(character);
        at += character.len_utf8();
    }
    rewritten
}

/// Find the assignment in a `let` statement, allowing a type annotation
/// between the binding and `=`. The scanner understands Rust delimiters and
/// literals so an `=` nested in a type (or in a comment/string) cannot be
/// mistaken for the binding assignment.
fn find_let_assignment(body: &str, start: usize) -> Option<usize> {
    let bytes = body.as_bytes();
    let mut at = start;
    let mut depths = [0usize; 4];
    while at < bytes.len() {
        if bytes.get(at..at + 2) == Some(b"//") {
            at += 2;
            while at < bytes.len() && bytes[at] != b'\n' {
                at += 1;
            }
            continue;
        }
        if bytes.get(at..at + 2) == Some(b"/*") {
            at = find_comment_end(bytes, at)?;
            continue;
        }
        if bytes[at] == b'r' && raw_string_start(bytes, at).is_some() {
            at = skip_raw_string(bytes, at);
            continue;
        }
        if matches!(bytes[at], b'"' | b'\'') && is_literal_quote(bytes, at) {
            at = skip_quoted(bytes, at, bytes[at]);
            continue;
        }
        let ch = body[at..].chars().next()?;
        let width = ch.len_utf8();
        match ch {
            '(' => depths[0] += 1,
            ')' => {
                if depths[0] == 0 {
                    return None;
                }
                depths[0] -= 1;
            }
            '[' => depths[1] += 1,
            ']' => depths[1] = depths[1].saturating_sub(1),
            '{' => depths[2] += 1,
            '}' if depths[2] == 0 => return None,
            '}' => depths[2] -= 1,
            '<' if bytes.get(at + 1) != Some(&b'=') => depths[3] += 1,
            '>' => depths[3] = depths[3].saturating_sub(1),
            '=' if depths.iter().all(|depth| *depth == 0)
                && bytes.get(at + 1) != Some(&b'=')
                && bytes.get(at.wrapping_sub(1)) != Some(&b'=')
                && bytes.get(at + 1) != Some(&b'>') =>
            {
                return Some(at);
            }
            ';' if depths.iter().all(|depth| *depth == 0) => return None,
            _ => {}
        }
        at += width;
    }
    None
}

fn channel_aliases(
    definition: &Definition,
    used_channels: &[usize],
    endpoint_binding: &str,
) -> String {
    let mut aliases = String::new();
    for &index in used_channels {
        let channel = &definition.channels[index];
        let parameters = channel
            .arguments
            .iter()
            .map(|argument| format!("{}: {}", argument.name.name, argument.ty))
            .collect::<Vec<_>>()
            .join(", ");
        let arguments = channel
            .arguments
            .iter()
            .map(|argument| argument.name.name.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        aliases.push_str(&format!(
            "let {} = |{}| {endpoint_binding}.{}({});\n",
            channel_alias_name(channel),
            parameters,
            channel.name.name,
            arguments,
        ));
    }
    aliases
}

fn channel_alias_name(channel: &Channel) -> String {
    format!("__join_channel_{}", channel.name.name)
}

fn identifier_end(bytes: &[u8], start: usize) -> Option<usize> {
    if start >= bytes.len() || !is_identifier_start(bytes[start]) {
        return None;
    }
    let mut end = start + 1;
    while end < bytes.len() && is_identifier_byte(bytes[end]) {
        end += 1;
    }
    Some(end)
}

fn is_identifier_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'_'
}

fn has_explicit_receiver(bytes: &[u8], mut at: usize) -> bool {
    while at > 0 && bytes[at - 1].is_ascii_whitespace() {
        at -= 1;
    }
    if at == 0 {
        return false;
    }
    if bytes[at - 1] == b'.' {
        return true;
    }
    // A path-qualified function (`module::channel(...)`) has two adjacent
    // colons. A single colon is the field separator in a named reply map
    // (`return { channel: channel(...) }`) and must not suppress rewriting.
    bytes[at - 1] == b':' && at >= 2 && bytes[at - 2] == b':'
}

#[derive(Clone, Copy)]
enum EarlyReturnMode {
    DirectUnary,
    UnaryOrPair,
    Dynamic,
}

/// Convert nested named reply maps into ordinary Rust early returns. The
/// final map is removed by [`split_return_map`] and is emitted by the normal
/// endpoint path; maps nested in `if`/`match` blocks need an equivalent
/// `return Ok(...)` so the generated reaction closure can short-circuit while
/// still completing every matched invocation.
fn rewrite_early_return_maps(
    definition: &Definition,
    resolved: &[(usize, &Channel, &Pattern)],
    body: &str,
    mode: EarlyReturnMode,
    rule_index: usize,
) -> Result<String, String> {
    let mut rewritten = String::with_capacity(body.len());
    let mut cursor = 0;
    while cursor < body.len() {
        let Some(relative) = find_keyword(&body[cursor..], "return") else {
            rewritten.push_str(&body[cursor..]);
            break;
        };
        let return_at = cursor + relative;
        let Some((_map_open, map_close, replies)) = return_map_at(body, return_at) else {
            let next = return_at + "return".len();
            rewritten.push_str(&body[cursor..next]);
            cursor = next;
            continue;
        };
        validate_replies(definition, resolved, &replies, rule_index)?;
        rewritten.push_str(&body[cursor..return_at]);
        let value = match mode {
            EarlyReturnMode::DirectUnary => {
                if resolved.len() == 1 {
                    reply_value_expression(&replies, resolved[0].1)?.to_string()
                } else {
                    return Err("direct unary early return matched multiple channels".into());
                }
            }
            EarlyReturnMode::UnaryOrPair => {
                if resolved.len() == 1 {
                    reply_value_expression(&replies, resolved[0].1)?.to_string()
                } else {
                    let values = resolved
                        .iter()
                        .map(|(_, channel, _)| reply_value_expression(&replies, channel))
                        .collect::<Result<Vec<_>, _>>()?;
                    format!("({})", values.join(", "))
                }
            }
            EarlyReturnMode::Dynamic => {
                let values = resolved
                    .iter()
                    .map(|(_, channel, _)| {
                        if let Some(reply_type) = channel.reply.as_deref() {
                            let expression = reply_expression(&replies, channel)?;
                            Ok(format!(
                                "Ok(::joins_runtime::erase_reply::<{reply_type}>({expression}))"
                            ))
                        } else {
                            Ok("Ok(::joins_runtime::erase_reply::<()>(()))".to_string())
                        }
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                format!("vec![{}]", values.join(", "))
            }
        };
        rewritten.push_str("return Ok(");
        rewritten.push_str(&value);
        rewritten.push(')');
        cursor = map_close + 1;
    }
    Ok(rewritten)
}

fn split_return_map(body: &str) -> Option<(&str, Vec<(String, String)>)> {
    let mut cursor = 0;
    let mut selected = None;
    while cursor < body.len() {
        let Some(relative) = find_keyword(&body[cursor..], "return") else {
            break;
        };
        let return_at = cursor + relative;
        if let Some((map_open, map_close, replies)) = return_map_at(body, return_at) {
            // The named reply map is the rule's top-level completion. Return
            // maps nested in `if`, `match`, closures, or macro blocks are
            // early exits and are rewritten separately by
            // `rewrite_early_return_maps`.
            if brace_depth_at(body, return_at) == 0 {
                selected = Some((return_at, map_open, map_close, replies));
            }
            cursor = map_close + 1;
        } else {
            cursor = return_at + "return".len();
        }
    }
    let (return_at, _map_open, _map_close, replies) = selected?;
    Some((body[..return_at].trim(), replies))
}

fn return_map_at(body: &str, return_at: usize) -> Option<(usize, usize, Vec<(String, String)>)> {
    let map_open = next_nontrivia(body, return_at + "return".len())?;
    if body.as_bytes().get(map_open) != Some(&b'{') {
        return None;
    }
    let map_close = matching_delimiter(body, map_open, '{', '}')?;
    let mut replies = Vec::new();
    for field in split_top_level(&body[map_open + 1..map_close], ',') {
        let (channel, expression) = field.split_once(':')?;
        let channel = channel.trim();
        let expression = expression.trim();
        if channel.is_empty() || expression.is_empty() {
            return None;
        }
        replies.push((channel.to_string(), expression.to_string()));
    }
    Some((map_open, map_close, replies))
}

fn brace_depth_at(text: &str, end: usize) -> usize {
    let bytes = text.as_bytes();
    let mut at = 0;
    let mut depth = 0usize;
    while at < end && at < bytes.len() {
        if bytes.get(at..at + 2) == Some(b"//") {
            at += 2;
            while at < end && at < bytes.len() && bytes[at] != b'\n' {
                at += 1;
            }
            continue;
        }
        if bytes.get(at..at + 2) == Some(b"/*") {
            at = find_comment_end(bytes, at).unwrap_or(end).min(end);
            continue;
        }
        if bytes[at] == b'r' && raw_string_start(bytes, at).is_some() {
            at = skip_raw_string(bytes, at).min(end);
            continue;
        }
        if matches!(bytes[at], b'"' | b'\'') && is_literal_quote(bytes, at) {
            at = skip_quoted(bytes, at, bytes[at]).min(end);
            continue;
        }
        let ch = text[at..].chars().next().expect("byte offset is in text");
        match ch {
            '{' => depth += 1,
            '}' => depth = depth.saturating_sub(1),
            _ => {}
        }
        at += ch.len_utf8();
    }
    depth
}

fn split_top_level(text: &str, separator: char) -> Vec<&str> {
    split_top_level_impl(text, separator, false)
}

fn split_top_level_with_angles(text: &str, separator: char) -> Vec<&str> {
    split_top_level_impl(text, separator, true)
}

fn split_top_level_impl(text: &str, separator: char, track_angles: bool) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut start = 0;
    let mut depths = [0usize; 4];
    let bytes = text.as_bytes();
    let mut at = 0;
    while at < bytes.len() {
        if bytes.get(at..at + 2) == Some(b"//") {
            at += 2;
            while at < bytes.len() && bytes[at] != b'\n' {
                at += 1;
            }
            continue;
        }
        if bytes.get(at..at + 2) == Some(b"/*") {
            at = find_comment_end(bytes, at).unwrap_or(bytes.len());
            continue;
        }
        if bytes[at] == b'r' && raw_string_start(bytes, at).is_some() {
            at = skip_raw_string(bytes, at);
            continue;
        }
        if matches!(bytes[at], b'"' | b'\'') && is_literal_quote(bytes, at) {
            at = skip_quoted(bytes, at, bytes[at]);
            continue;
        }
        let ch = text[at..].chars().next().expect("byte offset is in text");
        let width = ch.len_utf8();
        match ch {
            '(' => depths[0] += 1,
            ')' => depths[0] = depths[0].saturating_sub(1),
            '[' => depths[1] += 1,
            ']' => depths[1] = depths[1].saturating_sub(1),
            '{' => depths[2] += 1,
            '}' => depths[2] = depths[2].saturating_sub(1),
            '<' if text.as_bytes().get(at + 1) != Some(&b'=') => depths[3] += 1,
            '>' => depths[3] = depths[3].saturating_sub(1),
            _ if ch == separator
                && depths[..3].iter().all(|depth| *depth == 0)
                && (!track_angles || depths[3] == 0) =>
            {
                parts.push(&text[start..at]);
                start = at + width;
            }
            _ => {}
        }
        at += width;
    }
    let tail = &text[start..];
    if !tail.trim().is_empty() {
        parts.push(tail);
    }
    parts
}

fn matching_delimiter(text: &str, open: usize, open_ch: char, close_ch: char) -> Option<usize> {
    let mut depth = 0usize;
    let bytes = text.as_bytes();
    let mut at = open;
    while at < bytes.len() {
        if bytes.get(at..at + 2) == Some(b"//") {
            at += 2;
            while at < bytes.len() && bytes[at] != b'\n' {
                at += 1;
            }
            continue;
        }
        if bytes.get(at..at + 2) == Some(b"/*") {
            at = find_comment_end(bytes, at).unwrap_or(bytes.len());
            continue;
        }
        if bytes[at] == b'r' && raw_string_start(bytes, at).is_some() {
            at = skip_raw_string(bytes, at);
            continue;
        }
        if matches!(bytes[at], b'"' | b'\'') && is_literal_quote(bytes, at) {
            at = skip_quoted(bytes, at, bytes[at]);
            continue;
        }
        let ch = text[at..].chars().next().expect("byte offset is in text");
        if ch == open_ch {
            depth += 1;
        } else if ch == close_ch {
            depth = depth.saturating_sub(1);
            if depth == 0 {
                return Some(at);
            }
        }
        at += ch.len_utf8();
    }
    None
}

/// Find a Rust keyword in body text without mistaking a string, character,
/// line comment, or block comment for syntax. The generated endpoint is
/// re-parsed by rustc later; this scan only locates the named reply map so
/// expressions may continue to use ordinary Rust text freely.
fn find_keyword(text: &str, keyword: &str) -> Option<usize> {
    let bytes = text.as_bytes();
    let mut at = 0;
    let mut block_depth = 0usize;
    while at < bytes.len() {
        if block_depth > 0 {
            if bytes.get(at..at + 2) == Some(b"/*") {
                block_depth += 1;
                at += 2;
            } else if bytes.get(at..at + 2) == Some(b"*/") {
                block_depth = block_depth.saturating_sub(1);
                at += 2;
            } else {
                at += 1;
            }
            continue;
        }
        if bytes.get(at..at + 2) == Some(b"//") {
            at += 2;
            while at < bytes.len() && bytes[at] != b'\n' {
                at += 1;
            }
            continue;
        }
        if bytes.get(at..at + 2) == Some(b"/*") {
            block_depth = 1;
            at += 2;
            continue;
        }
        match bytes[at] {
            b'"' | b'\'' => {
                at = skip_quoted(bytes, at, bytes[at]);
                continue;
            }
            b'r' if raw_string_start(bytes, at).is_some() => {
                at = skip_raw_string(bytes, at);
                continue;
            }
            _ => {}
        }
        if bytes.get(at..at + keyword.len()) == Some(keyword.as_bytes())
            && (at == 0 || !is_identifier_byte(bytes[at - 1]))
            && (at + keyword.len() == bytes.len() || !is_identifier_byte(bytes[at + keyword.len()]))
        {
            return Some(at);
        }
        at += 1;
    }
    None
}

fn next_nontrivia(text: &str, mut at: usize) -> Option<usize> {
    let bytes = text.as_bytes();
    loop {
        while at < bytes.len() && bytes[at].is_ascii_whitespace() {
            at += 1;
        }
        if bytes.get(at..at + 2) == Some(b"//") {
            at += 2;
            while at < bytes.len() && bytes[at] != b'\n' {
                at += 1;
            }
            continue;
        }
        if bytes.get(at..at + 2) == Some(b"/*") {
            let end = find_comment_end(bytes, at)?;
            at = end;
            continue;
        }
        return (at < bytes.len()).then_some(at);
    }
}

fn find_comment_end(bytes: &[u8], start: usize) -> Option<usize> {
    let mut at = start + 2;
    let mut depth = 1usize;
    while at < bytes.len() {
        if bytes.get(at..at + 2) == Some(b"/*") {
            depth += 1;
            at += 2;
        } else if bytes.get(at..at + 2) == Some(b"*/") {
            depth = depth.saturating_sub(1);
            at += 2;
            if depth == 0 {
                return Some(at);
            }
        } else {
            at += 1;
        }
    }
    None
}

fn skip_quoted(bytes: &[u8], start: usize, quote: u8) -> usize {
    let mut at = start + 1;
    while at < bytes.len() {
        if bytes[at] == b'\\' {
            at = at.saturating_add(2);
        } else if bytes[at] == quote {
            return at + 1;
        } else {
            at += 1;
        }
    }
    bytes.len()
}

/// Distinguish character literals from lifetime spellings such as `'a` while
/// scanning body text. Double quotes are always string literals; an apostrophe
/// is a character literal only when a closing apostrophe follows the one
/// character (or escape) payload immediately.
fn is_literal_quote(bytes: &[u8], start: usize) -> bool {
    if bytes.get(start) == Some(&b'"') {
        return true;
    }
    if bytes.get(start) != Some(&b'\'') {
        return false;
    }
    if bytes.get(start + 1) == Some(&b'\\') {
        bytes.get(start + 3) == Some(&b'\'')
    } else {
        bytes.get(start + 2) == Some(&b'\'')
    }
}

fn raw_string_start(bytes: &[u8], start: usize) -> Option<usize> {
    if bytes.get(start) != Some(&b'r') {
        return None;
    }
    let mut at = start + 1;
    let hash_start = at;
    while bytes.get(at) == Some(&b'#') {
        at += 1;
    }
    (bytes.get(at) == Some(&b'"')).then_some(at - hash_start)
}

fn skip_raw_string(bytes: &[u8], start: usize) -> usize {
    let Some(hashes) = raw_string_start(bytes, start) else {
        return start + 1;
    };
    let content_start = start + hashes + 2;
    let mut at = content_start;
    while at < bytes.len() {
        if bytes[at] == b'"'
            && bytes
                .get(at + 1..at + 1 + hashes)
                .is_some_and(|closing| closing.iter().all(|byte| *byte == b'#'))
        {
            return at + hashes + 1;
        }
        at += 1;
    }
    bytes.len()
}

fn is_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}
