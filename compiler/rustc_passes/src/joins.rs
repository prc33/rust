//! Collection of the typed compiler seam for experimental join endpoints.

use rustc_hir as hir;
use rustc_hir::{ImplItemKind, ItemKind, find_attr};
use rustc_middle::middle::joins::{JoinChannel, JoinDefinition, JoinDefinitions, JoinRule};
use rustc_middle::query::Providers;
use rustc_middle::ty::TyCtxt;
use tracing::info;

fn join_definitions(tcx: TyCtxt<'_>, _: ()) -> JoinDefinitions<'_> {
    let mut endpoints = Vec::new();

    // `owners()` includes the synthetic crate-root owner for the crate-wide
    // item collection. That owner is a module, rather than an `Item`, so using
    // `hir_expect_item` on it triggers an ICE. Iterate the actual free items;
    // inherent impls are included there and the synthetic root is not.
    for item_id in tcx.hir_crate_items(()).free_items() {
        let impl_def_id = item_id.owner_id.def_id;
        let item = tcx.hir_expect_item(impl_def_id);
        let ItemKind::Impl(impl_) = item.kind else { continue };

        let Some((declared_channels, declared_rules, declared_arity, declared_async_rule, direct_unary, queue_bound)) = find_attr!(
            tcx,
            impl_def_id,
            RustcJoinEndpoint { channels, rules, arity, async_rule, direct_unary, queue_bound } =>
                (*channels, *rules, *arity, *async_rule, *direct_unary, *queue_bound)
        ) else {
            continue;
        };

        let endpoint_def_id = match impl_.self_ty.kind {
            hir::TyKind::Path(hir::QPath::Resolved(_, path)) => {
                path.res.opt_def_id().and_then(|def_id| def_id.as_local())
            }
            _ => None,
        };

        // The builtin expansion emits constructors first, then one method per
        // channel, and finally the dispatch method. Restricting this query to
        // that generated shape keeps channel identity tied to HIR owner IDs
        // while the frontend grows explicit channel nodes.
        let mut channel_items = Vec::new();
        let mut constructor_def_id = None;
        let mut scoped_constructor_def_id = None;
        let mut dispatch_method = None;
        for item_id in impl_.items {
            let item = tcx.hir_impl_item(*item_id);
            let ImplItemKind::Fn(_, _) = item.kind else { continue };
            let method_def_id = item.owner_id.def_id;
            if item.ident.name.as_str() == "__join_dispatch_once" {
                dispatch_method = Some(method_def_id);
            } else if item.ident.name.as_str() == "new" {
                constructor_def_id = Some(method_def_id);
            } else if item.ident.name.as_str() == "new_in_scope" {
                scoped_constructor_def_id = Some(method_def_id);
            } else {
                channel_items.push((method_def_id, item.ident.name));
            }
        }

        let span = item.span;
        let channels = channel_items
            .into_iter()
            .take(declared_channels as usize)
            .enumerate()
            .map(|(index, (channel_method_def_id, name))| {
                // An impl may contain several private adapters with identical
                // ABI. Match the compiler-owned source coordinates encoded in
                // each marker and reject ambiguity instead of taking the first
                // marker found in declaration order.
                let mut adapters = impl_.items.iter().filter_map(|item_id| {
                    let item = tcx.hir_impl_item(*item_id);
                    let method_def_id = item.owner_id.def_id;
                    find_attr!(tcx, method_def_id, RustcJoinDirectAdapter { channel, rule, constructor } =>
                        (*channel, *rule, *constructor))
                        .filter(|(channel, _, constructor)| *channel == index as u32 && !constructor)
                        .map(|(_, rule, _)| (method_def_id, rule))
                });
                let direct_method_def_id = match (adapters.next(), adapters.next()) {
                    (Some((adapter_def_id, rule)), None)
                        if declared_rules == 1
                            && declared_arity == 1
                            && rule == 0
                            && tcx.erase_and_anonymize_regions(
                                tcx.fn_sig(adapter_def_id.to_def_id()).instantiate_identity(),
                            ) == tcx.erase_and_anonymize_regions(
                                tcx.fn_sig(channel_method_def_id.to_def_id()).instantiate_identity(),
                            ) =>
                    {
                        // The marker identifies the source coordinate, while
                        // the group-shape and signature checks keep the
                        // generated adapter's ABI tied to the channel method.
                        // Missing, ambiguous, or incompatible adapters remain
                        // unavailable to MIR rewriting even before full
                        // pattern identities are available in HIR.
                        Some(adapter_def_id)
                    }
                    _ => None,
                };
                let mut private_constructors = impl_.items.iter().filter_map(|item_id| {
                    let method_def_id = tcx.hir_impl_item(*item_id).owner_id.def_id;
                    find_attr!(tcx, method_def_id, RustcJoinDirectAdapter { channel, rule, constructor } =>
                        (*channel, *rule, *constructor))
                        .filter(|(channel, rule, constructor)|
                            *channel == index as u32 && *rule == 0 && *constructor)
                        .map(|_| method_def_id)
                });
                let private_constructor_def_id = match (
                    direct_method_def_id,
                    constructor_def_id,
                    private_constructors.next(),
                    private_constructors.next(),
                ) {
                    (Some(_), Some(original), Some(private), None)
                        if tcx.erase_and_anonymize_regions(
                            tcx.fn_sig(original).instantiate_identity(),
                        ) == tcx.erase_and_anonymize_regions(
                            tcx.fn_sig(private).instantiate_identity(),
                        ) => Some(private),
                    _ => None,
                };
                JoinChannel {
                    method_def_id: channel_method_def_id,
                    direct_method_def_id,
                    private_constructor_def_id,
                    index: index as u32,
                    name,
                    signature: tcx
                        .fn_sig(channel_method_def_id.to_def_id())
                        .instantiate_identity()
                        .skip_normalization(),
                }
            })
            .collect();
        let rules = dispatch_method
            .into_iter()
            .map(|method_def_id| JoinRule {
                method_def_id,
                arity: declared_arity,
                is_async: declared_async_rule,
                body_def_ids: tcx.nested_bodies_within(method_def_id),
                span,
            })
            .collect();

        endpoints.push(JoinDefinition {
            impl_def_id,
            endpoint_def_id,
            declared_channels,
            declared_rules,
            declared_arity,
            declared_async_rule,
            frontend_direct_unary: direct_unary,
            frontend_queue_bound: (queue_bound != u32::MAX).then_some(queue_bound),
            span,
            channels,
            constructor_def_id,
            scoped_constructor_def_id,
            rules,
        });
        info!(target: "rustc_join", endpoint = ?impl_def_id, "join endpoint descriptor collected");
    }

    JoinDefinitions { endpoints }
}

pub(crate) fn provide(providers: &mut Providers) {
    providers.join_definitions = join_definitions;
}
