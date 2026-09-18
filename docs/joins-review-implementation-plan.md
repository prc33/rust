# Implementation plan following the rustc joins review

Date: 2026-09-17. Review baseline: rust HEAD `3c62aa29475` plus working-tree
changes to builtin expansion, join facts, and MIR analysis. This plan converts
a read-only source review into implementation gates. The review did not rebuild
the compiler or execute its proposed counterexamples; reproduce findings before
claiming a demonstrated miscompile or a validated fix.

## Direction and relationship to other plans

Execute the correctness gates below before expanding result fusion or shared
matcher specialisation. This is the corrective implementation order for the
reviewed checkpoint and takes precedence over conflicting completion claims or
sequencing in [joins-next-slice.md](joins-next-slice.md). Retain that document's
longer-term design where compatible with these gates.

The accepted [async semantics](../../joins-library/docs/async-join-semantics.md)
and [shared execution policy](../../joins-library/docs/ir-cfa-evidence/shared-policy.md)
define the target behaviour. The existing compatibility runtime does not yet
implement all of that target. Distinguish an optimisation preserving today's
baseline from a semantic correction applied consistently in every CFA mode.
Never use an optimise-only rewrite to change the language contract.

The intended architecture is typed join declarations and operations, followed by
instance analysis and representation selection, then ordinary Rust MIR and
coroutine lowering. Preserve full join patterns until matcher specialisation.
Reuse existing futures, pinning, drop elaboration, and coroutine machinery for
reaction execution. See [optimisations versus LLVM](optimisations-vs-llvm.md)
for the backend boundary.

## What is already present

September 18 reply follow-up: the first-move approximation is replaced by an
executable MIR walk to rustc's own await boundary. Three newly added negative
cases were incorrectly accepted by the previous proof; the expanded nine-case
negative fixture now retains all public channel calls. The positive case
supports two named move aliases. Stage-1 native gates pass off/analyze/optimize.
See [the precise proof domain](joins-reply-consumer-proof.md). This closes that
local proof gap, not the full shared execution or instance-privacy gates.

Checkpoint update, 2026-09-18 at Rust commit `8398cbf0782`: Gates 1A/1B/1C
and 3 have a first conservative vertical slice. Generated direct adapters carry explicit
channel/rule coordinates and the descriptor query checks the one-rule unary
shape plus exact resolved ABI. Optimize-only fusion rejects scoped constructor
identity, candidate aliases passed to unsupported calls, projections/casts,
returns/yields, ordinary aggregates, or later call-result overwrites, and stale
concrete operands; the body dump records a machine-readable refusal. Direct
local copy/move/borrow flow and the exact reaction-body coroutine's own capture
are the only accepted alias propagation forms. Dynamic rule aliases bind to each rule's
cloned endpoint.
Fresh stage-1 off/analyze/optimize native runs pass the same-signature adapter,
aggregate-capture, cancelled-scope, and sync/async re-emission witnesses.
These are deliberately conservative fixes, not completion of the full gates:
complete source patterns, interprocedural candidate proofs, pass-wide proof
invalidation and shared semantic baseline remain open.

- Restricted isolated unary joins have zero-sized endpoints and caller-owned
  futures with declared outputs in all CFA modes. Preserve this behaviour.
- Typed endpoint descriptors, local analysis, constructor-origin propagation
  through direct helpers, and optional crate summaries exist.
- Ordinary MIR calls carry `JoinCall`; legacy marker statements are metadata
  with no executable operands. They survive optimised MIR and are removed at
  the SSA codegen boundary.
- A narrow optimise-only transform retargets a channel call to a generated
  `Reply::ready` adapter. Its current eligibility checks are insufficient for
  the claimed private-instance contract.
- Native HIR patterns, executable protocol MIR, general instance-sensitive
  proofs, and specialised shared matcher generation remain incomplete.
- LLVM receives ordinary lowered code, without join attributes or intrinsics.

Do not describe the current adapter rewrite as full intermediate-protocol
elimination. It leaves construction and other lifecycle work to subsequent
optimisation and has not established the complete shared semantic contract.

## Gate 0: capture a reproducible starting point

Record both repository revisions, local diffs, compiler binary hash/version,
sysroot, and test settings. A stage-1 binary reporting an unknown embedded commit
is not proof it contains the current source changes. Preserve unrelated edits,
including the existing AGENTS.md deletion and untracked files.

Use fresh output directories and the existing native fixture runner. Record
off/analyze/optimize separately. Archive relevant source, MIR, JSON, and actual
exit status. Use bounded execution for witnesses that would otherwise remain
pending; prefer manual poll checks over timeouts where possible.

Completion: the exact source/binary pair and baseline failures are recorded.
Do not interpret an old successful fixture run as validation of today's edits.

## Gate 1: close the current optimisation correctness gaps

### 1A. Associate adapters with exactly one channel

Review [descriptor collection](../compiler/rustc_passes/src/joins.rs): each
channel currently searches for the first `RustcJoinDirectAdapter` in its impl.
That marker does not encode the channel it implements. Consequently, multiple
channels can acquire the same adapter identity.

Encode an explicit channel/rule association and validate it against the group
definition. Check receiver, payload, result, ABI, and generic substitutions before
retargeting. Reject missing, ambiguous, or incompatible associations. Do not infer
the association solely from a generated method-name prefix or declaration order.

Required regression: a dynamic group with two result-bearing channels of the
same signature, but a unary rule for only one channel. A private request to the
unmatched channel must not execute the matched channel's adapter. Matching
signatures are essential to expose a semantic error independently of type errors.
Add differing-signature and declaration-order controls.

Completion: only the intended channel is eligible; unmatched requests preserve
their baseline pending/error behaviour in all modes, with no adapter call in MIR.

### 1B. Preserve scope, cancellation, and execution ownership

Review [the fusion consumer](../compiler/rustc_mir_transform/src/joins.rs),
especially `try_fuse_private_result` and `join_call_target_map`. Both `new` and
`new_in_scope` currently become `Constructor` edges. The generated adapter
executes immediately and returns `Reply::ready`, bypassing runtime scope checks,
executor submission, reply registration, and tracing.

Initially reject scoped construction. Retain the exact constructor identity in
the proof instead of relying only on an endpoint identity. Support for scoped
fusion requires a separate proof and lowering that preserves cancellation,
executor rejection, execution ownership, and observable accounting/tracing.

Required regressions, constructed inside an otherwise eligible reaction:

- Already-cancelled and closed scopes: the body must not execute successfully
  where baseline registration rejects it. Count body executions explicitly.
- A rejecting executor: preserve the rejection outcome and body execution count.
- A controlled executor that queues work: preserve its ownership and scheduling
  contract; avoid race-dependent timing assertions.
- Scoped tracing: keep the public path until its observability is preserved.

Unscoped construction is not by itself proof that immediate execution is valid.
Audit the synchronous trampoline and reentrancy behaviour too. Reject situations
where the baseline queues execution but the adapter executes immediately unless
equivalence is established.

September 18 follow-up: the nested-poll counterexample was reproduced (off
passes, optimize fails). Generated adapters now preserve the dispatch context
and use the original channel path when the synchronous trampoline is already
active. See [the regression and scheduling contract](joins-reentrancy-evidence.md).
This is a guarded runtime scheduling boundary, not a static proof that all
callers execute outside the trampoline. The full gate remains open for the
other policy and reply-consumer cases listed here.

Completion: MIR confirms rejection of unsupported policies and behaviour matches
across all modes. If the supported domain cannot yet be stated and enforced
precisely, disable this rewrite until the next gate is complete.

### 1C. Prove privacy of the actual candidate instance

The current endpoint escape summary is based on the enclosing endpoint type;
the candidate inner group can have a different type. Ordinary local helper
calls are not sufficient evidence that its handles remain private. The narrow
consumer now builds a candidate-alias use set from the actual constructor
result, rejects unsupported local uses (including projections/casts,
returns/yields, ordinary aggregates, indirect calls, and call-result
overwrites), and permits only direct local propagation plus the reaction's own
coroutine aggregate. This closes the intraprocedural use-domain hole; it does
not replace the crate-level instance proof or establish interprocedural
ownership.

Build an explicit candidate-instance use set from the constructor result.
Account for copies, moves, borrows, projections, captures, storage, returns,
clones, and calls. Treat every unsupported use as rejection. For an initial
small domain, reject any helper/callback receiving an instance alias instead of
trying to establish general interprocedural safety immediately.

Similarly, one immediate move of a reply does not prove its eventual use is an
await. Track its consumers through the supported chain, including borrows,
calls, drops, aggregate storage, suspension, and return. Preserve the specified
drop and cancellation behaviour.

Required negative fixtures:

- A helper clones or publishes the candidate endpoint.
- An endpoint or borrowed handle is captured by a closure or stored in an
  aggregate; include projected accesses.
- A helper issues another invocation on the same group.
- The reply is moved through a temporary and then passed to a helper, returned,
  stored, or dropped without polling.
- Construction/channel execution repeats in a loop, or aliases merge across
  branches or several constructor sites.
- Generic substitutions, indirect calls, and cross-crate calls outside the
  supported domain.

Keep a positive witness and show why every use is supported. Unknown effects
and exhausted analysis must reject, with an explicit reason. An allocation site
labelled `Unique` is not proof that only one dynamic instance exists.

Completion: an auditable proof explains the instance, all relevant uses, policy,
and consumer. Negative cases retain the original call. The transform must not
silently accept a case because an escape category was never collected.

## Gate 2: make proof validity and metadata scope explicit

The uncommitted `join_mir_fingerprint` hashes instruction kinds and counts, but
omits actual successor identities, many operands/constants, and local types.
It also reuses previously extracted facts when checking freshness. It cannot
certify arbitrary intervening MIR changes.

For the initial transform, analyse and consume the proof within one controlled
phase, with no intervening mutations. Separate diagnostic snapshots from proof
objects. If a later consumer is needed, use explicit invalidation/reanalysis or
a fully specified revision mechanism maintained by every relevant mutation.
A partial structural hash must not authorise rewriting.

Before rewriting, verify the current callee, operands, destination, types,
substitutions, and normal/unwind edges against the proof. After rewriting,
invalidate or refresh affected summaries and descriptors. Old source locations
may remain diagnostic coordinates, but must be labelled as such.

Required tests include changing branch destinations without changing successor
counts, replacing an operand/callee, local renumbering, and inlining/cloning.
Each must either invalidate the proof or trigger fresh analysis. Test this at a
controlled compiler boundary; do not merely assert that a hash field exists.

For legacy markers, enforce the operand-free invariant in validation. Do not
leave populated Place/Operand fields that visitors ignore. Distinguish remappable
DefIds from raw local indices when encoding/importing summaries.

Completion: no optimisation consumes stale facts, and diagnostics identify the
snapshot to which they refer. Update the older fingerprint claims accordingly.

## Gate 3: repair dynamic multi-rule capture generation

The working-tree expansion creates `__join_rule_endpoint`, but generated alias
closures still reference `__join_endpoint`. Wire each rule's aliases to its own
capture using a deliberate binding/AST representation. An unused clone does not
fix a moved outer capture.

Required fixture: at least two rules that each re-emit through their own endpoint
aliases. Include both synchronous and async bodies as supported. Check repeated
execution as well as compilation, without changing selected execution policy.

Completion: every closure owns the intended handle, and re-emission works in all
modes. Keep this independent frontend fix reviewable separately from fusion.

## Gate 4: preserve complete patterns as compiler-owned data

Current `JoinRule` describes the generated dispatcher, not every source rule.
One dispatcher can contain multiple patterns, so its enumerated index is not a
source-rule identity. Counts and arity cannot drive matcher generation.

Introduce authoritative group/channel/rule definitions with:

- Stable typed identities, source spans, and generic substitutions.
- Channel payload and reply types, distinguishing one-way emission from a
  request returning `()`.
- A distinct entry for each source rule: participating channels, bindings,
  reaction body, and channel-to-result mapping.
- Execution/admission/demand/cancellation policy or explicit references to it.
- Enough information to derive competing rules and legal atomic claims.

Native HIR declarations should own these identities. A transitional descriptor
is acceptable only if it preserves the complete source structure and is produced
directly by the frontend, rather than reconstructed from generated method names.
Carry typed invocation information through typing/THIR into MIR construction.

Required tests: multiple competing patterns, mixed one-way/result channels,
several replies, declaration reordering, nested definitions, generics, and
cross-crate identity where supported. Unsupported cross-crate analysis must
decline optimisation rather than reconstruct local identities.

Completion: a compiler dump can reconstruct the full pattern set without parsing
runtime calls or generated strings. Each rule/body/reply mapping is unambiguous.

## Gate 5: introduce executable join operations and a lowering boundary

Define the semantic operations before selecting their exact MIR encoding:

| Operation | Information and effects that must be explicit |
| --- | --- |
| Create group | Static definition, dynamic instance, captures, scope/policy |
| Emit/register request | Instance, channel, payload moves, admission outcome, optional reply ownership |
| Demand/poll | Invocation/reply, context/waker, progress and pending/ready outcomes |
| Claim | Full pattern, atomic input consumption, competing-rule selection, reaction ownership |
| Complete replies | Claimed invocation capabilities, typed outputs, exactly-once completion |
| Withdraw/abandon/cancel | Identity, pre/post-claim state, cleanup and shared cancellation policy |

Ordinary function calls and registration must remain distinguishable. One-way
emission and request registration can share an operation family if reply semantics
are explicit. Do not label all future construction as shared registration.

Choose dedicated MIR forms or compiler-recognised operations with defined
semantics. Preserve real operands exactly once. Effectful operations need proper
normal, failure, unwind, and cleanup behaviour; a metadata no-op is insufficient.
Retain complete patterns through analysis and representation selection.

Specify how borrow checking, move analysis, drop elaboration, MIR validation,
coroutine transformation, interpretation, and each backend handle the new forms.
Either teach ownership analysis their semantics or lower to an ownership-faithful
representation at an explicit boundary while retaining the necessary semantic
identity. A post-borrowck annotation cannot create missing lifetime guarantees.

Use existing coroutine bodies for reaction suspension. Define a `LowerJoins`
boundary that produces ordinary MIR early enough for required drop/coroutine
processing; keep analysis-only metadata separate from executable operations.
Only metadata may be erased without code generation.

Before expanding this layer, consider the current `TerminatorKind` increase from
80 to 136 bytes. Compare a boxed descriptor or compact handle and measure compiler
memory/time on ordinary code as well as joins. This is a representation cost,
not a reason to omit semantic information.

Completion: ownership and protocol tests pass, actual operations appear at their
execution points, and supported backends receive fully lowered code.

## Gate 6: establish shared semantics before shared optimisation

The compatibility path currently submits and dispatches from channel methods.
It does not establish the accepted demand-gated shared contract merely because
the reply implements Future.

Implement the same semantic baseline in off/analyze/optimize. Validate immediate
registration separately from execution demand; complete atomic matching;
one-way-only rules; independent reply waiters; unmatched withdrawal; post-claim
abandonment; selected all-consumers-gone policy; panic/failure and executor
rejection; admission rollback; and local versus cross-thread lifetime bounds.
Include forget/leak scenarios when assessing borrowed shared support.

Completion: behavioural witnesses establish the accepted contract before any
shared optimisation claims rely on it. Preserve the already-working isolated
unary contract as a separate case.

## Gate 7: consume instance proofs to select representations

Extend the existing helper-flow analysis deliberately. Record whether results
are context-sensitive, which paths/callers are covered, and whether iteration
limits or unknown effects prevent a proof. Keep allocation-site uniqueness,
dynamic cardinality, closedness, queue bounds, and storage lifetime separate.

Start with one closed forwarding witness. Derive a complete proof and lower away
the intermediate protocol. Then progress to bounded slots, specialised pairs,
and generated bitfield/matching code using preserved patterns. Each representation
requires its own semantic and resource proof. Stack storage additionally requires
a lifetime proof. A frontend queue hint is not a hard capacity guarantee.

Completion for each optimisation:

1. Positive and negative semantic fixtures pass in every mode.
2. A proof/rejection record explains the decision for the concrete instance.
3. MIR demonstrates the intended transformation; LLVM inspection confirms which
   allocations, dispatch, atomics, or other costs actually disappeared.
4. Matched benchmarks include construction, execution, and destruction as
   relevant, with raw results and equal executor/semantic policies.

Do not interpret module-wide IR line/atomic counts as dynamic performance, and
do not attribute old off-versus-optimise unary measurements to the current
mode-independent representation. Re-run the specific comparison when its
lowering or semantic baseline changes.

## Handoff requirements

Land or report correctness fixes in small, independently testable slices before
representation work. Use focused compiler checks and the native runner; batch
stage-1 builds and avoid unrelated application rebuilds. Move enduring regressions
into the compiler suite where practical, retaining real-runtime integration
tests for the protocol contract.

For each gate, update the checkpoint with source and binary identity, commands,
results, supported domain, rejection cases, and remaining limitations. Keep
`JOINS-SUMMARY.md`, the next-slice specification, and this plan consistent.
Do not mark a gate complete based solely on adding metadata or finding a marker
in optimised MIR.
