# Execution specification: authoritative join MIR and first result fusion

The paired private-storage implementation is now validated in all three native
modes and in a fresh 30-block lifecycle benchmark. Forwarding is 483.45/489.10/
30.43 ns/op off/analyze/optimize, with 11/11/0 allocation calls. **Start at
[the handover](joins-private-storage-handover.md)** for the remaining profiling
and negative-coverage gates; do not widen the proof domain yet.

Latest immediate-await proof and all-mode native gates passed. The follow-up
[lifecycle run](joins-forwarding-private-storage-20260918/summary.md) measures
the validated private-storage path. Next is LLVM/hot-path attribution and
negative coverage; do not widen eligibility before those gates.

September 18 measured follow-up: the guarded private forwarding path is now
472.30 ns/op off, 476.74 analyze and 89.85 optimize, including construction and
drop (30 randomized blocks). Allocation probes count 11/11/2 calls per op.
See [the committed raw evidence](joins-forwarding-20260918/summary.md) and
[the reproduced/fixed scheduling regression](joins-reentrancy-evidence.md).
Prioritize the following bounded slice before expanding the eligible domain:

1. Completed the narrow immediate-await reply-consumer proof and negative
   witnesses. See [proof and gates](joins-reply-consumer-proof.md). Sequential
   moves must lead to rustc's await desugaring; helpers, borrowing, storage,
   returns, drops, branches and explicit user-written `into_future` refuse.
   General interprocedural reply-consumer analysis remains open.
2. Preserve the scheduling guard in any constructor elimination. The existing
   adapter needs a real endpoint on its nested-dispatch fallback. Hoisting or
   sinking construction requires a proof that admission, drop and panic
   effects remain equivalent on both paths. Do not merely delete `new`.
3. Represent the complete group/policy and allocation instance at that
   decision, then eliminate private matcher setup on the proven inline path.
   Leave unproved/shared cases on the existing implementation.
4. Require the same native gates, one explicit rewrite record, zero allocation
   calls on the proposed direct path, and a fresh randomized lifecycle
   comparison. Preserve the two-allocation result as the pre-change control.
   Compare LLVM/assembly for surviving allocation, reference counting and
   dispatch before proposing another pass.

Implementation order update, 2026-09-17: follow the correctness gates in
[the review implementation plan](joins-review-implementation-plan.md) before
extending fusion or shared matcher specialisation. It identifies gaps in adapter
association, scope preservation, instance privacy, and the snapshot fingerprint
described below. Earlier completion claims here do not establish those gates.

Updated 2026-09-18 at Rust commit `8398cbf0782`, after `c53d044d913`. Steps 1 and 2's call carrier, the mode-independent unary
contract, and the first result-channel forwarding rewrite are implemented on
the working branch. The review safety gates for adapter identity, scoped
construction, candidate-instance aggregate escapes, concrete operand checks,
and dynamic rule captures are also implemented and covered by fresh native
runs. The remaining steps below are deliberately narrower:
typed cross-crate identities, a complete certificate/rejection domain, and
shared/fixed-storage optimisation.
This document is the immediate implementation order, superseding conflicting
sequencing in earlier IR plans.
The companion library's `docs/async-join-semantics.md` is the language contract;
its `JOINS-IMPLEMENTATION-HANDOVER.md` retains the longer research programme.

## Deliverable and current evidence

Deliver one compiler-produced elimination of an intermediate result channel,
with identical source semantics in off/analyze/optimize modes, an explicit CFA
certificate, rejected counterexamples, MIR/LLVM evidence and matched timings.
The scalar witness is now present; it remains a deliberately small forwarding
rewrite and is not yet the general JCAM fusion pass.
Do not mark this complete for adding metadata, choosing an expansion by mode,
or retaining a manually selected fused runtime implementation.

Baseline: rust `b967581afa1`, library `56f38dc`. The native suites passed and
markers survived optimized runtime MIR. Since that baseline, the first IR
slice has removed duplicate operand visitation, moved call-site identity onto
the real `Call` terminator, and made the storage strategy conservative. This
still establishes neither correctness under every MIR transformation nor
general compiler-driven fusion. Remaining limitations are:

- `JoinCall` now carries a group `DefId` plus typed channel/rule coordinates,
  alongside transitional endpoint/rule `DefId`s for old dump readers. Full
  typed policy, substitutions and cross-crate import/remapping are not yet
  authoritative.
- `Body::join_info` still describes an earlier body and is not a current proof
  after inlining, local renumbering, CFG rewriting or coroutine transformation.
  Each summary now carries a deterministic structural `mir_fingerprint`, and
  the result-fusion consumer refuses a changed snapshot. This is a conservative
  local freshness guard, not yet a pass-wide revision/certificate protocol:
  fingerprints do not replace re-analysis after every transformation and do
  not by themselves provide cross-crate type or policy evidence.
- Isolated unary expansion is now mode-independent: the direct endpoint is a
  zero-state caller-owned future with the declared `Future::Output`, including
  borrowed and non-`Send` local cases. Shared operation forms remain
  operand-free compatibility metadata.
- A narrow optimize-only consumer now retargets one proven monomorphic result
  call to a compiler-private inline-ready adapter. It requires one constructor,
  one channel, unique local alias flow, a verified immediate-await reply path and no known
  competing join edge. It also requires the unscoped constructor identity,
  rejects endpoint aliases passed to unsupported calls, projections/casts,
  returns/yields, ordinary aggregates, indirect calls, or later call-result
  overwrites, validates the concrete call operands, and records an explicit
  `fusion_rejection` when the proof is declined. It does not yet remove the
  explicit `Reply` await or prove all JCAM cancellation/admission conditions.

This is the owner's explicitly authorized AI-written research fork. No upstream
review is requested; any upstream proposal would be separately rewritten by hand.
All compiler subsystems are available. Preserve type, ownership and concurrency
soundness. Never replace recognized protocols with library locks. Ordinary
fields, futures, atomics and CAS are permitted implementation mechanisms.

Known join calls are annotated in ordinary and async caller bodies as well as
generated join bodies. This keeps a source registration visible on the real
caller-side Call terminator; generated channel bodies also carry their typed
source channel index on the Register operation.

## 0. Inventory and capture the failing gates

Record git status/revisions, compiler binary hash and remotes before editing.
Preserve the existing builtin-macro capture patch and AGENTS.md deletion; do not
stage them incidentally. Build only after a coherent set of changes is ready.

Read these implementation points first (paths relative to rust):

| Area | Entry point |
| --- | --- |
| Current expansion | `compiler/rustc_builtin_macros/src/joins.rs` |
| Group descriptors | `compiler/rustc_passes/src/joins.rs` |
| Analysis and strategy labels | `compiler/rustc_mir_transform/src/joins.rs` |
| Definitions and summary types | `compiler/rustc_middle/src/middle/joins.rs` |
| MIR representation and visitation | `compiler/rustc_middle/src/mir/{syntax,visit}.rs` |
| Query forcing | `compiler/rustc_interface/src/passes.rs` |
| Pass ordering | `compiler/rustc_mir_transform/src/lib.rs` |
| Current erasure | `compiler/rustc_codegen_ssa/src/mir/mod.rs::lower_join_markers` |

Create tests before claiming the fixes below: duplicate move/store visitation;
two requests outstanding on one instance; two instances from one constructor
site; changed/inlined body rejecting an old proof. Record the observed failures.
Do not reintroduce `optimized_mir` scans over all `mir_keys`.

## 1. Remove false authority from transitional metadata

1. Remove fixed-storage selection based only on `solve_body_occupancy`. Keep
   those numbers explicitly named `body_interval`, useful as analysis inputs.
   Rename existing strategy output to `candidate` or remove it. No candidate
   grants permission to remove queues, synchronization, drops or executor work.
2. Remove duplicated operand-bearing no-op statements. During migration, keep
   historical diagnostic summaries separate from authoritative executable MIR.
   Do not solve duplicate moves by reporting all operands as copies: this still
   changes liveness and cannot describe a consuming operation.
3. Move the annotation to the actual call terminator as specified in step 2.
   Operand and destination visitation then occurs exactly once. Remove entry
   markers that pretend CompleteReplies happened before the body ran.
4. Keep snapshot block/local numbers only for diagnostics of that snapshot.
   Invalidate attached proof data before ordinary transformations. Regenerate
   proofs from current executable operations when running the fusion pass.

Gate status: passed by the stage1 compiler check and native MIR dump. The
visitor no longer reports descriptor operands a second time, and method-local
occupancy cannot select a fixed slot or pair matcher. Drop counters and unwind
fixtures still pass. The exact cross-crate typed-definition gate remains open.

## 2. Authoritative operation carrier and typed group definition

Use a single optional `join` descriptor on `TerminatorKind::Call` for this slice
(update call constructors and exhaustive patterns). This is the chosen minimal
carrier: ordinary Call supplies the actual function, typed arguments,
destination, return target, unwind action and call source. Keep its descriptor
through optimized MIR and into LLVM-facing codegen. Do not duplicate operands
in the descriptor. Tail calls involving joins are unsupported in the first
slice and must receive a diagnostic or conservative lowering.

The descriptor must contain:

- `group: DefId`, generics represented by normal typed substitutions;
- `channel`/`rule`: typed indices within that group definition, not local DefId
  integers; each rule also has its own resolved body DefId;
- `operation` from the table below, argument-role indices and reply mapping;
- placement/lifetime/admission policy from the typed group;
- source span and source operation identity for diagnostics only. Inlining
  clones a source identity; never treat it as dynamic instance identity.

Validate every role index and argument/destination type when constructing MIR.
Unknown roles/effects prevent specialization. Ordinary function calls have None.
Generated operation functions are identified by a compiler-owned
`#[join_direct_adapter]` marker and the resulting method `DefId`, never by
helper spelling. Import descriptors through rustc's normal `DefId` remapping.
Construct these operations in every mode. Off disables optional CFA/rewrite,
analyze computes facts without consuming them, optimize consumes checked proofs.
Mandatory correct lowering does not depend on mode or analysis budget.

The typed group query must record each channel's payload/reply types, each
rule's full multiset of channel inputs, binding order, body, reply mapping,
competition, captures and policies. Preserve AST bodies, hygiene and spans.
For the first unary path, migrate that path out of string reconstruction; leave
unmigrated shared paths explicitly classified as legacy and ineligible.

| Operation | Arguments/result and ownership contract |
| --- | --- |
| Create | Moves captures into a group; destination initialized on success only |
| RegisterRequest | Group plus moved payload; creates reply future; shared admission returns original payload on failure |
| Emit | Group plus moved payload; no reply capability; distinguish from request returning unit |
| Demand | Pinned reply and Context borrows; returns Poll; body runs only here or under the selected shared owner |
| Claim | Complete eligible input set consumed atomically; returns unique claim or no match |
| Execute | Consumes claim/body inputs into exactly one ordinary body or future owner |
| Complete | Consumes result values/reply rights once; publishes each named reply and wakes independent waiters |
| Withdraw/Abandon | Unmatched request withdrawn atomically; matched consumer abandons only its reply |
| CancelScope | Applies the recorded scope contract at defined cancellation points |

For unary, Create/RegisterRequest/Demand and ordinary drop cover the first
executable path; there is no fictitious Claim for a queue that does not exist.
Shared operations remain unsupported by fusion until each contract is present.

The ordinary called function is the canonical executable lowering, including
ownership/drop/unwind semantics, not a second call beside a semantic instruction.
Borrowck, const evaluation and generic codegen can therefore execute/check its
normal ABI. Specialization replaces this operation and its lowering together.
LLVM consumes surviving descriptors while emitting the canonical calls. Never
erase an effectful call as if it were a no-op marker. Other backends may use the
canonical call; if no valid fallback exists, issue an unsupported diagnostic.

Audit inlining: preserve annotated operation boundaries until the join pass has
consumed them, or explicitly transfer descriptors to the replacement operations.
Once consumed, ordinary inlining is free to optimize the generated computation.
An annotation that outlives its associated call cannot authorize a rewrite.

Gate status: partial but executable. Optimized MIR prints the descriptor on the
real call, with actual call operands and no operand-bearing duplicate marker;
ordinary/async caller bodies receive the same descriptor when they contain a
known join call, and generated channel bodies expose their source channel
coordinate on the Register operation.
The descriptor also carries the frontend queue/storage bound as a conservative
fact; it never authorizes a fixed slot without a concrete instance proof.
codegen clears it only at the backend boundary. The descriptor now records the
group identity and typed channel/rule coordinates, plus an optional body-local
fusion witness. Cross-crate remapping, full ownership policy and native shared
operation forms are still open.

## 3. Establish isolated unary semantics in every mode

Create `joins-library/compiler-tests/joins_unary_contract.rs`. First witness:

```rust
join impl Step {
    channel step(x: u32) -> u32;
    async when step(x) {
        return { step: x + 1 };
    }
}
async fn control(x: u32) -> u32 { x + 1 }
```

Require `Step::new().step(41)` to implement Future<Output = u32>. Compare it
against control using stack pinning. No universal Result<T, JoinError>, allocation,
Send, 'static or pool requirement may be added to this isolated case. Application
Result outputs remain exactly the declared Result. Panic unwinds through poll.
Choose caller ownership for isolated default unary rules in all three modes.
Explicit executor/scope placement is a separate policy and excludes this rewrite.

The direct unary lowering is itself an ordinary opaque future: construction
captures the payload without running the body, and polling drives the generated
future. The direct endpoint is zero-sized (including generic `PhantomData`),
has no matcher/reply allocation, and does not add `Send`, `'static`, pool or
`JoinError` requirements. Existing shared/multi-input forms retain the matcher
and their distinct registration-before-demand semantics. Thus off, analyze and
optimize have the same unary contract even with zero analysis budget.
Do not preserve eager execution as the off-mode baseline.

Extend the fixture with: side effects absent before poll; drop before poll;
PendingOnce that wakes once and completes on the second poll; drop after Pending;
String/DropProbe payloads dropped exactly once; borrowed payload with an actual
source lifetime parameter; Rc payload; application Err; catch_unwind around poll.
Run matching ordinary async controls and compare event sequences. Borrow escaping
its owner must fail normal borrowck; local non-Send futures must compile.

Gate: passed for the current contract witness in off/analyze/optimize, including
budget zero. The fixture covers deferred side effects, Pending+wake, drop before
poll, non-`Send` `Rc`, borrowed input, application `Result` and panic unwinding.
Keep expanding it with post-Pending drop and explicit ordinary-async trace
comparisons. Update the old optimize-only fixture and delete obsolete claims.
Keep shared registration-before-demand semantics separate: do not delay shared
registration just because unary uses an ordinary captured future.

## 4. First result-channel fusion witness and bounded CFA

Create `joins_fusion_result.rs`; the checked first witness uses a static inner
endpoint with an extra one-way channel so its public `step` call remains on the
shared compatibility matcher until the compiler rewrites it:

```rust
join impl Inner {
    channel step(y: u32) -> u32;
    channel notify();
    when step(y) {
        return { step: y + 1 };
    }
}
join impl Outer {
    channel run(x: u32) -> u32;
    async when run(x) {
        let inner = Inner::new();
        let reply = inner.step(x);
        let result = reply.await.expect("private inner reply");
        return { run: result * 2 };
    }
}
```

Acceptance: run(20).await = 42 and matching poll/drop/effect sequences. First
version is scalar, caller-owned, isolated inner reaction, acyclic and
intraprocedural in the outer reaction body. This is result-forwarding fusion; it
does not establish shared multi-input fusion. The optimize MIR gate now shows
`Inner::step` in off/analyze and `Inner::__join_direct_step` in optimize, with a
`fusion.rewritten=true` body certificate. A second fixture must replace the
inner body with PendingOnce and prove that the suspension boundary is retained.
Existing explicit-continuation examples are additional tests, not substitutes
for this result-bearing witness.

Implement CFA over the current pre-coroutine body using rustc CFG/worklist
infrastructure. Domain per local: Bottom, finite set of origins (maximum 8), Top.
Origin = construction location within analysis context; track multiplicity
separately as Zero/One/Many/Unknown. Joins union sets; overflow becomes Top.
Moves transfer identity and kill the old binding; copies/borrows create aliases.
Inspect all uses before killing bindings so escape facts persist on the origin.
Unknown calls, aggregate/capture escape, indirect calls and unavailable bodies
mark the affected origin escaped/unknown. Propagate argument and return aliases
through at most one direct local helper context; recursion widens to Unknown.
Reject construction/use in CFG cycles for the first rewrite. One allocation
site inside a loop never proves a single live instance.

Use the existing analysis budget; every worklist transfer consumes a unit.
Exhaustion produces Unknown and zero dependent rewrites. Unrelated unknown facts
may remain, but every dependency of an accepted certificate must be complete.

Accept only if all these checks hold:

1. One construction reaches the request and dominates it; exactly one live
   instance and one invocation, no escaping handle or reply.
2. Exactly one rule/input/reply and no competition, external producer or re-entry.
3. Caller-owned policy, infallible isolated construction, no observable admission,
   tracing-allocation, scope, executor or group-drop effect would be removed.
4. Reply is moved once into an explicit await and does not escape through another
   call, storage location, spawn or independently observable consumer.
5. Known ordinary reaction body and all captures remain valid for the fused
   future; normal moves and source evaluation order are preserved.
6. Effects inside the body are preserved verbatim; Pending, waking, panic and
   destruction are not assumed pure or erased.

Emit candidate/proved/rewritten counts per source operation, distinct from
dynamic hits. Refusal codes: UnknownOrigin, MultipleInstances, Escape,
CompetingRule, SharedPolicy, AdmissionEffect, ObservableGroupEffect,
UnsupportedUse, RecursiveOrCyclic, UnknownCallee, Budget, StaleProof.

## 5. Certificate consumer, pass ordering and exact rewrite

Place JoinSpecialize after borrowck and analysis normalization, before drop
elaboration and coroutine StateTransform. This is a choice for this rewrite's
need to manipulate owned futures; it is not a requirement to erase all joins
there. Unconsumed operations/descriptors survive runtime and optimized MIR to
LLVM-facing lowering as requested.

Analyze and consume the same owned body in one pass invocation. The certificate
names body DefId, generic context, operation locations, origin, policy, complete
dependencies and a body revision/fingerprint. Check it immediately before the
rewrite. Any changed operand/CFG/policy invalidates it. Do not use the old
Body::join_info snapshot or unchecked cross-crate summary as authority.

Current implementation status: `JoinSemanticOps` performs a conservative
optimize-only call-target rewrite in the pre-cleanup body.  It consumes a
typed summary containing one constructor edge, one channel edge, unique
copy/move/borrow alias flow, one consuming reply move, and the channel's
compiler-owned `direct_method_def_id`.  The rewrite changes only the existing
MIR call's function operand to the private `Reply::ready` adapter; arguments,
destination, unwind edge and the explicit `.await` remain intact.  The body
summary records `fusion.rewritten=true`, and the native MIR gate checks the
  summary's MIR fingerprint immediately before the rewrite; a stale summary is
  rejected without mutating the call. The native MIR gate checks the off/analyze
  versus optimize call targets.  This is a real proof-gated result forwarding
  step, but not yet the full certificate described below: it does not remove
  the inner constructor or reply state. Failed optimize attempts now record a
  machine-readable `fusion_rejection` in the body summary, using the same
  refusal vocabulary as the later matrix; coverage of every negative witness
  and pass-wide invalidation is still pending.

For the first witness, replace construction/request/wrapper protocol with the
ordinary reaction future construction and the existing await of that future.
Remove the proven-dead inner group and intermediate reply ownership state.
Move x exactly once; preserve source order and source scopes. Keep inner body
code, wake behaviour, unwind targets and drop scopes. Generate ordinary
coroutine construction/polling and let normal drop elaboration and coroutine
lowering produce frames. No hand-written state machine or lock helper.

Use one mode-independent nominal wrapper `UnaryReply<F>` containing F, with
Future::Output = F::Output. Its poll delegates to the structurally pinned inner
future; ordinary drop owns F. Do not add an independent completed flag or panic
translation. Prefer normal compiler-generated projection machinery; any manual
pin projection needs a documented invariant and regression coverage.

For the first type-preserving rewrite, inline the proved wrapper construction
and delegating helpers using existing MIR inliner remapping, substitute their
aggregate construction/projection uses, and let existing scalar replacement
and dead-local cleanup eliminate intermediate storage. Keep declared local and
opaque return types valid; a nominal wrapper type may still appear in signatures
after its runtime storage has disappeared. If coroutine poll inlining is only
available after StateTransform, split selection from that final substitution:
carry the selected operation into runtime MIR, revalidate current operands and
ownership there, and perform the substitution before ABI attribute deduction.
Do not reuse pre-coroutine block/local indices as runtime proof locations.
Do not force-inline arbitrary user bodies or add a public inline annotation.

Never patch an opaque future's type after borrowck or change an already computed
frame layout. If existing inlining cannot express the substitution, extend its
type-preserving machinery and test that extension before enabling the consumer.
No arbitrary semantic rewriting is allowed in codegen after parameter/ABI
attributes have already been deduced; only the descriptor is erased there.

Gate target: pre/post MIR shows the exact consumed operations; optimized IR contains
ordinary future/body computation and no inner group/reply runtime calls. Run
with MIR validation after passes. With zero budget the canonical lowering
remains valid and rewritten=0. Renaming channels changes neither decision nor
result. If ordinary inlining already eliminates the entire wrapper in off mode,
report zero incremental speedup honestly; do not obstruct normal optimization
to manufacture a baseline gap. Still prove that the join pass consumed its
certificate and eliminated the specified semantic operations.

## 6. Required rejection and regression matrix

Add separate fixtures under `compiler-tests` and compiler UI/MIR tests as
appropriate. Each rejection asserts the refusal code and zero affected rewrites;
it must still run correctly through canonical lowering if the source is legal.

| Witness | Required result |
| --- | --- |
| Result chain, ready and PendingOnce | Equivalent traces; one intermediate instance fused |
| Returned handle / captured handle / stored reply | Escape or UnsupportedUse |
| Two live instances from one constructor site | MultipleInstances or RecursiveOrCyclic |
| Competing rule sharing the input | CompetingRule |
| Explicit executor or scope ownership | SharedPolicy |
| Fallible admission or observable group destruction | AdmissionEffect / ObservableGroupEffect |
| Function pointer / recursive helper / unknown foreign callee | UnknownCallee / RecursiveOrCyclic |
| Budget zero and small exhausted budget | Budget, zero dependent rewrites |
| Mutate body between proof and consumer in unit test | StaleProof |
| Same local indices in two crates, generic instantiations | Correct DefId/type remapping, no proof collision |
| Ordinary async crate, statics, consts, incremental rebuild | No ICE or joins-induced semantic change |
| Non-Copy payload, panic, cancellation before/after Pending | Same exact drop/effect counts as async control |

Shared semantic regression controls must also keep register-all/await-one,
independent reply wakers and cancellation-versus-claim behaviour. Legacy failing
cases stay explicitly open; never use them to claim shared fusion is complete.

## 7. Reproducible verification and timing

Existing commands (from workspace root); use explicit per-fixture timeouts in
the new runners. A failed build/test stops the dependent gate.

```sh
cd /root/join-rust/rust
./x check compiler/rustc_mir_transform compiler/rustc_codegen_ssa --stage 1 -j 2
./x build compiler --stage 1 -j 2
./x build library --stage 1 -j 2
cd /root/join-rust/joins-library
cargo test --offline --workspace
JOIN_CFA_MODE=analyze bash compiler-tests/run_native.sh
JOIN_CFA_MODE=optimize bash compiler-tests/run_native.sh
```

Rebuild library only when the compiler/sysroot compatibility requires it. Do
not run full builds for documentation-only changes. New scripts to implement:

```sh
bash compiler-tests/run_ir_slice.sh --modes off,analyze,optimize --budget default
bash compiler-tests/run_ir_slice.sh --modes analyze,optimize --budget 0
bash compiler-tests/run_ir_slice.sh --modes optimize --budget 1
bash compiler-tests/run_ir_slice.sh --modes optimize --incremental-twice
bash compiler-tests/bench_ir_slice.sh --blocks 30 --min-block-ms 100 --seed 1709
```

These commands are proposed interfaces, not existing successful runs. The IR
runner must build dependencies once per compatible compiler, compile/run all
positive fixtures, check negative diagnostics/refusals, validate MIR, compare
event traces against ordinary async, and save commands, exit codes, JSON proof
records and before/after MIR. Inspect JSON structurally, not regexes across
nested arrays. Include an LLVM IR emission for the positive fixture.

Benchmark direct function, ordinary async, unary join and result chain in each
mode. Same compiler, release flags (`-Copt-level=3 -Ccodegen-units=1 -Clto=off`),
unwind policy, inputs and caller-driven executor. Separate ready, PendingOnce,
construction/drop, and complete lifecycle. Use black_box on inputs and outputs;
check checksums outside timing. Build everything before timing. Run 30 randomized
paired blocks, each at least 100 ms; calibrate batch size before measurements.
Report median ns/op and paired bootstrap 95% intervals for ratios, with raw rows
and seed. Repeat a claimed material win independently. <=1.1x parity requires
the ratio interval upper bound <=1.1. No requirement to fake a speedup if LLVM
already removed the overhead. Count allocations, polls and wakes separately
outside timing; no profiler access means no claimed flamegraph attribution.

Commit scripts, compact evidence and an updated rust/JOINS-SUMMARY.md. Evidence
manifest must name source commits plus any dirty patch, binary hashes, commands,
policy, expected and observed site counts, and all open gates. Push rust commits
to prc33/joins; library commits remain local until a remote is provided.

## 8. Next slice after result fusion: fixed storage

Do not implement a fixed pair slot from method-local peak counts. Build a
per-instance transition system: available messages, demanded requests, claimed
inputs, suspended reactions and their possible emissions, cancellation and
admission credit. A bound must include every external producer and in-flight
owner. For the first proof restrict to a closed one-token protocol, no unknown
producer, one owner and finite states; exhaustively compare reachable states
against the analysis. Unknown/truncated analysis selects generic storage.

Only then lower a proven 0/1 channel to an initialized flag plus owned payload
slot, with exactly-once drop; no dynamic growth fallback. Stack/frame placement
needs a separate lifetime/escape proof, including forget. Shared atomic state,
publication, ABA/reclamation and waiter races need their own protocol and model
tests before concurrent fixed slots. General CAS lowering and DataFusion follow
this evidence, retaining the larger handover's gates.

## Completion checklist

- [x] 1: duplicate effects removed; misleading storage proof labels corrected.
- [ ] 2: authoritative typed call operations, remapping and ownership gates pass
      (call carrier and local group/channel coordinates are in place;
      cross-crate substitutions and full policy are pending).
- [x] 3: isolated unary semantics equal across modes and ordinary async controls
      for the current direct unary contract (shared/multi-input controls remain).
- [ ] 4: bounded CFA accepts and rejects the named witnesses with reasons.
- [ ] 5: a complete checked certificate drives the actual result-channel MIR
      rewrite (the narrow adapter rewrite is an executable partial gate).
- [ ] 6: negative, drop/unwind, incremental and cross-crate regressions pass.
- [ ] 7: committed IR, allocation and timing evidence; fork summary updated.

Evidence for this slice: rust stage1 `./x check compiler --stage 1 -j 2`,
`./x build compiler --stage 1 -j 2`, `./x build library --stage 1 -j 2`, and
`JOIN_CFA_MODE=optimize JOIN_CFA_DUMP=... JOIN_MIR_DUMP=... bash
compiler-tests/run_native.sh` all passed on 2026-09-17. The optimized witness
contains `Inner::__join_direct_step` on the rewritten call and a JSON
`fusion.rewritten=true` certificate; off/analyze contain `Inner::step`. The
dump also retains descriptors such as `join::Match` on ordinary calls and no
operand-bearing semantic marker.

Commit each passing slice. Continue to the next gate without commissioning a
separate slow review; do a substantial review after the proof-consuming rewrite.
No checklist item is complete merely because the compiler builds.
