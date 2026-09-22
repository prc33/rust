# NEXT: analysis-driven shared join specialization

Current review and immediate sequencing: [2026-09-20 assessment](joins-review-20260920.md).
It supersedes the next-step/completion claims below: validate one endpoint-wide
lowering plan and ABI contract, resolve cancellation ownership, then archive clean
paired timings before selecting further storage changes. The 187.71 ns/op mutex
result used instrumentation-enabled binaries with counters disabled and remains
provisional; a state-token bound does not establish a reply-queue bound.

Date: 2026-09-20. **This is the next execution plan. Start here.**

## Latest execution slice — 2026-09-22

This slice is complete and is the new baseline for the next agent:

* **MPSC:** keep the endpoint generic. Its CFA certificate is rejected for
  finite-state storage because producer multiplicity is unbounded; no source
  name, payload type, or `mpsc`-shaped protocol is recognized. The generated
  typed pair operation now has a proof-free, FIFO-preserving admission fusion
  (`submit_right_and_dispatch_at`) with an exact submit-then-dispatch fallback.
  The focused rerun improved the join median from 950.0 to 401.0 ns/op, versus
  130.3 ns/op for `std::mpsc`.
* **RwLock:** the fair phase-controlled benchmark is now part of the matrix.
  Endpoint-wide CFA follows all eight rules and re-emissions, proving the
  persistent `slot_a/slot_b/slot_c` state mask (`0b111`). Optimized MIR lowers
  the constructor to `new_with_finite_state_mask(11, 7)`; ordinary result
  channels stay queue-backed and duplicate state admissions use a compatibility
  overflow queue. The fair result is 14,935 ns/op for joins versus 14,684
  ns/op for the native control.
* **Representation boundary:** the finite-state path is a generic JCAM-style
  transition product selected from typed rule/re-emission edges. It still uses
  the existing matcher mutex and does not recognize or depend on a lock
  implementation. The next optimization gate is to lower a proven claim and
  completion transition into ordinary typed MIR locals/atomics, not to add
  another named runtime helper.

* **Async reactions are now in the value/state CFA domain.** The endpoint
  proof no longer rejects a rule merely because `rule.is_async`. It follows
  the typed channel edges emitted by the async reaction, proves the
  `AsyncStateMachine`/completion shape's unit `ready()` bit, and leaves the
  payload-bearing `remaining(u64)` channel queue-backed. The existing
  coroutine/future runtime retains claimed inputs across suspension and
  cancellation; this change selects storage, not an executor-free execution
  path. The executable `joins_async` fixture runs the shape in off, analyze
  and optimize modes, and the optimize MIR dump shows
  `new_with_finite_state_mask(4, 8)` plus the certified async dispatch call.
  Body records now retain `is_async` separately from value facts, so bounded
  context CFA marks the reaction's `may_suspend` effect without making the
  registration adapter itself look suspending.
  The same split now applies to ordinary async helper bodies: a direct async
  call remains an ordinary value-flow edge (arguments, aliases and return
  values are solved by the existing MIR transfer), while the helper record is
  marked `is_async` and contributes `may_suspend` to its reachable contexts.
  This prevents a helper call from being treated as opaque for CFA while still
  preventing a local/closed execution proof from removing its coroutine
  boundary.

The detailed focused commands/results are in
[`join-benchmarks/docs/focused-20260922-rwlock-mpsc.md`](../join-benchmarks/docs/focused-20260922-rwlock-mpsc.md)
and the root summary is
[`JOINS-PRIMITIVES-SUMMARY.md`](../JOINS-PRIMITIVES-SUMMARY.md).

This plan follows the private forwarding work, state-token bridge at Rust
`c3f548c89f5`, and all-channel dispatch benchmark at library `b547504`. It supersedes the immediate sequencing
in `joins-private-storage-handover.md`, `joins-next-slice.md`, and older
optimization inventories. Their safety requirements and regression fixtures
remain applicable. The accepted async semantics remain authoritative.

## Objective and starting point

Implement the missing chain in rustc:

**channel/instance flow → closedness and occupancy proofs → specialized
storage and matching → eligible transition fusion → ordinary MIR/LLVM optimization.**

The next endpoint-wide slice also includes the JCAM-style finite transition
product. It records, for every source rule, the persistent one-way channels
claimed and re-emitted by that rule. A proven state mask may lower those
channels to bit storage while request/result channels remain ordinary queues.
This is a generic rule-graph optimization, not recognition of an MPSC or
RwLock-shaped API. Until caller-sensitive multiplicity is complete, duplicate
state admissions retain a compatibility overflow queue; the fast path itself
does not depend on a library lock implementation.

The first deliverable is a compiler-selected representation for a state-token
counter protocol, with explicit proof and rejection records, equivalent behavior
across CFA modes, and measured removal of generic coordination work. Then extend
the representation to completion and queued delivery. DataFusion follows these
gates; it remains the application-level objective.

Already implemented: ordinary caller-owned isolated unary futures in every CFA
mode; typed metadata on real MIR calls; local value/escape analysis and limited
helper propagation; a narrow private constructor/result-forwarding rewrite;
zero-allocation optimized forwarding. Do not reimplement those slices.

The latest complete matrix exposes the larger remaining gaps: roughly 8.5×
MPSC, 32–33× completion/mutex, and 77–96× RWLock versus handwritten controls.
The same run is near parity for MPMC, barrier, thread join, once and
work/resource, while the canonical all-channel/rendezvous and condvar rows are
protocol-specific faster controls rather than evidence that every join is
already cheaper. These ratios are workload-specific, not guarantees of
achievable speedups. See the archived full report recorded below.

The Dovetail checkout has separate analysis and code-generation drivers. Its
closed/bounded representations are useful reference implementations; do not
assume the checkout automatically infers every attribute it consumes. The
standalone `joins-cfa` library is an oracle, not rustc's optimization authority.

### Compiler-native bounded CFA — 2026-09-21

The first compiler-owned semantic-history layer is now implemented in
`rustc_mir_transform`. `JoinCfaBodyRecord` retains typed call edges, MIR call
and yield counts, endpoint escapes, and parent identities. The solver keeps a
bounded k-history (`-Zjoin-cfa-depth`, default `1`), propagates monotone
`suspend`/`escape`/`external` effects, follows ordinary helper calls, and
connects nested MIR bodies through a non-consuming parent transition. Source
`CreateGroup` and channel `Register` events contribute tagged JCAM-style
history frames; generated dispatch and reaction adapters remain transparent
so one semantic event is not counted once per ABI wrapper. A configured work
budget makes partial graphs diagnostic-only.

The JSON certificate records context frames, truncation, local and inherited
effects, closedness, and `optimization_safe`. Proof consumers require the graph
to be complete and require every context instance to be safe, except for the
narrow closed re-emission cycle that the state-token proof itself certifies:
truncation must occur in a selected reaction body, carry no suspend/escape/
external effect, and end at the candidate token's typed registration. An
ordinary/helper/external truncation remains a rejection. The endpoint-wide
fixed-slot/pair lowering consumes this certificate without looking at runtime
lock implementations. The native gate passes in optimize, analyze, and off
modes; the current optimize run proves three state-token endpoints
(`FixedUnarySlot`, `FixedPairMatcher`, and `FixedAtomicU64Pair`). The dedicated
semantic-history fixture reports 46 transitions and 23 contexts at k=1, and
32 transitions and 14 contexts at k=0, with zero retained semantic frames in
the latter mode.

This is deliberately split at the LLVM boundary. rustc must establish
endpoint/rule/instance identity, ownership, protocol multiplicity, and
coroutine-sensitive effects while those facts still exist in typed MIR. LLVM
then receives ordinary calls, atomics, control flow, and layouts and can reuse
its call graph, alias analysis, inliner, SROA, MemorySSA, and target lowering.
LLVM cannot reconstruct erased channel matching or dynamic instance identity,
so no duplicate high-level join CFA is added there. A future LLVM pass is
justified only if a reduced witness shows a post-inlining opportunity that
ordinary LLVM passes cannot realize from the rustc-selected representation.

The layer is not the end of the thesis CFA: endpoint-specific instance/context
sets, capture-sensitive escape transfer, coroutine output/drop edges, and
context-qualified queue/reply bounds still need to feed fusion and completion
lowering. Until those are present, the generic matcher remains the fallback.

### JCAM value-CFA correction — 2026-09-21

The previous implementation failure was specific and now has a regression
test. MIR had recorded every aggregate as if it were a primitive and labelled
the closure with its enclosing body. That made the generated adapter look like
an escaping opaque operation, so a context fixed point did not mean that a
reaction body was ever analysed. `AggregateKind::Closure`, `Coroutine`, and
`CoroutineClosure` now provide the actual nested `DefId`; captures are retained
as a typed `Closure` constraint, and a channel `Emit` seeds/enters the matching
dispatch body. Closure construction is not itself an external escape; only a
later return or unknown boundary widens its captures. The 19 thesis/Dovetail
ports now all pass `context.complete` and `cfa_complete`, and the corpus gate
checks that closure bodies exist in the graph and closure values occur in the
solution.

The merged-static-body failure is now fixed in the value solver. Each retained
`Emit` history and closure creation site gets a context-qualified body
instance; the typed constraint slice for that body is instantiated under the
instance rather than entered once per `body_def_id`. Ordinary Rust-call edges
receive the same bounded treatment, and known closure targets consume their
payloads as foreground arguments instead of widening them to `Outer` by
default. The port validator requires context-qualified solution variables and
closure creation origins, so a body-global fixed point cannot satisfy the gate.

This is still not a claim of exact Dovetail result parity. The remaining
precision work is to export and compare exact inner/outer escape sets, retain
constructor and rule transition identities instead of reconstructing them from
generated MIR, and preserve source-level multi-definition attributes. Only
after that differential gate may the complete value solution drive fusion,
queue bounds, or LLVM-visible lowering.

### CFA precision corrections — 2026-09-22

Three sources of avoidable conservatism are now removed. The crate graph keeps
known local helpers even when their MIR has no join-relevant facts, so a leaf
helper is not confused with an unavailable/indirect callee. Generated
constructor/channel/dispatch/reaction wrappers are excluded from the
source-level constructor/use alias proof; their ABI receiver temporaries do not
create a second endpoint instance or invalidate a private unary proof. Finally,
direct unary calls classified through the shared `Dispatch` identity recover
the concrete generated `Channel` body and carry its channel coordinate into the
`Channel` value, history, and background gamma variable. Local `Emit` targets
are context-substituted as well, so separate retained histories cannot merge
their continuation locals.

The 19-fixture gate now reaches the strict constructor/use/value-CFA proof for
18 examples (up from 9): all except `nqueens`. `nqueens` still has two source
constructor allocations and is correctly rejected as non-unique. All 19 reach
both bounded-history and value-CFA fixed points. The remaining negative
state-token records (`MissingReemission`, loop/multiplicity, or competing-rule
cases) are separate queue/token certificates, not failures of the value fixed
point.

This does not make the projection identical to Dovetail. Exact `inner_escape`
and `outer_escape` sets are not yet first-class certificate fields; generated
MIR still requires source rule/constructor identity to be reconstructed; and
unknown non-scalar values at indirect, cross-crate, unsafe, or opaque
boundaries remain `Outer` by design. Those are real information boundaries,
not reasons to weaken the proof. They require typed source-level metadata or a
sound interprocedural ownership model before they can be made more precise.

Scalar tuples and arrays are projected recursively as `Prim`. Function items
and function pointers deliberately are not: a stateless code pointer carries
no endpoint capture, but an indirect call still needs a target-sensitive edge.
Until a typed function-value fact follows that edge, treating it as primitive
would erase control-flow information and make the CFA claim less precise.

## Current gate status — 2026-09-20

### Typed strategy carrier on real MIR calls — 2026-09-21

The selected storage strategy is now carried by the actual typed MIR call,
not only by a side-table record or the name of a rewritten runtime helper.
`JoinCall.lowering` starts as `Generic` during frontend classification and is
upgraded to `FixedPairMatcher`, `FixedAtomicU64Pair`, or another proven
strategy only after `JoinStorageLowering` consumes the interprocedural CFA
certificate. Runtime adapter calls which were not themselves present in the
frontend descriptor receive a compiler-owned `JoinCall` at the same point;
their ordinary receiver, payload, destination, unwind edge and call operands
remain unchanged.

Optimized runtime MIR therefore shows, for example,
`PairMatcher::submit_right_fixed_and_dispatch_at(...) [join::Register
lowering=FixedPairMatcher ...]` and the atomic equivalent. The MIR pretty
printer exposes the strategy, while the LLVM boundary still strips metadata
without emitting a second operation. This is the intended async-style split:
rustc owns typed protocol/state selection and CFA, while the runtime owns
future, waker, executor and scope services. The next step is to consume this
strategy carrier in a dedicated typed claim/completion lowering; no runtime
helper should be added merely to carry the field.

### Endpoint-wide certificate carrier — 2026-09-21

The storage pass now builds one `JoinEndpointLoweringPlan` per proven endpoint
instance before rewriting any generated body. It requires one unique CFA
allocation, `AtMost(1)` positive state-token proofs with matching origins, one
strategy for the complete endpoint, and a mask derived from those proofs. The
constructor adds its extra literal/allocation-edge checks, but channel and
dispatch bodies consume the same plan rather than recomputing a body-local
decision. Any ambiguity leaves the complete endpoint on the generic path.

Each positive state-token lowering has a deterministic certificate ID derived
from its compiler-owned transition evidence. The endpoint plan combines those
IDs with the allocation, mask and strategy; optimized `JoinCall` metadata now
carries that endpoint certificate on the real MIR call. This is provenance for
later typed MIR/LLVM lowering, not a runtime handle and not permission to infer
semantics from helper names. The native gate checks that fixed pair and atomic
calls carry `certificate=Some(...)`; off/analyze still emit no fixed calls.

### Synchronous completion boundary in MIR — 2026-09-21

`JoinSemanticOps` now places `CompleteReplies` metadata at each actual
`Return` terminator of a synchronous reaction body, rather than at body entry.
The marker is still erased before backend code generation, but its MIR
location now matches the ownership/lifetime boundary where a typed completion
lowering can publish every reply. The marker now carries the compiler-resolved
`reply_channel_indices` map and the typed return destination (`_0`) as well; a
two-result rule is visible as `replies=[0, 1], destination=_0` in optimized MIR.
One-way reactions have no completion marker.
Async reactions deliberately do not receive an invented entry marker: their
completion belongs at the coroutine output edge after ordinary coroutine
lowering. This keeps the representation honest while leaving the existing
runtime adapter unchanged.
The per-body CFA JSON records the same map as `reply_channels:[…]`, so a dump
can be checked without parsing pretty MIR or consulting generated method names.

### Runtime/compiler boundary consolidation — 2026-09-20

The compiler-facing fixed-pair boundary has been narrowed without changing
the selected hot path. `PairMatcher`'s ordinary typed operations now detect a
proof-selected fixed state and route to the existing fixed implementation;
this keeps the fallback and fixed endpoints on one source-level operation
ABI. The current MIR consumer still retargets those operations to direct fixed
symbols when that removes the state-kind branch, so the consolidation is
performance-neutral rather than a claim that all fixed helpers have already
been deleted. The runtime test
`fixed_pair_uses_canonical_operations_after_constructor_selection` exercises
the shared ABI directly.

The exact `FixedAtomicU64Pair` path remains a deliberately separate compiler /
runtime primitive. Its left input is represented by an `AtomicU64`, while the
generic `PairMatcher<L, ...>` operation cannot safely reinterpret an arbitrary
`L`. It therefore retains its three type-specialized entry points until the
compiler emits the token state and claim/completion operations directly in
ordinary MIR. This is analogous to async lowering: rustc owns the typed state
machine and representation selection, while the runtime keeps futures,
wakers, executors and scope services. It is not lock recognition, and the
compiler now requires target CAS support as well as 8/64-bit atomic widths.

The ABI proof compares instantiated payload/result types (with only method
receiver lifetime identities erased) and safety, ABI, variadic and splat
metadata. A missing or incompatible helper rejects the whole candidate. The
next consolidation step is to consume the endpoint-wide plan in MIR and
replace the fixed/atomic adapter calls with explicit typed state transitions;
do not add another runtime helper family for each payload width.

The first fixed-pair result path is implemented; the next work is attribution,
not another broad runtime rewrite. The compiler now records cyclic CFG blocks
in CFA body records and rejects a state-token producer inside a loop with
`LoopMultiplicity`. The loop witness is executable in
`joins-library/compiler-tests/joins_state_token.rs`. The positive canonical
mask-1 pair still lowers to `FixedPairMatcher`, while loop, competing-rule,
scoped and reordered witnesses stay generic. Async reactions may now use the
finite state-mask representation when their typed transition graph proves it,
but their coroutine/executor work remains explicit. The lowering pass plans
all recognized rewrites in a body before mutating MIR, and the three serialized
native gates (`off`, `analyze`, `optimize`) pass with MIR validation.

The compiler gate is deliberately conservative: it does not query other
already-stolen MIR bodies from a pass invocation. A state-token seed hidden in
an ordinary helper is rejected with `HelperMultiplicity`, because one static
helper edge can execute repeatedly; the helper witness is executable beside
the loop witness. Generated fixed shims are
resolved by compiler-owned runtime identities and checked for compatible typed
output/arity before replacement; a missing or malformed operation rejects that
body before any rewrite. The runtime still retains the generic fallback for
every unproven case. Optional library instrumentation (the
`joins-runtime` `instrumentation` feature) counts fixed locks/claims, ready
replies, pending reply-cell admissions and generic fused fallbacks. Use those
counters and assembly to identify the remaining costs before extending CFA.

The latest serialized focused result is 35.43 ns/op handwritten, 907.16
joins-off, 610.78 analyze and 313.86 optimize (100 samples, matching
checksums). This is directional because variants were sequential, not paired;
the optimize path remains 8.86× the handwritten control. Do not rerun the full
matrix until the attribution gate explains the remaining reply-cell, mutex,
FIFO and trampoline work.

The first attribution window now explains that gap. For 40,000 optimized
`mutex` operations, 38,311 replies were immediately ready and 1,689 used a
pending reply cell, but the path still made 123,380 fixed-state mutex calls and
81,690 fixed claims. Off/analyze recorded 40,000 generic fallback calls and no
fixed calls. Non-instrumented assembly shows the fixed submit/dispatch symbols
are smaller and have no queue-growth calls, yet still contain mutex/CAS,
reply/drop, trace and trampoline paths. The evidence supports a join-specific
atomic state-token lowering; it does not support recognizing a library lock.
Full counters and symbol metrics are in the benchmark repository's
`docs/attribution-fixed-pair-20260920.md`.

### Atomic state-token gate completed — 2026-09-20

The attribution target is now implemented and verified. Optimize-mode MIR
selects `FixedAtomicU64Pair` only for the exact `u64` one-way-token witness;
off/analyze remain generic and the `u32` pair remains `FixedPairMatcher`.
The runtime uses a release/acquire `AtomicU8` state around an `AtomicU64`
token, a separate result FIFO, identity-based withdrawal for dropped pending
requests, and explicit cancellation draining. The atomic runtime has a
mutex-based fallback definition for targets without both atomic widths, while
the compiler target gate prevents selecting this ABI there. This is generated
join storage, not lock recognition.

Verification is complete for this slice: 75 runtime tests pass, including a
dispatch/cancellation race; the rebuilt stage-1 off/analyze/optimize native
gates pass; and the untimed attribution counters show 40,000 generic
fallbacks in off/analyze versus 40,000 successful atomic claims in optimize.
A serial 100-sample mutex timing window measured 39.840 ns/op handwritten,
398.375 off, 380.738 analyze and 187.714 optimize. The result is directional
until the same rows are rerun in a committed paired/shuffled artifact, but it
establishes that the compiler-selected atomic path is active and halves the
optimized runtime relative to the generic path. The remaining work is not
another lock tweak: attribute and lower the result-side FIFO, reply-cell
completion/ownership, tracing and trampoline before broadening the CFA proof.

### Pending-right allocation experiment — 2026-09-21

A candidate cleanup replaced the per-request atomic-path identity `Arc` with
a monotonic `AtomicU64` ID while retaining weak-state withdrawal and FIFO
linearization. It passed the 75-test runtime suite, but a same-configuration
serial comparison did not justify keeping it: 100 samples of the four-worker
mutex row measured 207.1 ns/op median (ID) versus 182.7 ns/op with the
preceding `Arc` implementation, with a substantially higher mean as well.
The candidate was reverted. This is useful negative evidence: allocation
removal alone is not a performance win here, and the next optimization should
target typed reply completion/ownership rather than add another runtime
identity mechanism.

The current post-rebuild optimize-only snapshot is 173.560 ns/op median
(100 samples, four workers, checksum `800020000`); it is directional because
the handwritten control was not rerun in the same shuffled artifact. Details
are in `../join-benchmarks/docs/typed-reply-map-current-20260921.md`.

### Perf attribution checkpoint — 2026-09-21

With perf access restored, a serial 200,000-operation, four-worker optimize
run captured 601 cycle samples with zero loss. The largest local symbols were
the generated `JoinMutex::available` (13.78%), atomic fused admission (11.09%),
atomic dispatch (11.05%), generated `acquire` (10.91%), and `PairMatcher` drop
glue (10.26%). Reply demand was 3.69%, allocator samples were 3.86%/3.66%,
and kernel futex wakeup was 3.33%. Annotation put 89.30% of the `available`
symbol's local samples on an atomic increment immediately before generated
dispatch-closure construction. The binary lacks usable source lines for that
instruction, so the evidence is recorded as endpoint/closure setup rather than
asserting which counter it updates. The generated source does currently clone
the endpoint for every owned reaction closure. Full command and output are in
`../join-benchmarks/docs/perf-atomic-mutex-20260921.md`.

This changes the next optimization priority: test a compiler-visible
borrowed/local claim boundary for proven unscoped synchronous reactions, or an
equivalent ordinary-MIR lowering, before changing queue storage again. Scoped,
async, and shared/executor-owned reactions must retain their owned boundary.
The experiment is successful only if it preserves cancellation, unwind/drop,
and checksum gates while removing the setup/drop symbols from the profile.

## Next slice after the atomic gate

1. **Commit a paired attribution artifact.** Re-run the mutex row with native,
   off, analyze and optimize in deterministic shuffled order, retain raw
   JSONL, checksums, counters and assembly, and report paired ratios. Do not
   expand the full matrix until this artifact confirms the atomic result.
2. **Remove result-side generic costs by typed MIR lowering.** Extend the
   current `FixedAtomicU64Pair` proof to a compiler-owned reply slot/completion
   operation. Preserve typed payloads, independent waiter ownership, panic and
   drop edges; lower the result FIFO only when CFA proves its bound. The
   fallback must remain the ordinary matcher, and no transformation may
   pattern-match a lock implementation.
3. **Lower eligible reactions through ordinary coroutine MIR.** Keep the body
   as the existing async/coroutine future, but make claim, completion and
   cancellation explicit MIR operations before codegen. Verify optimized MIR
   and LLVM contain no erased generic matcher calls for the selected witness;
   verify all unsupported bodies retain them.
4. **Add target and semantic regression coverage.** Cross-check the atomic
   target-width fallback, direct/async single-input equivalence, dropped
   unmatched requests, cancellation linearization, borrowed-state rejection,
   and independent multi-reply completion. A point-in-time `cancel_pending`
   race may linearize a concurrent emission after cancellation; document this
   unless a permanent closed-state contract is introduced.
5. **Only then expand the benchmark matrix and DataFusion port.** Preserve the
   native/async/manual controls, collect serial flamegraph/perf attribution,
   and report executor-policy differences. DataFusion changes must consume
   first-class generated operations rather than call the hidden atomic ABI
   directly.

### Progress on this plan (2026-09-19)

- The typed-definition slice is implemented: HIR markers preserve ordered rule
  inputs, reply mapping, asyncness and body ordinals; endpoint IR records the
  selected shared policy. The crate CFA graph now dumps these facts.
- Dynamic endpoints now emit one compiler-marked named reaction helper per
  source rule. `JoinRule.reaction_method_def_id` is the executable HIR/MIR
  owner; shared dispatch is represented once without a fabricated rule index.
  Restricted unary/pair expansions retain their existing nested-body evidence.
  Duplicate, missing, or out-of-range reaction markers clear all body
  identities for that endpoint rather than authorizing a partial proof.
- MIR now records sorted per-channel body-local occupancy intervals in addition
  to its aggregate interval. This is an evidence surface only; no fixed-slot
  rewrite consumes it yet.
- The native analyze and optimize fixture gates pass after the reaction-helper
  change; optimize still reports the existing narrow forwarding rewrites.
- The first cross-body state-token proof is now live.  The positive dynamic
  witness records one ordinary seed, one complete-pattern claim and one
  named-helper re-emission, proving `AtMost(1)`; a competing-rule witness is
  rejected before it can authorize storage.  Endpoint-local completeness
  ignores generated wrapper escapes while still rejecting unknown source
  callers and unknown effects in the selected leaf reaction.
- Optimize mode now consumes only those positive certificates into an explicit
  `state_token_lowerings` record selecting `FixedUnarySlot`; analyze mode emits
  the evidence but selects no representation.  The first section-6 step is now
  executable: generated dynamic constructors carry a compiler-owned channel
  mask, and `JoinStorageLowering` rewrites only the proven bit after validating
  the exact constructor identity and allocation site.  Typed runtime storage
  consumes that mask; specialized matching, lock/queue removal, and assembly
  evidence remain outstanding.  A serialized LLVM gate at `-O0` and `-O3`
  observes the same positive `0/2` mode split as an immediate call argument;
  the generated IR still contains the generic matcher machinery.
- The library runtime now has a proof-facing `DynamicMatcherStoragePolicy` and
  exact per-channel inline slots with fallible admission; occupied proven slots
  never grow a FIFO while unrelated channels retain dynamic queues.  All 60
  runtime unit tests pass.  Generated dynamic constructors now start with a
  zero channel mask, and the optimize-only `JoinStorageLowering` MIR pass
  consumes a proven `FixedUnarySlot` state-token record and rewrites only the
  proven bit.  The rebuilt native gate observes positive mask `2`, negative
  mask `0`, and scoped mask `0`; off/analyze retain mask `0`.  This proves the
  typed MIR bridge, but not yet a runtime allocation/lock removal or a speedup.
- One-way dynamic admissions now carry no withdrawal token: because they have
  no reply future, they cannot be withdrawn before matching.  Result-bearing
  admissions retain the weak-token withdrawal protocol.  This removes one
  per-message `Arc` allocation without recognizing or replacing any lock
  implementation; the runtime unit suite remains at 60 passing tests.
- A serialized 100-sample `work-resource` run (10,000 operations, four
  workers) after that change measured medians of 1,092.4 ns/op native, 1,807.5
  joins-off, 1,611.4 joins-analyze, and 1,167.6 joins-optimize.  The optimized
  path is therefore 1.07x native (bootstrap 95% CI 1.03–1.10x) and 35.4%
  below joins-off for this focused workload.  This is evidence for the
  channel-mask plus one-way-admission slice only; the generic matcher still
  owns the mutex, erased payloads, reply cells and dispatch, and broader
  workloads remain to be measured.
- Canonical declaration-order patterns now use a compiler-emitted
  `__join_dispatch_*_all` operation.  The runtime claims every declared queue
  under the existing mutex after checking all occupancies; it does not infer
  or replace a lock implementation.  Reordered, partial, competing and
  scoped rules retain the generic pattern operation.  The 60-test runtime
  suite and optimize/analyze/off compiler fixture gates pass.  A serialized
  100-sample follow-up measured 1,033.5 ns/op native, 1,147.2 joins-off,
  1,193.9 joins-analyze and 1,164.7 joins-optimize (about 1.11–1.16x native).
  This closes a dispatch-validation gap but leaves type erasure, reply cells,
  allocation and mutex costs for the next slice.
- The complete serialized **expanded-source** matrix is now finished and
  archived at
  `../join-benchmarks/results/full-all-dispatch-20260919/` (30 samples, 5,000
  iterations, five warmups, four workers, deterministic per-operation variant
  shuffling, and 10,000-repetition bootstrap intervals). Every expected sample
  passed validation and all checksums matched. This is the baseline for the
  next structural change; no further timing run is needed until a
  storage/reply representation changes.
- A safe typed admission slice then removed an unobservable completion cell
  from restricted two-channel one-way participants. `PairMatcher` now stores an
  optional completer and the macro emits typed `submit_*_oneway_at` calls;
  result-bearing participants retain their ordinary reply/withdrawal path.
  The runtime suite passes 61 tests. A serialized 100-sample mutex gate is
  archived at
  `../join-benchmarks/results/focused-pair-oneway-20260919/`: medians are
  27.73 ns/op native, 928.73 off, 1,051.37 analyze, and 779.82 optimize.
  Optimize is about 20% below the previous 976.1 ns/op mutex row, but remains
  28.12× native. This is a typed join-semantic optimization, not lock
  recognition; the remaining reply-cell, queue, mutex, executor and
  re-emission costs are still the next target.
- The same one-way PairMatcher slice was measured on the MPSC-shaped pair in
  `../join-benchmarks/results/focused-pair-oneway-mpsc-20260919/`: medians are
  95.07 ns/op native, 608.25 off, 1,006.62 analyze, and 548.17 optimize.
  Optimize is 5.77× native here, about 19% below the previous full-matrix
  optimize row. The serialized analyze outlier is retained as evidence, not
  attributed to CFA; all records and checksums pass.
- The benchmark harness has now been corrected to compile the original join
  source directly for the final executable. The former expanded-source
  workaround removed the compiler-visible join graph before the final build,
  so `full-all-dispatch-20260919` is a useful compatibility-runtime history
  but is **not** valid evidence that CFA affected those binaries. A direct
  source, 100-sample mutex focus (10,000 iterations, ten warmups, four
  workers) measured medians of 35.35 ns/op native, 1,055.61 off, 744.88
  analyze and 752.75 optimize. The source-preserving optimize build is about
  1.40× faster than off on this run, but is still about 21.3× the native
  control; the full direct-source matrix must be archived before broad ratios
  are reported.
- A codegen-boundary audit found that
  `rustc_codegen_ssa::mir::lower_join_markers` currently clones the optimized
  body immediately before backend lowering, removes join call descriptors and
  marker statements, and clears `Body::join_info`. This is correct for the
  current compatibility lowering, but it means no join metadata or CFA proof
  reaches LLVM. Any optimization that needs join facts must therefore consume
  them into executable, ordinary MIR (or an explicit typed lowering) before
  this boundary; an LLVM pass cannot recover the erased pattern.
- The current mask bridge is deliberately only a proof-to-policy adapter: it
  changes the generated constructor's scalar channel mask, which lets the
  runtime select an inline queue slot, but it does not produce a typed matcher
  or remove the generic `PairQueue`/mutex/reply machinery. The next executable
  compiler step is a proof-gated typed MIR lowering to a `FixedPairMatcher`
  (with the existing generic matcher as its fallback), not another
  metadata-only strategy label. This lowering must carry typed payload/reply
  operands, ownership and unwind/drop behavior, and be visible in optimized
  MIR before `lower_join_markers` erases descriptors.
- The first runtime structural follow-up is now complete in library commit
  `473a5d6`: `PairMatcher` uses one guarded typed `PairState` for both queues,
  preserving the generic FIFO fallback and exact proof-selected slots while
  making pair claims atomic under one lock interval. The 62-test runtime suite
  passes. A serialized direct-source mutex focus measured 36.0 ns/op native,
  715.8 off, 742.0 analyze and 560.8 optimize (100 samples, 10,000
  iterations, ten warmups, four workers). This is a meaningful reduction from
  the prior 779.8 ns/op optimize result, but it remains about 15.6x native;
  reply publication, wake/scheduling, trampoline and generic matcher work are
  now the priority. Do not treat this runtime simplification as the typed MIR
  lowering promised above.
- The first proof-consuming pair ABI slice is now complete in Rust
  `8424aa6953e` and library `f7d358e`/`34c4eff`. A positive, canonical,
  synchronous two-channel endpoint with a proven `AtMost(1)` token now
  selects `FixedPairMatcher` in optimize mode. The MIR constructor, generated
  channel admissions, and synchronous dispatch are retargeted to distinct
  fixed methods (`new_with_fixed_pair_mask`, `submit_*_fixed_at`, and
  `__join_dispatch_once_fixed_at`) and carry the proven mask (`1` in the
  positive fixture). `off` and `analyze`, plus competing, reordered, async,
  scoped and non-canonical endpoints, retain the generic methods and mask `0`.
  The optimize dump contains all three fixed operation classes and the CFA
  graph records `strategy=FixedPairMatcher`; the three native gates and
  stage-1 compiler build pass. The library fixed ABI now uses a separate
  typed `FixedPairState`: an inline left token plus a typed FIFO of right
  requests, with atomic claim/restore under its own guard. It does not silently
  grow the proven slot or inspect/replace a library lock implementation.
  This removes the generic `PairQueue` dispatch from the selected methods, but
  still retains an `Arc<Mutex<...>>` and a FIFO for pending right requests. The
  result-bearing right admission is now fused in library `3e9dfcb`: when the
  proven left token is already present and no older right request is waiting,
  the reaction runs in the caller and returns `Reply::ready`; pending requests
  retain the shared reply/waker path. Four focused tests cover ready and
  pending replies, FIFO, sibling completion, panic, and cancellation, and the
  complete runtime suite passes 68/68. A focused direct-source run after the
  fused slice measured 35.43 ns/op native, 907.16 off, 610.78 analyze and
  313.86 optimize (100 samples, 10k iterations, four workers; all checksums
  matched). Variants were sequential, not paired/shuffled, so this is
  directional evidence only; repeat it with paired ordering after assembly
  and allocation attribution.

## Constraints throughout

- This is the owner's AI-written research branch. No upstream maintainers are
  expected to review it; any upstream proposal would be rewritten by hand.
- Every compiler layer is available. Preserve Rust ownership, destruction,
  panic, lifetime and concurrency semantics. Reuse ordinary coroutine MIR for
  reaction bodies and the existing compiler infrastructure where appropriate.
- Do not recognize a lock protocol and replace it with a library lock.
  Generate fields, matching branches and justified atomics/CAS from join facts.
- Preserve the forwarding execution-context guard until a separate proof
  establishes that removing it preserves scheduling and progress.
- No performance annotations from the programmer may authorize a rewrite.
  Unsupported analysis or exhausted budgets must select the valid generic path.
- Never run benchmarks or profiles concurrently, or alongside builds/tests.
  Batch compiler changes and rebuild once per meaningful verification gate.

## 1. Restore trustworthy broad regression coverage

Keep forwarding as the quick attribution case and the full 12-operation matrix
as the structural-change gate. Add bounded process timeouts, operation/variant
progress records and explicit failure status. An incomplete run must not render
as a successful full comparison. Preserve failures and raw samples.

Archive benchmark source, scripts, source hashes and compiler binary hash with
results. The current `join-benchmarks` directory has no Git repository; ensure
the relevant source is committed in an owned repository as well as the results.
Verify whether direct source compilation now succeeds and remove the old
expanded-source capture workaround if its original defect is fixed.

Correct stale reports/inventories: unary semantics are mode-independent, narrow
compiler result fusion exists, and queue-bound metadata is not a general proof.
Use the same statistic for a displayed ratio and its confidence interval.
Keep the Tokio executor comparison and RWLock admission probe clearly labelled.

Gate: intentional timeout/assertion failures are reported as failures; every
expected operation has the requested sample count; direct source builds are
checked; a reproducible source snapshot accompanies the next complete report.
No timing rerun is needed solely for documentation changes.

## 2. Make rule and policy information authoritative

Work principally in `rustc_builtin_macros/src/joins.rs`,
`rustc_passes/src/joins.rs`, `rustc_middle/src/middle/joins.rs`, and
`rustc_mir_transform/src/joins.rs`.

Replace count-only/dispatch-wide information with typed definition records:
channel identities and payload/reply types; exact rule inputs and binding order;
body identity; reply mapping; captures and re-emission; competing rules; and
admission, demand, execution-owner and cancellation policies. Distinguish the
static definition from each dynamic construction site and context.

Use resolved compiler identities, types and bodies. Do not reconstruct semantic
facts from generated names or scan generated source strings. Preserve semantic
operations on their real MIR operands, destinations, normal/unwind edges and
drop paths through the specialization decision. Introduce explicit forms where
the existing call descriptor cannot express the required contract. State the
LowerJoins boundary and ensure ownership is visible to borrowck/drop elaboration.

Gate: deterministic dumps show exact patterns and policies for unary, pair,
competing-rule, state-token and async fixtures. MIR validation passes before and
after lowering. Unrepresented policy or remapping is an explicit rejection.
Metadata alone does not count as executable specialization.

## 3. Establish shared semantics before authorizing specialization

The compatibility runtime still has semantic gaps. First record the selected
shared execution owner, fallible admission API, failure contract and lifetime
restrictions, then implement the required behavior for the first supported
domain in every CFA mode.

Requests register immediately; polling expresses demand. Claim a complete
eligible pattern atomically, without reserving undemanded partial matches.
One demanded result suffices and every named reply completes independently.
One-way-only rules run when enabled. An emission has no reply capability;
a request returning `()` has observable completion.

Withdrawal races atomically with matching. Dropping a matched reply abandons
only that reply. Specify behavior when all consumers disappear and on scope
cancellation. Start with owned inputs for executor-owned shared work; do not
justify borrowed lifetime safety through destructors alone.

Gate: deterministic witnesses cover registration of all inputs followed by
awaiting one output, no premature body execution, competing patterns, separate
waiters, match/withdraw races, scope cancellation, admission failure with owned
arguments returned, and exactly-once consumption/destruction. Include negative
lifetime/Send checks at actual execution boundaries. Apply the same contract in
off/analyze/optimize. Do not benchmark changed semantics as an optimization win.

## 4. Extend channel flow and prove closedness per instance

Extend the existing monotone solver with bounded construction/call contexts,
channel-valued argument/result flow and capture flow. Handle direct helpers
first, then known closures and recursive strongly connected components.
Unknown indirect calls, cross-crate bodies or unsupported aggregates widen to
unknown; context and iteration budgets must terminate conservatively.

Use Dovetail's bounded histories, foreground/background distinction and
inner/outer closure sets as precision references. A different Rust abstraction
is acceptable only with a written explanation of its guarantees and losses.
Reuse rustc CFG/SCC/dataflow infrastructure rather than cloning a general solver
unnecessarily.

Keep these separate: externally closed, locally executed, uniquely owned,
bounded occupancy, and safe stack lifetime. None implies all the others.
An instance whose channels stay internal may still have concurrent reactions.

Gate: two constructions of the same definition remain distinguishable; helper
and capture positives reach the correct channels; escape/recursion/unknown-call
negatives refuse unsafe conclusions; zero budget causes no optional rewrite.
For a supported common subset, compare compiler facts against the oracle or
Dovetail fixtures. Report analyzed/unknown/rejected counts and reasons.

## 5. Prove per-channel occupancy on the counter witness

Use the existing state-token pattern (`available(value)` plus result-bearing
`acquire()`, with the reaction re-emitting the updated state). Establish its
initial token count, permitted producers and the effects of claiming and
re-emitting. Account for the token owned by an executing or suspended reaction,
and paths involving panic, cancellation and drop.

Prove the state channel has occupancy at most one under the explicit witness
contract. Pending acquisition requests can still be unbounded. Never turn a
bound on one channel into a bound on the whole instance. A public producer
capable of submitting extra state tokens invalidates the proof unless its
reachable use is established. Cover loops and merged paths conservatively.

Gate: expose a proof record identifying the instance, channel, bound and
supporting transitions. Reject duplicate seed tokens, escaping producers,
unknown callbacks, extra emissions and unsupported cycles. Test a valid loop
and multiple pending requests. No fixed-storage selection from frontend hints.

## 6. Consume the proof in generated storage and matching

For the proven channel, generate typed inline storage and explicit matcher
operations. A statically proven bound requires no dynamic growth fallback for
that channel. Unknown channels may retain queues. Stack allocation additionally
requires that all users, replies and suspended bodies fit the owning lifetime.
Otherwise retain the necessary owned storage.

Generate matching specialized to the actual rule inputs; avoid temporary
enqueue/dequeue when an eligible complete match can consume an incoming value
directly. The first executable slice is the canonical declaration-order
all-channel claim, which removes repeated pattern validation but still uses
the generic queues and mutex. Preserve demand and competition. For shared
state, specify the atomic
claim/ownership protocol, memory ordering and linearization points before
implementing CAS. Use systematic interleaving tests for that protocol.

Apply rewrites through validated current-MIR proof objects; validate all affected
sites before mutating any. Recompute or invalidate facts after transformations.
Then expose ordinary typed operations and coroutine state to standard MIR/LLVM
optimization. Inspect the executed path for surviving allocation, type erasure,
reference counting, queue traffic and scheduling calls.

Gate: optimize selects the representation only on positive fixtures;
off/analyze retain equivalent generic behavior; negatives refuse with reasons.
Ownership/race gates pass. MIR and assembly demonstrate the specific removed
work. Merely selecting an independently handwritten counter implementation is
not completion.

### 6.1 Next slice: make the proof-selected pair representation pay off

The proof-selected constructor and operation ABI are now the completed first
step, not the target representation. Implement the next slice in this order:

1. Define the compiler/runtime contract for `FixedPairMatcher` using the actual
   channel payload and reply types. It may use ordinary Rust fields and
   atomics/CAS or a proven local synchronization mechanism, but it must not be
   selected because the code resembles a library mutex and must not depend on
   a particular lock implementation. Keep a generic queue-backed matcher for
   every unsupported case.
2. Keep the existing `JoinStorageLowering` proof checks as the admission gate.
   The fixed constructor now selects a separate typed state with an inline
   proven token slot and a typed pending side; fixed submit/claim methods and
   the fused result admission are selected in executable MIR. The immediate
   reply path is only valid for the canonical unscoped synchronous mask-1
   proof; the runtime constructor asserts that contract, and the MIR pass
   rejects other masks so they retain the generic matcher. The compiler must
   not identify or replace a library lock implementation. Any atomics/CAS must
   be justified by the join state protocol and have an explicit
   ownership/ordering proof. The generic `PairQueue`/reply path remains the
   fallback for pending, scoped, competing, reordered, async, or unknown
   cases.
3. Preserve the operation through optimized MIR long enough for ordinary MIR
   passes and coroutine lowering to see the typed fields, direct matching
   branch, and reply completion. Lower to the canonical runtime ABI only after
   ownership, drop, panic/unwind and cancellation paths have been checked. At
   the existing backend boundary, erasing a consumed descriptor is acceptable;
   erasing it before this lowering is not.
4. Extend the current positive and negative MIR fixtures. The positive
   state-token pair must show `FixedPairMatcher` and the fixed constructor;
   once the runtime specialization is real, its post-inline MIR/assembly must
   show no dynamic `PairQueue` construction on the proven channels and must
   distinguish the ready-reply and pending-reply paths. A
   competing rule, extra producer, escaped instance, reordered pattern,
   unknown call, borrowed payload, and non-proven bound must retain the
   generic matcher and record a rejection reason. Off and analyze must keep
   the generic representation while preserving behavior.
5. Verify the generated MIR and assembly for removed enum dispatch, queue
   growth, reply-cell allocation on the immediately matched path, and
   unnecessary scheduling work. The current gate is symbol/mask/strategy
   evidence and the 68-test runtime suite; the next gate must add allocation
   counters and instruction-level evidence for the fused result call. Then run
   the focused direct-source benchmark serially, with allocation counters and
   checksums, before touching the full matrix. A successful gate requires a
   measured reduction in the identified generic work, not just a changed
   symbol or metadata dump.

The constructor and generated-operation retarget is the first place where the
CFA result becomes an executable compiler optimization. Do not proceed to completion/MPSC
generalization until the fixed body has a sound fallback and a direct-source
gate demonstrates that the specialized representation, rather than only its
symbol, reaches generated code.

### Atomic fused-admission follow-up — 2026-09-21

The runtime half of the exact-`u64` pair now carries atomic pending-right and
admission-in-flight counts. When both are zero, the proof-selected fused
admission can claim the token without taking the result FIFO mutex; queued,
withdrawn, cancelled, and contention paths still use the mutex and preserve
FIFO semantics. Updating the counts under the admission protocol prevents an
older producer from being bypassed while it links its item. This removes one
known empty-queue lock from the hot path without recognizing or replacing any
library lock. The runtime suite (75 tests) and optimize compiler gate pass.
The initial post-change 50-sample mutex snapshot is 200.31 ns/op optimized
versus 34.29 ns/op handwritten; treat this as directional until a paired,
shuffled attribution run is archived. The next performance gate should compare
queue-lock counts and generated assembly before and after this guard, then
move the typed token claim/reply completion into MIR rather than adding more
runtime entry points.

## 7. Measure, generalize, then migrate DataFusion

After correctness gates, run the focused counter benchmark against the native
control and all CFA modes. Collect allocation counts separately and sequential
perf profiles with instruction/basic-block attribution. Record sample counts
and uncertainty; do not interpret sampled IP percentages as exact instruction
latency. The focused gates are complete, but the broad matrix must be
compiled from direct source after the harness correction. The 100-sample
`work-resource` archive is in
`join-benchmarks/results/focused-work-resource-20260919-token/`, the
all-channel follow-up is in
`join-benchmarks/results/focused-work-resource-20260919-all-dispatch/`, and the
full matrix is in `join-benchmarks/results/full-all-dispatch-20260919/`.
The following table is the **historical expanded-source** report's medians
(joins optimize versus handwritten baseline):

| operation | optimize / baseline | interpretation |
| --- | ---: | --- |
| MPMC | 1.00× | parity within noisy paired interval |
| barrier | 0.97× | parity; interval overlaps 1 |
| thread join | 0.97× | parity; interval overlaps 1 |
| once | 1.00× | parity; interval overlaps 1 |
| work/resource | 0.93× | interval overlaps 1 |
| MPSC | 8.50× | major generic queue/dispatch gap |
| completion | 33.39× | reply/admission overhead dominates |
| mutex | 32.51× | per-operation coordination overhead dominates |
| RWLock | 76.53× | shared-state representation is not competitive |

These ratios must not be used as CFA speedup claims: the expanded final source
did not preserve the compiler-visible join graph. Retain them only as a
compatibility-runtime history until the direct-source matrix supplies a valid
replacement. Rendezvous (0.03×) and condvar (0.43×) use intentionally
different protocol work from their handwritten controls and must not be
counted as general wins.
The async-request row is compared with the Tokio baseline and is 0.12× in this
harness; it is likewise a protocol/measurement witness, not a claim that the
generic join matcher beats an ordinary async function.

All 30 samples per row passed, with matching checksums, but those samples do
not establish compiler CFA consumption. CFA dump summaries
contain 156 records and 57 reaction bodies in each mode; only four frontend
direct-unary and four exact-queue-0 facts are currently recorded, with zero
interprocedural direct candidates. Therefore the full matrix establishes the
next attribution target—typed storage, reply allocation and generic
coordination—rather than showing that CFA has already removed those costs.
The next broad gate is a serialized direct-source attribution pass for the
high-gap MPSC/completion/mutex/RWLock rows: count allocations and instrument
queue admissions, reply-cell creation, wakeups, task submissions and
atomic/lock acquisitions. The immediate implementation target is the
compiler-proven `FixedPairMatcher` lowering above, while retaining the generic
matcher for partial, reordered, competing, escaping or borrowing-sensitive
cases. No lock implementation may be recognized or substituted; the
optimization must be justified by the join proof and visible in MIR before
codegen erases the descriptors.

The initial performance gate is a repeatable reduction in the identified
generic work and measured cost. The target remains parity with the native
primitive; do not declare success merely for a marginal improvement. If the
gap remains, use profiles to select the next change.

Next extend proofs/codegen to completion (state transitions and executor cost),
then MPSC (genuinely queued delivery). Add functional/no-storage channels,
closed local fast execution, and broader transition/definition fusion where
proofs justify them. Preserve suspension, scheduling and parallelism; do not
equate closedness with permission to run every reaction immediately.

Only after those gates, port one bounded DataFusion coordination path and
measure equivalent operator/application workloads and code complexity. Keep
the full primitive matrix alongside application benchmarks.

## Delivery discipline

Each slice records: supported domain, proof facts, rejected counterexamples,
actual rewrite counts, verification commands and results, and remaining gaps.
Build/check cheaply first; run native off/analyze/optimize gates against one
rebuilt stage1 compiler and matching standard library. Test affected runtime
code and concurrency contracts before timing. Do not rebuild DataFusion during
these compiler slices.

Commit compiler changes and current results in `JOINS-SUMMARY.md` plus linked
evidence, and push `rust` branch `joins` to `prc33`. Commit companion library
changes locally (no remote is currently configured). Preserve unrelated
worktree changes, including `AGENTS.md` deletion and `ph2`.
## Completed callable-value slice — 2026-09-22

The previously open function-value boundary is now wired through the first
proof consumer. `FnDef` assignments and safe reification to `fn` pointers are
recorded in MIR as typed `Function` facts; indirect call terminators retain the
function local. A crate-level copy/move fixed point resolves a call only when
one function body is possible, then reuses ordinary-local argument/return
constraints and the existing context history. The state-token optimizer accepts
one non-cyclic helper path and consumes the resolved edge when selecting
`FixedPairMatcher`. An unknown/conflicting function value remains unknown; an
unknown callable in an endpoint subgraph explicitly rejects fixed storage as
`IncompleteAnalysis`.

Verification is complete for this slice: the `joins_callable` fixture executes
both a resolved and an opaque callable, and native `off`, `analyze`, and
`optimize` suites pass. The serial 100k-operation benchmark (25 samples per
cell, `-C opt-level=3`) records 590.48 → 379.56 ns/op for direct helpers and
626.13 → 359.34 ns/op for typed indirect helpers when CFA selects fixed storage.
See `../joins-library/docs/callable-cfa-benchmark.md` and the raw TSV.

Remaining callable work is intentionally separate: propagate callable facts
through ordinary helper parameters/returns, model closure/function captures,
handle trait-object/foreign calls with cross-crate summaries, and expose the
resolved fact to result-channel fusion once that transform has a sound
ownership certificate. Do not treat this slice as general devirtualization.
