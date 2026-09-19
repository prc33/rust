# NEXT: analysis-driven shared join specialization

Date: 2026-09-19. **This is the next execution plan. Start here.**

This plan follows the private forwarding work, state-token bridge at Rust
`c3f548c89f5`, and all-channel dispatch benchmark at library `b547504`. It supersedes the immediate sequencing
in `joins-private-storage-handover.md`, `joins-next-slice.md`, and older
optimization inventories. Their safety requirements and regression fixtures
remain applicable. The accepted async semantics remain authoritative.

## Objective and starting point

Implement the missing chain in rustc:

**channel/instance flow → closedness and occupancy proofs → specialized
storage and matching → eligible transition fusion → ordinary MIR/LLVM optimization.**

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
  selects `FixedPairMatcher` in optimize mode. The MIR constructor call is
  retargeted to the distinct `PairMatcher::new_with_fixed_pair_mask` symbol
  and carries the proven mask (`1` in the positive fixture); `off` and
  `analyze`, plus competing, reordered, async, scoped and non-canonical
  endpoints, retain `new_with_channel_mask` and mask `0`. The optimize dump
  contains the fixed symbol and the CFA graph records
  `strategy=FixedPairMatcher`; the three native gates and stage-1 compiler
  build pass. This is real executable-MIR selection, but the ABI currently
  constructs the same typed `PairState` implementation as the generic mask
  path. It therefore proves safe selection and fallback, not yet removal of
  `Arc`, `Mutex`, reply cells or all `PairQueue` branches, and no speedup is
  attributed to it until a paired timing/assembly gate demonstrates one.

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

The proof-selected constructor ABI is now the completed first step, not the
target representation. Implement the next slice in this order:

1. Define the compiler/runtime contract for `FixedPairMatcher` using the actual
   channel payload and reply types. It may use ordinary Rust fields and
   atomics/CAS or a proven local synchronization mechanism, but it must not be
   selected because the code resembles a library mutex and must not depend on
   a particular lock implementation. Keep a generic queue-backed matcher for
   every unsupported case.
2. Keep the existing `JoinStorageLowering` proof checks as the admission gate,
   then make `new_with_fixed_pair_mask` construct a representation whose hot
   paths are statically specialized (for example typed fixed slots and a
   direct complete-pair branch). The compiler must not identify or replace a
   library lock implementation. Any atomics/CAS must be justified by the
   join state protocol and have an explicit ownership/ordering proof. The
   generic `PairQueue`/reply path remains the fallback.
3. Preserve the operation through optimized MIR long enough for ordinary MIR
   passes and coroutine lowering to see the typed fields, direct matching
   branch, and reply completion. Lower to the canonical runtime ABI only after
   ownership, drop, panic/unwind and cancellation paths have been checked. At
   the existing backend boundary, erasing a consumed descriptor is acceptable;
   erasing it before this lowering is not.
4. Extend the current positive and negative MIR fixtures. The positive
   state-token pair must show `FixedPairMatcher` and the fixed constructor;
   once the runtime specialization is real, its post-inline MIR/assembly must
   show no dynamic `PairQueue` construction on the proven channels. A
   competing rule, extra producer, escaped instance, reordered pattern,
   unknown call, borrowed payload, and non-proven bound must retain the
   generic matcher and record a rejection reason. Off and analyze must keep
   the generic representation while preserving behavior.
5. Verify the generated MIR and assembly for removed enum dispatch, queue
   growth, erased payload/reply-cell allocation and unnecessary scheduling
   work. The current gate is only symbol/mask/strategy evidence; the next gate
   must add allocation counters and instruction-level evidence. Then run the
   focused direct-source benchmark serially, with allocation counters and
   checksums, before touching the full matrix. A successful gate requires a
   measured reduction in the identified generic work, not just a changed
   symbol or metadata dump.

The constructor retarget is the first place where the CFA result becomes an
executable compiler optimization. Do not proceed to completion/MPSC
generalization until the fixed body has a sound fallback and a direct-source
gate demonstrates that the specialized representation, rather than only its
symbol, reaches generated code.

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
