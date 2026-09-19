# NEXT: analysis-driven shared join specialization

Date: 2026-09-19. **This is the next execution plan. Start here.**

This plan follows the private forwarding work and expanded benchmark run at
Rust `8ad80e7ed2f` and library `ce12252`. It supersedes the immediate sequencing
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

Latest focused forwarding: 533.90/536.86/21.89 ns/op off/analyze/optimize.
The expanded matrix exposes the larger remaining gaps: roughly 10× MPSC, 30×
completion and 37× mutex/counter versus handwritten controls. These ratios are
workload-specific, not guarantees of achievable speedups. See
[the expanded evidence](joins-benchmark-expanded-20260918/README.md).

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
- The first cross-body state-token proof is now live.  The positive witness
  records one ordinary seed, one complete-pattern claim and one named-helper
  re-emission, proving `AtMost(1)`; the duplicate-producer witness is rejected
  as `DuplicateSeed`.  Endpoint-local completeness ignores generated wrapper
  escapes while still rejecting unknown source callers and unknown effects in
  the selected reaction.
- Optimize mode now consumes only those positive certificates into an explicit
  `state_token_lowerings` record selecting `FixedUnarySlot`; analyze mode emits
  the evidence but selects no representation.  This is a checked compiler
  decision surface, not yet executable storage: section 6 must still lower the
  record into typed MIR operations and remove the generic channel queue without
  changing off/analyze behavior.
- The library runtime now has a proof-facing `DynamicMatcherStoragePolicy` and
  exact per-channel inline slots with fallible admission; occupied proven slots
  never grow a FIFO while unrelated channels retain dynamic queues.  All 58
  runtime unit tests pass.  The compiler-to-constructor
  bridge is intentionally still absent, so this preparation does not affect
  benchmark numbers or claim a completed storage optimization.

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
directly. Preserve demand and competition. For shared state, specify the atomic
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

## 7. Measure, generalize, then migrate DataFusion

After correctness gates, run the focused counter benchmark against the native
control and all CFA modes. Collect allocation counts separately and sequential
perf profiles with instruction/basic-block attribution. Record sample counts
and uncertainty; do not interpret sampled IP percentages as exact instruction
latency. Run the full randomized matrix after this structural change.

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
