# Join concurrency primitives: performance and optimisation status

Updated 2026-09-22.

This is the compact performance and gap summary for the concurrency primitives
used throughout the research prototype.  The detailed raw samples, confidence
intervals, compiler provenance and CFA dump counts are in the
[full benchmark report](../join-benchmarks/results/full-20260922-callable-cfa/benchmark-report.html)
and its [protocol matrix](../join-benchmarks/PROTOCOL-MATRIX.md).

## How to read the numbers

The main table is the latest complete matrix: 5,000 iterations, five warmups,
30 randomized blocks, four workers, and 10,000 bootstrap repetitions.  Every
sample passed its operation-count and checksum/invariant check.  “Joins —
optimize” means the current `-Zjoin-cfa=optimize` mode at the time of that run;
it does **not** mean that the complete thesis optimisation programme is
implemented.  The ratio is optimized join time divided by the handwritten
baseline, so values below 1.0 are lower elapsed time.

The current matrix was built from Rust
`488a7e554e55bf9a9df2e21f65f4c20366919237` and library
`2c7633f80899ffc653fc0caca743e498c24ca12c`. The result archive records the
working-tree status and stage-1 compiler provenance.

## Complete primitive matrix

| Primitive | Native implementation | Joins — CFA off | Joins — CFA analyze | Joins — CFA optimize | Optimize / native |
| --- | ---: | ---: | ---: | ---: | ---: |
| Rendezvous | 21,945 ns/op | 583.7 | 564.3 | **574.2** | **0.03×** |
| MPSC delivery | 79.9 ns/op | 586.0 | 517.1 | **580.8** | **7.27×** |
| MPMC delivery | 535.8 ns/op | 560.4 | 524.0 | **555.9** | **1.04×** |
| Condvar hand-off | 19,328 ns/op | 9,725 | 10,294 | **11,081** | **0.57×** |
| Work/resource admission | 1,243 ns/op | 1,322 | 1,322 | **1,418** | **1.14×** |
| Completion counter | 56.3 ns/op | 1,837 | 1,883 | **1,963** | **34.87×** |
| Reusable barrier | 14,516 ns/op | 16,573 | 15,192 | **14,070** | **0.97×** |
| Reader/writer admission probe | 48.1 ns/op | 3,929 | 4,472 | **4,312** | **89.61×** |
| Reader/writer fair schedule | 14,953 ns/op | — | — | **15,375** | **1.03×** (pooled focused rerun; see below) |
| Mutex/counter | 28.4 ns/op | 720.6 | 528.3 | **536.2** | **18.90×** |
| Scoped thread join | 61,845 ns/op | 56,171 | 60,448 | **57,321** | **0.93×** |
| One-time initialization | 55,833 ns/op | 60,959 | 61,470 | **60,890** | **1.09×** |
| Async request/reply | 407.0 ns/op (Tokio) | 52.0 | 52.7 | **51.5** | **0.13×** |

These are coordination microbenchmarks, not a claim that a join is a better
implementation of every named standard primitive.  Their protocol definitions
matter:

* **Rendezvous** compares a two-input local join with a zero-capacity channel
  round trip; it has different participant placement and wake behaviour.
* **Condvar** compares the join state machine with a mutex/condvar predicate
  hand-off.  The result is useful evidence about this protocol, not a generic
  matcher win.
* **Work/resource** has an untimed exact-reply validation companion; the timed
  row is deliberately a lower-overhead admission comparison.
* **Completion** schedules an async reaction per decrement, while the native
  counter stays in one mutex/condvar protocol.
* **Reader/writer** is explicitly an admission probe.  Its separate validation
  witness checks reader overlap, writer exclusion and the real payload update;
  the timed join row must not be presented as a full `RwLock` replacement.
* **Reader/writer fair schedule** is a separate deterministic benchmark: three
  readers complete before one writer in every round, with the same barriers in
  both controls. It is the next apples-to-apples timing gate.
* **Async request/reply** uses Tokio as the native control, while the isolated
  unary join is caller-driven and executor-free.  It demonstrates the ordinary
  async-shaped fast path, not shared-reaction scheduling parity.
* **Thread join** and **once** include cold thread/initialisation setup, so their
  near-parity results do not establish hot-path equivalence.

The near-parity rows are MPMC, barrier, scoped thread join and once; the
work/resource row is modestly slower. The material remaining gaps in this
matrix are MPSC, completion, reader/writer admission and mutex. The large
apparent wins are the protocol comparisons called out above, not evidence that
all joins are already faster.

## Focused MPSC/RwLock follow-up — 2026-09-22

After the archived matrix, the compiler/runtime changes were rebuilt and the
two requested endpoints were rerun with 2,000 iterations, four warmups, 20
timed samples and four worker threads. Every sample passed its checksum and
operation-count checks.

| Protocol | Native | Join, `-Zjoin-cfa=optimize` | Ratio | Relevant proof/lowering |
| --- | ---: | ---: | ---: | --- |
| MPSC delivery | **142.0 ns/op** | **391.9 ns/op** | **2.76×** | MPSC remains generic: its payload/multiple producers require FIFO storage, with no MPSC/name/API recognizer. Typed `PairMatcher` admission fusion reduced an old generic rerun of 950.0 ns/op to 391.9 ns/op. |
| RwLock fair schedule | **14,953 ns/op** | **15,375 ns/op** | **1.03×** | Endpoint-wide CFA proved the three persistent slot bits (`0b111`) and lowered construction to `DynamicMatcher::new_with_finite_state_mask(11, 7)`. |

The MPSC fusion is deliberately representation-generic: it checks only the
already-typed pair matcher, preserves the older-left/FIFO condition, and falls
back to ordinary submit-then-dispatch. The CFA dump rejects that endpoint for
finite-state storage: its payload channel is not persistent unit state, and
multiple producers require FIFO storage. The RwLock
path is likewise generic JCAM transition storage: state bits and overflow
queues share the existing matcher lock, so this is not a lock-library pattern
match or a claim that the complete matcher is stack allocated. For context, the
same focused builds measured approximately 426.2 ns/op for MPSC with CFA off
and 15,818.8 ns/op for the fair RwLock with CFA off; the optimized RwLock path
is about 2.8% faster than that off window. The optimized/native medians above
pool two sequential 20-sample windows (40 observations per side) to reduce
the visible host scheduling variance.

The native and optimized fair runs were measured in separate processes on the
same host; the 1.03× ratio is therefore a close comparison, not a claim of a
statistically significant win. Raw focused samples and exact commands are
recorded in [`docs/focused-20260922-rwlock-mpsc.md`](../join-benchmarks/docs/focused-20260922-rwlock-mpsc.md).

## Completion/mutex follow-up — 2026-09-22

The same current optimized binary was also compared with CFA-off and native
controls (2,000 iterations, four warmups, 20 samples, four workers):

| Protocol | Native | CFA off | CFA optimize | Optimize/native |
| --- | ---: | ---: | ---: | ---: |
| Completion | **113.6 ns/op** | 2,587.5 ns/op | **1,763.9 ns/op** | **15.5×** |
| Mutex/counter | **42.4 ns/op** | 463.8 ns/op | **276.1 ns/op** | **6.5×** |

Thus the new analysis/fusion work helps (about 32% and 40% over CFA off), but
neither benchmark is competitive. Completion is now accepted by the
finite-state certificate: the async reaction's `ready()` re-emission is
represented by bit `0b1000`, while `remaining(u64)` stays on a FIFO and
`done()`/`wait()` retain their ordinary channels. The runtime still pays the
coroutine/executor, wake and scheduling costs, so selecting the bit mask did
not make the completion row competitive by itself. `JoinMutex` carries a
`u64` value token, so the unit-state bit-mask lowering does not apply; its
generic pair fusion still helps, but dynamic queue/reply and payload-transfer
costs remain. Closing these gaps requires generic CFA-proven value-token and
reply-slot lowering plus direct/shared coroutine continuation fusion, not a
matcher recognizer for mutex or counter APIs.

The async state-machine fixture in `joins-library/compiler-tests/joins_async.rs`
now executes this completion shape in all three CFA modes. In optimize mode
the graph proves the endpoint-wide state mask and MIR carries the same
`FiniteStateMask` certificate onto construction, registration and async
dispatch; the coroutine body remains the normal Rust future.
The CFA body record carries asyncness separately as a suspension effect, so
value-flow facts remain eligible for this representation while executor/
continuation-removal proofs still see `may_suspend`.
This now includes ordinary `async fn` helpers called by a reaction: their
typed MIR call edges participate in the same value-flow solution, while the
helper body is independently marked `is_async` and widens reachable contexts
with `may_suspend`. No helper is made opaque merely because it returns a
future.

### Async state-mask smoke rerun — 2026-09-22

After enabling the async proof, the completion row was rerun from freshly
rebuilt binaries (2,000 iterations, five warmups, 30 samples, four workers;
all checksums were `2000`). This is a separate serial window, so it is a
regression signal rather than a replacement for the paired matrix above:

| Variant | Median ns/op | Mean ns/op |
| --- | ---: | ---: |
| Handwritten control | **108.7** | 119.7 |
| Joins, CFA off | 2,627.4 | 2,728.1 |
| Joins, CFA optimize (async state mask) | **2,073.5** | 2,202.2 |

The state-mask proof is therefore active and preserves semantics, but it does
not remove the dominant async future/executor/reply work. The next useful
optimization is direct/shared coroutine continuation and reply-slot lowering,
not a broader unit-bit recognizer.

## Newer mutex-only result

The compiler-selected `FixedAtomicU64Pair` lowering was measured after the
complete matrix.  This is a separate serial 100-sample window, not a rerun of
the full randomized matrix:

| Variant | Median |
| --- | ---: |
| Handwritten mutex/counter | 39.840 ns/op |
| Joins, CFA off | 398.375 ns/op |
| Joins, CFA analyze | 380.738 ns/op |
| Joins, CFA optimize (`FixedAtomicU64Pair`) | **187.714 ns/op** |

The optimized path is 4.71× the separately measured native control and 0.471×
the join-off path.  The result is recorded in
[`join-benchmarks/results/atomic-pair-20260920/README.md`](../join-benchmarks/results/atomic-pair-20260920/README.md).
A later optimize-only smoke run measured 173.560 ns/op median (178.939 mean),
but did not rerun the handwritten control in the same artifact, so it is a
regression snapshot rather than a new ratio claim.  No complete post-atomic
matrix has been run yet.

Perf attribution for the atomic path found the largest local costs in generated
endpoint `available`/`acquire`, atomic admission and dispatch, `PairMatcher`
drop glue, reply demand, allocation/free and futex wakeup.  The next useful
experiment is compiler-visible local/borrowed claim lowering for proven
unscoped synchronous reactions; another queue heuristic is unlikely to close
the remaining gap by itself.  See the
[perf attribution note](../join-benchmarks/docs/perf-atomic-mutex-20260921.md).

## What the compiler currently proves or selects

The implemented slice is useful but deliberately narrow:

* Typed endpoint, channel and reaction identities survive into compiler-owned
  descriptors and CFA summaries.
* A bounded intrabody dataflow pass tracks join values, moves/copies,
  aggregates, escapes, yields and local occupancy.  Loop and helper
  multiplicity are rejected conservatively.
* The crate-level query propagates endpoint aliases through a bounded set of
  direct local helper arguments, returns and copy/move/borrow chains.  Its
  compiler-native k-context layer (`-Zjoin-cfa-depth`, default 1) retains
  ordinary helper call strings, connects nested MIR bodies without charging
  generated adapters, and joins suspension/escape/external effects.  Unknown
  calls, escaping handles, unsupported captures and wider control flow remain
  open/unknown; every context for a consumed proof must be safe.
* An endpoint-wide lowering certificate binds one allocation, compatible
  proofs, a channel mask and one storage strategy.  Optimized MIR carries the
  selected strategy and typed reply map; synchronous `CompleteReplies` is
  placed at the real `Return` with destination `_0`.
* The current executable storage choices are restricted unary/fixed-pair
  representations and the exact-`u64` atomic pair path.  One-way emissions do
  not manufacture reply cells.  The runtime uses atomics/CAS where selected;
  no optimization recognizes or substitutes a particular lock library.
* Endpoint-wide transition CFA now emits a generic JCAM-style state-machine
  certificate. Persistent one-way channels re-emitted by reactions use a
  bit-mask runtime path, while request/result channels retain their queues.
  Duplicate state admissions retain a compatibility overflow queue until
  caller-sensitive multiplicity proves that path unreachable. The lowering is
  selected from typed rule/re-emission edges, never from an MPSC or lock API.
* Isolated unary result-bearing rules can use the caller-driven ordinary-future
  shape.  Private forwarding/result fusion has a narrow validated witness, but
  it is not a general CFA-driven shared-join rewrite.

The semantic join operations are not yet fully executable native HIR/MIR
operations: the current typed markers and strategy metadata are consumed only
by a narrow lowering slice and are erased before generic backend codegen.  A
future implementation must lower claim, demand, completion, withdrawal and
cancellation into ordinary MIR/coroutine state before relying on LLVM to remove
the remaining work.

## Thesis and Dovetail optimisation gap

The project’s source audit is in
[`joins-library/docs/missing-optimisations.md`](../joins-library/docs/missing-optimisations.md)
and [`joins-library/docs/dovetail-audit.md`](../joins-library/docs/dovetail-audit.md).
The following are the thesis/Dovetail techniques that are still absent or only
partial in the compiler.  “Partial” means that a fact, runtime experiment or
metadata exists, but the proof is not yet consumed by generated code.

### CFA and representation work still missing

1. **Complete endpoint-specific instance-sensitive CFA.**  The compiler now
   has the first bounded call-string/effect layer, but it still needs to key
   contexts by concrete endpoint instances, propagate captures and
   foreground/background values, and model coroutine output/drop edges,
   general callers, loops, recursion and dynamically separated instances.
2. **Whole-instance closedness.**  Prove `Closed`, `Open` or `Unknown` for each
   concrete group instance, including participants, execution owner, demand,
   cancellation and lifetime.  A locally closed reaction body is not enough.
3. **General occupancy and queue-bound inference.**  Prove exact 0/1/N bounds
   over all producers, consumers, loops and competing rules.  Current
   `Exact(0)`/`AtMost(1)` facts are narrow metadata, not a general proof.
4. **Functional/no-storage channels.**  Dovetail’s functional channels and
   direct value transfer are not compiler-selected in Rust.
5. **Closed fast/slow representations.**  The thesis/Dovetail closed-instance
   path can avoid ordinary queues and use local/frame or stack storage.  Rust
   does not yet select this per concrete instance, and closedness alone must not
   be treated as a stack-lifetime proof.
6. **General fixed storage.**  Beyond the current unary/fixed-pair witnesses,
   select inline slots, fixed buffers, bitsets or stack/coroutine-frame state
   with exact ownership and drop behaviour.  Unknown cases must retain a safe
   dynamic representation.

### Matching, fusion and inlining still missing

7. **Immediate match-before-enqueue.**  Generate a typed atomic claim fast path
   that checks a complete eligible match before queueing, while preserving FIFO,
   competition, demand and admission semantics.
8. **Generated matching automata.**  Compile fixed definitions into typed
   decision trees/status masks and matching transitions rather than generic
   matcher objects.  JoCaml-style equivalent-channel grouping, status-bitfield
   construction and unreachable-state pruning are also absent; these are
   related reference optimisations rather than claims about the Rust standard
   library.
9. **General result/continuation fusion.**  Extend the private unary witness to
   explicit continuation passing and result-bearing channels, with independent
   reply demand, cancellation, panic/error and reentrancy preserved.  The
   `joins-cfa` fused matcher remains a library oracle, not rustc output.
10. **Transition and definition/instance inlining.**  Prove construction
    frequency, uniqueness and scheduling safety, then inline eligible
    transitions/definitions.  The thesis warns that indiscriminate transition
    inlining can remove parallelism or introduce deadlock.
11. **Singleton/unique-instance specialization.**  Prove uniqueness without
    conflating distinct allocations or thread lifetimes.  Dovetail’s audited
    `singleton` path is itself incomplete, so this is a research target, not a
    missing “known-good” reference feature.

### Async, ownership and backend work still missing

12. **Shared async reaction fusion.**  Reuse ordinary coroutine lowering while
    preserving pending/ready behaviour, independent wakers, pinning, drops,
    cancellation and one execution owner for multiple replies.
13. **Borrowed/local execution proofs.**  Eliminate endpoint clone/refcount
    setup for proven caller-owned synchronous reactions; permit non-`Send`
    local execution only where the lifetime and executor boundary prove it
    safe.  Detached/shared reactions still require owned state.
14. **Compiler lowering of semantic operations.**  Build native HIR/MIR for
    create/register/demand/claim/complete/withdraw/cancel and lower proven
    forms into normal calls, locals and coroutine state.  Current markers do not
    yet expose enough to borrowck/drop elaboration or codegen.
15. **LLVM-facing join lowering.**  Once typed MIR is real, expose only proven
    facts to ordinary LLVM optimisation (inlining, SROA, mem2reg, CFG cleanup,
    atomic lowering and target-aware codegen).  LLVM cannot reconstruct join
    protocol facts from erased queues and runtime symbol names, and no custom
    LLVM join pass exists yet.
16. **Scheduler/runtime specialisation.**  The compiler does not yet generate
    runnable transition work, work-stealing placement or a target-specific
    fast scheduler.  Runtime executor policy remains pluggable; demand alone
    does not create parallelism.

These gaps are ordered by dependency: instance CFA and closedness first, then
hard bounds and typed storage/matching, then fusion/inlining, then shared async
and backend cleanup.  DataFusion migration should consume only transformations
that have passed the corresponding semantic and benchmark gates.

## References and reproduction

* [Complete 2026-09-22 HTML matrix](../join-benchmarks/results/full-20260922-callable-cfa/benchmark-report.html)
* [Committed 2026-09-22 matrix notes](../join-benchmarks/docs/full-20260922-callable-cfa.md)
* [Protocol definitions and equivalence caveats](../join-benchmarks/PROTOCOL-MATRIX.md)
* [Atomic-pair follow-up](../join-benchmarks/results/atomic-pair-20260920/README.md)
* [Current perf attribution](../join-benchmarks/docs/perf-atomic-mutex-20260921.md)
* [Compiler optimisation inventory](../joins-library/docs/missing-optimisations.md)
* [Dovetail source audit](../joins-library/docs/dovetail-audit.md)
* [Current next-step plan](docs/joins-next-plan.md)
