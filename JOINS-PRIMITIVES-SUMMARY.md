# Join concurrency primitives: performance and optimisation status

Updated 2026-09-21.

This is the compact performance and gap summary for the concurrency primitives
used throughout the research prototype.  The detailed raw samples, confidence
intervals, compiler provenance and CFA dump counts are in the
[full benchmark report](../join-benchmarks/results/full-all-dispatch-20260919/benchmark-report.html)
and its [protocol matrix](../join-benchmarks/PROTOCOL-MATRIX.md).

## How to read the numbers

The main table is the latest complete matrix: 5,000 iterations, five warmups,
30 randomized blocks, four workers, and 10,000 bootstrap repetitions.  Every
sample passed its operation-count and checksum/invariant check.  “Joins —
optimize” means the current `-Zjoin-cfa=optimize` mode at the time of that run;
it does **not** mean that the complete thesis optimisation programme is
implemented.  The ratio is optimized join time divided by the handwritten
baseline, so values below 1.0 are lower elapsed time.

The matrix was built from Rust `eefa709551299f553b585d234312feea58baabaf`
and library `82f01e0f789ef36faaacb0a639700f73525f5087`.  The current Rust
branch is newer (`75f49897ae2`), and the fixed atomic-pair lowering landed
after this matrix, so the mutex follow-up is reported separately below.

## Complete primitive matrix

| Primitive | Native implementation | Joins — CFA off | Joins — CFA analyze | Joins — CFA optimize | Optimize / native |
| --- | ---: | ---: | ---: | ---: | ---: |
| Rendezvous | 21,287 ns/op | 589 | 596 | **588** | **0.03×** |
| MPSC delivery | 80.1 ns/op | 685 | 720 | **681** | **8.50×** |
| MPMC delivery | 680 ns/op | 695 | 705 | **679** | **1.00×** |
| Condvar hand-off | 21,950 ns/op | 9,321 | 9,404 | **9,521** | **0.43×** |
| Work/resource admission | 1,394 ns/op | 1,224 | 1,387 | **1,302** | **0.93×** |
| Completion counter | 53.0 ns/op | 1,730 | 1,708 | **1,770** | **33.39×** |
| Reusable barrier | 13,871 ns/op | 13,228 | 13,846 | **13,523** | **0.97×** |
| Reader/writer admission probe | 42.8 ns/op | 4,096 | 3,802 | **3,276** | **76.53×** |
| Mutex/counter | 30.0 ns/op | 1,004 | 1,008 | **976** | **32.51×** |
| Scoped thread join | 66,890 ns/op | 65,809 | 68,028 | **64,970** | **0.97×** |
| One-time initialization | 61,767 ns/op | 64,621 | 62,400 | **61,856** | **1.00×** |
| Async request/reply | 407.6 ns/op (Tokio) | 49.8 | 50.1 | **49.4** | **0.12×** |

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
* **Async request/reply** uses Tokio as the native control, while the isolated
  unary join is caller-driven and executor-free.  It demonstrates the ordinary
  async-shaped fast path, not shared-reaction scheduling parity.
* **Thread join** and **once** include cold thread/initialisation setup, so their
  near-parity results do not establish hot-path equivalence.

The near-parity rows are MPMC, work/resource, barrier, scoped thread join and
once.  The material remaining gaps in this matrix are MPSC, completion,
reader/writer admission and mutex.  The large apparent wins are the protocol
comparisons called out above, not evidence that all joins are already faster.

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
  direct local helper arguments, returns and copy/move/borrow chains.  Unknown
  calls, escaping handles, unsupported closures and wider control flow remain
  open/unknown.
* An endpoint-wide lowering certificate binds one allocation, compatible
  proofs, a channel mask and one storage strategy.  Optimized MIR carries the
  selected strategy and typed reply map; synchronous `CompleteReplies` is
  placed at the real `Return` with destination `_0`.
* The current executable storage choices are restricted unary/fixed-pair
  representations and the exact-`u64` atomic pair path.  One-way emissions do
  not manufacture reply cells.  The runtime uses atomics/CAS where selected;
  no optimization recognizes or substitutes a particular lock library.
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

1. **Instance-sensitive interprocedural CFA.**  Complete the bounded history /
   foreground-background value analysis across closures, general callers and
   returns, loops, recursion, aggregates and dynamically separated instances.
   The current direct-helper slice is not an implementation of the thesis
   analysis.
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

* [Complete 2026-09-19 HTML matrix](../join-benchmarks/results/full-all-dispatch-20260919/benchmark-report.html)
* [Protocol definitions and equivalence caveats](../join-benchmarks/PROTOCOL-MATRIX.md)
* [Atomic-pair follow-up](../join-benchmarks/results/atomic-pair-20260920/README.md)
* [Current perf attribution](../join-benchmarks/docs/perf-atomic-mutex-20260921.md)
* [Compiler optimisation inventory](../joins-library/docs/missing-optimisations.md)
* [Dovetail source audit](../joins-library/docs/dovetail-audit.md)
* [Current next-step plan](docs/joins-next-plan.md)

