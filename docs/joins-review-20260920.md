# Review checkpoint — 2026-09-20

This review controls the immediate order in `joins-next-plan.md`. It is a quick
source/evidence review, not a full soundness audit. No benchmarks were rerun.

## Assessment

The performance direction is promising. Isolated unary joins already use ordinary
futures and approach ordinary async costs. Private forwarding eliminates real
allocations. Shared state-token CFA now changes executable MIR, and counters
confirm that the atomic implementation is used. However, the latest mutex figures
(39.84 ns/op native, 398.37 off, 380.74 analyze, 187.71 optimize) are provisional:
timing used instrumentation-enabled join binaries with counting disabled, variants
were sequential, and the preceding fixed implementation was not measured in the
same experiment. They do not isolate the atomic change's incremental benefit.
Off/analyze also improved substantially versus the previous run. Bootstrap
intervals over samples cannot remove those experimental confounders.

The IR direction is reasonable but its implementation is accumulating adapters.
The compiler diff against the merge base with local origin/main spans 59 files,
8,375 insertions and 14 deletions in compiler/, including tests/formatting only
where located there. Size is a warning to consolidate, not proof of bad design.
JoinCall on ordinary Call terminators preserves Rust operands and unwind edges;
reaction bodies can reuse coroutine MIR. The current atomic change nevertheless
retargets library helper calls: matching is not yet generated as ordinary MIR
fields, branches and atomics. The specialized runtime still uses a FIFO mutex.
It is a useful intermediate experiment, not completion of the no-library-lock
optimized architecture. Avoid adding a new helper family for every primitive or
payload width.

## Corrections and prerequisites

- Instantiating signatures is not full ABI validation: both resolver helpers
  still compare input count and output, not input types, generic parameter layout,
  predicates or calling convention. MIR validation in tests is not a production
  proof. Check layout before instantiating a candidate; reject incompatible shims.
- Constructor and endpoint methods are rewritten in separate bodies. Per-body
  preflight does not establish all-or-nothing representation selection for the
  endpoint. Build one validated endpoint plan before applying any rewrite.
- A 0/1 state token does not prove a 0/1 request queue or reply storage bound.
  Four concurrent callers can require multiple pending replies. Closedness alone
  does not bound multiplicity either. Require a separate invocation/liveness proof.
- Target width checks must include CAS capability (`target.atomic_cas`). The new
  fallback does not make the whole runtime portable: existing IDs use AtomicU64.
- Atomic cancellation drains the request queue and takes the token in separate
  steps. The claimed single linearization point needs a proof or correction.
  Withdrawal currently removes/drops payloads under the queue mutex; review
  reentrant destructors and move destruction outside the guard where necessary.
- Shared immediate execution remains a compatibility policy. Verify demand,
  admission, failure and cancellation against the accepted async contract before
  presenting these benchmarks as the final language semantics.
- Counter evidence identifies executed operations, not their latency. Fresh
  assembly/perf evidence is needed to call FIFO/reply/trampoline the dominant cost;
  dormant trace branches do not establish executed trace overhead.

## Next execution order and gates

1. Consolidate one endpoint lowering plan containing definition/instance identity,
   validated ABI operations, policy and proven storage facts. Reject the entire
   endpoint on any missing/malformed shim, unsupported generic layout, recursive
   multiplicity or unsupported atomic capability. Add negative fixtures that
   prove constructor and all operations stay generic together. Batch one build.
2. Resolve cancellation/withdrawal ownership above, with adversarial race and
   reentrant-drop tests. Preserve declared async demand timing in any new lowering.
3. Freeze clean non-instrumented timing binaries and separate diagnostic binaries.
   Run shuffled paired native/off/analyze/optimize mutex samples, plus a matched
   pre-atomic fixed control if claiming the atomic increment. Archive raw data,
   compiler/source hashes, flags, checksums and instrumentation status. No timing
   alongside builds, tests or other benchmarks.
4. Use measured attribution to choose one reusable lowering from the endpoint
   plan into ordinary MIR. Keep one semantic operation carrier and typed group
   definition; analysis summaries are derived diagnostics, not another authority.
   Emit fields/claim branches/atomics with explicit ownership and unwind effects;
   reuse ordinary coroutine lowering for suspending bodies. Remove the superseded
   adapter in the same slice. Do not force synchronous reactions into coroutines.
5. Bound request/reply storage only with a separate proof covering concurrent
   consumers, completion lifetime and cancellation. Prove stack lifetime separately
   from capacity. Unknown cases use the generic representation; proved fixed
   storage never silently grows. Verify positive and negative MIR/LLVM witnesses.
6. Once the focused result and semantic gates pass, restore the complete benchmark
   matrix before further optimization families. Then choose a DataFusion protocol
   using those same operations and measure both code complexity and execution cost.

Pause for a guiding review after steps 1–3 with the endpoint plan, rejection
fixtures and paired measurements. The next decision should be based on those
artifacts, rather than assuming a bounded reply slot is already justified.
