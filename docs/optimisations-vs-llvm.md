# Join optimisations versus LLVM

Compiler-agent handoff, reviewed 2026-09-16.

## Recommendation

Use rustc to establish join semantics and choose representations; expose ordinary
control flow, concrete values, and direct calls so LLVM can optimise the result.
Avoid implementing scalar replacement, dead-store elimination, ordinary function
inlining, constant propagation, or generic CFG simplification again for joins.

A custom LLVM pass is justified when an optimisation needs facts that become
available after LLVM inlining or LTO, benefits materially from LLVM analyses, or
operates on a stable runtime interface shared by several frontends. There is no
demonstrated need for such a pass in this checkout yet. Private forwarding fusion
is a possible experiment, not an established recommendation to move fusion out
of MIR.

The initial inventory was a source/documentation review. A small generated-IR
probe is now archived in
[`joins-library/docs/ir-cfa-evidence/llvm-lowering-20260916.tsv`](../../joins-library/docs/ir-cfa-evidence/llvm-lowering-20260916.tsv);
it is deliberately limited to attribution of the current unary lowering and
does not claim a backend join transform. The inventory is
[missing-optimisations.md](../../joins-library/docs/missing-optimisations.md).

## Corrections to the preceding discussion

1. **LLVM coroutine elision is not available merely by enabling a pass for Rust
   futures.** Rust already constructs the future frame, poll state machine, and
   drop implementation in [MIR coroutine lowering](../compiler/rustc_mir_transform/src/coroutine/mod.rs).
   LLVM CoroSplit/CoroElide require their own coroutine intrinsic representation.
   Adopting it would be a substantial lowering/ABI project, with Rust pinning,
   suspension, drop, and cancellation requirements to preserve. Ordinary LLVM
   optimisation can still simplify the current poll functions.
   See [LLVM coroutines](https://llvm.org/docs/Coroutines.html).
2. **SROA and mem2reg are not general heap-to-stack transformations.** They can
   eliminate suitable local allocas; they do not turn an arbitrary
   `Arc<Mutex<ReplyCell>>` into an SSA value because it is annotated private.
   Allocation elimination is conditional and must be demonstrated on emitted IR.
   See [LLVM frontend guidance](https://llvm.org/docs/Frontend/PerformanceTips.html).
3. **Inlining a function differs from running a reaction immediately.** LLVM's
   inliner substitutes an existing call body. Replacing enqueue/schedule/wake
   with a direct call changes a protocol and needs a separate semantic proof.
4. **A custom LLVM pass can understand concurrency/runtime semantics.** The
   location of a pass does not prohibit that. LLVM's
   [OpenMPOpt](https://openmp.llvm.org/optimizations/OpenMPOpt.html) is a real
   precedent for runtime-aware optimisation. The question is where the required
   facts and stable operations are easiest to retain and verify.
5. **Custom attributes are not automatically actionable or safely transported
   proofs.** Their meanings, scope, and handling under cloning, inlining, and
   linking must be designed. A function attribute cannot express a property of
   just one dynamic group instance without additional representation.

## Evidence from this checkout

Reviewed rust commit `183c090545f` (with CFG transfer at `d766b9f7d50`) and
joins-library commit `308559a`. The available
`rust/build/host/stage1/bin/rustc -vV` reports Rust `1.100.0-dev`, LLVM `23.1.1`;
its embedded commit is unknown. Online LLVM documentation tracks development,
so check exact attribute spelling and pass availability against the actual build.

- [Builtin join expansion](../compiler/rustc_builtin_macros/src/joins.rs)
  selects direct unary futures but emits matcher submission and dispatch for
  shared cases. Even the direct-unary generated endpoint still contains a
  matcher field and constructs it: bypassing method dispatch does not establish
  that endpoint construction costs disappear.
- [Join facts](../compiler/rustc_middle/src/middle/joins.rs) explicitly
  distinguish body-local occupancy from a bound on a concrete group instance.
  A complete local event summary is not sufficient to constrain all callers,
  loops, producers, and competing rules. `Closed` is currently reserved for the
  caller-owned direct-unary representation.
- [The runtime](../../joins-library/joins-runtime/src/lib.rs) includes Arc ownership, mutexes,
  reply cells, wakers, cancellation registration, tracing, and executor state.
  These may carry observable effects; removing their storage is more than
  eliminating an unused temporary.
- [The LLVM wrapper](../compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp)
  builds standard optimisation/LTO pipelines and loads pass plugins. A custom
  pass has an integration route, but that alone is not a reason to add one.

The first probe compiles `joins-library/compiler-tests/joins_optimize.rs` with
the stage-1 compiler at `-C opt-level=3 -C codegen-units=1 -C lto=off`. In the
off mode the generated module is 14,934 lines and contains 142 dispatch
references, 180 atomic RMWs and 17 compare-exchanges. In optimize mode the
module is 1,542 lines, has no dispatch references or compare-exchanges, and has
24 atomic RMWs. `UnaryMatcher` references fall from 72 to 14. This is the
expected consequence of selecting the caller-owned future before LLVM; the
remaining references belong to support code and construction/drop paths. It
is a measured lowering result, not evidence that LLVM inferred join semantics.

## Inventory and recommended ownership

“LLVM cleanup” below means a candidate for existing passes after legal lowering,
not a guarantee that the current runtime representation will optimise away.

| Inventory item | Work required before generic LLVM optimisation | LLVM contribution / recommended location |
| --- | --- | --- |
| Direct isolated unary future | Select the direct future and preserve construction/first-poll/drop semantics. Audit residual matcher construction. | LLVM can simplify visible poll calls and temporaries. Keep representation selection in rustc. |
| Arity-specialised endpoints | Generate concrete per-definition storage and operations where useful. | Inline and specialise visible helpers; remove constant dispatch. Existing LLVM passes. |
| Bounded unary slot | Distinguish a hint with overflow fallback from a proved bound or explicit admission contract. | Simplify fixed storage and branches. Do not replace the fallback with an assumption. |
| Native join IR and semantic operations | Preserve endpoint, instance, rule, and operation identity. | Infrastructure enabling later lowering; no generic LLVM substitute. |
| Intrabody value-flow/escape CFA | Determine join-specific facts and their scope. | LLVM capture/alias analyses can supplement low-level facts; they do not establish the complete join protocol. |
| Interprocedural, instance-sensitive CFA | Track concrete groups and channel flows across calls. | LTO exposes additional bodies and calls, but does not supply join CFA automatically. Prefer rustc initially. |
| Closedness to fast/stack groups | Prove lifetime and concurrency conditions; choose local/frame/shared storage. | Scalar replacement of suitable local storage. Closedness alone does not prove stack lifetime or absence of concurrent access. |
| General queue-bound inference | Prove occupancy across all relevant executions, or enforce capacity under the API contract. | Range/loop analyses can help a custom analysis, but do not infer general asynchronous queue bounds. Storage selection belongs with the proof. |
| Functional/no-queue channels | Establish that direct transfer preserves the protocol and eliminate queue operations. | Optimise resulting values and calls. LLVM does not need a special pass for this cleanup. |
| Immediate match-before-enqueue | Generate an atomic claim/fast path with correct FIFO, competing-rule, and admission behaviour. | Simplify emitted conditions and calls. Prefer semantic lowering or a runtime operation with that contract. |
| Private forwarding/result-channel fusion | Prove intermediate protocol removal safe, including observation and cleanup paths. | Prefer MIR first; consider an LLVM runtime-aware pass if post-inlining/LTO visibility supplies a measured extra opportunity. |
| General transition inlining | Prove immediate execution safe with respect to scheduling and reentrancy. | Let the standard inliner handle ordinary direct calls after that decision. |
| Definition/instance inlining | Preserve allocation identity, construction frequency, sharing, and lifetime. | Constructor/helper inlining and constant propagation help, but are not the whole instance transformation. |
| Equivalent-channel grouping | Establish equivalent synchronisation behaviour and encode the grouped representation. | Optimise index operations afterward. Keep grouping in semantic codegen. |
| Status bitfield/matching automaton | Construct representation and transitions. | Optimise masks, switches, and branches; do not expect generic passes to synthesise an automaton from queues. |
| Status pruning/state-space compression | Derive protocol invariants and reachable states. | SCCP/SimplifyCFG remove states exposed as unreachable in IR. General automaton minimisation still needs semantic analysis. |
| Singleton/unique-instance specialisation | Prove uniqueness without conflating distinct allocations or thread lifetimes. | Internal linkage and visible constants help specialise code. A mutable singleton is not a constant. |
| Shared async join/future fusion | Preserve pending/ready behaviour, wakers, pinning, cancellation, drops, and execution order. | Optimise the resulting ordinary state machine. LLVM coroutine passes require a different input representation. |

The reusable LLVM toolkit includes inlining, SROA, SCCP/IPSCCP, InstCombine,
SimplifyCFG, GVN, DSE, and ordinary loop optimisations. Availability, profitability,
and pipeline placement matter; a pass being listed is not evidence it will solve
a particular join case. See the [LLVM pass overview](https://llvm.org/docs/Passes.html).

## Standard attributes: expose facts, not intentions

Audit existing rustc emission and LLVM inference before adding annotations.
Prefer representing facts through ordinary Rust/MIR ownership and visible code
where possible. Parameter effects differ from whole-function effects.

| Fact | Possible encoding | Required care |
| --- | --- | --- |
| Memory effects | `memory(none)`, `memory(read)`, or location-specific effects | Include callbacks, runtime accesses, and exceptional paths. A pure reaction does not make its dispatcher pure. |
| Pointer capture | Version-appropriate capture attribute, e.g. `captures(none)` | Capturing into a task, queue, or callback normally defeats this contract. |
| Aliasing | `noalias` or scoped alias information | Private group identity does not prove that all accesses satisfy the alias contract. |
| Valid memory | `nonnull`, alignment, `dereferenceable` | Respect actual lifetime and Rust validity, including suspension. |
| Known predicate | `llvm.assume` or appropriate range information | Must already hold at the annotated point. An assumption is not a capacity check. |
| Execution/cleanup effects | `nounwind`, `willreturn`, `nosync`, `nofree` | Each needs its own proof; closedness alone implies none of these. |
| Hotness or inlining preference | `cold`, branch weights, `inlinehint`, selective `alwaysinline` | Profitability hints do not authorise protocol changes. |

These are semantic contracts, not requests for LLVM to prove them. Consult the
[LLVM language reference](https://llvm.org/docs/LangRef.html) for the precise
version-specific definitions. In particular, do not annotate mutable status
loads as invariant. Synchronisation operations also require the separate
reasoning described in [LLVM's atomics guide](https://llvm.org/docs/Atomics.html).

## When a custom LLVM pass is worth considering

### 1. Runtime specialisation after inlining or LTO

Suppose LLVM imports and inlines callers and can now establish that a specific
runtime group is confined to one execution region. A pass could select an
equivalent specialised runtime entry point, using LLVM alias/capture and call
graph information plus a documented runtime contract.

This is a credible advantage over a pass that runs before those bodies are
visible. It still requires proofs of every changed observable behaviour.
ThinLTO importing only part of a program does not establish whole-program
closedness. The OpenMPOpt precedent supports the architecture, not the claim
that it already knows how to optimise joins.

### 2. Private transfer elimination exposed by LLVM inlining

Recognisable send/receive operations on a private temporary may become adjacent
or have tractable control flow after inlining. A custom pass could use dominance,
alias analysis, and MemorySSA to help prove a local rewrite. MemorySSA alone does
not prove concurrent protocol equivalence.

Only pursue this if a reduced example survives existing optimisations, and its
opportunity genuinely depends on LLVM-stage information. If rustc already knows
the producer, consumer, and complete legality proof, direct MIR lowering is
usually simpler and retains Rust types and cleanup structure.

### 3. Target-dependent final automaton lowering

With an already-defined automaton and fixed semantics, a backend pass could
choose among masks, tables, or decision trees using target costs. First emit
ordinary switches/bit operations and measure LLVM's existing lowering. Add a
custom pass only for a demonstrated remaining gap.

## Contract required for an LLVM experiment

Use a small, versioned compiler/runtime operation interface. It may be recognised
runtime calls with correct ordinary effects and a fully correct fallback, or
properly supported intrinsics with mandatory lowering. Arbitrary names beginning
with `llvm.` are not a supported way to invent intrinsics in a plugin.

Record operation kind, actual group SSA operand, payload/layout information, and
the exact proof scope. A static endpoint or channel ID identifies a declaration,
not a unique dynamic allocation. Payload moves, destruction, and unwind handling
must be part of the contract.

Custom metadata may be lost or copied as IR changes. Define what inlining,
cloning, loop unrolling, importing, and linking do to each fact; conservatively
revalidate or reject when identity/scope is uncertain. Missing metadata must
leave a correct fallback. Do not depend on an optional annotation to preserve
essential effects against ordinary optimisations.

Schedule the pass while operation calls still exist, after the visibility it
needs becomes available, and before generic cleanup. Define behaviour for both
non-LTO and LTO pipelines. LLVM provides
[pipeline extension points](https://llvm.org/docs/NewPassManager.html) and
[pass plugins](https://llvm.org/docs/WritingAnLLVMNewPMPass.html).

For forwarding fusion, single-producer/single-consumer and non-escape are only
part of the proof. Account for FIFO and competing rules, timing of execution,
reentrancy, suspension, cancellation, panic/unwind, drops, wakeups, admission,
and any observable tracing or accounting. An unknown condition keeps the
fallback; it does not become `llvm.assume`.

## Concrete next steps for the compiler agent

1. Select small witnesses: direct unary including construction, a private
   forwarding edge, a bounded local pair, and an open/shared negative case.
2. Capture MIR and LLVM IR before and after optimisation using the actual
   compiler build. Record optimisation level, codegen units, panic mode, and LTO.
   The unary capture is now automated by `run_llvm_probe.sh`; the next capture
   must use a result-channel forwarding witness and include the complete
   construction-to-drop lifetime. Inspect allocations, atomics, locks, dispatch,
   and indirect calls rather than relying on line counts alone.
3. Prototype the simplest legal specialised lowering. Check what existing LLVM
   passes remove before implementing any new backend pass. Use
   [optimisation remarks](https://llvm.org/docs/Remarks.html) to diagnose missed
   opportunities; inspect IR for transformations that emit no remark.
4. For each remaining cost, identify whether it needs a semantic proof, better
   representation/visibility, a missing standard attribute, or a new transform.
   Provide a reduced IR reproducer before assigning work to LLVM.
5. Validate semantic changes with relevant cancellation, panic/drop, pending
   future, overlapping submission, and competing-rule cases. For a custom pass,
   add IR tests for successful rewrites and mandatory rejections, including
   multiple instances, escaped handles, missing facts, and LTO/cloning scope.
6. Benchmark the complete operation and construction/destruction costs, and
   compare code size. Report exactly what disappeared and under which settings.

The immediate implementation priority remains sound join proofs and explicit
specialised lowering. A custom LLVM pass should follow evidence that LLVM-stage
information or target decisions add an opportunity that this approach misses.
