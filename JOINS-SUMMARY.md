# Joins research checkpoint — 2026-09-17

This is the owner's AI-authored research fork, with no intended upstream review
of this branch. The goal is a sound Rust extension that combines ordinary async
reaction bodies with join coordination, compiler CFA and measured optimisations,
then applies that work to DataFusion.

## Implemented and measured

Restricted isolated unary lowering produces ordinary caller-owned futures.
The direct endpoint is zero-sized and returns the declared `Future::Output`
without a matcher, reply cell, `Send`/`'static` or `JoinError` requirement.
Typed compiler descriptors and MIR summaries record operations, call identities,
local flow and escapes. The current working IR slice attaches a `JoinCall`
descriptor directly to the ordinary MIR `Call` terminator, so the call's
function, arguments, destination and unwind edges remain the sole executable
operands. Legacy body-boundary markers are operand-free metadata only. The
descriptor carries operation kind, group identity and typed channel/rule
coordinates, with provisional endpoint/rule identities retained for transition,
and survives optimized runtime MIR; codegen clears it at its final boundary.
The same descriptor is attached to known calls in ordinary and async caller
bodies, so source-side registrations remain visible without classifying the
caller as a generated join body.
The current slice also runs `join_cfa_crate_summary` after HIR analysis:
it snapshots each eligible `mir_built` body before the MIR ownership transfer
and follows a constructor result through same-body copy/move/borrow flow to a
known channel/dispatch receiver. The `InstanceTraffic` witness crosses a direct
`forward_instance` helper and yields a distinct `Unique` allocation with
`known_uses=2` in both analyze and optimize runs. The graph remains
conservatively incomplete for unsupported effects and escapes; closure
captures, loop contexts, indirect calls and general ordinary-caller
propagation are still pending. A narrow optimize-only MIR consumer now proves a
single monomorphic constructor/channel path and retargets its result call to a
private inline-ready adapter (`Reply::ready`); off/analyze retain the public
matcher call. The body JSON records the constructor/channel locations and
`fusion.rewritten=true`. This is result-forwarding only: native shared
admission/match/reply MIR, full certificate invalidation and general shared-join
fusion remain incomplete. The marker is metadata beside the compatibility
runtime call, not a claim that the runtime helper is itself the semantic IR.

The quick unary microbenchmark used 200,000 iterations, five repetitions per
mode and black-boxed checksums. Medians below are nanoseconds per operation;
`block_on` rows include the caller-driven executor and stack-poll rows isolate a
single first poll. Raw rows are committed at
`joins-library/docs/ir-cfa-evidence/native-microbench-20260917-unary.tsv`.

| Case | CFA off | Analyze | Optimize |
| --- | ---: | ---: | ---: |
| Direct function | 1.03 | 1.07 | 1.27 |
| Ordinary async through `block_on` | 65.88 | 64.43 | 67.65 |
| Shared unary join through `block_on` | 60.74 | 66.60 | 65.04 |
| Async join through `block_on` | 77.00 | 79.77 | 83.25 |
| Ordinary async, stack-pinned first poll | 1.03 | 1.05 | 1.08 |
| Unary join, stack-pinned first poll | 1.03 | 1.06 | 1.09 |

The direct unary path is therefore at ordinary-async first-poll parity; the
full lifecycle still includes executor overhead. These five-repetition numbers
are directional rather than the final 30-block confidence gate, and they do
not establish a DataFusion speedup. The earlier bounded-slot sample remains
archived at `docs/ir-cfa-evidence/native-microbench-20260915-bounded-slot.tsv`.

The LLVM probe at opt-level 3, one codegen unit, LTO off emits 14,934 versus
1,542 lines, 142 versus zero dispatch references, and 180 versus 24 atomic RMW
occurrences for off versus optimize. These are module-wide static counts, not
dynamic execution counts. See [LLVM boundary and evidence](docs/optimisations-vs-llvm.md).

The standalone `join-benchmarks` controls ran 1,000 iterations, two warmups and
five samples: mpsc 241 ns/op, work/resource 1,169 ns/op, rendezvous 19,672 ns/op,
Tokio request/reply 392 ns/op. Join snippets still need protocol validation and
executable benchmark drivers. Pair/multi-input compatibility lowering exists.
These quick baseline samples establish no join performance advantage.

The late-MIR boundary is verified with the stage-1 compiler and native suite:
`JOIN_CFA_MODE=off`, `analyze` and `optimize` pass all fixtures and UI gates.
With `JOIN_MIR_DUMP` enabled in off mode, five `runtime-optimized` MIR bodies
contain `join::Register`/`join::Match` descriptors on ordinary calls; no
operand-bearing semantic marker or duplicated `OrdinaryCall` marker appears.
The result-forwarding MIR gate additionally observes `Inner::step` in off and
analyze, `Inner::__join_direct_step` only in optimize, and a matching JSON
fusion certificate.
The LLVM-facing codegen path clones only metadata-bearing bodies, removes
legacy metadata statements, clears call descriptors and drops the backend-only
summary; generated code therefore receives no join instruction while the
optimized-MIR query remains available for future CFA/fusion passes.

## Next execution gates

Follow [the concrete next-slice specification](docs/joins-next-slice.md), steps
0–7. It supersedes older sequencing: first fix duplicate marker effects and
unjustified storage labels, then authoritative call operations, equal unary
semantics, bounded instance CFA and one result-channel rewrite. It includes
exact witnesses, rejection reasons, pass boundaries and verification commands.
The duplicate-visitor and body-local-storage portions of gate 1 are complete;
the call-carrier portion of gate 2 is partial. Mode-independent unary semantics
and a narrow result-adapter rewrite are complete; typed group/channel
remapping, full proof/rejection accounting, shared result fusion and fixed
storage remain pending. Surviving join descriptors stay through runtime MIR to
the LLVM-facing boundary; effectful operations cannot be erased as no-ops.

1. Validate the accepted unary/shared async semantics and equivalent benchmark
   protocols, including demand, cancellation, ownership and declared outputs.
2. Complete native HIR identities and typed semantic MIR for a closed forwarding
   witness, extending the current marker with group/instance, admission, demand,
   reservation, waker/scope, cancellation and normal/unwind/drop effects.
   Retain ordinary Rust coroutine MIR for reaction bodies.
3. Extend the bounded interprocedural CFA beyond direct local helpers to
   closure captures, loops, indirect-call rejection and general callers;
   distinguish closed and escaped instances. The current query proves a
   constructor-to-channel path through `forward_instance`; next make
   `LoopTraffic` flow through its enclosing producer while retaining
   conservative unknown results.
4. Expand the existing proof-driven result-channel MIR rewrite into a complete
   certificate consumer: add revision/type fingerprints, explicit rejection
   reasons and negative witnesses, then remove the proven-dead inner protocol
   rather than only retargeting its result adapter.
5. Prove per-instance queue bounds and select fixed storage without dynamic
   growth. Stack allocation additionally requires a lifetime/non-escape proof.
6. Measure the generated path against equal-semantics controls, inspect LLVM
   output and sampled profiles, then resume DataFusion coordination migration
   and performance/complexity comparisons.

The longer research programme is in the companion library checkout at
`JOINS-IMPLEMENTATION-HANDOVER.md`; the next-slice specification above controls
immediate compiler implementation.
Use focused checks, batch stage-1 builds and avoid broad DataFusion rebuilds
until the compiler-generated optimisation gate passes. Record evidence and
limitations here as each gate completes.
