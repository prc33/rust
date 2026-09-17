# Joins research checkpoint — 2026-09-17

This is the owner's AI-authored research fork, with no intended upstream review
of this branch. The goal is a sound Rust extension that combines ordinary async
reaction bodies with join coordination, compiler CFA and measured optimisations,
then applies that work to DataFusion.

## Implemented and measured

Restricted isolated unary lowering produces ordinary caller-owned futures.
Typed compiler descriptors and MIR summaries record operations, call identities,
local flow and escapes; the current pushed tip `973c809b84f` adds a typed
`NonDivergingIntrinsic::Join` carrier and keeps it visible through optimized
runtime MIR. The marker carries operation kind, endpoint/rule identities, source
location, and actual receiver/destination/argument operands at known call sites.
The current slice also runs `join_cfa_crate_summary` after HIR analysis:
it snapshots each eligible `mir_built` body before the MIR ownership transfer
and follows a constructor result through same-body copy/move/borrow flow to a
known channel/dispatch receiver. The `InstanceTraffic` witness crosses a direct
`forward_instance` helper and yields a distinct `Unique` allocation with
`known_uses=2` in both analyze and optimize runs. The graph remains
conservatively incomplete for unsupported effects and escapes; closure
captures, loop contexts, indirect calls and general ordinary-caller
propagation are still pending. Native semantic admission/match/reply MIR and
proof-consuming shared-join MIR fusion remain incomplete. The marker is metadata
beside the compatibility runtime call, not a claim that the runtime helper is
itself the semantic IR.

The archived seven-process bounded-slot microbenchmark has these median ns/op:

| Case | CFA off | Optimize |
| --- | ---: | ---: |
| Direct function | 1.16 | 1.18 |
| Ordinary async through block_on | 82.1 | 85.5 |
| Sync unary join through block_on | 393.0 | 89.7 |
| Async unary join through block_on | 31,953.0 | 86.6 |
| Ordinary async, stack-pinned first poll | 1.21 | 1.16 |
| Unary join, stack-pinned first poll | 282.6 | 0.84 |

These are ready unary representation measurements. The async compatibility
control crosses a worker boundary; its improvement includes changing execution
placement. They do not establish shared-join CFA fusion, suspension performance,
or a DataFusion speedup. Raw rows are in the companion library at
`docs/ir-cfa-evidence/native-microbench-20260915-bounded-slot.tsv`.

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
`JOIN_CFA_MODE=analyze` and `JOIN_CFA_MODE=optimize` both pass all fixtures and
UI gates. With `JOIN_MIR_DUMP` enabled, five `runtime-optimized` MIR bodies
contain `join::Register`/`join::Match`. The LLVM-facing codegen path clones only
marked bodies, removes those metadata statements and clears the backend-only
summary; generated code therefore receives no join instruction while the
optimized-MIR query remains available for future CFA/fusion passes.

## Next execution gates

Follow [the concrete next-slice specification](docs/joins-next-slice.md), steps
0–7. It supersedes older sequencing: first fix duplicate marker effects and
unjustified storage labels, then authoritative call operations, equal unary
semantics, bounded instance CFA and one result-channel rewrite. It includes
exact witnesses, rejection reasons, pass boundaries and verification commands.
All those gates remain pending. Surviving join descriptors stay through runtime
MIR to the LLVM-facing boundary; effectful operations cannot be erased as no-ops.

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
4. Apply one proof-driven result-channel MIR fusion while the marker is still
   available, with a matching rejection witness and explicit
   candidate/proof/rewrite counters. Only the final codegen clone should erase
   an unreplaced marker.
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
