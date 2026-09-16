# Joins research checkpoint — 2026-09-16

This is the owner's AI-authored research fork, with no intended upstream review
of this branch. The goal is a sound Rust extension that combines ordinary async
reaction bodies with join coordination, compiler CFA and measured optimisations,
then applies that work to DataFusion.

## Implemented and measured

Restricted isolated unary lowering produces ordinary caller-owned futures.
Typed compiler descriptors and MIR summaries record operations, call identities,
local flow and escapes; commit `d766b9f7d50` adds CFG occupancy transfer.
Native semantic MIR construction and interprocedural instance CFA are incomplete.
No shared-join MIR fusion currently consumes a CFA proof.

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

## Next execution gates

1. Validate the accepted unary/shared async semantics and equivalent benchmark
   protocols, including demand, cancellation, ownership and declared outputs.
2. Complete native HIR identities and typed semantic MIR for a closed forwarding
   witness, retaining ordinary Rust coroutine MIR for the reaction bodies.
3. Connect allocation sites, receivers, arguments/returns and closure captures
   in bounded interprocedural CFA; distinguish closed and escaped instances.
4. Apply one proof-driven result-channel MIR fusion, with a matching rejection
   witness and explicit candidate/proof/rewrite counters.
5. Prove per-instance queue bounds and select fixed storage without dynamic
   growth. Stack allocation additionally requires a lifetime/non-escape proof.
6. Measure the generated path against equal-semantics controls, inspect LLVM
   output and sampled profiles, then resume DataFusion coordination migration
   and performance/complexity comparisons.

The detailed canonical plan is in the companion library checkout at
`docs/ir-and-rustc-cfa-plan.md`, current execution checkpoint dated 2026-09-16.
Use focused checks, batch stage-1 builds and avoid broad DataFusion rebuilds
until the compiler-generated optimisation gate passes. Record evidence and
limitations here as each gate completes.
