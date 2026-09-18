# Immediate-await result-fusion proof — 2026-09-18

The previous first-move heuristic did not establish its claimed await
contract. On the expanded `joins_fusion_reject.rs` fixture, the old compiler
rewrote three cases: a reply passed through a move to a helper, a dropped
reply, and a returned reply. These are reproduced proof-domain violations,
not demonstrated wrong program outputs. All three programs still returned
their expected values in this experiment.

`reply_has_immediate_await` now inspects executable MIR starting at the normal
successor of the channel call. It follows only sequential, type-preserving
moves of the reply between whole locals, non-executable bookkeeping, and
unconditional control-flow edges. Cycles are rejected. It requires the first
call encountered to be the `IntoFuture::into_future` language item at a span
marked as Rust's own await desugaring, moving the tracked reply and returning
the same concrete reply type. An explicit user-written `into_future` call is
not sufficient.

This deliberately narrow check rejects helper calls, borrows, aggregate
storage, projections, drops, return-place moves, conditional consumption and
unrecognised statements before the await boundary. Multiple ordinary moves
before an immediate await remain eligible. It does not infer arbitrary
eventual consumption across helpers or branches.

The check uses existing coroutine lowering rather than introducing a second
polling representation. Once the compiler-generated await boundary takes
ownership, rustc's existing polling, suspension, pinning and drop machinery
continues to apply. This does not prove the complete shared join protocol or
justify removing group construction: the guarded adapter still requires the
original matcher for nested-dispatch fallback.

Verification gates:

- Run `compiler-tests/run_native.sh` with fresh CFA and MIR dump directories
  in `off`, `analyze`, and `optimize` modes.
- `joins_fusion_result.rs` transfers its reply through two named aliases;
  optimize must retarget the caller to `Inner::__join_direct_step`, and
  off/analyze must keep `Inner::step`.
- Every `joins_fusion_reject.rs` caller must retain `EscapedInner::step`,
  including helper/borrow/drop/return/conditional cases. Test both conditional
  branches. The runner checks actual optimized MIR, not helper declarations.
- Keep the nested-dispatch regression passing in all modes.
- Re-run the complete-lifecycle forwarding benchmark with its one-rewrite
  assertion and separate allocation instrumentation; this proof change should
  preserve the eligible path's measured benefit, not claim a new speedup.

These native gates passed in all three modes on September 18 with rebuilt
stage-1 compiler and standard library. Fixture revision: library `61ae5cd`.
Outputs: `/tmp/join-reply-proof-{off,analyze,optimize}/{cfa,mir,bin}`; each
runner exited zero. The optimize MIR contains one rewritten positive caller
and nine negative callers retaining the public method. The explicit
`into_future` negative also passes. These are local verification artifacts,
not substitutes for the committed test sources.

The [post-change benchmark](joins-forwarding-reply-proof-20260918/summary.md)
also passed its rewrite-count gates: off/analyze/optimize forwarding medians
541.99/550.21/97.01 ns/op, allocations 11/11/2. The paired optimize/off ratio
0.184 [0.179, 0.191] is consistent with the earlier guarded-adapter run. Do
not attribute the absolute timing change between runs to this proof change.
