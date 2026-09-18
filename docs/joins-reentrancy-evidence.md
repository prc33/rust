# Result-adapter scheduling correction — 2026-09-18

The review's trampoline concern is a reproduced semantic difference, not just
an untested suspicion. At compiler `c77bb3f3b1f`, the new
`joins-library/compiler-tests/joins_fusion_reentrant.rs` passes with CFA off
and fails with optimize. A dynamic synchronous reaction manually polls an
isolated async forwarding reaction. Its private inner request must enqueue
work on the already-active trampoline. The first poll returns `Pending` and
the inner body has executed zero times. Before the fix, the ready-reply adapter
executes the inner body immediately and returns `Ready`.

The generated adapter now uses `__join_sync_inline` as a scheduling boundary.
When the trampoline is already active it calls the original public channel
method with the original payload. Otherwise it runs the inline reaction under
the ordinary active-dispatch context, then drains any queued children before
returning. This also preserves the ordering of reactions emitted by ordinary
helper functions called from the body. The helper introduces no new lock or
allocation on the inline path; its fallback retains the compatibility matcher.
It does not select or substitute a library concurrency primitive based on a
recognised join pattern.

The compatibility runtime currently executes these synchronous result rules
eagerly. This correction preserves that baseline in every CFA mode; it does
not implement the accepted demand-gated shared semantics. Scoped constructors
are still excluded from fusion. Complete reply-consumer analysis, scope policy,
and general shared cancellation proofs remain open.

Verification includes the native regression in all three CFA modes, the
existing positive/rejected MIR witnesses, and runtime tests for nested order,
single-branch payload ownership, and resetting the dispatch context on unwind.
The compiler forwarding benchmark measures the guarded path through full
construction, first poll and destruction against ordinary async and direct
functions. It requires exactly one recorded rewrite in optimize and none in
off/analyze before collecting timings.
