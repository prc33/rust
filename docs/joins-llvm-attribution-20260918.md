# LLVM and hot-path attribution — 2026-09-18

This is a static attribution note for the validated private-storage forwarding
run. It is not a flamegraph and it does not turn whole-binary symbol presence
into evidence that a symbol ran on the timed path.

## Sampling status

The first attempt to check the already-built optimized binary with `perf`,
separately from the benchmark matrix, was blocked by the container policy:

```text
/proc/sys/kernel/perf_event_paranoid = 4
perf stat: Access to performance monitoring and observability operations is limited
```

With the owner's authorization, `kernel.perf_event_paranoid` was lowered to
`1`; the container then allowed user-space counters and call-graph sampling.
The resulting reports are committed in
[`joins-perf-profile-20260918/README.md`](joins-perf-profile-20260918/README.md). They contain
330 optimized-forwarding samples and 4,761 off-forwarding samples, with zero
lost samples. The initial failure remains recorded here because ordinary
unprivileged runs on this host will still hit the original policy.

## Static evidence

The inputs are the compiler-generated artifacts from
`docs/joins-forwarding-private-storage-20260918/`:

```text
build/off
build/analyze
build/optimize
build/{off,analyze,optimize}.ll
build/{off,analyze,optimize}.s
```

The optimized executable is 597,320 bytes; the off executable is 591,008
bytes. The corresponding assembly files are 453,841 and 450,037 bytes. These
sizes include all benchmark cases and the compatibility runtime, so they are
not a measure of the forwarding path by themselves.

`nm -S --defined-only ... | c++filt` identifies the following representative
symbols:

| build | symbol | size |
| --- | --- | ---: |
| optimize | `Forward::run::{closure#0}` | 0x3119 |
| optimize | `run_dynamic_reaction::<...>` | 0x1e5b |
| off | `Forward::run::{closure#0}::{closure#0}` | 0x2f4e |
| off | `run_dynamic_reaction::<...>` | 0x1e5b |

The optimized `main` calls the outer `Forward::run` closure; the off build
calls the nested ordinary-future closure. The optimized assembly still
contains the generic reply, queue, tracing, mutex and dynamic-reaction symbols.
That is expected: the binary contains fallback branches and the other cases,
and the private adapter must retain a guarded nested-dispatch fallback. A
whole-module search therefore cannot establish that those operations execute
for the measured private forwarding case.

The strongest current hot-path evidence is dynamic allocation instrumentation
from the same run: private forwarding performs 0 allocation calls per
operation in optimize versus 11 in off/analyze, while direct, ordinary async
and isolated unary controls remain at 0. The timing run also asserted matching
checksums and exactly one optimize rewrite. This demonstrates removal of the
measured allocation path, not removal of every runtime branch or synchronization
instruction.

## Profiling gate result

The three already-built forwarding/control binaries were run one at a time
under `perf stat`; optimized and off forwarding were also sampled with DWARF
call graphs. The optimized profile is dominated by the generated forwarding
closure, synchronous queue pumping and endpoint cleanup. The off profile is
dominated by dynamic reaction completion, allocation/free, matcher creation,
queue growth and reply cleanup. See the committed profile README for exact
percentages and commands.

Do not run profiling jobs concurrently with one another or with the benchmark
matrix. A future privileged run should compare any new lowering against these
same case selections and preserve the binary hashes and sample counts.

Do not add a work-stealing scheduler or a lock-specific compiler rewrite based
on this static evidence. The current scheduler is a compatibility runtime, and
the next performance changes should be justified by a measured hot-path cost
and lowered to ordinary fields/atomics/CAS where the join proof permits it.
