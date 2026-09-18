# LLVM and hot-path attribution — 2026-09-18

This is a static attribution note for the validated private-storage forwarding
run. It is not a flamegraph and it does not turn whole-binary symbol presence
into evidence that a symbol ran on the timed path.

## Sampling status

The already-built optimized binary was checked with `perf`, separately from
the benchmark matrix. Sampling is unavailable in this container:

```text
/proc/sys/kernel/perf_event_paranoid = 4
perf stat: Access to performance monitoring and observability operations is limited
```

The process has none of the capabilities (`CAP_PERFMON`, `CAP_SYS_PTRACE` or
`CAP_SYS_ADMIN`) required to override that policy. No CPU sample counts or
flamegraph have therefore been claimed. A privileged host, or an external
profiler that can attach to this process, is still required for cycle-level
attribution.

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

## Next profiling gate

Run the three already-built binaries one at a time under a permitted sampler,
using the same case selection and iteration count. Record sample counts for the
forwarding closure, the private adapter, fallback dispatch, allocator, reply
cell, tracing and synchronization. Compare against ordinary async. Keep the
off/analyze/optimize artifacts and profiler settings together; do not run
profiling jobs concurrently with one another or with the benchmark matrix.

Do not add a work-stealing scheduler or a lock-specific compiler rewrite based
on this static evidence. The current scheduler is a compatibility runtime, and
the next performance changes should be justified by a measured hot-path cost
and lowered to ordinary fields/atomics/CAS where the join proof permits it.
