# Perf call-graph evidence — 2026-09-18

This is the first privileged CPU profile of the compiler-generated forwarding
benchmark. It uses the already-built binaries from
`joins-forwarding-private-storage-20260918`; no compilation occurred during
the profile runs, and profiles were run one at a time.

The kernel setting was temporarily lowered from `perf_event_paranoid=4` to
`1` with the owner's authorization. The profile processes completed without
lost samples. The source binaries are identified in `binary-sha256.txt`.
Their reproducibility manifest is the original
`/tmp/join-private-storage-bench-20260918/manifest.json`: Rust
`3538e2df43d0`, library `d69bf13592a6`, one million operations per counter
run, and `-O -Ccodegen-units=1 -Clto=off`.

## Counter summary

Each counter row is three sequential `perf stat` runs of one million
operations. The full stderr is retained beside this file.

| binary/case | cycles | instructions | branches | branch misses |
| --- | ---: | ---: | ---: | ---: |
| CFA off / forwarding | 1,204,410,365 | 3,049,985,546 | 595,012,507 | 186,739 |
| CFA optimize / forwarding | 81,692,342 | 153,664,700 | 29,342,050 | 43,523 |
| CFA off / ordinary async | 6,930,574 | 12,454,813 | 1,299,889 | 36,901 |
| CFA optimize / ordinary async | 6,159,962 | 12,416,620 | 1,292,619 | 35,109 |

The forwarding optimize/off counter ratios are approximately 0.068 cycles and
0.050 instructions for this separate one-million-operation run. These are
profile counters, not replacements for the 30-block timing evidence.

## Call-graph samples

Commands, run separately:

```text
perf record -F 999 -g --call-graph dwarf -o /tmp/join-perf-opt-forwarding.data -- \
  build/optimize forwarding 10000000
perf record -F 999 -g --call-graph dwarf -o /tmp/join-perf-off-forwarding.data -- \
  build/off forwarding 10000000
perf report --stdio --percent-limit 0.5 -i ...
```

The optimized profile captured 330 samples with zero lost samples. Its samples
are concentrated in the generated `Forward::run` closure (about 69% self),
with about 13% in `run_one_queued_sync_job`, 8% in `Inner` drop glue, and 2.7%
in the dispatch-inline reset guard. This is the remaining compatibility
trampoline/drop cost after allocation removal; it is not evidence that a pool
or work-stealing scheduler is needed.

The off profile captured 4,761 samples with zero lost samples. Its largest
children were `run_dynamic_reaction` (about 29.7%), dynamic invocation/reply
completion and frees (about 12.3%), `Inner` drop glue (12.4%), source-location
construction (10.6%), matcher construction (6.9%), and queue growth (4.0%).
The report shows `malloc`/`free`, `VecDeque::grow`, `Arc<ReplyCell>` and
`DynamicInvocation` cleanup on the baseline path.

These profiles support the allocation and timing attribution: the large gap is
mostly dynamic admission/completion/storage work, while the optimized path's
remaining cost is generated control flow, dispatch pumping and cleanup. They
do not prove that every generic runtime symbol is hot in every case.

## What the samples say at instruction granularity

`perf record` samples the instruction pointer at a fixed frequency and
`perf annotate` maps those samples back to disassembly. It therefore identifies
hot basic blocks and their callers, but it does not measure the latency of one
instruction exactly. In particular, the percentage beside an instruction is
the percentage of samples landing there; it is not proof that that `mov` or
branch consumes that percentage of cycles. The result must be read with the
counter totals and an A/B rebuild.

The optimized forwarding profile makes the remaining work concrete:

* The generated `Forward::run` closure has a roughly `0x2c8` stack frame and
  retains a large continuation/state-copy path. The block at `0x20693--0x206a5`
  copies a reply/state value (`movups`/`movaps`) and then calls through an
  indirect adapter; `0x20698` receives 37.28% of local samples. This marks the
  state-machine block as hot, not the individual `movaps` as intrinsically
  slow.
* The TLS active-dispatch test at `0x20462` receives 4.57% of local samples.
  The call-graph view attributes about 13% of child samples to the
  `run_one_queued_sync_job` pump and about 2.7% to the `Reset` drop guard.
  Those are compatibility work for possible nested re-emission. A CFA proof
  that the reaction cannot re-emit, suspend, or invoke an unknown join can
  select a direct ready-result lowering and remove this guard/pump from that
  case; the fallback must remain for unproved cases.
* About 8% of child samples are endpoint `Inner` drop glue. A unique, non-
  escaping private instance should not need to construct and tear down the
  generic matcher state on every short-lived benchmark invocation.

The off profile shows work that is not needed at all for the proven private
unary case: allocator calls (`malloc` 12.44% self, `_int_free` 10.79%, and
`cfree` 7.34%), `DynamicMatcher::new` (2.83%), `VecDeque` growth, dynamic
invocation/reply completion, Arc refcount traffic, source-location construction
and its `memmove` (4.61%). These are protocol/storage costs, not a slow join
body. The next lowering should eliminate them by construction rather than
pattern-matching a lock implementation.

The profiles were taken from the already-built private-storage binaries before
the later unmatched-request withdrawal-hook commit. That hook is on the shared
dynamic path and does not execute on the profiled private fast path; rerun the
same protocol after the next lowering before treating the numbers as final.

Raw textual reports:

- [`opt-forwarding-perf-report.txt`](opt-forwarding-perf-report.txt)
- [`off-forwarding-perf-report.txt`](off-forwarding-perf-report.txt)
- [`opt-forwarding-perf-stat.txt`](opt-forwarding-perf-stat.txt)
- [`off-forwarding-perf-stat.txt`](off-forwarding-perf-stat.txt)
- [`opt-async-perf-stat.txt`](opt-async-perf-stat.txt)
- [`off-async-perf-stat.txt`](off-async-perf-stat.txt)

The binary `perf.data` files are intentionally not committed; the reports,
sample counts, commands and binary hashes are sufficient to audit the result.
