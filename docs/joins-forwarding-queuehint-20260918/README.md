# Empty-dispatch-queue follow-up — 2026-09-18

This is a clean follow-up to the private-storage forwarding benchmark. The
runtime commit `c09b6db` adds a thread-local non-empty bit for the synchronous
dispatch queue. The generated inline adapter still checks the active-dispatch
context and retains the public matcher fallback; when the body emitted no
nested work, it skips the empty queue pop and indirect job call.

The benchmark was run once, sequentially, with 30 randomized blocks of one
million operations and three warmups. Construction, first poll and destruction
are included; there is no executor or thread handoff. The complete provenance,
raw samples and allocation probe are in this directory.

| Case (ns/op) | CFA off | Analyze | Optimize |
| --- | ---: | ---: | ---: |
| Direct function | 1.47 | 1.42 | 1.41 |
| Ordinary async | 1.40 | 1.39 | 1.38 |
| Isolated unary join | 1.28 | 1.44 | 1.44 |
| Private result forwarding | 533.90 | 536.86 | 21.89 |

The paired optimize/off median ratio is 0.041 (bootstrap 95% interval
[0.040, 0.042]). Allocation calls are 13/13/0 for forwarding and zero for the
three controls. The previous private-storage checkpoint was 30.43 ns/op in
optimize mode; absolute off-path timings vary with host load, so this run is
evidence for the optimized-path change rather than a replacement for every
earlier comparison.

The assembly still contains the active-context fallback and
`run_one_queued_sync_job` for the branch where nested work is possible. This
change does not establish that the guarded branch can be removed: that requires
an execution-context proof in addition to a body-level no-re-emission proof.
