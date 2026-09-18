# Expanded coordination benchmark — 2026-09-18

This is the first post-fix run that restores the complete coordination matrix:
11 synchronous operations plus the Tokio request/reply control, 5,000
iterations, five warmups, 30 randomized blocks, and four worker threads. Each
mode ran sequentially; every sample passed its operation-count and checksum
invariant. The standalone [HTML report](benchmark-report.html) contains all
samples, confidence intervals, compiler provenance, and CFA dump counts.

| Operation | Handwritten | Joins off | CFA analyze | CFA optimize |
| --- | ---: | ---: | ---: | ---: |
| rendezvous | 24,669 ns | 624 ns | 627 ns | 609 ns |
| mpsc | 88 ns | 792 ns | 782 ns | 911 ns |
| mpmc | 840 ns | 934 ns | 873 ns | 906 ns |
| condvar | 22,372 ns | 11,772 ns | 12,686 ns | 12,271 ns |
| work-resource | 1,184 ns | 1,661 ns | 1,590 ns | 1,698 ns |
| completion | 65 ns | 2,226 ns | 1,923 ns | 1,933 ns |
| barrier | 15,097 ns | 15,408 ns | 17,614 ns | 17,133 ns |
| rwlock admission probe | 47 ns | 3,822 ns | 3,766 ns | 3,743 ns |
| mutex/counter | 32 ns | 1,119 ns | 1,099 ns | 1,166 ns |
| thread-join | 74,565 ns | 72,464 ns | 70,636 ns | 72,830 ns |
| once | 59,804 ns | 63,216 ns | 64,618 ns | 67,021 ns |
| async-request | 436 ns (Tokio) | 53 ns | 52 ns | 55 ns |

The large wins on rendezvous and condvar are protocol-specific comparisons, not
evidence that a generic join matcher has replaced a standard primitive. The
`rwlock` row is explicitly an admission probe; its untimed witness checks the
real exclusion/payload invariant. The `async-request` join is the isolated
unary `async when` lowering: it is caller-driven and returns its declared value
directly, whereas the baseline includes Tokio current-thread scheduling.

The CFA dump contains 156 records per mode, 57 reaction bodies, four frontend
direct-unary endpoints, and four proven queue-bound-zero endpoints. No general
dynamic/shared matcher is fused yet; those rows still exercise the compatibility
runtime. The benchmark build uses the temporary endpoint-capture expansion
documented by `scripts/build-join-suite.sh`; it does not modify the rustc
checkout during measurement.

Raw JSONL is kept beside this note. `manifest.txt` records the base Rust and
library revisions plus their working-tree status at measurement time; the
one-way admission fix used by the run was committed afterward as Rust
`c587a288162` and library `6f3ee99`. The protocol definitions are in
[PROTOCOL-MATRIX.md](PROTOCOL-MATRIX.md).
