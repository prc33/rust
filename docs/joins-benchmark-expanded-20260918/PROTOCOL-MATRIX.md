# Benchmark protocol matrix

The benchmark runner treats a process exit or a nonzero checksum as insufficient
evidence. Every driver now checks its operation count and an exact checksum, or a
written invariant where scheduling makes an exact checksum impossible. This
matrix records what each row actually measures so a ratio is not mistaken for a
semantic equivalence result.

| Operation | Handwritten control | Join control | Validation | Comparability |
| --- | --- | --- | --- | --- |
| `rendezvous` | Zero-capacity request and reply channels, one worker, reply `value + 1` | Two-input local rendezvous; both replies return `left + 1` | Sum `1..=N` | Same arithmetic, but the join has an extra input and reply participant |
| `mpsc` | `std::sync::mpsc`, four producer partitions and one receiver | `message` plus result-bearing `receive` | Every delivered value contributes to `0..N-1` sum | Same message count and producer partitioning |
| `mpmc` | Mutex/Condvar queue, two producers and two consumers | Two producer and two result-demanding receiver partitions | `0..N-1` sum and fixed count | Same counts; consumer identity is intentionally not observable |
| `condvar` | Producer/consumer predicate hand-off of values `1..=N` | `state(value)` matched with `wait()` | Exact `1..=N` sum | Same hand-off values; wake policy differs |
| `work-resource` | Job queue plus worker and permit ID queues in the validation witness | Timed row uses `job`, `worker`, and `permit` three-way rule; validation companion returns a `WorkReceipt` to all three participants | Timed checksum plus untimed exact job/worker/permit ID sets; missing, duplicate, out-of-range, and wrong replies fail | Same logical admission, different storage and wake path; resource IDs are checked outside timing |
| `completion` | Mutex completion counter releases one waiter | Async `done` reaction decrements `remaining`, then signals `ready` | Exactly `N` completions | Same logical result, but join uses an executor-backed reaction |
| `barrier` | `threads` workers plus coordinator, two phases | Four fixed worker channels plus coordinator, two phases | Round sum and operation count | Matched only for `--threads 4`; join arity is fixed |
| `rwlock` | Real mutable `RwLock`, readers and writer | Timed row uses three reader admission tokens and a writer token; replies are constants. The validation companion performs the same atomic payload read/write and slot protocol. | Timed row checks final writer value and a bounded reader sum. Untimed validation requires three overlapping readers, no reader/writer overlap, exactly one payload increment, and no probe violations. | Timed row remains an admission-overhead probe; the companion now establishes the payload/exclusion invariant without changing the timed comparison |
| `mutex` | Shared `Mutex<u64>` increments; checksum is sum of observed counter values | Monotonic `available(value)` state token; `acquire` returns next value | Final counter/last-token sequence is `1..=N` | Same serialized counter semantics, different implementation |
| `thread-join` | Two scoped child threads and two returned values | Two child messages matched with one result-bearing `join` | Exact `N(N+2)` sum | Same child/result lifecycle |
| `once` | Fresh `OnceLock` per trial, four concurrent readers | `initialize` plus re-emitted `initialized` state | Exactly `42 × readers` | Same one-initialization result; cold setup is included |
| `async-request` | Tokio current-thread manager, bounded `mpsc` and `oneshot` | Isolated unary `async when request(value) -> value + 1`, polled by the caller | Exact `1..=N` sum | Ecosystem control; the join is intentionally the ordinary-async fast path and is executor-free |

The formulas use `N = iterations`; `threads` is the configured worker count.
The runner validates warmups as well as timed samples, and an assertion failure
terminates the trial instead of producing a misleading timing record. The
The timed `rwlock` join row is deliberately retained as an admission-overhead
probe and must not be presented as a speedup over `RwLock`. `--validate-only`
uses `JoinRwLockChecked` and the stable `RwLock` witness to exercise the real
atomic payload access and exclusion protocol outside timing.

The focused A2 gate can be run with `scripts/verify-work-resource.sh`. It runs
the stable and join work/resource validation witnesses without timing them,
then compiles a temporary join source whose reply is deliberately wrong and
requires that process to fail. The temporary mutation is removed on exit. The
rwlock A3 witness is run with `--operation rwlock --validate-only` for each
join mode and the stable control; it is likewise outside timed samples.
