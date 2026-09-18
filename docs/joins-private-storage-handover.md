# Private storage elimination: implementation and bounded follow-on work

Date: 2026-09-18. This is the next-agent entry point. It supersedes the
constructor-elimination instructions in `joins-next-slice.md`, but not the
review's remaining correctness gates or the accepted async semantics.

## Validation completed — 2026-09-18

The full compiler/library rebuild, targeted MIR check and native suites completed
successfully. `run_native.sh` passed in `off`, `analyze` and `optimize` with
`-Zvalidate-mir`; expected compile-error and panic-transport fixtures behaved as
designed. Optimized MIR contains the paired
`Inner::__join_private_new()`/`Inner::__join_direct_step()` calls, while the
other modes retain public construction and registration.

The fresh lifecycle run is archived at
`docs/joins-forwarding-private-storage-20260918/`: 30 randomized blocks of one
million operations, three warmups, construction/poll/drop included. Forwarding
is 483.45/489.10/30.43 ns/op off/analyze/optimize; allocation calls are 11/11/0.
The paired optimize/off ratio is 0.063 with bootstrap 95% interval [0.062,
0.064]. This validates private storage for the narrow eligible domain; it does
not validate shared joins, fixed queues or general JCAM fusion.

Static LLVM/assembly attribution is recorded in
[`joins-llvm-attribution-20260918.md`](joins-llvm-attribution-20260918.md).
Hardware sampling remains unavailable under this container's
`perf_event_paranoid=4` policy; do not call the static note a flamegraph.
The bounded negative coverage below has also been extended.
The complete HTML status report is
[`joins-project-report-20260918.html`](joins-project-report-20260918.html).

This branch is the owner's AI-written research project. No upstream maintainer
is being asked to review it; any eventual upstream proposal will be rewritten
by hand. All compiler layers are available, but sound ownership, concurrency,
and truthful performance comparisons remain requirements. Do not recognise a
lock-like protocol and replace it with a library lock. Generated fields,
ordinary futures, and ultimately justified atomics/CAS are the intended tools.

## Structural decisions already made

The difficult change is **paired representation selection**, not deletion of
an apparently unused constructor. A private instance and its sole eligible
request are rewritten together, before ordinary MIR cleanup and coroutine
lowering:

| Original call | Selected call | Meaning |
| --- | --- | --- |
| `Inner::new()` | `Inner::__join_private_new()` | Construct an endpoint with no matcher |
| `inner.step(payload)` | `inner.__join_direct_step(payload)` | Execute through the existing guarded adapter |

These are compiler-generated private methods, not a programmer-facing API or
source opt-in. Only definitions already eligible for a private synchronous
unary result adapter get the alternative storage representation:
`Option<DynamicMatcher>`. Ordinary `new` and `new_in_scope` construct `Some`;
the private constructor constructs `None`. Other dynamic definitions retain
their existing storage type. This representation is identical in all CFA
modes; only the proof-consuming MIR rewrite selects the private constructor.

The adapter uses the existing synchronous dispatch guard. Outside dispatch,
it executes the body and produces its ready reply without constructing a
matcher. During nested dispatch, it must register on the ordinary matcher:
use the existing matcher when present, otherwise create an ordinary endpoint
and call its public channel. Queued work owns its required state after that
temporary endpoint drops. **Never replace this fallback with an immediate
body call.** The fallback may allocate and return `Pending`.

Rust's existing move, drop, coroutine and LLVM machinery handles the selected
representation. This slice adds no polling machine, lazy-initialisation lock,
new runtime scheduler, or hand-coded concurrency primitive.

### Why eliminating this construction is permitted

The generated unscoped dynamic constructor creates empty queues and an `Arc`
containing matcher state. It registers no scope hook and exposes no invocation
identity. The proof establishes one private constructor and one eligible
request, excludes escapes, and requires an immediate compiler-generated await.
No user destructor may observe the endpoint. Elision removes allocator calls;
allocator-call counts are diagnostic measurements, not guaranteed observable
Rust program semantics. This is **not** a claim that arbitrary constructors
can be sunk or erased.

The nested fallback reconstructs only that otherwise-unobservable empty state,
before registering the request. The body still executes under the same
dispatch policy, and input ownership transfers once. Scoped construction,
existing queued messages, multiple requests, captures/re-emission, custom
endpoint destruction, or unknown instance use invalidate this argument.

### Code locations and authority

- `rustc_builtin_macros/src/joins.rs`: emits storage, constructors and guarded
  adapter. It does not decide which caller is private.
- `rustc_attr_ir` / `rustc_attr_parsing`: the internal adapter marker carries
  channel/rule coordinates and a constructor-role bit.
- `rustc_passes/src/joins.rs`: resolves unique, matching adapter and private
  constructor identities and compares their ABIs with the public methods.
- `rustc_middle/src/middle/joins.rs`: typed descriptor stores the private
  constructor identity; `JoinFusionFact` records whether it was selected.
- `rustc_mir_transform/src/joins.rs`: validates the instance, immediate await,
  lack of user destructor, generic restrictions, and both actual MIR call
  sites **before mutating either one**. A failure must leave both unchanged.

`PrivateInstancePlan` owns an exclusive borrow of the validated MIR body and
typed call locations/targets until application. It cannot be serialized or
survive an intervening pass; application has no fallible proof checks after
the first mutation. This structure is already implemented, not a task for the
next agent. The existing diagnostic snapshot's limitations still apply to
analysis before this capability is constructed.

The `fusion.private_constructor` JSON field is evidence of the selected
rewrite, not an independent reusable certificate. Stored summary fingerprints
are incomplete freshness guards. Do not carry this proof through arbitrary
MIR changes or treat `Body::join_info` as authoritative after transformation.

## Fixed eligibility: do not widen it during the following tasks

Keep monomorphic, local, unscoped, uniquely constructed instances with one
synchronous unary result rule, no channel re-emission/capture, one supported
channel call, and the immediate-await move path. Reject user-defined `Drop`
on the endpoint. Keep the existing escape, projection, overwrite, competition,
cycle, scoped-policy and unknown-origin refusals. Isolated unary async joins
must continue using ordinary caller-owned futures in every CFA mode.

This is not full JCAM fusion, full typed HIR patterns, shared demand semantics,
or fixed-queue analysis. Do not mark any of those complete from this result.

## Task 1 — extend tests without changing eligibility (partly complete)

Work in `../joins-library/compiler-tests/`. Add cases to existing fixtures,
not a second test harness. Use manual bounded polls rather than timeouts.

1. Extend `joins_private_owned.rs` with a zero-argument request and a request
   returning an owned drop-counted value. Check input/output destruction once
   after successful consumption and after abandoning the result.
2. Extend `joins_fusion_reentrant.rs` with an owned payload and a counting
   waker. First poll inside the trampoline must be `Pending`, body count zero;
   after the driver completes, body count one, the registered waiter is woken,
   and the saved future produces the correct value. Also drop a pending
   outer future and check that the queued body is not duplicated.
3. Add two same-type constructions and a second channel invocation as negative
   cases. Each must retain ordinary construction in optimized MIR. Preserve
   the existing custom-destructor, scope, explicit-IntoFuture and alias cases.
4. Add per-fixture JSON checks for the owned positive and reentrant positive:
   exactly one paired rewrite in optimize, zero in off/analyze. Do not accept
   another fixture's rewrite record as their evidence.

Completion so far: all three native suites exit zero with `-Zvalidate-mir`; the
owned-payload, destructor, reentrant, paired-MIR and zero-allocation gates pass.
The two same-type-instance and repeated-request negatives now also pass in all
three modes and retain the public path. Pending-abandonment and per-fixture JSON
rewrite assertions remain before widening eligibility.

## Task 2 — attribute remaining cost, using current generated code (timing complete)

Run `scripts/run_compiler_forwarding.py` from the library with a new output
directory, `--iterations 1000000 --samples 30`. It compiles actual join source,
asserts paired rewrite counts, and measures construction-to-drop. Do not time
while compiling or running other tests. Repeat the whole run if the machine
is busy; retain both runs, do not cherry-pick samples.

The driver requires zero allocation calls for the optimized forwarding path
and the direct/async/unary controls. Off/analyze forwarding must allocate.
Separate allocation probes are not timing samples. Preserve raw randomized
blocks, source and compiler hashes, output checksums, and both CFA modes.

Inspect its `build/optimize.ll` and `build/optimize.s` (check actual emitted
filenames). Trace the **executed standalone path**, not the entire binary:
allocation and matcher symbols can legitimately remain in the cold nested
fallback. Record the hot loop, TLS guard, branch to fallback, calls that
survive on the hot path, and any reply/endpoint stack storage remaining.
Compare with the ordinary async loop. If attribution needs sampling, use
longer runs of these already-built binaries; report permissions/sample counts.
Do not label a whole-binary symbol search a flamegraph or proof of hot-path
allocation. First improvement target is unnecessary hot-path work, not removal
of a required scheduling branch.

Completion so far: allocation evidence is committed and the optimized path is
zero-allocation. Static LLVM/assembly inspection is committed in
[`joins-llvm-attribution-20260918.md`](joins-llvm-attribution-20260918.md).
Privileged hardware profiling remains before another lowering patch; no
speculative optimization patch is needed for that profiling task.

## Task 3 — small cleanup only, with preserved evidence (complete for this slice)

`JOINS-SUMMARY.md` now records the current run, exact scope and limitations.
The preceding 11-to-2-allocation run remains the control. Constructor
elimination is marked complete only for this narrow domain; older measurements
retain their historical wording. Remove obsolete statements that all
*current* forwarding retains construction.
Do not delete the compatibility matcher, dispatch guard, source lowering or
library code still reached by negatives/fallbacks. Do not delete historical
evidence. Remove helpers only after `rg` and successful native/workspace tests
show they have no remaining callers.

## Task 4 — next compiler work, bounded and diagnostic-first

Inventory missing source-rule information in `JoinDefinition`. Produce
a table for each fixture: exact rule input channels, result channels, async
body identity, competition, and selected policy. Identify fields currently
represented only by counts/dispatch-wide bodies. Do not invent facts from
generated function names or treat declared queue bounds as proved occupancy.
Keep this inventory diagnostic-only until an explicit typed schema and
ownership/lowering specification are approved for the next structural slice.

## Cheap-to-expensive verification order and commands

1. Check worktrees; preserve unrelated `AGENTS.md` deletion and `ph2`.
2. For compiler edits, run `./x check compiler/rustc_mir_transform
   compiler/rustc_builtin_macros compiler/rustc_passes --stage 1 -j2` in rust.
   Batch changes before one full compiler build and subsequent library build.
3. Reuse that stage-1 compiler for tests and measurements. In the library:

```sh
JOIN_CFA_MODE=optimize JOIN_CFA_DUMP=/tmp/UNIQUE-opt/cfa \
JOIN_MIR_DUMP=/tmp/UNIQUE-opt/mir JOIN_TEST_OUT=/tmp/UNIQUE-opt/bin \
bash compiler-tests/run_native.sh
```

Repeat with separate fresh paths and `off`/`analyze`. Run `cargo test
--workspace` if library runtime code changes. Then, with no builds running:

```sh
python3 scripts/run_compiler_forwarding.py /tmp/UNIQUE-bench \
  --iterations 1000000 --samples 30
```

4. Commit compiler changes, root summary and evidence in rust, and companion
   test/driver changes in the library. Push rust to `prc33 joins`; the library
   currently has no remote. Do not claim it was pushed.

Stop and report rather than weakening a gate if a negative starts rewriting,
pending becomes ready under nested dispatch, destruction changes, the
optimized hot path allocates, or a claimed speedup depends on changing the
source contract between CFA modes. New shared/borrowed execution semantics and
elimination of the dispatch guard require a new design, not a local patch.
