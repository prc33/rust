# Private storage elimination: implementation and bounded follow-on work

Date: 2026-09-18. This is the next-agent entry point. It supersedes the
constructor-elimination instructions in `joins-next-slice.md`, but not the
review's remaining correctness gates or the accepted async semantics.

## Resume here — unfinished verification at credit-limited handover

The structural code is implemented but **NOT yet native-tested or benchmarked**.
The initial multi-crate `./x check` passed before the final
`PrivateInstancePlan` refactor. The full compiler/library build is still running
in tool session `38422` (`./x build compiler --stage 1 -j2 && ./x build library
--stage 1 -j2`). A subsequent MIR check is waiting for the build lock in session
`28482`, with output in `/tmp/join-private-plan-check.log`. Initial successful
check log: `/tmp/join-private-check.log`. Shell/Python syntax checks and both
worktree diff checks passed. Do not delete the build lock or start another
compiler build while these processes are active.

**First task is verification of this patch, not Task 1's extra coverage.**
Poll the existing sessions if available. Otherwise check build status and let
the existing build finish before issuing a cached build/check. Run the native
suites in all three modes with fresh `/tmp/join-private-storage-MODE` paths,
then the benchmark with `/tmp/join-private-storage-bench-20260918`. Fix failures
without weakening gates. Newly added `joins_private_owned.rs`, the destructor
negative, saved reentrant future, paired MIR assertions and zero-allocation
driver assertions have not run against the rebuilt compiler yet.

The most recent validated checkpoint is rust `cf50cfc835b`, library `61ae5cd`:
forwarding 541.99/550.21/97.01 ns/op off/analyze/optimize, allocations 11/11/2.
Do not report zero allocations or a speedup for the new patch until measured.
Only after those gates pass should the bounded follow-on tasks below begin.

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

## Task 1 — extend tests without changing eligibility

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

Completion: all three native suites exit zero with `-Zvalidate-mir`; every
positive has its own matching record and every negative retains public calls.
No compiler rebuild is needed for test-only changes.

## Task 2 — attribute remaining cost, using current generated code

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

Completion: committed evidence answers what remains after zero allocation;
no speculative optimization patch is needed for this task.

## Task 3 — small cleanup only, with preserved evidence

Update `JOINS-SUMMARY.md` with the current run, exact scope and limitations.
Keep the preceding 11-to-2-allocation run as the control. Link this handover
from older plans and mark constructor elimination complete only for this
domain. Remove obsolete statements that all forwarding retains construction.
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
