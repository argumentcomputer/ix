# Focused anonymous FLT regression suite

Use this for the inner optimization loop, before whole-Mathlib/FLT checks.
The kernel checks each selected **work item only**, trusting lazily ingressed
dependencies. This is a diagnostic benchmark, not full-corpus verification.
Declaration names and expression metadata are not needed or loaded.

For separate diagnostics, `IX_GUARD_STACKS=1` on the subject helper emits
bounded native stacks at resource guards. `IX_DEF_EQ_NEAR_GUARD=1` emits
bounded expression-pair summaries near the depth limit. Leave both off
for paired timings. Guard fuel counters inside a speculative comparison
describe its temporary slice; the final helper report accounts for the
actual total work charged to the subject.

For separate cache/reduction diagnostics, the subject helper prints cache
hit rates to stderr with `IX_PERF_COUNTERS=1`, and the top 20 delta/iota
addresses with `IX_REDUCE_HISTO=1`. Histogram totals include addresses beyond
the displayed top 20. These counters measure reduction events, not proof
size or unique allocations. Diagnostics leave the subject JSON unchanged;
keep both flags unset for paired timings.

`IX_SAME_HEAD_PROFILE=1` reports actual same-head comparisons by outcome
and definition head. Inclusive fuel overlaps across nested attempts;
exclusive and root fuel do not double-count it. Window skips and rejected-
probe cache hits are separate from attempts. Failed-attempt fuel is not
necessarily all avoidable: attempts may also populate useful caches.
Per-head attribution is bounded and holds no expression graphs. Leave this
flag unset for clean paired timing runs; subject JSON stays unchanged.

The same-head report also ranks roots separately and prints at most 32
expensive root-pair snapshots (at least 65,536 fuel) per thread/check.
These carry expression uids, the legacy context identity, and compact shapes;
they do not canonicalize free variables or claim alpha-equivalence.
`IX_HOT_MISSES=1` prints the final member's top 25 miss shapes once when the
subject helper finishes; add `IX_HOT_MISS_CTX=1` for context keys. It does
not require the much noisier per-guard `IX_REC_FUEL_DUMP`.
The hot-miss collector retains at most 4,096 keys, with labels capped at
512 UTF-8 bytes. Its Space-Saving summary can discover late hotspots by
replacing low-frequency entries. Printed counts are lower/upper bounds
(exact before replacement); the number of retained keys is **not** the
total number of distinct misses. Exact expression/context identities, not
truncated labels, distinguish keys. No expression graphs are retained, and
the collector resets per member. Leave it off for clean timings.

Application inference selectively caches repeated dependent prefixes using
the existing exact context-sensitive keys and separate full/infer-only result
caches. Only successful inference publishes a prefix type; a bounded two-touch
fingerprint filter merely nominates work and never supplies a type or a
validity judgment. Each spine materializes at most one extra dependent suffix
for caching, leaving the remaining telescope substitution batched. The
admission history resets per member and retains at most 32 KiB of slots. With
`IX_PERF_COUNTERS=1`, `dependent_prefix_inserts` counts these materializations.

Same-head congruence probes use a 131,072-fuel slice for Regular definitions
and 4,096 for other hints. Nested probes inherit the remaining allowance.
Exhaustion resumes ordinary unfolding with consumed work charged to the
check; it does not establish inequality. Regular root probes back off after
33,554,432 fuel in unsuccessful attempts across the declaration. This is an
admission threshold: the last admitted attempt can cross it by up to its
allowance. There is no per-head blacklist. Successful roots do not charge
the history;
nested work is charged only as part of its unsuccessful root. Skips resume
ordinary unfolding, and `skipped_backoff` is reported separately from actual
attempts. This constant-space history resets per member; it is not a
semantic cache.
Non-Regular probes retain their startup window, measured in actual work
rather than temporarily withheld fuel. The per-constant fuel cap is unchanged.

To resolve anonymous addresses to names without decoding expression
metadata, use the `resolve_anon_names` Rust example with `FILE.ixe` followed
by hex prefixes (8–64 digits). It prints all aliases, not a single guessed
name. This separate diagnostic reads the full file into RAM: apply an
appropriate memory limit for large artifacts. Name lookup is not checking.

`cases.json` pins the exact existing `.ixe` by SHA-256 and byte length. It
tracks 138 target addresses: 120 fuel failures, four depth failures, five
unfinished tails, and nine passing-baseline controls. The default **25-case core**
contains all five original tails, all four depth cases, ten fuel failures,
and six positive controls. Five fuel cases were promoted
from the existing extended inventory after they formed the final tail of
the completed 100M full FLT run; no addresses were duplicated. The positive
control that needed 558 seconds in the original full sweep belongs to the
extended suite. The remaining V3 failure `fuel-6c43f78d96e1` is also promoted
with 100M fuel and a 300-second timeout, without adding a duplicate address.

Six controls were added after early backoff V5 regressed the full FLT sweep.
The three new failures (`50cb089d71a0`, `6234fd409441`, `7bf34ca3444c`) and
V3's highest-fuel passing subject (`6303d6c017f7`, 28.385M) are in the core.
Two near-cap V5 passes (`bfeba60bbbc6`, `eac5f4ec9db3`) are extended controls.
All six have explicit 100M/300-second budgets. Their recorded observations
are full-sweep results under contention, not isolated benchmark timings.

Initial observations came from the stopped `28fc2270` full FLT run at 40M
fuel and 64 workers, plus the earlier bounded single-subject trials. The
five new core cases are `fuel-f38456f556fd`, `fuel-f5ebaf348a49`,
`fuel-fa1b74facf9a`, `fuel-fbba56420b6b`, and `fuel-fdfcfa70a9e8`. Each
exhausted 100M fuel in `check-flt-fuel100m-v1-1` (September 6, 2026).
Their recorded full-run times are under 64-worker contention, not isolated
benchmark results. Resolved names/aliases in the manifest are descriptive
only: execution remains anonymous and addresses are authoritative. Resource
failures are not expected kernel rejections: fuel/depth limits leave checking
unresolved.
“Unfinished” does not establish a deadlock. Addresses identify declarations
in this pinned artifact; do not substitute a rebuilt corpus silently.

## Build and run

Build the same `check_anon_subject` example against each kernel variant,
using the same native CPU/toolchain/feature settings. Preserve both binaries
under distinct filenames before running; never rebuild while measuring.

```sh
nix develop --offline --command cargo build -p ix-ffi --release \
  --example check_anon_subject --features parallel,net --offline
```

On the Linux CPU box, run inside tmux. The harness is Lean (`import Lean`
only; no project rebuild needed). It uses GNU time/timeout, systemd, and
noninteractive sudo for the per-process scopes.
The output directory must not exist. No corpus is copied or rebuilt.

```sh
lean --run Benchmarks/Kernel/AnthropicFLT/RunSuite.lean \
  --ixe /path/to/flt-after-source-hints-1.ixe \
  --baseline /path/to/check-subject-baseline \
  --adaptive /path/to/check-subject-adaptive \
  --output /path/to/new-run-directory
```

Use `--case tail-04e32656609b` (repeatable) for a tiny iteration, `--rounds 3`
for repeated pairs, or `--suite all` for the extended set. The extended set
can take much longer; it is not the default inner loop.

The preflight resolves every recorded target to its work-item primary in
**both** binaries, without checking it. Both resolutions must agree.
Members of the same mutual block are deduplicated for matching fuel budgets.
Each timed invocation has a fresh process/KEnv, one checker worker, the
manifest's fixed fuel cap, 96 GiB MemoryMax, and zero MemorySwapMax. Defaults
are 40M fuel and 120 seconds per process; the 17.1M-fuel passing control uses
20M, and the extended slow positive control gets 600 seconds. The five
newly promoted tail cases explicitly use **100M fuel and 300 seconds per
process**, still one worker and 96 GiB/no swap. The original 15 cases keep
their old budgets for comparable performance regressions; the additional
V3 failure and the six backoff controls also have explicit 100M/300-second
budgets. Raising the
kernel default does not override the manifest. Pair order
alternates across cases and rounds. Hot-miss/perf/step diagnostics are off.

## Results and interpretation

- `run.json`: complete manifest, selected IDs, artifact and binary hashes,
  file identities, host, driver hash, and start time. `source/` preserves
  the explicit prototype source files and pinned Cargo/toolchain inputs.
- `resolved.json`: target-to-primary mapping and deduplicated selected work.
- `results.jsonl`: flushed after every invocation, even if a later one times
  out. Contains outcome, raw helper report, wall/CPU time and peak RSS.
- Per-invocation `.log`, `.stderr.log`, `.time.json`, and `.command.json`:
  original evidence, exact argv, and the unique cgroup scope name. Both
  streams are flushed as they arrive, and the harness prints a heartbeat
  every 30 seconds. Caught orchestration errors clean up only that scope;
  the child's independent timeout remains in force if the harness is killed.
- `summary.json`: written only after all scheduled pairs finish; compares
  completed results/work counts and checker times. A completed *harness*
  does not mean its subjects all passed. Read each outcome.

Checker time excludes initial mmap/enumeration; whole-process time includes
load, checking, and teardown. Peak RSS includes the whole helper process,
not just scratch storage. A timeout is censored, not a kernel failure or an
exact checker-time measurement; no speedup ratio is manufactured from it.
Exit 137 is reported as `killed`, not automatically called OOM. Missing time
or JSON data remains missing. Compare fuel usage only under matched caps.

The helper's `last_member_fuel` and `last_member_def_eq_peak` refer to the
last checked member. The latter is a **definitional-equality depth metric**,
not an overall peak infer/WHNF recursion-depth measurement. Do not label
these as block aggregates. Operation counts span the work item; aggregate
fuel is unavailable with perf diagnostics disabled.

For the storage-only scratch change, completed outcomes and work/fuel counts
should agree. The driver flags mismatches without treating timeout cases as
passes. For algorithmic optimizations such as batched binder inference,
explicitly pass `--allow-work-changes`: changed work/fuel/depth counts are
still recorded, but labeled `same_outcome_changed_work` when the verdict,
error, and target count agree. Verdict/error/target changes remain mismatches
requiring review; timeouts remain incomplete. The selected policy is saved
in `run.json`; the default storage-only policy is unchanged. Keep passing
controls, kernel tests, Mathlib, and periodic full FLT sweeps as separate
correctness and whole-run performance gates.

```sh
lean --run Benchmarks/Kernel/AnthropicFLT/RunSuite.lean --self-test
```
