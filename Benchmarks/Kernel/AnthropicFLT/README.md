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

To resolve anonymous addresses to names without decoding expression
metadata, use the `resolve_anon_names` Rust example with `FILE.ixe` followed
by hex prefixes (8–64 digits). It prints all aliases, not a single guessed
name. This separate diagnostic reads the full file into RAM: apply an
appropriate memory limit for large artifacts. Name lookup is not checking.

`cases.json` pins the exact existing `.ixe` by SHA-256 and byte length. It
tracks 132 target addresses: 120 fuel failures, four depth failures, five
unfinished tails, and three positive controls. The default **15-case core**
contains all five tails, all four depth cases, four measured fuel failures,
and two reasonably fast positive controls. The positive control that needed
558 seconds in the original full sweep belongs to the extended suite.

Observations came from the stopped `28fc2270` full FLT run at 40M fuel and
64 workers, plus the earlier bounded single-subject trials. They are not
expected kernel rejections: fuel/depth limits leave checking unresolved.
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
20M, and the extended slow positive control gets 600 seconds. Pair order
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
