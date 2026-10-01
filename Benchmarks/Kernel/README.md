# Certified kernel benchmarks

The certified checker's measurements are its environment check:
`kernel-check-ixe` (`Benchmarks/Kernel/CheckIxe.lean`, entry
`CheckIxeMain.lean`) checks a compiled environment (an `.ixe`) constant by
constant with con-leche's checker behind the Ixon reader and writes one JSON
row per constant. It measures coverage and time; it is not a certified
verdict (`Ix.Ixon.Admission.checkBytes` is). Its inputs, options and
watchdog are described in `docs/kernel.md` ("Environment check").

```sh
lake build --wfail kernel-check-ixe
lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --out .lake/envs/initstd.ixe
systemd-run --user --scope -p MemoryMax=24G -p MemorySwapMax=0 \
  env CHECK_IXE_WATCH_MB=12000 scripts/check-ixe-guarded.sh \
  .lake/build/bin/kernel-check-ixe .lake/envs/initstd.ixe .lake/envs/initstd.jsonl
python3 scripts/check-ixe-report.py .lake/envs/initstd.jsonl
```

Run one environment check at a time, with no concurrent build. A row's
`micros` is the constant's install-and-check time and `readMicros` its
reading time; a family
and its separate recursor share one timing, so sums over rows are
diagnostics, not process times.

## Paired runs

`scripts/bench-check-ixe.py run` alternates fresh processes of a
baseline and a candidate binary over the same `.ixe` (one warmup and three
measured samples each by default) and records GNU time's peak RSS, whole
process wall time, and executable, environment and source fingerprints. The
output directory must be new. Every baseline acceptance the candidate loses,
including missing rows, is listed and makes the runner exit nonzero; gained
acceptances and other outcome changes are reported separately, and different
coverage is flagged next to the wall-time ratio.

```sh
python3 scripts/bench-check-ixe.py run \
  --baseline-binary /tmp/kernel-base/.lake/build/bin/kernel-check-ixe \
  --baseline-revision <baseline-commit> \
  --binary .lake/build/bin/kernel-check-ixe --revision <candidate-commit> \
  --input .lake/envs/initstd.ixe --output-dir .lake/check-ixe-paired
python3 scripts/bench-check-ixe.py compare before.jsonl after.jsonl --output comparison.json
```

## Other drivers (untrusted, measurement only)

- `kernel-check-ixe --fold` (`Benchmarks/Kernel/CheckIxeFold.lean`): con-leche's
  batch fold over the constants the environment check accepts, for
  comparison with the per-constant step.
- `kernel-check-ixe-opt` (`Benchmarks/Kernel/CheckIxeOpt.lean`): the environment check with
  driver-side switches (load mode, worker lane, persistent mark, two-phase
  pool).

## Recorded results (2026-10-01)

Init+Std compiled with Lean 4.34.0 (`initstd.ixe`, 97,877 constants), on an
AWS Xeon 6975P, one core per run:

| Outcome | Constants |
| --- | ---: |
| accepted | 96,975 |
| declined: 813 `partial` and 75 `unsafe` definitions, 8 unsafe opaques, 6 unsafe axioms | 902 |
| rejected, blocked | 0 |

Check time summed over accepted constants is 75.1 s and reading 3.5 s; the
process takes 101.0 s wall with a 4.55 GB peak RSS. On the same machine,
upstream con-leche (`ae0c0c4e`, Lean 4.33.0) takes 88.0 s of install plus
check at one worker (90.2 s wall) on a lean4export of the same Init+Std.

Mathlib (`mathlib.ixe`, 672,938 constants): 669,032 accepted, 3,906
declined (3,314 `partial` and 561 `unsafe` definitions, 15 unsafe opaques,
6 unsafe axioms, 5 unsafe inductive blocks with their recursors), 0
rejected, 0 blocked. Load 147.8 s, check 875.0 s summed over accepted
constants, reading 41.5 s; 19 min 38 s wall at one core. The driver holds
the decoded environment, so the peak RSS is 47.3 GB. On the same machine,
upstream con-leche (`3ca9e2fe`, `--verified --jobs=1`) takes 17.8 min and
9.6 GB on a lean4export of Mathlib.

The intrinsic kernel's native benchmark runner (`bench-certified-kernel`)
and its environment check (`kernel-census-intrinsic`) were retired with that kernel
(`docs/kernel.md`, "The retired intrinsic kernel"); their measurements are
in this file's history.
