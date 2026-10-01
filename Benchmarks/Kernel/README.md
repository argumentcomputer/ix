# Certified kernel benchmarks

The certified checker's measurements are its environment check:
`kernel-check-ixe` (`Benchmarks/Kernel/CheckIxe.lean`, entry
`CheckIxeMain.lean`) checks a compiled environment (an `.ixe`) constant by
constant with the verified checker behind the Ixon reader and writes one JSON
row per constant. It measures coverage and time; it is not a certified
verdict (`Ix.Ixon.Admission.checkBytes` is). Its inputs, options and
watchdog are described in `docs/kernel.md` ("Environment check").

```sh
lake build --wfail kernel-check-ixe
lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --out .lake/envs/initstd.ixe
CHECK_IXE_WATCH_MB=12000 .lake/build/bin/kernel-check-ixe --guarded --memory-max 24 \
  .lake/envs/initstd.ixe .lake/envs/initstd.jsonl
.lake/build/bin/kernel-check-ixe --report .lake/envs/initstd.jsonl
.lake/build/bin/kernel-check-ixe --summary .lake/envs/initstd.jsonl --json initstd-summary.json
```

`--guarded` reruns the check, in a fresh process, with every constant the
driver's watchdog recorded in `<output>.runaway` skipped, until it completes;
`--memory-max <GB>` runs each attempt in a cgroup scope capped at that size
(`Ix.Watchdog`; exit 137 when the cap kills it), and `--binary <path>` runs
another driver with the same contract (`kernel-check-ixe-opt`). `--report
<rows> [top]` prints outcome counts, check time, decline reasons and the
blocking roots ranked by reach; `--summary <rows> [--top N] [--json <out>]`
writes the same as Markdown tables, with timing quantiles and the slowest
rows. A compressed row file is decompressed first.

Run one environment check at a time, with no concurrent build. A row's
`micros` is the constant's install-and-check time and `readMicros` its
reading time; a family
and its separate recursor share one timing, so sums over rows are
diagnostics, not process times.

## Paired runs

`kernel-check-ixe --paired` alternates fresh processes of a baseline and a
candidate binary over the same `.ixe` (its first 4,300 primary records unless
`--limit` says otherwise; one warmup and three measured samples each by
default) and records GNU time's peak RSS, whole process wall time, and
executable, environment and source fingerprints. The output directory must be
new, and the samples run without the caller's `CHECK_IXE_*` variables, under a
timeout (`--timeout`, 180 s). Every baseline acceptance the candidate loses,
including missing rows, is listed and makes the runner exit nonzero; gained
acceptances and other outcome changes are reported separately, and different
coverage is flagged next to the wall-time ratio.

```sh
.lake/build/bin/kernel-check-ixe --paired \
  --baseline-binary /tmp/kernel-base/.lake/build/bin/kernel-check-ixe \
  --baseline-revision <baseline-commit> \
  --binary .lake/build/bin/kernel-check-ixe --revision <candidate-commit> \
  --input .lake/envs/initstd.ixe --output-dir .lake/check-ixe-paired
.lake/build/bin/kernel-check-ixe --compare before.jsonl after.jsonl --output comparison.json
```

## Other drivers (untrusted, measurement only)

- `kernel-check-ixe --fold` (`Benchmarks/Kernel/CheckIxeFold.lean`): the
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

With `kernel-check-ixe-opt` (untrusted measurement driver; same reader and
verified check) on the same machine (AWS r8i.16xlarge, Xeon 6975P-C, one
process at a time on an idle machine): a streaming load
(`CHECK_IXE_LOAD=stream-free CHECK_IXE_THREAD=1 CHECK_IXE_MARK=1`, one core)
gives the same rows in 19 min 43 s at a 20.2 GB peak. The two-phase pool
(`CHECK_IXE_LOAD=stream CHECK_IXE_MARK=1 CHECK_IXE_PAR=n`) installs in a
sequential phase A (234 s after a 60 s load, then 10 s of marking) and
checks the 659,344 recorded checks in phase B, with 0 failures:

| Workers | Phase B | Speed-up | Wall | Peak RSS |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 997.9 s | 1.00× | 21 min 49 s | 22.3 GB |
| 4 | 253.3 s | 3.94× | 9 min 24 s | 22.3 GB |
| 8 | 127.1 s | 7.85× | 7 min 18 s | 22.3 GB |
| 16 | 64.1 s | 15.6× | 6 min 15 s | 22.3 GB |
| 32 | 34.0 s | 29.4× | 5 min 45 s | 22.3 GB |

The certified entry `Ix.Ixon.Admission.checkBytes` is sequential.
