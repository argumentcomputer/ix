# Certified kernel benchmarks

The certified checker's measurements are its environment check:
`kernel-check-ixe` (`Benchmarks/Kernel/CheckIxe.lean`, entry
`CheckIxeMain.lean`) checks a compiled environment (an `.ixe`) constant by
constant with the verified checker behind the Ixon reader and writes one JSON
row per constant. It measures coverage and time; it is not a certified
verdict (`Ix.Kernel.Admission.checkBytes` is). Its inputs, options and
watchdog are described in `docs/kernel.md` ("Environment check").

```sh
lake build --wfail kernel-check-ixe
lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --out .lake/envs/initstd.ixe
CHECK_IXE_WATCH_MB=12000 .lake/build/bin/kernel-check-ixe --guarded --memory-max 24 \
  .lake/envs/initstd.ixe .lake/envs/initstd.jsonl
.lake/build/bin/kernel-check-ixe --report .lake/envs/initstd.jsonl
.lake/build/bin/kernel-check-ixe --summary .lake/envs/initstd.jsonl --json initstd-summary.json
```

The check streams the records by default: the `.ixe` is loaded
metadata-light, the order and the record views are built over record
skeletons, and a record is decoded in full only at its turn and dropped once
it is read (`CheckIxeStream.lean`). `--load eager` decodes and keeps the
whole environment up front instead; the rows are the same. `--jobs <n>` runs
the check in the fold's two phases, the recorded checks on `n` worker
threads (`CheckIxePool.lean`), and writes the same rows; each row's `micros`
is then its install plus its checks, on whichever workers ran them.

```sh
.lake/build/bin/kernel-check-ixe .lake/envs/initstd.ixe stream.jsonl
.lake/build/bin/kernel-check-ixe --load eager .lake/envs/initstd.ixe eager.jsonl
.lake/build/bin/kernel-check-ixe --jobs 8 .lake/envs/initstd.ixe jobs8.jsonl
.lake/build/bin/kernel-check-ixe --compare eager.jsonl jobs8.jsonl
```

`--guarded` reruns the check, in a fresh process, with every constant the
driver's watchdog recorded in `<output>.runaway` skipped, until it completes;
`--memory-max <GB>` runs each attempt in a cgroup scope capped at that size
(`Ix.Watchdog`; exit 137 when the cap kills it), and `--binary <path>` runs
another build of the driver with the same contract; the arguments after
these are the check's (`--load`, `--jobs`, input, output, limit). `--report
<rows> [top]` prints outcome counts, check time, decline reasons and the
blocking roots ranked by reach; `--summary <rows> [--top N] [--json <out>]`
writes the same as Markdown tables, with timing quantiles and the slowest
rows. A compressed row file is decompressed first.

Run one environment check at a time, with no concurrent build. A row's
`micros` is the constant's install-and-check time and `readMicros` its
reading time (under the streaming load, including the decoding of its
record); a family and its separate recursor share one timing, so sums over
rows are diagnostics, not process times.

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

## Recorded results (2026-10-01)

Init+Std compiled with Lean 4.34.0 (`initstd.ixe`, 97,877 constants), on an
AWS Xeon 6975P, one core per run (times measured with the earlier driver,
which loaded eagerly):

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
rejected, 0 blocked. Measured with the earlier driver, which loaded eagerly
(as `--load eager` does): load 147.8 s, check 875.0 s summed over accepted constants, reading 41.5 s;
19 min 38 s wall at one core; the driver holds the decoded environment, so
the peak RSS is 47.3 GB. On the same machine,
upstream con-leche (`3ca9e2fe`, `--verified --jobs=1`) takes 17.8 min and
9.6 GB on a lean4export of Mathlib.

The streaming load and the pool, measured with the earlier prototype of
these modes (the same reader, verified check, load and phases) on the same
machine (AWS r8i.16xlarge, Xeon 6975P-C, one process at a time on an idle
machine): the streaming load (the default now) gives the same rows in
19 min 43 s at one core with a 20.2 GB peak, about 85 s less loading and as
much more reading, since a record is decoded at its turn. The two phases
(`--jobs <n>`; the prototype kept the `.ixe`'s buffer resident) install in a
sequential phase A (234 s after a 60 s load, then 10 s of marking) and check
the 659,344 recorded checks in phase B, with 0 failures:

| Workers | Phase B | Speed-up | Wall | Peak RSS |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 997.9 s | 1.00× | 21 min 49 s | 22.3 GB |
| 4 | 253.3 s | 3.94× | 9 min 24 s | 22.3 GB |
| 8 | 127.1 s | 7.85× | 7 min 18 s | 22.3 GB |
| 16 | 64.1 s | 15.6× | 6 min 15 s | 22.3 GB |
| 32 | 34.0 s | 29.4× | 5 min 45 s | 22.3 GB |

At one worker the two phases are slower than the per-record check, and the
sequential part (load, phase A, marking: about 310 s) bounds the wall time.
The prototype wrote no rows in this mode; `--jobs` now writes the per-record
rows after phase B, which adds a pass over the order without reading or
checking.

The certified entry `Ix.Kernel.Admission.checkBytes` is sequential.
