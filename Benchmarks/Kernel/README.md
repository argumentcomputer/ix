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

## Recorded results (2026-10-02)

Measured on an AWS r8i.16xlarge (Intel Xeon 6975P-C, 32 cores, 64 threads),
one process at a time on an otherwise idle machine, each started with the
1-minute load below 1, under `CHECK_IXE_WATCH_MB=60000`; one-core runs are
pinned with `taskset -c 6`. Lean 4.34.0, Ixon v4.

Init+Std (`initstd.ixe`, 97,877 constants):

| Outcome | Constants |
| --- | ---: |
| accepted | 96,975 |
| declined: 813 `partial` and 75 `unsafe` definitions, 8 unsafe opaques, 6 unsafe axioms | 902 |
| rejected, blocked | 0 |

| Load | Wall | Peak RSS | Check (summed over accepts) | Reading |
| --- | ---: | ---: | ---: | ---: |
| streaming (default) | 1 min 39.7 s | 1.52 GB | 75.4 s | 11.0 s |
| `--load eager` | 1 min 54.8 s | 3.60 GB | 74.6 s | 3.3 s |

On the same machine, upstream con-leche (`ae0c0c4e`, Lean 4.33.0) takes
88.0 s of install plus check at one worker (90.2 s wall) on a lean4export of
the same Init+Std.

Mathlib (`mathlib.ixe`, 672,938 constants): 669,032 accepted, 3,906
declined (3,314 `partial` and 561 `unsafe` definitions, 15 unsafe opaques,
6 unsafe axioms, 5 unsafe inductive blocks with their recursors), 0
rejected, 0 blocked, with the same rows in every mode below.

| Load | Wall | Peak RSS | Load phase | Check (summed over accepts) | Reading |
| --- | ---: | ---: | ---: | ---: | ---: |
| streaming (default) | 19 min 3.5 s | 14.7 GB | 98.1 s | 887.3 s | 119.0 s |
| `--load eager` | 20 min 58.7 s | 34.2 GB | 328.7 s | 844.8 s | 36.3 s |

The eager load holds the decoded environment; the streaming load decodes a
record at its turn (its reading time includes the decoding) and drops its
bytes once read. On the same machine, upstream con-leche (`3ca9e2fe`,
`--verified --jobs=1`) takes 17.8 min and 9.6 GB on a lean4export of
Mathlib.

`--jobs <n>` on Mathlib (streaming load; pinned to cores 8-9, 8-12, 8-16,
8-24 and 0-31 for 1, 4, 8, 16 and 32 workers): phase A installs every record
and records 659,344 checks, and phase B checks them on the workers, with 0
failures:

| Workers | Phase B | Phase B speed-up | Wall | Wall speed-up | Peak RSS |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 949.1 s | 1.00× | 21 min 25.0 s | 1.00× | 15.2 GB |
| 4 | 241.8 s | 3.93× | 9 min 36.8 s | 2.23× | 15.3 GB |
| 8 | 121.1 s | 7.84× | 7 min 35.8 s | 2.82× | 15.3 GB |
| 16 | 60.9 s | 15.6× | 6 min 35.7 s | 3.25× | 15.4 GB |
| 32 | 30.8 s | 30.8× | 6 min 6.7 s | 3.50× | 15.7 GB |

Phase B's time summed over the workers grows from 948.3 s at one worker to
983.1 s at 32. The sequential part bounds the wall time: the load (98 s),
phase A's install (208–210 s, ending about 310 s after the start), marking
the installed environment persistent (7.6 s), and the rows pass after phase
B (about 18 s), about 335 s in all. At one worker the two phases are slower
than the per-record check.

The certified entry `Ix.Kernel.Admission.checkBytes` is sequential.
