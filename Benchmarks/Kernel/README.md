# Certified kernel benchmarks

The certified checker's measurements are its census: `kernel-census`
(`Benchmarks/Kernel/ConLecheCensus.lean`, entry `CensusCertifiedMain.lean`;
`kernel-census-cl` is the same driver under its earlier name) checks a
compiled corpus record by record with con-leche's checker behind the Ixon
reader and writes one JSON row per record. It measures coverage and time; it
is not a certified verdict (`Ix.Ixon.Admission.checkBytes` is). Its inputs,
options and watchdog are described in `docs/kernel.md` ("Census").

```sh
lake build --wfail kernel-census
lake exe ix compile Benchmarks/Compile/CompileInitStd.lean --out .lake/census/initstd.ixe
systemd-run --user --scope -p MemoryMax=24G -p MemorySwapMax=0 \
  env CENSUS_WATCH_MB=12000 scripts/census-guarded.sh \
  .lake/build/bin/kernel-census .lake/census/initstd.ixe .lake/census/initstd.jsonl
python3 scripts/census-report.py .lake/census/initstd.jsonl
```

Run one census at a time, with no concurrent build. A row's `micros` is the
record's install-and-check time and `readMicros` its reading time; a family
and its separate recursor share one timing, so sums over rows are
diagnostics, not process times.

## Paired runs

`scripts/bench-kernel-census.py run` alternates fresh processes of a
baseline and a candidate binary over the same `.ixe` (one warmup and three
measured samples each by default) and records GNU time's peak RSS, whole
process wall time, and executable, corpus and source fingerprints. The
output directory must be new. Every baseline acceptance the candidate loses,
including missing rows, is listed and makes the runner exit nonzero; gained
acceptances and other outcome changes are reported separately, and different
coverage is flagged next to the wall-time ratio.

```sh
python3 scripts/bench-kernel-census.py run \
  --baseline-binary /tmp/kernel-base/.lake/build/bin/kernel-census \
  --baseline-revision <baseline-commit> \
  --binary .lake/build/bin/kernel-census --revision <candidate-commit> \
  --input .lake/census/initstd.ixe --output-dir .lake/census-paired
python3 scripts/bench-kernel-census.py compare before.jsonl after.jsonl --output comparison.json
```

## Other drivers (untrusted, measurement only)

- `kernel-census --fold` (`Benchmarks/Kernel/ConLecheFold.lean`): con-leche's
  batch fold over the census's accepted records, for comparison with the
  per-record step.
- `kernel-census-opt` (`Benchmarks/Kernel/ConLecheOpt.lean`): the census with
  driver-side switches (load mode, worker lane, persistent mark, two-phase
  pool).

## Recorded results (2026-10-01)

Init+Std compiled with Lean 4.34.0 (`initstd.ixe`, 97,877 records), on an
AWS Xeon 6975P, one core per run:

| Outcome | Records |
| --- | ---: |
| accepted | 96,975 |
| declined: 813 `partial` and 75 `unsafe` definitions, 8 unsafe opaques, 6 unsafe axioms | 902 |
| rejected, blocked | 0 |

Check time summed over accepted records is 76.3 s and reading 3.7 s; the
process takes 101.6 s wall with a 3.9 GB peak RSS. On the same machine,
upstream con-leche (`ae0c0c4e`, Lean 4.33.0) takes 88.0 s of install plus
check at one worker (90.2 s wall) on a lean4export of the same Init+Std.

Mathlib (`mathlib.ixe`, 672,938 records): 668,628 accepted, 3,906
`partial`/`unsafe` declines and 0 rejects before the level comparison's
Géran fallback. The 404 records that depended on that comparison
(`RatFunc.liftOn_def`, `RatFunc.liftOn'_def` and 402 dependents) are
accepted with it, checked on their closure. The driver holds the decoded
corpus, about 38 GB for Mathlib.

The intrinsic kernel's native benchmark runner (`bench-certified-kernel`)
and census (`kernel-census-intrinsic`) were retired with that kernel
(`docs/kernel.md`, "The retired intrinsic kernel"); their measurements are
in this file's history.
