# Benchmarking

Ix is benchmarked on two surfaces, both driven by one curated constant set and
the same backend drivers:

- **`!benchmark` PR comment** (`.github/workflows/bench-pr.yml`) — on demand,
  posts a **main-vs-PR** comparison table on the pull request.
- **Bencher.dev** (`.github/workflows/bench-main.yml`) — on every push to `main`,
  tracks each measure over time at <https://bencher.dev> (project `ix`).

## Backends

| backend | what it measures | metrics |
|---|---|---|
| `aiur` | IxVM kernel typecheck in the Aiur STARK prover (out-of-circuit execute + in-circuit prove) | `fft-cost`, `execute-time`, `prove-time`, `peak-rss`, `constants`, `throughput` |
| `zisk` / `sp1` | the same kernel in the Zisk / SP1 zkVM hosts, **execute** only (proving needs a GPU) | `cycles`, `execute-time`, `throughput`, `peak-rss` (+ `shards`, `max-shard-cycles` for sharded runs) |
| `native` | the same kernel run **out-of-circuit and in parallel** (`ix check`) — far faster | `throughput` (constants/s), `check-time`, `peak-rss`, `constants` |

In **prove** mode, `run.sh` proves each constant whose Aiur fft-cost fits the
prover RAM ceiling (`AIUR_PROVE_MAX_FFT`, ~128 GB at 2.34 GB per billion fft) and
falls back to **execute-only** for the rest, so every primary still reports
metrics. The `native` backend reports two views: the **whole env** (`ix check
--anon`, keyed by env) and a **per-primary subject check** (`ix check --consts`,
keyed by constant — apples-to-apples with the zkVM `--skip-deps` execute).

All four are driven by `.github/scripts/run.sh` (compile the env `.ixe`, run the
backend, emit a neutral `{ "<name>": { "<metric>": n } }` JSON). The PR workflow
compares two such JSONs; the bencher workflow wraps one in Bencher Metric Format.

## Constant set — `Benchmarks/Vectors.csv`

One CSV is the single source of truth: `name,env,tier,shard_target,primary,aiur_fft,zisk_cycles`.

- `env` — compile target the constant resolves in (`initStd` / `lean` / `mathlib`).
- `tier` — `cheap` (prove-feasible on a CI runner) or `heavy` (execute-only; a
  single-shard prove would OOM).
- `primary` — the **~11-constant default subset**, spanning shape and the
  cheap→heavy cost range (3 are shard targets). Everything defaults to this;
  the full ~60-constant set is opt-in.

`bench.py manifest` selects names by env + mode (`prove`→cheap, `execute`→all) +
`--primary`. `bench.py compare` renders the PR table.

## `!benchmark` grammar

Maintainer comment on a PR:

```
!benchmark [aiur] [zisk] [sp1] [native | all]  [execute|prove]
BENCH_ENVS=initStd,mathlib     # which compiled envs (default initStd)
BENCH_FULL=1                   # run the full curated set, not the ~11 primary
BENCH_TIER=cheap|heavy|all     # override the mode default (execute=all, prove=cheap)
BENCH_SHARD=1                  # restrict to the multi-shard target constants
BENCH_GPU=1                    # allow zkVM prove on a self-hosted GPU runner
RUST_LOG=info                  # passthrough env (allowlisted)
```

Defaults: `aiur`, `execute`, `initStd`, primary subset. Backends fan out as a
matrix; `main` results are cached by base SHA. zkVM `prove` is skipped with a
note unless a GPU runner is selected.

## Bencher jobs (`bench-main.yml`)

`build → compile → { prove, zkvm-execute, native-check }`, each reporting to its
own testbed + **workload** (`aiur`, `zisk`, `sp1`, `native-check`, `ix-compile`).
Deterministic measures (cycles, fft-cost, constants, …) are pinned exactly;
noisy wall-clock measures (time, RAM, throughput) ride percentage bounds, both
windowed to the per-workload `bencher-thresholds-reset-<workload>` tag.

To re-baseline a workload after an intended step change, comment
`!bencher-thresholds-reset <workload|all>` on the merging PR, or run the
`bencher-thresholds-reset` workflow (`.github/workflows/bencher-thresholds-reset.yml`).

## Not yet covered

- **zkVM proving** (Zisk/SP1 `prove`) needs a self-hosted GPU runner; on CPU
  runners it is execute-only.
