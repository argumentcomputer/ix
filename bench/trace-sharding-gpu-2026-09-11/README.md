# GPU trace-sharding runs, 2026-09-11

Latest evidence: [queue22](queue22/README.md). Current code pins, results, and
Mathlib instructions: [pre-Mathlib handoff](../../docs/aiur-gpu-mathlib-handoff.md).
The recipe and headline below describe the earlier run in the measurement ladder.

Recipes behind `docs/aiur-gpu-plan-status.md`. Box: 32 cores, 249 GiB,
one RTX PRO 6000 (96 GB), THP `always`.

- `runlib.sh`: `run TAG BIN ARGS...` proves under `/usr/bin/time -v` with a
  1 s GPU-utilization/RSS sampler and an RSS watchdog on the prover process
  (the child of `time`, not `time` itself), then verifies the proof.
- `prove-distributed.sh IXE IXES MAX_RAM_GIB CELLS [EXEC_JOBS] [args...]`:
  the distributed prove with the retry fallback — on a kill by the memory
  cap (exit 137) it reruns with `--exec-jobs` halved, down to one. Run it
  under the cap: `systemd-run --scope -p MemoryMax=230G -- ./prove-distributed.sh ...`.

The headline run (6:18 wall, verified):

```
IX_CUDA=1 LIBCLANG_PATH=/usr/lib/llvm-18/lib lake build ix
ix compile Benchmarks/Compile/CompileInit.lean --out init.ixe
ix shard init.ixe --shards 1 --out init-1.ixes                 # verification manifest
ix shard init.ixe --ordered --shards 8 --out init-ordered-8.ixes
AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24 \
  ix prove --ixe init.ixe --ixes init-ordered-8.ixes --distributed \
    --cells 1500000000 --max-ram 200 --texray --no-index
ix verify --ixe init.ixe --ixes init-1.ixes <batch address>
```

## Env-shard pipeline (afternoon and evening of 2026-09-11)

The runs behind the env-shard sections of `docs/aiur-gpu-plan-status.md`.
Queue scripts in `~/benchdata/trace-shards-gpu/` (Init) and
`~/benchdata/mathlib-gpu/` (Mathlib); each stage runs under the cgroup cap
with the child-PID watchdog and the GPU/RSS sampler from `runlib.sh`.

| script | what |
|---|---|
| `queue26.sh` / `queue27.sh` | Init as 4 / 8 ordered env-shard claims: Stage 1, direct-join Stage 2 |
| `queue28.sh` | the same on `init-mincut-4.ixes` (`ix shard init.ixe --shards 4`) |
| `queue29–31.sh` | Stage 2 with `--wrap-root` (once, then until one shard) |
| `queue32.sh` | Stage 1 with `--exec-jobs 4` (executions ahead of the prover) |
| `queue33.sh` | Init end to end on the reverted (namespace-free) kernel |
| `queue34.sh` | Init end to end with the two-lane Stage 2 scheduler and ready-order Stage 1 |
| `run-env-mathlib.sh` | Mathlib Stage 1 (128 min-cut claims, `--exec-jobs 4`, cap retry) |
| `verify-native.sh` | the native parallel composed verdict on Init and Mathlib |
| `run-mathlib-stage2.sh` | Mathlib Stage 2 from the stored claims, `--wrap-root`, root verify |
