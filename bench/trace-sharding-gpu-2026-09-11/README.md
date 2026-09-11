# GPU trace-sharding runs, 2026-09-11

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
