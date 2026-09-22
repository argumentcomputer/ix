# GPU trace generation after removing tree retention

**Result:** GPU trace generation used **5.93% less end-to-end time** and
**16.02% less process CPU time** in the measured pair.

| Trace generation | End-to-end | Process CPU | Peak host RSS | Sampled peak VRAM/GPU |
| --- | ---: | ---: | ---: | ---: |
| CPU | 304.11 s | 5592.72 s | 191.52 GiB | 65.29 GiB |
| GPU | 286.06 s | 4696.62 s | 192.14 GiB | 65.48 GiB |

Both runs verified the same root, completed the same fresh claims and joins,
and had zero LDE spills. These are one trial per mode. The tree cache is
removed; GPU generation remains opt-in. See the
[full results](results/analysis.md) and [machine-readable comparison](results/comparison.json).

One CPU-trace trial and one GPU-trace trial use the same CUDA CLI and frozen
eight-claim Init fixture. Both use four resident GPU provers and regenerate
each shard for round two. Only `AIUR_GPU_TRACE` changes (`cpu` / `blake3`).
This measures the effect on complete proving time, including execution,
joins and final verification. It is not an isolated kernel timing.

The Merkle-tree cache, its byte-budget selector and checkpoint/restore APIs
have been removed. The generated main commitment still checks space for
each trace/LDE construction separately from Merkle hashing. The
[retention experiment](../tree-cache-2026-09-15/README.md) is archived.

## Validation and controls

Five focused CUDA tests passed, including generation/commitment on devices
0–3, canonical cell equality, source release after failures and at the batch
barrier, CPU/GPU proof-byte equality, and rejection of corrupted regenerated
values. The complete sharded proof also passed with forced LDE spills and
three-row lookup recovery tiles. The test build used two jobs and a separate
test workspace with release LTO disabled; the benchmark CLI uses its normal
release profile. No validation-only spill settings enter timed trials.

Each trial has a fresh proof cache, four lanes, two execution jobs per lane,
200 GiB per-worker RAM budget, 1.5 billion committed cells per trace shard,
and maximum piece log height 24. The outer scope limits host RAM to 400 GiB
with swap disabled; each trial has a 15-minute watchdog. Host worker pools
use their normal defaults, with effective CPU affinity recorded.

The runner requires eight fresh claims, seven fresh joins, the historical
verified Init root, and 182 main commitments across both rounds. CPU mode
must use only the host main-commitment path. GPU mode must use the generated
path and report the expected 120 generated sources / 110,892,480 rows.
The counters come from structured fields in CLI tracing; a direct prover
report API is not implemented. Missing or mismatched results fail the run.

Wall time, process CPU time, peak process RSS, sampled GPU memory, logical
LDE spill bytes, binary/fixture hashes and environment settings are retained.
GPU memory is sampled once per second, not an exact allocation peak. Seed
preparation bytes and LDE spill bytes do not measure PCIe traffic. One trial
per mode is an initial measurement and does not establish small changes
outside normal run variation.

## Reproduce

`build.py` builds against `~/repos/multi-stark` using a temporary Cargo path
override. It limits Cargo and Lean to two jobs, checks that other dependency
resolutions stay unchanged, and restores Cargo configuration and the
lockfile. It preserves source diffs, build settings and the executable in
`target/gpu-trace-build/`. The tracked backend pin still needs updating when
the backend changes are committed.

```sh
python3 bench/gpu-trace-regenerate-2026-09-15/build.py
systemd-run --user --scope -q -p MemoryMax=400G -p MemorySwapMax=0 -- \
  python3 bench/gpu-trace-regenerate-2026-09-15/run.py \
    --binary target/gpu-trace-build/ix-no-tree-cache \
    --fixture target/tree-cache-bench/fixture \
    --output target/gpu-trace-bench-new
```

The two trials take approximately ten minutes, excluding the build. Add
`--mode cpu` or `--mode gpu` to run only that mode. Output directories must
be new. The runner does not rebuild, repartition, or remove proof caches.

The fixture comes from `Benchmarks/Compile/CompileInit.lean` under Lean
4.33.1 and was partitioned once into eight claims. Its construction commands
and hashes are preserved with the retention experiment.

Metadata, commands, counters, source patches, build records and compressed
raw logs are archived in `results/`. Binaries, fixture blobs and proof caches
remain under `target/`. The measured binary is
`target/gpu-trace-build/ix-no-tree-cache`, SHA-256
`9883ee50815f2812f85d5512995ee8ab554830bb9fd6718cb57f5dab3452b623`.
The ordinary `.lake/build/bin/ix` was rebuilt from the same source as well.

Regenerate the table from completed trial records with:

```sh
python3 bench/gpu-trace-regenerate-2026-09-15/summarize.py target/gpu-trace-bench
```
