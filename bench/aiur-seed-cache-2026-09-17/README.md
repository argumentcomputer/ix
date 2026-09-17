# Device-resident seeds on the Init environment, one GPU

**Result (2026-09-17):** on the four-shard Init proof
(`bench/aiur-trace-init-2026-09-16`, same fixture hashes `e51437ef…` and
`3d45a1a3…`, same flags, `--exec-jobs 2 --max-ram 200`), keeping a round-two
source's seeds resident on the device between its commitment and the lookup
pass cuts the device callbacks inside lookup construction from 11.32 s to
6.26 s and lookup construction from 53.7 s to 48.6 s; the proving union falls
from 256.5 s to 250.6 s and the end-to-end time from 433 s to 431 s. Same
root `cef56bca…`, same composed verdict, 191 seed caches uploaded, none
refused by the 16 GiB limit, no fallbacks. One run per configuration, one
binary, same day, run back to back; the cache is switched off with
`AIUR_GPU_SEED_CACHE_BYTES=0`.

The first cache-on run of the day aborted at the round-two header check:
the multi-span cache upload restarted the pinned ring's chunk counter per
span and reused a slot before its previous DMA had landed. The fix carries
the counter across spans (`stage_copy` in `crates/aiur/cuda/trace_runtime.cu`);
`ix-cache2` is the binary with it. `resident_seeds_serve_tiles_until_released`
now stages five spans through the ring.

## Runs

| Run | Binary | Wall | End to end | CPU user s | Peak RSS | GPU util |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `q4-nocache-generated` | `ix-cache` (`0c8bca92…`), `AIUR_GPU_SEED_CACHE_BYTES=0` | 436.0 s | 433 s | 2086 | 93.7 GiB | 43.2% |
| `q4-cache2-generated` | `ix-cache2` (`c75ca783…`), cache on, 16 GiB limit | 433.8 s | 431 s | 2078 | 93.0 GiB | 42.3% |

The two binaries differ only by the ring fix, which the cache-off run does
not exercise. The cache-off run reproduces the recorded `ix-new6` generated
run (441 s wall, proving 258.0 s, lookup 54.1 s, callbacks 27.4 s) within
run-to-run noise, so the earlier ladder's CPU-trace baselines apply here.

| Union over all claims and joins, both rounds | cache off | cache on | change |
| --- | ---: | ---: | ---: |
| `aiur/prove_planned` | 256.5 s | 250.6 s | −5.9 s |
| `stark/batch_round_two` | 187.3 s | 181.7 s | −5.7 s |
| `stark/stage1_commit` | 128.8 s | 128.1 s | −0.7 s |
| `stark/lookup_construction` | 53.7 s | 48.6 s | −5.1 s |
| `aiur/codegen_device_rows`, all | 27.3 s | 21.8 s | −5.5 s |
| `aiur/codegen_device_rows` inside lookup construction (12,764 callbacks) | 11.32 s | 6.26 s | −5.06 s |
| `aiur/codegen_device_rows` inside stage-one commit (25,528 callbacks) | 15.94 s | 15.58 s | −0.4 s |
| `stark/quotient` / `stark/fri_open` | 35.3 / 30.9 s | 35.3 / 30.9 s | 0 |
| `aiur/codegen_seeds` | 43.8 s | 46.6 s | +2.8 s |
| `aiur/witness` / `aiur/cpu_witness` | 57.2 / 42.6 s | 57.3 / 43.3 s | 0 |

`split.py` attributes each callback to the phase whose interval contains
its start. The commit-time callbacks are unchanged by design: the commit
still uploads every seed once, now into one allocation that the lookup
tiles reuse. A lookup tile went from 0.89 ms to 0.49 ms; what remains is
the tile blank, the writer kernel, its launch and the error-word wait.

## Reading it against the ladder

Against CPU traces on the same tree (`q4-ix-new3-cpu`: 460 s, lookup
construction 38.2 s), generated traces had raised lookup construction by
15.5 s, of which 11.3 s were the regeneration callbacks; the cache removes
5.1 s of that. The end-to-end gain on Init is at the noise floor because
the four-shard graph leaves the one GPU worker waiting on executions and
joins for much of the run; on a graph that keeps the worker busy, such as
the 78-shard Mathlib partition, the 9.5% of lookup construction reaches the
wall clock.

## Reproduce

`BENCH_SCRATCH=<dir with init.ixe, init-4.ixes> run.sh <binary> <label> generated init-4.ixes --exec-jobs 2 --max-ram 200`,
once with `AIUR_GPU_SEED_CACHE_BYTES=0` in the environment and once without;
`compare.py ../aiur-trace-init-2026-09-16/spans.py runs/<a> runs/<b>` prints
the table, `split.py` the callback attribution. The binary is `lake build ix`
with `IX_CUDA=1 IX_CUDA_TRACE_CODEGEN=1`; on this host that needed
`CLANG_PATH=/usr/lib/llvm-21/bin/clang` for bindgen and `CFLAGS=-std=gnu17`
so gcc 15 does not redirect `strtol` to a C23 symbol the Lean toolchain's
libc lacks. Both binaries were built with a temporary Cargo config that
pointed multi-stark at the local checkout and, unintentionally, replaced
the repository's `-Ctarget-cpu=native` rustflag; the two runs share that, and
the cache-off run still reproduces the recorded `ix-new6` figures.
