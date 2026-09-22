# Generated traces on the Init environment, one GPU

Paired proofs of the Lean `Init` environment, four claims and three joins,
on one RTX PRO 6000 Blackwell with 32 CPU threads, comparing the CPU trace
builder (`AIUR_GPU_TRACE=cpu`) with the generated GPU provider
(`AIUR_GPU_TRACE=generated`) across three revisions of the branch. Every run
verified the same root and composed verdict from an empty cache:

```text
cef56bca82bd3d5fb10c162e174c6f26550b3eaff51d92570d7bce7ba92d5f0e
```

## Fixture and command

```sh
ix compile --no-build Benchmarks/Compile/CompileInit.lean --out init.ixe   # 65,994 constants, 195 MB
ix shard init.ixe --shards 4 --out init-4.ixes
```

`run.sh <binary> <label> <mode> init-4.ixes --exec-jobs 2 --max-ram 200`
runs `ix prove --ixe init.ixe --ixes init-4.ixes --trace-shards --lanes 1`
with `AIUR_TRACE_ONLY_LOOKUPS=1`, `AIUR_MAX_PIECE_LOG_HEIGHT=24`,
`AIUR_TRACE_SHARD_MAX_CELLS=1500000000`, a fresh `AIUR_LANES_CACHE_DIR`,
`AIUR_PROFILE` span events and a one-second `nvidia-smi` sample. Each
`q4-*` directory holds the prover's log, GNU time, the span summary
(`spans.py`) and the GPU samples. The summaries were recomputed on
2026-09-17 after a fix to `spans.py`: it had overwritten a span's completed
intervals when the tracing layer reused its ID, which undercounted the
short, numerous spans (device callbacks, lookup construction, quotient,
FRI) by up to 6x; long spans such as `aiur/witness` and `aiur/codegen_seeds`
were unaffected. Fixture hashes: `init.ixe`
`e51437ef2d6638ea…`, `init-4.ixes` `3d45a1a39749282c…`.

A first pair was discarded: Claude Code's rust-analyzer flycheck compiled
the workspace, including nvcc, alongside it and stretched one CPU-trace run
from 472 to 604 s. The `q4-*` runs below were taken with that process
stopped and no compiler running; the discarded logs are not included.

## Binaries

| Binary | Tree | Generated writers (ixvm / multi-stark / ix-aggr) |
| --- | --- | ---: |
| `ix-baseline` (`63a3b4f38f7cbd77…`) | typed schema, serial seed packing, handwritten provider removed | 1 / 1 / 1 |
| `ix-new` (`fc39552d8068e6f0…`) | + parallel chunked packing, compact-circuit selection, schema contract, pointer bounds fix | 14 / 10 / 4 |
| `ix-new2` (`f420688ff29fef7f…`) | + zeroed host matrices, no lookup payloads in trace-only mode, exact span preallocation | 14 / 10 / 4 |
| `ix-new3` (`75e4bfb5ddb74564…`) | same tree as `ix-new2`; its weighted selection did not resolve, so this pair is a repeat measurement | 14 / 10 / 4 |
| `ix-new4` (`a31e406c60e7aae5…`) | + memory tables generated on the device (`prepare_memory`, `aiur_trace_memory`) | 14 / 10 / 4 |
| `ix-new5` (`49a51b37befc9609…`) | + `weightedCircuits`: the IxVM circuits ranked by measured host witness time; memory generation opt-in and off | 42 / 10 / 4 |
| `ix-new6` (`47898b3bc5868d87…`) | + pipelined seed upload (ring of eight pinned 2 MiB chunks with transfer events), tile blanked by one memset instead of a zero pass per row in every kernel, grids sized by real rows | 42 / 10 / 4 |

## Results

Wall time is the prover's own end-to-end figure. Unions are of overlapping
host spans across all claims and joins, both rounds, and do not add.

| Run | End to end | Proving union | Stage-one commit union | Host witness union | Zero-fill union | Seed prep union | CPU user s | Peak RSS | Mean GPU util |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| baseline, cpu | 472 s | 300.8 | 158.2 | 173.8 | 116.5 | | 3537 | 98.0 GiB | 39% |
| baseline, generated | 452 s | 275.2 | 138.4 | 118.8 | 58.7 | 19.4 | 2983 | 97.8 GiB | 41% |
| new, cpu | 472 s | 299.1 | 156.4 | 174.2 | 116.5 | | 3546 | 98.0 GiB | 39% |
| new, generated | 454 s | 284.0 | 143.1 | 116.8 | 57.3 | 16.2 | 2944 | 97.4 GiB | 40% |
| new2, cpu | 459 s | 276.0 | 156.5 | 102.8 | 7.6 | | 3454 | 90.0 GiB | 38% |
| new2, generated | 452 s | 271.1 | 139.3 | 85.9 | 7.0 | 18.7 | 2876 | 92.1 GiB | 40% |
| new3 (repeat of new2's tree), cpu | 460 s | 276.0 | 156.5 | 103.0 | 7.5 | | 3463 | 90.9 GiB | |
| new3, generated | 452 s | 270.3 | 138.9 | 85.4 | 6.9 | 18.9 | 2866 | 91.9 GiB | |
| new4 (+ memory tables on device), generated | 457 s | 279.3 | 143.2 | 85.1 | 6.4 | 20.0 (+19.2 memory) | 2867 | 94.8 GiB | |
| **new5 (weighted coverage, 42 ixvm writers), generated** | **442 s** | **260.4** | **131.6** | **41.3** | 6.1 | 45.2 | **2106** | 93.4 GiB | |
| new6 (+ pipelined upload, memset blanking), generated | 441 s | 258.0 | 129.8 | 43.5 | 6.1 | 44.6 | 2094 | 93.7 GiB | 42% |
| new6, generated, `--exec-jobs 3` | 428 s | 257.7 | 129.8 | 42.0 | 6.1 | 44.6 | 2092 | 107.5 GiB | 43% |

Execution (`aiur/execute_ixvm`) is a 340 s union in every run, and the
GPU is sampled busy about 40% of the time. The lanes log explains the idle
time: nothing can be proven until the first claim has executed (112 s);
the four claim proofs then run back to back on the one worker; a join is
dispatched only once both child proofs exist, because its execution
verifies them; and the root executes after the last join publishes. So
join 5's execution (33 s) and the root's (26 s) sit on the critical path
with the GPU idle. A third executor (`q4-ix-new6-generated-exec3`) closes
the one gap the executor count caused, claim 3 waiting for a free executor,
and gets join 2 an executor as soon as its children are proven: 425 s end
to end against 438 s, at 14 GiB more peak RSS. The rest of the idle time is
the graph's shape at four shards, not a supply problem.

## What the numbers say

- **Row-weighted coverage is what moved the numbers.** With the 24
  circuits that the measured profile ranked highest generated on the device
  (`ix-new5`), end to end fell to 442 s against 452 s for BLAKE3-only
  generation and 472 s for CPU traces, the proving union to 260 s, host
  witness union from 85 to 41 s, and CPU time to 2106 s, 40% below the CPU
  baseline. 382 seed spans, no guard fallbacks, same root. Seed preparation
  union grew to 45 s and device callbacks to 30 s: that is now the largest
  host cost inside proving, and the next target.
- **Generation makes lookup construction slower.** `stark/lookup_construction`
  is 38 s of union wall in every CPU-trace run and 44 to 56 s in the
  generated runs (54 s for `ix-new5` and `ix-new6`). The generated commit
  path releases the raw device trace after the LDE and retains no host
  copy, so the lookup kernel regenerates its row tiles through the same
  callbacks; the CPU path keeps the host matrix. Of `ix-new6`'s 27 s of
  device callbacks, the share inside lookup construction is that
  regeneration. Retaining expensive raw traces while device memory allows,
  or caching the compact device seeds, is the trace-generation change with
  a measured target; see the Mathlib bench for the same effect at scale.
- **The uploader's share is the kernel, not the copy.** Instrumenting one
  65,536-row BLAKE3 span (11.5 MB typed) split its 2.2 ms into 0.72 ms of
  host copy into pinned memory, 0.22 ms of DMA and 1.15 ms of kernel, of
  which a third was the zero pass each thread made over its 4.3 KB row.
  `ix-new6` overlaps the host copy with the DMA through a ring of pinned
  chunks and blanks the tile with one memset that runs during the copy;
  the kernels write only set columns. The span now takes 1.80 ms against
  2.31 ms, and on Init the device-callback union fell from 29.9 to 27.4 s
  over the same 38,292 callback spans, the proving union from 260 to
  258 s, at the same root. Splitting the kernel per chunk was tried first and lost:
  12,000-row launches run on a fraction of the device and serialize on the
  stream, so the tile took 3.3 ms. What remains per span is kernel time on
  a 254-register, spilling kernel and the uncoalesced row-major stores, and
  the 0.7 ms host copy that a packer writing straight into pinned memory
  would remove.
- **BLAKE3-only generation is worth about 4 to 5% of wall time and 16 to
  19% of CPU time on Init**, consistent with the earlier four-GPU Init
  measurement (298 to 286 s). The typed schema did not change that: the
  seeds were already 176 bytes.
- **Wider coverage did not move wall time.** `ix-new` generates 28 circuits
  instead of 3, chosen statically by seed compression, and produced 182
  seed spans against 90; end to end was 454 s against 452 s. The added
  circuits carry few rows in this environment. Row weights, not static
  ratios, have to pick coverage.
- **Zeroed host matrices removed the fill pass but little wall time.**
  `aiur/witness_zero` fell from 116 s to 7.6 s of union time, host witness
  union from 174 to 103 s, peak RSS by 8 GiB, and CPU time by 2.4%; end to
  end fell 13 s (2.8%). The fill was mostly overlapped with device work.
- **Parallel seed packing did not shorten the seed spans in production.**
  The tile microbenchmark improved 3.6x, but the prover already runs
  circuits under a saturated Rayon pool, so the union barely moved (19.4 to
  16.2 s). It still matters on a lightly loaded host.
- **Memory tables on the device do not pay here.** `ix-new4` generated every
  memory table range on the GPU: 274 spans, 16,980 device callbacks, 19 s of
  seed-copy union. End to end rose from 452 to 457 s and the proving union
  from 270 to 279 s. A memory seed carries every value plus the pointer and
  multiplicity, so it is as large as the row it replaces less one column;
  there is no byte saving to offset the launches. The generator stays in the
  tree behind `AIUR_GPU_TRACE_MEMORY=1` for hosts where building rows, not
  moving them, is the limit.
## Compiled writers

For the 42-writer IxVM unit plus the 10 and 4 of the join programs, nvcc's
`-Xptxas -v` reports 20 to 40 registers for every generated row writer, one
at 146 and one at 254; the only function that spills is the pre-existing
canonical-codec BLAKE3 variant (176 bytes stored, 208 loaded). All 97 GPU
tests, including the coverage-aware registration test and the memory-table
parity test, pass against this bundle, and `ix codegen --trace-bundle
--check` reports it fresh.

- **The remaining host witness time is the heavy traversal circuits.**
  `weights.py` over the generated run's spans ranks IxVM circuits by host
  witness time: `blake3_compress_chunks` (199 M rows, 46 s union),
  `get_tag4`, `get_u64_le`, `g_list_has`, `list_snoc.G`, `expr_glb_walk`,
  `expr_inst_many_walk` and about fifteen more at 12 to 25 s each. Their
  typed seeds are 0.3 to 0.85 of the row. That list is the
  `weightedCircuits` selection in `Ix/Cli/CodegenCmd.lean` that `ix-new5`
  measures; `weights-new2-generated.md` is the ranking it came from and
  `q4-ix-new5-generated/weights.md` the profile after it.
