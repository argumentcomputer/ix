# Formal Aiur on CUDA: hardware validation and pipeline bottlenecks

Historical record: measured 2026-10-31 on one RTX PRO 6000 Blackwell Server
Edition (96 GB, driver 595.99.02, CUDA 13.3, `MULTI_STARK_CUDA_ARCHS=120`), a
32-thread Xeon Platinum 8559C and 249 GB of RAM, starting from `129c8056`.
Prover benchmarks pin `RAYON_NUM_THREADS=16` and disable transparent huge
pages, as in the earlier measurements. The same machine also ran the complete
CPU pipeline.

## Hardware validation

`IX_TEST_CUDA=1 tools/ixvm/check-formal.sh` passed. CPU and CUDA proofs and
keys are byte-identical for IxVM, recursion and aggregation under retain and
regenerate, with host and graph-derived lookups. This includes the single-shard
graph-lookup retain/regenerate cases added by the
[batch preparation follow-up](formal-aiur-gpu-preparation.md), which had not
run on a GPU before. The one-device controller proofs pass, and the CPU host
verifies every GPU proof. The gate also checks GPU stage-one population
(`AIUR_GPU_TRACE=generated`) for all three applications, sharded and
single-shard; with every change below, all 43 earlier proof and key files are
byte-identical to the first run and the 10 new ones match the CPU. The 97 Rust
tests of the CUDA-featured `aiur`, `ixvm`, `stark-verifier` and `ix-prover` and
multi-stark's 54 CPU and 88 CUDA tests pass. The gate uses grep, not ripgrep,
so it runs on hosts without ripgrep.

## Prover benchmark

Trace generation, proving and verification; median of three processes,
seconds. Formal artifacts were exported at `129c8056`. The fixes below do not
change this single-shard path.

| Workload | CUDA, host lookups | CUDA, graph lookups | CPU |
|---|---:|---:|---:|
| `Nat.add_comm` frontier | 0.183 | 0.179 | 0.334 |
| 342-constant environment | 0.493 | 0.440 | 1.854 |
| Small recursive verifier | 0.092 | 0.091 | 0.157 |
| Large recursive verifier | 4.172 | 2.724 | 23.855 |

The 2026-10-29 review measured 20.288 s and 8.330 s for the large recursive
verifier on CUDA (host and graph lookups) and 1.286 s and 0.680 s for the
environment; `44ea8742` accounts for the difference. The large verifier costs
87.3 billion FFT-cost units.

With host lookup buffers, multi-stark's CUDA prover took the graph path for all
68 lookup jobs of the large verifier even though host buffers were supplied:
the buffers are built (0.97 s, about 17 GB) and never read unless device memory
pressure forces a fallback. `Blake3::compress` alone, with 226 lookup slots and
1,672 lookup values per row over 2^20 rows, accounts for 14 GB of that. A
different allocator does not change it (mimalloc: 4.05 s versus 4.13 s).

## Pipeline: `ix prove --lanes 1`

The 342-constant environment, partitioned with `ix shard --shards 4`, proved
with `ix prove --ixe env.ixe --ixes env4.ixes --trace-shards --lanes 1
--exec-jobs 2 --max-ram 160 --no-index --no-cache`. Every successful run
verifies its root; runs of the same configuration produce the same root.

| Configuration | Wall | Peak RSS | Sampled GPU peak |
|---|---:|---:|---:|
| `129c8056`, its GPU default (`--shard-rows 65536`) | fails after 204–211 s | 37–38 GB | 4.6 GB |
| `129c8056`, `--shard-rows 4194304`, graph lookups | 94.7 s | 23.1 GB | 32.5 GB |
| `129c8056`, `--shard-rows 4194304`, host lookups | 105.5 s | 41.0 GB | 32.5 GB |
| With these fixes, defaults, graph lookups | 63.3–66.6 s (four runs) | 26.5 GB | 32.5 GB |
| With these fixes, defaults, host lookups | 73.6–74.5 s (three runs) | 45.6 GB | 32.5 GB |
| With these fixes, graph lookups, `--exec-jobs 4` | 57.6 s | 33.3 GB | 32.5 GB |
| With these fixes, graph lookups, `--direct-joins` | 64.0 s | 34.8 GB | 32.6 GB |
| With these fixes, two lanes sharing the GPU, 96 GB each | 56.6 s | 33.3 GB | 64.1 GB |

At the old GPU default, each wrapped leaf became a 64-shard, ~30 MB proof. The
next join then executed for 65 s (34 billion instructions), produced a 29.8 GB
record and 10.9 billion stage-one cells, and planned a 121 GB peak against an
85 GB lane budget, so the run stopped with exit 75. The fixed and 4M-row runs
publish the same root, `ce29cb0e…3108b`.

Formal bytecode wraps one leaf in 7.8–8.9 s and joins two wraps in 7.2–7.9 s.

## Where formal pipeline time goes

The fixed pipeline spends 61 s executing and 22.5 s proving, with recursive
executions on the critical path (7–9 s each, as above); the GPU is busy
16–20% of the time. A per-function profile (`aiur/function-profile`) of the
large recursive verifier input (a 7.2 MB IxVM proof, 8.0 s, 3.3 billion
instructions) attributes half the execution to Blake3:

| Function | Self time | Calls |
|---|---:|---:|
| `Blake3::compress` | 50% | 911,439 |
| `Blake3::compress_chunks` | 7% | 1,101,373 |
| `Pcs::ro_fold` | 7% | 1,259,911 |
| `Pcs::rows_pop` | 5% | 667,757 |
| proof, key and stream decoding | about 15% | |

Each `compress` call (one Blake3 round) executes about 172 byte-table
operations, 57 field additions and 28 word hints, at roughly 15 ns per
operation. A microbenchmark of random multiplicity updates over eight 512 KiB
tables costs 3–5 ns per update, so table cache misses do not explain this. The
cost is interpreter dispatch, which compiled execution removes.

## Recursion under per-lane budgets

Aggregation converges only when each recursive proof has few shards: a wrap
or join verifies every shard of its children, so a child split by its lane's
budget makes the parent's record and trace larger, and so on up the tree. At
`129c8056` the controller gave every lane an equal, fixed share of the prover
workspace.

The complete CPU pipeline (`ix prove --aggregate`, same environment and
partition, `--exec-jobs 4 --max-ram 192 --no-cache`) shows both failure modes:

| CPU configuration | Result | Wall | Peak RSS |
|---|---|---:|---:|
| `--jobs 2`, former default 65536 rows | first joins exceed the budget (exit 75) | 3:05 | 46 GB |
| `--jobs 2 --shard-rows 4194304` (the guide's former recipe) | root wrap exceeds the budget (exit 75) | 5:16 | 86 GB |
| `--jobs 1`, automatic rows | verified root `ce29cb0e…` | 3:19 | 67 GB |

At 65536 rows the first join reproduced the GPU failure exactly (78 s of
execution, a 29.8 GB record, 256 shards, a 121 GB plan against 51 GB). With two
lanes, each lane's 51 GB could not hold a single-shard wrap of a leaf (75 GB
planned), so wraps used 8 shards, joins 8, the next join 32, and the root
wrap's stage-one trace alone (5.5 billion cells) exceeded the lane. Records
grew 6.7 → 7.4 → 11.2 → 15.1 GB. With one lane every recursive proof had one
shard (the root join two) and the CPU pipeline produced the same root as the
GPU pipeline.

The same divergence affected CUDA, because the shared planner charged the CPU
prover's commitment phases to host RAM even when they run on the device. At
`--max-ram 96` (the per-GPU budget of the orchestration guide's four-GPU example)
one GPU lane failed in 2:33 with host or device lookups. The standalone CUDA
host shows the overestimate for the large recursive verifier:

| Shards, lookups, retention | Planned before | Planned after | Measured RSS |
|---|---:|---:|---:|
| 1, host, retain | 76.4 GiB | 42.7 GiB | 25.0 GiB |
| 1, device, retain | 76.5 GiB | 15.2 GiB | 10.5 GiB |
| 1, host, regenerate | — | 51.7 GiB | 32.1–33.0 GiB |
| 8, host, regenerate | 46.4 GiB | 48.6 GiB | 30.8–31.6 GiB |
| 8, device, regenerate | 46.4 GiB | 23.3 GiB | 14.7–14.9 GiB |

Measured RSS covers the whole process, including execution; every plan stays
above it. Forced retention of eight shards still plans the CPU commitment
model and is refused. With the CUDA host model below, the `--max-ram 96`
pipeline verifies its root in 75.3 s with 40 GB peak RSS: every wrap and join
plans one shard, and the root join four. At `--max-ram 160` the plans, proofs
and root (`ce29cb0e…`) are unchanged (73.6 s with host lookups, 66.2–66.6 s
with device lookups; the earlier 63.3 s used the same plans and differs only in
job order).

## Fixes

**Buffered JSON outputs.** `stark-verifier` and the controller wrote each
recursive proof's `input.json` (every proof byte as a JSON number) through an
unbuffered `File`, one write syscall per token. That cost about 2.3 s of lane
time per 3.5 MB proof and 18 s for a 30 MB, 64-shard proof. Buffering cut lane
time per recursive job from 4.5–4.9 s to 2.3–2.5 s; the proof and `input.json`
bytes are unchanged.

**Automatic, device-sized shards.** `--shard-rows` defaults to automatic
planning: the largest shards that fit the RAM budget. On CUDA the planner also
bounds each shard's committed cells (stage-one, stage-two and quotient columns
over padded rows) by `AIUR_TRACE_SHARD_MAX_CELLS`, 1.5 billion by default; one
such shard of the large recursive verifier (1.46 billion cells) peaks near
33 GB. CPU builds apply a cell bound only when `max_cells` is given. Explicit
`--shard-rows` remains a cap. Lower the cell bound on smaller devices. The CPU
pipeline failed the same way at 65536 rows (above).

**CUDA host-memory model.** CUDA plans charge host RAM for what the host holds
while the device commits, builds stage two and opens: the source matrices, the
shard witness (trace and, unless the device derives them, lookup buffers), the
next shard's witness when there are several, and 256 MiB of upload staging. A
retained single shard moves its trace from the source and is charged only its
lookups. Retained multi-shard commitments keep the CPU model, because device
pressure can spill them to host memory. CPU builds are unchanged.

**Parallel slicing, moved on last use.** Multi-shard batches copied every
shard's rows with a serial `to_vec`, again in round two when regenerating.
Slices are copied in parallel. On a shard's last supply, matrices that no later
shard reads (fixed tables and circuits no taller than one shard) move into the
prover instead of being copied. The large recursive verifier as two shards,
standalone host, proving seconds:

| Case | Before | After |
|---|---:|---:|
| Graph lookups, regenerate | 8.13 | 2.76 |
| Host lookups, regenerate | 11.31 | 5.70 |
| Host lookups, retain | 6.39 | 3.19 |
| One shard (automatic plan) | 1.79 | 1.79 |

In the pipeline, the upper join that needed two shards went from 13.2 s to
4.2 s of proving. All standalone proofs above are byte-identical to `129c8056`.

**Device lookups by default, with a safe fallback.** CUDA proving does not
build host lookup buffers by default. multi-stark's direct and CPU lookup
paths, taken when device memory pressure keeps a commitment off the device,
aborted on shape-only buffers before multi-stark `ed65a7c`. From that revision
they rebuild the omitted values from the committed trace: the committed LDE's
evaluations on `gH` interpolate the trace back onto `H` (a retained host trace
is used when present), and multi-stark's lookup evaluator, parallel over rows,
derives the values. With `MULTI_STARK_CUDA_MIN_FREE_BYTES` holding 85 or 93 GB
of the device free, the large recursive verifier went from an aborted prover to
12.0–14.6 s and the same proof bytes as an unpressured run (host lookups take
6.8 s under the same pressure). Unpressured it proves in 1.84 s with 10.5 GiB
peak RSS, against 3.19 s and 24.9 GiB with host buffers. The pipeline default
dropped from 73.3 s and 45.8 GB to 66.0 s and 26.7 GB. multi-stark's CPU tests
prove shape-only witnesses (with preprocessed columns, and batches under both
retention policies) byte-identically. `AIUR_TRACE_ONLY_LOOKUPS=0` restores host
buffers.

**Shared prover workspace.** Lanes reserve their planned peak from one
workspace instead of owning a fixed share. A recursive job that its share would
split into more shards plans within the whole workspace and waits for it; on
CPU it also takes every lane's threads. The CPU pipeline with `--jobs 2
--max-ram 192`, which failed before, proves single-shard wraps and the same
root as one lane in 3:20 (69 GB peak RSS).

**Run from anywhere, prepare ahead.** Formal `ix` resolves its exporters,
sources and artifact cache against the checkout it was built in (or
`IX_ROOT`) instead of the working directory, and announces a first-use
export. `ix prepare` exports the IxVM and aggregation artifacts ahead of
time. At `129c8056` the IxVM export took 9.5
minutes: 41 s parsing and checking, 10 s table checks, 35 s bytecode and 480 s
compiling the certified circuits, grouping and population plans.

**Multi-lane GPU smoke tests.** Every multi-stark CUDA entry point selects its
device explicitly, and its process-wide caches are host-only or keyed by
device, so lanes on different devices in one process do not share device
state. With one GPU, the test opt-in `IX_PROVER_SHARED_DEVICES=1` lets lanes
share a device: `check-controller.py --devices 0,0` passed (jobs split across
both lanes, every proof byte-identical to the CPU reference), and the pipeline
with `--lanes 2` on device 0 proved the same root as one lane in 56.6 s.

**Opt-in GPU stage-one population.** `AIUR_GPU_TRACE=generated` fills on the
device every function circuit whose population plan reads only recorded calls
(through a device hash of the callee's queries), the U8 byte tables and the
word hints: `crates/aiur/cuda/population.cu` interprets the compiled plans and
group placements, and the rows reach multi-stark as generated traces, so the
host neither builds nor uploads them. The record tables they read are uploaded
once per proof. In the recursive verifier 3 of 54 circuits qualify, among them
`Blake3::compress` (over half the cells); the rest use memory or stream hints,
or are ROMs and fixed tables. Proofs are byte-identical: a unit test covers a
grouped program sharded and whole under both retention policies, the hardware
gate covers IxVM, recursion and aggregation, and the pipeline publishes the
same root. The large recursive verifier proves with 7.8 GiB peak RSS instead of
10.5 GiB, but host population only drops from 0.66 s to 0.51 s while proving
grows from 1.84 s to 2.29 s: the interpreter fills `compress` in about 10 ms per
64K rows, and graph lookups regenerate its tiles (42 tile fills, 2.6 times the
trace). The pipeline takes the same 66.0 s with 14.0 GB peak RSS (26.7 GB by
default) and 28 GB on the GPU (32.5 GB).

## Gaps at `129c8056`

- **Native execution.** Recursive-verifier execution was the critical path
  (61 s of execution against 23 s of proving; the GPU busy 16–20% of the
  time), and half of it was `Blake3::compress` in the bytecode interpreter.
  More lanes and `--exec-jobs` helped (56.6–57.6 s). See
  [native execution](formal-aiur-native-execution.md).
- **GPU trace generation speed.** `AIUR_GPU_TRACE=generated` is correct and
  halves host RAM but was not faster: it interprets plans and covers only plans
  without memory or stream state. CPU population cost 5.2 s across the pipeline
  (0.63–0.73 s per large recursive job), and the covered circuits were about
  0.15 s of each. A speedup needs generated kernels covering memory and ROM
  circuits too, the same code generation as native execution.
- **Multiple physical GPUs.** Lanes on distinct devices were reviewed and
  smoke-tested on one shared device, not run on several devices.
- **Row-capped shards.** Every circuit shorter than the row cap stays in shard
  zero, so a job just over the cell bound becomes one large shard plus small
  ones, and graph lookups regenerate every shard of a multi-shard batch.
- **Export time.** The certified IxVM export took 9.5 minutes, 85% of it in
  circuit compilation, grouping certification and population plans. `ix
  prepare` moves it out of the first proof but does not shorten it.
- **multi-stark revision.** The lookup fallback was multi-stark `ed65a7c` on
  branch `formal-aiur/lazy-lookups`, on top of the previous pin `c7324887`
  (`perf/aiur-lookup-writes`).

## Data

[Prover medians](benchmarks/formal-aiur-gpu-validation/prover.csv) and
[pipeline runs](benchmarks/formal-aiur-gpu-validation/pipeline.json).
