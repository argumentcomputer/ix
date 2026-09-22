# Prover CPU/GPU timeline investigation — 2026-09-15

## Findings

Prioritize main-trace construction and the stage-one upload/commitment path.
Kernels occupy 56% of the representative claim's proving interval and 58–59% in
the two join replays. The remaining time includes
substantial transfers and host work inside commitment; it is not all witness
generation or a batch barrier.

Packed BLAKE3 seeds with bounded pinned staging are a contained first A/B.
The larger follow-on for claims is generating more traces on the GPU or sending
compact representations of columns with proven bounds: BLAKE3 seeds account for
only 18.12 GiB of the claim's 175.60 GiB of H→D traffic.

| Measurement | Join 33 | Root join 154 |
|---|---:|---:|
| Trace pieces | 7 | 13 |
| Prepare slot, including advice and VM execution | 30.46 s | 70.87 s |
| Prove planned batch | 27.86 s | 49.97 s |
| Union of kernel intervals inside proving | 16.28 s | 29.45 s |
| Kernel busy time / proving time | 58.4% | 58.9% |
| Transfers with no kernel running | 3.83 s | 6.45 s |
| Stage-one commitment, both rounds | 15.08 s | 25.28 s |
| Stage-one commitment with no kernel running | 6.76 s | 10.47 s |
| Lookup construction and commitment | 5.63 s | 9.94 s |
| Quotient | 2.70 s | 4.91 s |
| FRI/opening | 2.46 s | 5.36 s |
| Outside those four GPU stages | 2.00 s | 4.49 s |
| Outside those stages while preparing witnesses | 1.84 s | 4.20 s |
| BLAKE3 seed uploads | 25.81 GiB | 43.73 GiB |
| BLAKE3 seed transfer time | 2.72 s | 4.59 s |
| Sampled device memory peak | 64.56 GiB | 64.53 GiB |

Rows overlap where indicated. Kernel busy time is the union of kernel intervals,
not a sum of durations across streams, and is not SM occupancy. CPU span totals
include time blocked in CUDA. A host `cudaStreamSynchronize` interval is not
automatically wasted GPU time.

### Repeated BLAKE3 seed uploads

The host seed is still 162 `u64`s (1,296 bytes). The generated trace is committed
in round one, regenerated and committed in round two, and generated again for
lookup construction after the raw device trace is released. Lookup tiles also
include a boundary row. The traces directly associate 25.81/43.73 GiB of H→D
transfers with `aiur/blake3_device_rows`.

At 176 bytes per packed seed, the same rows would require approximately
3.51/5.94 GiB: 86.4% fewer seed bytes. This is a byte-volume calculation, not a
measured speedup. Packing does not reduce the execution record itself or the
full-width LDE. An A/B must preserve the trace-piece plan to distinguish faster
transport from repartitioning.

The non-root join sends 68.20 GiB H→D altogether. BLAKE3 generation takes 3.80 s
including its uploads, whereas its CUDA generator kernels occupy only 0.42 s.
The copy path deserves attention before optimizing this generator's arithmetic.
The first experiment should compare packed seeds and bounded pinned staging
against the current pageable seed copies, with the same trace-piece boundaries.
Then consider retaining compact device seeds for the round-two lookup pass,
subject to measured live device memory. Avoid retaining the expanded raw trace
just to save the seed upload without first measuring that memory tradeoff.

Relevant code:

- [Seed layout and writer](../../crates/aiur/src/gpu_trace/mod.rs).
- [Pageable seed upload and per-tile synchronization](../../crates/aiur/cuda/blake3_trace.cu).
- `multi-stark/src/cuda/witness.rs`: releases raw device traces after commitment.
- `multi-stark/cuda/kernels.cu`: `staged_upload` leases one 64 MiB pinned buffer,
  copies a chunk into it, uploads it, synchronizes, and repeats. Its four slots
  permit concurrent callers; one caller does not pipeline its own chunks.
- The same CUDA file's lookup graph path invokes the retained trace writer again.

### Witness overlap and synchronization

Join 33 spends 8.07 s in witness preparation, but only 1.84 s intersects time
outside the four consumer stages. The existing `consume_ahead` pipeline already
hides much of this work. Accelerating all 8.07 s would not subtract 8.07 s from
wall time.

`cudaStreamSynchronize` occupies 10.78 s of host time in join 33, but only 0.66 s
of that has no kernel running. Kernel launch API calls occupy 0.27 s, with only
0.033 s intersecting kernel-idle time. These observations do not support making
CUDA graphs the first implementation target.

The largest actual kernel family is the FFT: radix-8 and radix-2 stages account
for about 7.05 s in join 33. Quotient evaluation is already nearly continuously
GPU-active (2.66 of 2.70 s). Those are separate kernel-tuning opportunities.

### Representative claim 9

Claim 9 was selected because its 29.19 GiB execution record is close to the
78-shard run's mean. It reproduced the original 31,343,346,409-byte record,
14 trace pieces, and cached proof address. This run used physical GPU 3 after
unrelated GPU 0 jobs interrupted earlier attempts.

| Measurement | Claim 9 |
|---|---:|
| VM execution | 144.39 s |
| Prove planned batch | 66.15 s |
| Kernel busy time | 37.13 s (56.1%) |
| Transfers with no kernel running | 4.74 s |
| Stage-one commitment, both rounds | 31.47 s |
| Stage-one commitment with no kernel running | 13.83 s |
| Lookup construction and commitment | 9.88 s |
| Quotient | 8.74 s |
| FRI/opening | 8.13 s |
| Witness preparation, union of intervals | 39.05 s |
| Outside the four consumer stages while preparing witnesses | 7.68 s |
| H→D bytes | 175.60 GiB |
| BLAKE3 seed H→D bytes / transfer time | 18.12 GiB / 1.93 s |
| Tracked live device allocation peak | 63.63 GiB |
| Sampled device memory peak | 65.11 GiB |

CPU trace construction accounts for 38.75 s of the witness interval; zero-fill
allocation spans cover 17.93 s of that time. These are unions of wall intervals,
not CPU-seconds and not additive savings. The slowest CPU function circuits by
union time are 12, 106, 107, 42, and 119 in the frozen IxVM layout. Their
individual timings are in `claim9-gpu3/analysis.json`.

The claim makes the case for broader trace generation/transport work stronger
than the join-only measurements do. Most of its upload volume is outside the
BLAKE3 generator. Existing witness overlap hides much of the construction time,
but there is still 7.68 s outside the consumer stages and substantial host time
inside commitment.

FRI/opening also has 5.21 s without a kernel running. This trace does not separate
proof-of-work grinding from the other host work in that span. The configured
query proof of work is 20 bits; attributing the gap to it requires a finer span
or a CPU sample, not just the presence of `grind` in the source.

### Tail and concurrency

Root execution/advice takes 70.87 s before its 49.97 s proof. Root wrapping is
additional work; the root replay in this table does not perform those wraps.
Two provers per GPU cannot overlap the final dependent root with another ready
job. Cheaper recursive proofs could improve both execution and proving in the
tail.

The sampled ~64.5 GiB join device peaks include cached allocations. The claim's
CUPTI allocation timeline resolves that uncertainty: its tracked live peak is
63.63 GiB, with no unmatched frees and 0.875 GiB of persistent allocations left
at exit. Two such peaks require 127.26 GiB, beyond this device's capacity.
Two provers therefore need memory admission or smaller trace pieces; simply
starting two unrestricted workers is not justified. The peaks need not coincide
under a coordinated scheduler, so this is a capacity constraint, not proof that
overlap cannot help. Allocation-event lifetime is also distinct from SM occupancy.

## Method and validation

Sources were reconstructed from `target/shared-execution-build`: pinned ix and
multi-stark commits, the saved working-tree patches, and saved untracked Rust
sources. Only the instrumentation patch and the span collector were added. The
Rust FFI was rebuilt with four jobs and relinked against the existing compiled
Lean objects. Networking is disabled in this profiling executable. See
[build metadata](build.json) and [instrumentation patch](instrumentation.patch).

Each run uses one GPU and 24 CPU cores, the 78-shard manifest, 1.5 billion
committed cells per trace piece, BLAKE3 GPU traces, trace-only lookups, and a
230 GiB planning budget. These are isolated diagnostics, not replacements for
the four-GPU throughput measurements.

Both join replays verified natively and reproduced the original cached proof
addresses exactly:

- Join 33: `12beead9b79adc380e89315c871294470a76d7e9d574cce5e76b791e887697e2`.
- Root join: `84c8094f0bd029241c2b0b151642b130d6cbd21cec033424068371ce85bfe1b2`.

Claim 9 independently passed `ix verify` and matched its original index entry:
`0e5ad48b46e2d822b12859ab2a7545daf88b3d00f837959318245cfdc4f11b8b`.
See [verification output](claim9-gpu3/verify.out).

They used `--no-write`; the proof store and aggregate cache were not changed.
CUPTI reported 240,541 records for join 33, 399,561 for the root, and 680,484 for
the claim, all with zero dropped or invalid records. The collector smoke
test verifies a one-integer kernel and both transfer directions. Analyzer tests
cover overlapping intervals, shared spans entered on multiple threads, nested
re-entry, and reused allocation addresses.

The same join replay without CUPTI took 27.287 s to prove versus 27.862 s with
CUPTI, a 0.575 s / 2.1% difference. Both used the timestamped span collector.
This single pair includes run-to-run variance and does not isolate the span
collector's overhead. Allocation activity was added for the claim; its overhead
was not separately controlled. The claim also uses the existing `--texray` subscriber.
Treat the profiles as phase diagnostics, not precise throughput predictions.

Two claim attempts (`claim9/` and `claim9-clean/`) were stopped during CPU
execution when independent GPU jobs appeared. Their metadata marks them invalid;
do not use their GPU samples. Neither completed join overlapped those jobs.
The runner now refuses an occupied GPU and stops if a foreign CUDA process
appears during a run.

## Instrumentation

`AIUR_PROFILE=/new/path.jsonl` enables timestamped span events for aggregate
replays and the shared lane scheduler. For the single-claim CLI, also pass
`--texray`. The optional subscriber uses existing dependencies and is disabled
by default. Events include span IDs, parents, fields, Linux thread IDs, and
timestamps in nanoseconds on the same `CLOCK_REALTIME` clock used by CUPTI.
The analyzer handles simultaneous entries of a shared span on different threads.

`AIUR_AGGREGATE_CACHE_DIR` selects an existing aggregate cache for read-only
replays. Without it the normal `~/.ix/cache/aggregate` location is used.

The CUDA 13.3 injection library records concurrent kernels, copies, memsets,
runtime/driver APIs, and allocation lifetimes. It does not serialize kernels for
profiling. The source and smoke test are local; Nsight Systems is not installed.

```bash
python3 bench/prover-profile-2026-09-15/build.py
g++ -std=c++17 -shared -fPIC -O2 -Wall -Wextra -Werror \
  -I/usr/local/cuda-13.3/include \
  -I/usr/local/cuda-13.3/extras/CUPTI/include \
  bench/prover-profile-2026-09-15/cupti_trace.cpp \
  -L/usr/local/cuda-13.3/extras/CUPTI/lib64 \
  -Wl,-rpath,/usr/local/cuda-13.3/extras/CUPTI/lib64 -lcupti \
  -o target/prover-profile-build/libcupti_trace.so
python3 bench/prover-profile-2026-09-15/run.py join 33 --label new-join33
python3 bench/prover-profile-2026-09-15/analyze.py \
  bench/prover-profile-2026-09-15/new-join33
python3 -m unittest discover -s bench/prover-profile-2026-09-15 -p test_analyze.py
```

`run.py` also accepts `claim N`, `--device`, `--cpus`, `--timeout`, and
`--no-cupti`. Claim proving persists its content-addressed proof but disables
shard-index writes. Each run has its own command/environment metadata, logs,
device samples, span events, and CUDA activity records. `analysis.json` contains
the measurements; `timeline.json` is a Chrome/Perfetto trace with CPU spans,
CUDA API calls, GPU work, and live device allocation counters. Large raw traces
and generated timelines are ignored by Git.
