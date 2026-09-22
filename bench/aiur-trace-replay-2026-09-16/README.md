# Production trace-provider comparison

One paired replay of FLT aggregate slot 19 passed with handwritten and
compiler-generated BLAKE3 providers. **Proving time is comparable in this
sample: 23.49 s versus 23.55 s (generated +0.22%).** Both runs reproduced
the same verified proof and six-piece trace plan. This validates production
BLAKE3 replacement performance; other circuits still generate traces on
the CPU.

## Results

| Metric | Handwritten | Generated |
| --- | ---: | ---: |
| Proving, both rounds | 23.494 s | 23.545 s |
| Execution and planning | 24.491 s | 24.143 s |
| Replay, including execution and verification | 48.436 s | 48.169 s |
| Full process, including FLT input loading | 84.80 s | 84.75 s |
| BLAKE3 seed preparation | 2.332 s | 2.779 s |
| BLAKE3 synchronous device callbacks | 1.126 s | 1.204 s |
| Other CPU witness work | 8.439 s | 8.443 s |
| Peak process RSS | 32.78 GiB | 33.29 GiB |
| Sampled peak GPU memory | 64.50 GiB | 64.49 GiB |

Generated seed preparation took 19.2% longer (+0.447 s), and device callbacks
took 6.9% longer (+0.078 s). These are union durations of host profile spans;
parallel phases overlap and their deltas must not be added to predict proof
wall time. Device callbacks include staging, upload and synchronization, not
just kernel execution. This pair does not establish a speedup, a statistically
significant regression, or GPU utilization improvement. It also does not
override the earlier isolated 65,536-row microbenchmark: this workload packs
million-row pieces from a much larger live record.

Both modes prepared 2,079,176,704 bytes of 176-byte seeds across 12 preparations
and made 288 device callbacks. The record model counted 11,275,541,816 bytes
(10.50 GiB). Stage-one data was regenerated for round two; tree caching was
disabled. Peak GPU memory was sampled every 200 ms and can miss short peaks.

The proof wrapper digest matches the original cached FLT join:

```text
418bb309dd431b581f19a1f77725acc75d4479348eb7a5d1fac4c89e72e6069f
```

[compare.py](compare.py) verifies successful exits, proof equality, binary and
input hashes, settings, CPU affinity, exact trace-piece ranges and widths,
record size, seed shapes/bytes and actual provider dispatch before emitting
[comparison.json](comparison.json). Raw logs, spans, metadata and GPU samples
are in [handwritten](flt19-handwritten-structural/meta.json) and
[generated](flt19-generated-structural/meta.json). Each mode ran once,
handwritten first, sequentially on GPU 3 with CPU affinity 0–7 and eight
Rayon/Lean threads. No other GPU compute process was observed during the
pair; [host.json](host.json) records the RTX PRO 6000 Blackwell Server Edition,
driver, clocks and process snapshot. These measurements use lightweight host
spans, without CUPTI injection.

## Build

The [small frontend](Replay.lean) calls the existing production
`aggregateCmd`. Both cases use the same release Rust library built with
`parallel,cuda-trace-codegen` and the paired backend worktree.

Before native linking, 390 hashes were checked across 130 imported modules:
current Lean source, generated C and native object. The only source change
was `Ix.Aiur.Stages.Bytecode`, which was rebuilt using its Lake setup
metadata to preserve package-qualified symbols. The frontend was also
compiled afresh. Unchanged imported objects match their Lake traces.

[Build metadata](build.json), [Rust build log](replay-ffi-build.log),
[native inputs](replay-native-inputs.json), [hash checks](replay-native-hashes.tsv)
and [native build commands](replay-native-build.json) preserve provenance.
The eight-core build took 2m35s for the Rust library.

## Run

Use an exclusively available GPU. Run [run.py](run.py) once with each mode,
keeping the binary, environment, manifest, cache, slot and device identical:

```sh
python3 run.py --binary /path/to/ix-aggregate-trace-replay \
  --mode blake3 --ixe /path/to/environment.ixe --ixes /path/to/environment.ixes \
  --cache /path/to/aggregate-cache --slot 19 --structural-above 0 \
  --device 3 --output handwritten
python3 run.py --binary /path/to/ix-aggregate-trace-replay \
  --mode generated --ixe /path/to/environment.ixe --ixes /path/to/environment.ixes \
  --cache /path/to/aggregate-cache --slot 19 --structural-above 0 \
  --device 3 --output generated
python3 compare.py handwritten generated
```

Each run is limited to CPU cores 0–7 and eight Rayon/Lean threads, and uses
`--no-write`. It records the binary/input hashes, settings, span timeline,
GPU samples, peak RSS, stdout/stderr and exit status. Output directories
must be new. Proof and trace-plan equality are required before comparing
performance.

The measured inputs are `~/benchdata/flt/anthropic-flt.ixe` and
`~/benchdata/flt/anthropic-flt-900.ixes`, with aggregate children from
`~/benchdata/flt/flt900-gpu/cache/aggregate`. The cache run used ix
`8a6864ba4acfd6e56fa7d9ff7bc0d8b1bc5623e8` and multi-stark
`b6629c29a5435ded52f1453aeb3b86ac9ad121d8`. The replay executable uses the
earlier bases recorded below in build metadata; both cached children verify
under it, and the target proof digest is identical to the cached original.
Only the provider selector changes between the measured runs. Both use the
same backend, including its performance characteristics.

Input hashing occurs before the timed process and reads the full 30 GB FLT
environment in both runs. The replay verifies cached child slots 15 and 18,
executes and proves slot 19, verifies it and computes its wrapper digest.
`--no-write` leaves the proof store and cache unchanged. Input loading and
statement preparation are outside the reported `aiur/prove_planned` time.

The join policy must also match the cache. The FLT lanes run used all
structural joins (`--structural-above 0`), while the aggregate command defaults
to 4096. The initial FLT cache check with that default missed child slot 15;
the corrected policy loaded and verified both children. An earlier pre-merge
Mathlib cache check missed child slot 25. Neither check reached proving;
their logs are retained in `flt19-handwritten` and `mathlib-cache-check` and
excluded from the results. A previous launch while FLT occupied the GPUs
was refused before benchmarking.
