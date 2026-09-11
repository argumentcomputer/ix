# Checked reserve/reuse counter folding: paired protocol

This PERF3 experiment uses the runtime reversal source and every dataset,
timing row, full-result oracle, driver operation and timer convention from
[protocol version 1](protocol.md). The comparison is `baseline` versus
`counter-fold`, built by the same producer with identical GCC 14.3.0 driver
objects and link options. Native records identify the common `compilatrix`
driver; enclosing records bind the variant to its actual executable digest.

The selected rewrite removes only the cancelling reservation/live counter
changes in an adjacent reserve/reuse pair: twelve instructions per consumed
cons cell. It retains all cell loads/stores and cumulative reuse/payload
counter updates. Every final general-purpose register and arena word agrees
with the baseline.
The combined operation is atomic with respect to the source resource relation;
intermediate reservation accounting is not an observation boundary for the
folded body. The canonical exclusive-arena, guard, ABI and word-range contracts
are identical. The default selector still emits the original baseline.

Both variants pass the independent native artifact gate, eight runtime inputs,
203 malformed calls, complete reclamation and corruption tests. The timing
binaries also pass all 585 inputs and 19,305 capacity cases, with exact equality
of complete arena observations, malformed-dataset checks and timing smoke.
The gate's `--artifacts` option binds every benchmark artifact byte for byte
to its freshly checked counterparts. The paired build pins both reviewed goldens; the original PERF1 manifest and
reference bundle retain their original identities.

The pilot targets 200 ms, taking the larger count required by either variant
for each row and rounding to a multiple of 24,576 operations (4,096 chunks,
six primary patterns). A confirmation pass requires at least 100 ms before
freezing all counts. There are 30 paired blocks, in three groups of ten,
separated by 60 seconds. Row and variant orders use the existing deterministic
shuffle with seed 1210345809. Each variant starts a new worker process for
each block, warms for one second and records three samples for all 38 rows:
6,840 accepted samples in total. Workers and controller are pinned separately.
All builds, checks and network setup finish before the pilot.

The existing floors apply: at least 100 ms per sample, minimum chunk duration
at least 100 times the observed minimum clock-pair cost, peak worker RSS no
greater than 2 GiB, and no drift in recorded stable machine/environment fields.
At most three complete attempts are retained for an invalid block; wrong
results, artifacts, schemas or process failures stop publication. Every valid
slow observation stays. The timer control is retained without subtraction.

Analysis uses the median of three samples per variant/block and reports all
38 baseline/folded distributions and paired ratios. Ratios above one favor
folding. The same 10,000 hierarchical bootstrap index vectors resample three
sessions and ten paired blocks within each selected session, seed 2671931027.
This shared-host experiment and its three clusters cannot establish CI timing
thresholds or remove between-day uncertainty. RSS, raw context switches,
page faults, environment observations and timer controls remain in the bundle.

Generation and independent-gate wall/CPU/RSS are diagnostic envelopes, not
isolated compiler or proof-checker phases. Generation includes modeled fixture
executions; each independent gate includes two generations, artifact checking,
corruption regressions and a native harness. The report includes both envelopes,
serialized pipeline bytes and object `.text` sizes. The proof checks are run
before timing and documented separately.

Run in the pinned repository environment, using fresh directories:

```sh
lake build compiler-benchmark compiler-source-native-runtime compiler-check-source-native-runtime
.lake/build/bin/compiler-benchmark counter-fold-build BUILD
.lake/build/bin/compiler-benchmark counter-fold-verify BUILD VERIFY
.lake/build/bin/compiler-benchmark counter-fold-smoke BUILD SMOKE 2
taskset --cpu-list 0 .lake/build/bin/compiler-benchmark counter-fold-pilot BUILD VERIFY PILOT 2
taskset --cpu-list 0 .lake/build/bin/compiler-benchmark counter-fold-measure BUILD VERIFY PILOT MEASURED 2
.lake/build/bin/compiler-benchmark counter-fold-analyze BUILD MEASURED MEASURED/analysis
.lake/build/bin/compiler-benchmark counter-fold-reproduce BUILD MEASURED REPLAY
```

Select available controller/worker cores before piloting and retain them for
measurement. Replay extracts and validates the source snapshot, uses an empty
environment plus recorded variables and retained hashed producer/checker seeds,
rebuilds exact objects/executables, repeats full correctness, and regenerates
the same analysis from retained raw process records. It does not equate fresh
clock readings or claim an independent physical host. The source, tools,
objects, schedules, raw samples, diagnostic costs and replay are retained in
a digest-addressed archive under `benchmarks/runs/`.
