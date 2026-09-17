# Collecting lightweight prover metrics

Set `AIUR_METRICS` to a **new JSONL file** when running the normal `ix`
prover. The parent directory must exist. An existing file is never
overwritten; a creation/write failure prints a warning and proving continues.
`AIUR_METRICS_RUN_ID` is an optional label recorded in the metadata.

Use the usual CUDA build; ix pins the published multi-stark and sppark
revisions, so no local dependency overrides are needed. Host setup is in the
[build notes](../bench/prover-profile-init-2026-09-17/README.md#reproducing-on-this-host).
AOT seed metrics require `IX_CUDA_TRACE_CODEGEN=1`
(Cargo feature `cuda-trace-codegen`). No additional metrics feature is needed.
An old binary will ignore `AIUR_METRICS`.

## Collection

Add the two variables to your existing command, preserving its input,
concurrency, memory limits and trace settings:

```bash
metrics_dir="$(mktemp -d /tmp/aiur-metrics.XXXXXX)"
export AIUR_METRICS="$metrics_dir/metrics.jsonl"
export AIUR_METRICS_RUN_ID=mathlib-sppark
```

For lightweight collection, run `ix` directly, without `profile.sh`, Nsight
or the CUPTI injector. Unset profiling controls inherited from that workflow:

```bash
unset AIUR_PROFILE AIUR_CUDA_PROFILE CUDA_INJECTION64_PATH
unset RUST_LOG MULTI_STARK_CUDA_MEMORY_LOG
```

Also remove a profiler from `LD_PRELOAD` if one was installed there. Leave
`--texray` off. These controls are independent: setting `AIUR_METRICS` does
not turn off another profiler.

For example, a Mathlib run with four GPU lanes and four executors per lane:

```bash
AIUR_GPU_TRACE=generated AIUR_TRACE_ONLY_LOOKUPS=1 \
AIUR_MAX_PIECE_LOG_HEIGHT=24 AIUR_TRACE_SHARD_MAX_CELLS=1500000000 \
.lake/build/bin/ix prove \
  --ixe mathlib.ixe --ixes mathlib-mincut-128.ixes \
  --trace-shards --lanes 4 --exec-jobs 4 --max-ram 230 \
  > "$metrics_dir/run.out" 2> "$metrics_dir/run.err"
```

Use the manifest and resource limits chosen for the actual run. Its usual
proof-cache behavior still applies: reused proofs generate no proving-piece
summaries. Save the command, input/manifest identity, ix and multi-stark
revisions, binary identity, CPU affinity, GPU configuration and cache state
alongside the output. The metadata automatically captures selected environment
overrides, not those complete provenance details or effective defaults.

The same switch works for a single claim or a join replay. For the existing
Init fixture, with a fresh output path for each invocation:

```bash
AIUR_METRICS="$metrics_dir/claim1.jsonl" AIUR_METRICS_RUN_ID=init-claim1 \
AIUR_GPU_TRACE=generated AIUR_TRACE_ONLY_LOOKUPS=1 \
AIUR_MAX_PIECE_LOG_HEIGHT=24 AIUR_TRACE_SHARD_MAX_CELLS=1500000000 \
.lake/build/bin/ix prove \
  --ixe ~/benchdata/init-gpu/init.ixe \
  --ixes ~/benchdata/init-gpu/init-4.ixes \
  --trace-shards --max-ram 200 --shard 1 --no-index
```

For a join, prefix the existing `ix aggregate --reprove-slot ...` command
the same way. Preserve the exact child proofs between comparison runs.
For multiple OS processes, give each process a separate file. One lanes
process writes all its devices to one file. Unset `AIUR_METRICS` when done.

## Reading the output

The first line is `type: metadata`, followed by `type: summary` records at
witness, round-one piece, round-two piece, proof and lane-unit boundaries.
Each record has a process ID, unique summary `id`, `parent` and inherited
`identity`. Lane identities contain `work` (`Claim(n)`, `Join(n)`, `Root`)
and worker; piece identities contain the trace `shard` and `round`.
Separate proofs within one unit have separate parent IDs. Direct proof
invocations still have proof/piece IDs, but do not have lane work labels.

`wall_elapsed_ns` measures the boundary's lifetime. Use the
`aiur/prove_planned` or `aiur/prove_records` boundary for proof duration.
The lane-unit boundary also includes serialization, storage and root
wrapping/verification where applicable. Execution before proving remains
outside these proof timings; retain the ordinary run log for overall progress.

Each entry in `metrics` groups an operation/event by its `name` and `labels`:

| Field | Meaning |
| --- | --- |
| `count` | Number of matching operations or events in this boundary |
| `elapsed_sum_ns` | Sum of host span durations; nested or concurrent spans overlap |
| `counters` | Additive counts/bytes within this boundary |
| `last` | Latest gauge or cumulative snapshot; never sum across records |

Examples using streaming `jq` (no whole-file load):

```bash
jq -c 'select(.type == "summary" and .boundary == "aiur/prove_planned") |
  {id, parent, identity, seconds: (.wall_elapsed_ns / 1e9)}' "$AIUR_METRICS"

jq -c 'select(.type == "summary") | . as $s | .metrics[] |
  select(.name == "trace" or .name == "seed_pack") |
  {id: $s.id, identity: $s.identity, metric: .}' "$AIUR_METRICS"
```

The collected groups are:

- **AOT coverage:** `trace` records CPU/generated provider, circuit kind,
  assigned live rows, padded height, width and padded cells. Circuit/function
  indexes refer to that proof's compiled program. `fallback` distinguishes
  uncovered function circuits from preparation errors. CPU selection also
  covers disabled providers and memory generation, so it is not itself an error.
- **Packing:** per-function filter, pack, widen and concatenate host times;
  `seed_pack` records scanned/live rows, actual and canonical seed bytes,
  encoding and widened runs. No second traversal of witness rows is performed.
- **Resident seeds:** upload/failure/release events, bytes and reuse hits
  accumulated until release. `seed_cache_device_snapshot` contains current
  retained bytes and cumulative refused requests per device. Refusals count
  requests, which can recur across tiles, rather than unique circuits.
- **Coset cache and uploads:** host coset builds/hits and cached bytes;
  `cuda_device_snapshot.last` holds cumulative device coset hits/misses,
  successful constant uploads, staged upload calls/requested bytes/chunks,
  failures and host elapsed nanoseconds. Staged-upload time includes staging,
  slot waits and the operation's existing completion wait; it is not DMA time.
- **NTT:** coarse DFT/LDE operation host times with device, backend
  and dimensions, plus `ntt_snapshot.last.transforms` by log-height and width
  bucket (`1`, `2`, `3-7`, `8+`). Native counts are transform attempts, not
  butterfly-stage launches. All GPU transforms use sppark; there are no
  taken/declined counters or separate backend buckets. CPU/no-op dispatch
  is labeled in the Rust spans.
  Lookup/quotient LDE spans include their surrounding work, not just the NTT.
- **Memory/admission:** LDE spill bytes, lookup job path and admission sizes,
  process RSS at boundaries, and the last driver-free/total-device reading
  from an existing memory query. These are samples, not peaks. Admission's
  available bytes can include reusable async-pool memory excluded from
  driver-free bytes.

## Comparing runs and measurement cost

Compare identical inputs, shapes, settings and cache conditions. Count AOT
coverage within one round to avoid counting regenerated rows twice. Compare
proof wall duration separately from packing and other overlapping host sums;
do not sum parent and child boundaries to infer elapsed time.

Native snapshots are **process/device cumulative**, sampled at piece ends.
Use the latest snapshot per device for run totals (or differences across
explicitly isolated intervals). Do not attribute snapshot differences to
individual overlapping proofs. Snapshot fields are read independently and
can reflect concurrent updates. Compare cold coset builds separately from
warm hits. GPU counts now cover the sppark entry points at every height.
Historical snapshots may include separate first-party/sppark buckets and
taken/declined counts; new snapshots use one transform-shape bucket set.

The collector aggregates coarse spans/events in memory and writes only at
boundaries. It adds no CUDA events, device synchronizations, kernel activity
collection, per-row checks or per-tile log records. Native counts use relaxed
atomics, staged uploads use one host timer pair per call, and memory samples
reuse existing GPU queries. Boundary writes and host tracing still cost time;
end-to-end overhead has not been measured on Mathlib. This output cannot
establish kernel occupancy, exact GPU/NTT time, DMA overlap or AOT correctness.
An `incomplete: true` summary indicates unwinding, not a verifier verdict;
aborts/kills can leave the current boundary unwritten. Check the run's exit
status and normal verification result as well as the metrics file.
