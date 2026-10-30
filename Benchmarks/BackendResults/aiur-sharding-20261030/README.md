# Aiur sharding calibration evidence

Retained evidence for the [automatic proving plan](../../../docs/aiur-proving-heuristic-plan.md),
targeting `kzg-bn254` (reviewed at `2f956090`). These are existing measurements,
not results from an implemented candidate heuristic.

Current implementation terminology is `multi_gpu` and the integrated
checking-to-PLONK pipeline. Historical logs use `lanes` and show the flags
used for those runs; their manual resource settings are calibration inputs,
not the intended automatic user interface.

## Measurements

| Evidence | Scope and result | Relevance |
| --- | --- | --- |
| [Init partition](init-partition.log) | October 29: 55,575 blocks, about 66.71 MB of serialized block bytes; automatic seed selected 3 shards with a 49.9 GiB record share. | Explains the historical three-shard count without requiring that count in the new heuristic. |
| [Init root](init-root.log) | October 29: 3 claims and 2 joins, 200 GiB host budget, 1.5 billion trace cells; verified aggregate root at the prover's 398 s mark. | Successful checking/aggregation configuration. This timer excludes later normalization and compression. |
| [Init attempt](init-attempt.json), [raw log](init-attempt.log) | October 30: failed after 1,027.47 s during root wrapping, at a 128 GiB per-record limit. The preceding root had 476 trace shards. No cgroup OOM or final PLONK proof. | Regression case for trace fragmentation, recursive grouping and progress. |
| [Mathlib partition](mathlib-partition.log) | October 29: 672,973 blocks, about 1.1416 billion serialized block bytes; automatic seed selected 80 shards with a 31.4 GiB share. | Current corpus representation and seed reference. |
| [Mathlib root](mathlib-root.log) | October 29: 80 claims, 180 GiB host budget, 1 GPU; verified root at the prover's 6,403 s mark. Claim records average 25.14 GiB, maximum 37.45 GiB. | Distribution of retained records, workspace reservations, execution/proving overlap, and root contraction. No PLONK time is included. |
| [Nat and Array stages](small-workloads.json) | Fresh complete PLONK runs: 271.10 s and 298.71 s. Checking/aggregation take 11.45 s and 22.61 s, respectively. | Separate stage and E2E regression gates; both use one environment shard. |
| [FLT leaves](flt-leaves.csv) | September 18: 572 leaves covering 1,321,973 checked constants and 1,310,054 blocks. Mean retained record 32.05 GiB, maximum 174.24 GiB. | Outliers and candidate profile features, including `nat_arith`. This dataset combines the original run and its resumed heavy leaf. |

The Mathlib and FLT shard counts are calibration observations, not hard-coded
outputs. The historical workloads, prover revisions, trace modes and resource
settings differ; these files do not establish a controlled performance
comparison between corpora or dates.

## Units and timing boundaries

JSON `*_seconds` and CSV `execution_s`/`proof_s` are seconds. Byte fields are
bytes; GiB in this note means bytes divided by 2³⁰. FLT CSV `bytes` is
serialized owned block size, `record_bytes` is the retained execution record,
and operation-count columns are counts from the native checker profile.
CSV `trace_shards` counts internal trace proofs, not environment leaves.

Execution and proving overlap across workers. Do not sum their durations to
obtain E2E time. Successful root logs end at aggregation, whereas
`small-workloads.json` measures the complete fresh process through final
PLONK output. Its stage intervals come from progress events polled at 10 ms.
The first timing gate covers checking plus aggregation; the second covers
complete E2E proving. Doubling the former would increase Nat E2E by only
4.2% and Array E2E by 7.6%, so an E2E-only 10% gate misses that regression.

The completed Nat/Array proofs and failed Init attempt used the same frozen
Ix executable from `9e46f7e4` plus recorded uncommitted changes. Their artifact
hashes and source revision are retained in the JSON. Their 230 GiB cgroup cap
is a runtime limit, not the proposed input to initial partitioning.

## Sources

The partition logs are unchanged copies of `target/fixed-root-20261029/shard.log`
and `mathlib-shard.log` in the `ix-stack` worktree. Root logs are unchanged
copies of `Benchmarks/BackendResults/ix-20261029/evidence/{init,mathlib}-checking-aggregation.log`
in `ix-backend-comparison`. The failed Init summary and log are unchanged
copies from `target/backend-bench/ix-init-20261030/{summary.json,fresh-001/prove.log}`.
Absolute paths inside these records identify original artifacts; the data
needed for the observations above is retained here.

`small-workloads.json` selects timing, workload identity, executable identity,
and outcome fields from the two original Nat/Array summaries. It records their
paths and SHA-256 hashes. Large source archives, keys, proofs and complete
working-tree inventories remain with the original runs.

`flt-leaves.csv` preserves the data from
`bench/flt-lanes4-2026-09-18/data/leaves.csv` at
`13feef0f33ea78f73b35073f875ed4d1c9ca424d` (Git blob
`366196f338ad424a256ebcec7b52d5a41778182d`), with CRLF line endings normalized
to LF. The historical notes provide additional context:

- [Mathlib seed calibration](https://github.com/argumentcomputer/ix/blob/13feef0f33ea78f73b35073f875ed4d1c9ca424d/bench/mathlib-seed-2026-09-15/README.md): 111 versus 78 shards under the shared scheduler.
- [Mathlib concurrency comparisons](https://github.com/argumentcomputer/ix/blob/13feef0f33ea78f73b35073f875ed4d1c9ca424d/bench/mathlib-lanes4-metrics-2026-09-17/README.md): 78 shards at four executions/GPU took 36min00s; 102 shards at five executions/GPU took 36min20s with a higher RAM budget. The changes are confounded.
- [FLT records and residency](https://github.com/argumentcomputer/ix/blob/13feef0f33ea78f73b35073f875ed4d1c9ca424d/bench/flt-lanes4-2026-09-18/README.md): about 65 GiB of environment residency outside the record pool, repeated refinement of the heavy leaf, and a restart with a 256 GiB record ceiling. The approximately five-hour representative time is reconstructed, not a clean uninterrupted run.
