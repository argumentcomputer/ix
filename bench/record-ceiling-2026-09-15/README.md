# Record ceiling and automatic environment-shard refinement

The shared scheduler limits each query record to **128 GiB of counted
retained bytes**, independently of the process-wide memory pool. Records
can still wait for shared capacity and grow below that ceiling. Override
the ceiling with `AIUR_RECORD_MAX_BYTES` (a positive integer in bytes).

An oversized environment claim stops new admissions. Already admitted
work drains and persists its proofs, then the offending leaf is bisected
using the existing dependency min-cut. Unaffected leaves retain their
identities and cached proofs. Refinement repeats if a child is still too
large. Atomic blocks remain indivisible; an oversized atomic block, join
or root wrap reports an error.

The refined manifest is saved atomically beneath
`$AIUR_LANES_CACHE_DIR/refined-manifests/`, keyed by the original manifest's
content hash. Restarting the original command resumes that partition.
`--out-ixes` writes the final partition after successful verification.

128 GiB is a provisional size policy (raised from 64 GiB after the FLT
probe measured single-constant records of 89.5 and 71.4 GiB), not a measured cache-performance
threshold. The accounting includes field payload and fixed entry overhead;
it does not measure RSS. The completed 78-shard Mathlib run's maximum
claim record was 44.9 GiB, below the default ceiling.

## Focused checks

- Eight record-pool tests pass, including clamped admission/growth credit,
  immediate ceiling rejection when the pool is full, and growth waiting
  below the individual ceiling.
- Five scheduler-support tests pass: queue closure, host-budget limits
  and atomic checkpoint replacement/failure cleanup.
- All 36 kernel shard tests pass, including exact coverage, stable
  unaffected leaves, repeated bisection and splitting multiple leaves.

## End-to-end validation

**Passed:** one forced split, a verified final proof and checkpoint resume.

| Measurement | Result |
| --- | ---: |
| Initial / final claims | 4 / 5 |
| Claim split | 0 into 0 and 4 |
| Completed claims reused after the split | 3 |
| Child record sizes | 13.3 / 10.7 GiB |
| Claims reused on restart | 5 of 5 |
| Prove-command wall time | 477.74 s |
| Peak RSS | 128.93 GiB |
| Maximum sampled VRAM/device | 65.73 GiB |
| Peak record grants | 88.0 GiB |
| Growth waits / contention retries / LDE spills | 0 / 0 / 0 |

Claim 0's next insertion requested 23,622,320,288 counted bytes, 160 bytes
above the 22 GiB test ceiling. The scheduler drained the other three
claims, refined the partition and resumed at +183 seconds. Both new child
records fit, so only one refinement was needed. The final root was
`f135eaf140f08a8b1189779344ac83df0c5bbcd5183d5fceff2057658b49ec50`.
Independent verification certified all **56,621** environment constants,
each covered exactly once, with no undischarged assumptions.

Restarting the original four-shard command loaded the five-shard
checkpoint and reused every claim. The root join was also cached. Its
first wrap then requested 53 bytes and failed under the one-byte ceiling,
confirming that wraps bind the record reservation on the proving thread.
The input manifest was unchanged and `--out-ixes` matched the checkpoint.

See the [result](results/init/result.json),
[independent verification](results/init/verify.log),
[restart log](results/init/resume.log), and
[build metadata](results/build/build.json). The measured binary's SHA-256 is
`fcee7ae4b3ee661c56f5189c200d388f0dcff1e91c180164e8927eec2bcbc67d`.
Timing includes discarded execution and the extra claim/join caused by
the deliberately low ceiling. The 128 GiB default remains unbenchmarked as
a performance threshold.

The root-wrap log's legacy `query-record peak` label reports an estimated
prover peak, which includes workspace. It is distinct from the counted
record bytes governed by this ceiling; the restart probe exercises the
wrap's actual record charge directly.

## Reproduce

The runner uses the existing four-shard Init fixture and a temporary
**22 GiB** ceiling to force refinement. It checks the final proof with
`ix verify`, proof reuse across passes, checkpoint contents and unchanged
input. A subsequent one-byte-ceiling probe checks that restarting loads
the refined partition and every cached claim before rejecting the first
root wrap. This probe avoids another complete proof run.

The build uses the release profile, all available cores, CUDA `sm_120`
and the local multi-stark checkout. Cargo configuration and the lockfile
are restored after the temporary backend path override; unrelated
dependency-version changes are rejected. The runner disables profiling
output and records its binary/input hashes and environment.

```sh
python3 bench/record-ceiling-2026-09-15/build.py
systemd-run --user --scope -q -p MemoryMax=920G -p MemorySwapMax=0 -- \
  python3 bench/record-ceiling-2026-09-15/validate.py \
    --binary target/record-ceiling-build/ix-record-ceiling \
    --input target/tree-cache-bench/fixture/init.ixe \
    --manifest target/shared-execution-init/four/init.ixes \
    --output target/record-ceiling-init
```

The output directory must be new. Add `--verify-existing` to check a
completed run's metadata and rerun only verification and the restart
probe. Raw logs, GPU samples and the proof cache remain there. See the
[runtime design](../../docs/aiur-multi-gpu-design.md#36-shared-execution-and-memory-budget)
for the memory-pool invariants and refinement behavior.
