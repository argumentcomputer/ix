# Queue22 evidence snapshot

Copied on 2026-09-11 for
[the pre-Mathlib handoff](../../../docs/aiur-gpu-mathlib-handoff.md).
The original run directory is `/home/ubuntu/benchdata/trace-shards-gpu/`.

- `queue22.log` contains the Stage 1 and Stage 2 verification verdicts.
- `init-gpu-gpu2-dist8.log` and `init-gpu-gpu2-stage2-range0.log` contain the
  commands, tracing output, proof addresses, resource reports, and exits.
- Their `-util.log` companions contain sampled device utilization/VRAM and
  process RSS. The sampler starts after process launch; these are sampled
  maxima and device-wide metrics.
- `queue22.sh` and `runlib.sh` preserve the historical invocation and external
  limits. They contain machine-specific paths and are provenance, not the
  portable runbook; use the handoff's commands for a new run.
- `build-gpu2.log` records build success but not source revisions.
- `queue23.log` is the completed lower-budget follow-up summary. Its full
  original log is fingerprinted in `snapshot.json`.
- `post-queue23-retention-trim.patch` captures the later uncommitted trim
  change under queue24 validation. It is not part of queue22.
- `snapshot.json` records reviewed source heads, artifact and log hashes,
  exact timings, sampled metrics, and the comparison runs' source paths.

Large environment files, binaries, and proof objects are not copied here.
Their sizes and identifiers are recorded so they can be matched to the
original artifacts. No jobs were rerun to create this snapshot.
