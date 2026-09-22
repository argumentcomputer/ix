# Trace-sharding benchmark scripts, Init, 2026-09-09/10

The scripts that produced the rows in
[the results record](../../docs/trace-sharding-results-2026-09-09.md). They
are written for one box (paths under `/home/ubuntu`, a 495 GB host, systemd
user units) and are kept as the exact recipes, not as portable tooling; the
commands they wrap are listed in [the handoff](../../docs/trace-sharding-handoff.md).

| Script | What it measures |
|---|---|
| `run-dist-regen.sh` | Stage 1 of all Init as one claim, 4 min-cut chunks, records re-executed for round two, then `ix verify` |
| `run-stage2-range.sh` | Stage 2 of a batch as a range tree (`SRC`, `RANGE`, `JOBS`, `RAM` parameters), then `ix verify --aggregate` |
| `run-env400-e2e.sh` | The env-shard baseline end to end at 400 GiB: 9 shards, wrap-first aggregation, verification |
| `run-lab-plan.sh` | `ix shard --ordered` at 4/8/16 chunks and `ix prove --distributed --plan-only` over every manifest; no execution |
| `run-ordered-stage1.sh` | Exec-only, then Stage 1, over the 8 ordered chunks |
| `run-suites.sh` | The Lean test suites |

Every timed run is bounded with `timeout`, records the commit and input
hashes, and verifies its proof; builds happen before the timer starts.
