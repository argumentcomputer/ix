# aiurExec: aggregating chained Aiur executions (prototype)

`AiurExec::aiur_exec` (`MultiStark/MultiStark/Modules/AiurExec.lean`) is an
aggregator of its own: it verifies batch proofs of one program entry under a
key supplied as data and bound by BLAKE3 in an 80-byte identity blob, and folds
them into a 104-byte claim `count ‖ H(first model) ‖ H(last model) ‖ data root`.
Shapes: a leaf over one program proof, a join of two aggregates whose chains
meet, a wrap of one aggregate. `ix_aggr`, the recursive verifier, the
compression wrapper and their keys are unchanged. Adopting it into Ix's claim
and protocol is not done here.

## Tools

| Example | What it does |
|---|---|
| `batch_root` | A single-shard batch proof of an execution package (a program proof directory). |
| `aiur_exec identity` | The aggregator's key, entry index and identity blob for a program. |
| `aiur_exec leaf/join/wrap` | One node, proven as one normalized shard (`prove_normalized`). |
| `aiur_exec root` | Lays a node out as an L3 ladder root directory. |
| `aiur_exec_tree` | A whole tree, proven the way `ix prove --aggregate` proves an environment (below). |
| `aiur_exec_check` | Checks a root's claim against a verifier-supplied specification: recompiles both keys, rebuilds the chain's endpoints and data root. |

All are built with `--features stark-verifier/parallel,stark-verifier/cuda`.
A build without `cuda` proves on the CPU; one `Fixed::step` join then takes
48 s and 97 GB, against 17 s and 14 GB for the same normalized proof on the
device.

## Proving a tree: `aiur_exec_tree`

The driver follows `aiur-gpu-proving.md` §3 and `prover-resource-defaults.md`
§4–5 with the same parts the aggregate controller uses:

- one resident `Backend::for_batch_on_device` prover per visible GPU, with a
  `ShardFeed` that builds the next trace shard's witness while it proves;
- executions on host threads, each under a `RecordReservation` from one
  `record_pool::RecordPool` (`execute_reserved`), followed by `plan_record`
  and `prepare_host` on the executor, so the lane receives a prepared record;
- the host budget `--max-ram`, else `MemTotal` less 20%, less the lane
  workspace for `AIUR_TRACE_SHARD_MAX_CELLS`-cell shards and the resident
  bytes; up to three executions per GPU whenever a share is free, more only
  while their predicted records fit; a join is charged the larger of its
  inputs' measured records, else the largest record so far, else 44 GiB;
- a join dispatched as soon as both children are proven; each proof planned
  as trace shards within the lane workspace and proven streamed
  (`prove_prepared`), then verified;
- finished node directories verified and reused; `--deadline` stops starting
  work so a run can be sliced.

The streamed proofs are trace-sharded (2–3 shards, 7–8.3 MB), so the tree's
top does not fit the pinned L3 wrap layout (`m16384w64-v3`) directly. Two
`aiur_exec wrap` nodes, proven as single normalized shards, bring it to the
shape the layout was admitted for (`G_cold0` at 0.96 of its 2^18 rows), as
`--wrap-root` does for `ix aggregate`.

## Measurements (2026-11-19, one RTX PRO 6000 96 GB, 32 threads, 249 GB)

Leaves (600, over the `Fixed::step` batch roots) had been proven earlier on
the CPU, one at a time (5,937 s); the joins were proven by `aiur_exec_tree`
under a cgroup cap (`systemd-run --user --scope -p MemoryMax=…`), with
`AIUR_GPU_TRACE=generated` (63 of 69 function circuits populated on the
device) and default cells.

| Run | Joins | Wall | Peak RSS | Per join | GPU |
|---|---|---|---|---|---|
| CPU, `aiur_exec join` (one) | 1 | 48 s | 97 GB | 12 s execution, 36 s proof | 0% |
| Subtree, 8 leaves, `--max-ram 200` | 7 | 67.1 s | 15.9 GB | 11–17 s execution, 3.0–4.5 s proof | busy 38% of samples |
| Full tree, `--max-ram 170` | 597 | 38:43 | 145 GB | 14.7 s execution, 3.6 s proof (mean) | busy 92%, mean 80% |

On the full tree execution keeps the device saturated: the device proved for
2,151 of the 2,322 s, records were 3.8–5.5 GiB, at most 30 executions ran at
once and the pool never waited, froze or cancelled. The peak RSS is records
held for the device under admission, so a smaller `--max-ram` lowers it
without slowing the run. The two wraps took 14 s and 9 s, the L3 ladder 202 s
(133 GB peak) to a 584-byte PLONK certificate with every ladder check
passing, and `aiur_exec_check` accepted the root against the full config's
inputs and expected weights.
