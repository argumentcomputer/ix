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

## Fewer, larger leaves: `Fixed::train_block`

A step tree is about 1,200 recursive proofs, so at 3–4 s of device time each
it cannot finish much under an hour. `Fixed::train_block` runs 20 steps in one
execution (`model ‖ lr ‖ 20 batches' inputs ‖ their targets`, 7,601 data
words), so the run is 30 executions and the tree 59 nodes. `AiurExecBlock`
(`aiurexec-export export PATH --block`) is the `AiurExec` module with that
claim shape; `aiur_exec_tree --prefix block` proves the tree over
`block-NNN` batch roots, and `aiur_exec_check … 30 20` checks its root.

The module keeps its word counts as constants. A variant that reads the data
length from the claim compiled to a different layout, and its double-wrapped
root needed 262,280 `G_cold0` rows in the pinned wrap layout (cap 262,144);
the constant-count instance needs 259,374. The margin is thin, so a root the
layout does not admit can be wrapped once more: a further wrap is a new proof
of the same claim.

Measured 2026-11-19 (one RTX PRO 6000, `AIUR_GPU_TRACE=generated`, default
cells, `--max-ram 170` under a 180G cgroup cap), from the 30 exported
packages to the certificate in one gated run:

| Stage | Wall | Notes |
|---|---|---|
| 30 block proofs (`batch_root`, one normalized shard each) | 23 s | 0.23 s proving each, 21.5 MB proofs |
| Tree, 30 leaves and 29 joins interleaved | 258 s | leaf: 4.8 GiB record, 2 shards, 2.7 s proof; join: 4.9 GiB, 2–3 shards, 4.0 s; 196 s of device proving, GPU busy 76% of samples; 122 GB peak RSS |
| Two normalized wraps | 29 s | `G_cold0` 0.99 of the wrap layout |
| L3 ladder to PLONK | 199 s | 143 GB peak; every ladder check passes |
| Total | 509 s | plus `aiur_exec_check`, 0.5 s |

Alone, a leaf over one block proof executes in 11 s with a 4.8 GiB record,
the size of a step-tree join; with 24 executions at once it took 19 s.
Exporting the 30 packages (one compilation of the block circuit, 127 s) took
136 s and the aggregator's package 87 s; both are made once per circuit.
