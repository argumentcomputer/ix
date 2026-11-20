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
| `program_root` | The same directory, proven on the device as planned trace shards, streamed; registers the word libraries' hint channels, so a program that hashes with BLAKE3 can be proven. |
| `aiur_exec identity` | The aggregator's key, entry index and identity blob for a program. |
| `aiur_exec leaf/join/wrap` | One node, proven as one normalized shard (`prove_normalized`). |
| `aiur_exec root` | Lays a node out as an L3 ladder root directory. |
| `aiur_exec_tree` | A whole tree, proven the way `ix prove --aggregate` proves an environment (below). |
| `aiur_exec_check` | Checks a root's claim against a verifier-supplied specification: recompiles both keys, rebuilds the chain's endpoints and data root (`--tree MODELS`: the Merkle root of one `train_tree` execution). |

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

## The whole run in one execution: `FixedTree::train_tree`

`Fixed::train` runs all 600 steps in one execution but takes the 600 batches
as arguments, so its entry row is 238,264 columns wide: too wide for the
verifying key's u16 widths and for the wrap. `FixedTree::train_tree`
(`Aiur/IxAITree.lean` in the ix-ai-pipeline worktree) keeps one execution and
narrows the claim instead. Its arguments are the initial model and `lr`; its
outputs are a 32-byte root and the trained model, a 697-word claim
`[1, entry, m₀, lr, root, m₆₀₀]`. Step `i` reads batch `i` from two hint
channels as range-checked bytes (two per word, `v + 32768` little-endian),
runs `Fixed::step` unchanged and hashes leaf `i = BLAKE3(enc(mᵢ₊₁) ‖ enc(batchᵢ))`.
`range` recurses over the steps as a balanced tree (`⌊n/2⌋ | ⌈n/2⌉`), so it
folds `step` left to right and returns the BLAKE3 Merkle root over the leaves.
The root binds every batch, every intermediate model and their order, so any
step can be opened later with its leaf and a Merkle path, and the data
commitment is BLAKE3 like the rest of the chain. `FixedTree` is a module of
its own: `Fixed` and every circuit compiled from it (the step and block keys)
are unchanged.

`AiurExecTrain` (`--train`) is the `AiurExec` module with this claim shape:
331 model words and 33 data words (`lr`, then the root's 32 bytes), so its
data root is `H(lr ‖ root)`. The step and block instances' source digests are
unchanged (`885f8d3a…`, `7baf0c5b…`).

The pipeline is one program proof, one leaf and one wrap:

1. `program_root` proves the package on the device. The trace is 4.0M rows
   and 275.6M committed cells, one trace shard under the default cell cap.
2. `aiur_exec_tree … 1 --prefix train` proves one leaf over it (streamed,
   3 trace shards).
3. The leaf does not fit the pinned wrap layout (`G_cold0` 1.55x, seven
   circuits over); one `aiur_exec wrap`, a normalized single shard, does:
   `G_cold0` 252,266 of 262,144 rows (0.96, 9,878 rows spare; the block
   route's second wrap used 0.99). A second wrap would be a new proof of the
   same claim if a layout ever needs more margin.
4. The compression pipeline turns that root into a 584-byte PLONK
   certificate, with its pinned wrap, GL, narrow and PLONK keys, as for
   IxVM.

`aiur_exec_check … 1 600 --tree MODELS` recompiles both keys, checks the
endpoints against `m₀` and the expected model, and recomputes the Merkle root
with the `blake3` crate from the specification's batches and the 600
intermediate models (`MODELS`, from `IxAICore`), so it also checks that the
circuit's BLAKE3 agrees with BLAKE3 on these inputs.

Measured 2026-11-19 (one RTX PRO 6000, `AIUR_GPU_TRACE=generated`, default
cells, 180G cgroup cap), from the exported package to the certificate:

| Stage | Wall | Notes |
|---|---|---|
| `train_tree` proof (`program_root`) | 4.6 s | 2.8 s execution, 0.83 s proving, 1 trace shard, 16.0 MB proof, 1.9 GB peak RSS |
| Leaf | 20.2 s | 15.3 s execution (5.7 GiB record), 3.9 s proving, 3 trace shards, 8.0 MB proof, 7.2 GB peak |
| Wrap and admission | 29.1 s | the wrap 13.5 s (8.4 s execution, 4.4 s proving, 5.9 MB), 12.5 GB peak; two wrap plans |
| Compression pipeline to PLONK | 196.7 s | 143 GB peak; every check passes |
| Total | 251 s | plus `aiur_exec_check`, 0.6 s; the block route took 509 s |

A repeat of the whole sequence as one gated invocation, from the package,
took 315 s: the program proof (byte-identical, `27d64cca…`), root key
(`8ee3db8d…`) and output claim (`32ec9bea…`) were the same and every stage
before the compression pipeline took the same time, but the pipeline took
259 s (its GL and narrow stages about 60 s slower each; their cause was not
investigated). Certificates: `26eb66b9…` and `9cf5e61f…` (PLONK proofs are
randomized).

Exporting the package (compiling the circuit) takes 129 s and the
aggregator's package 87 s, once per circuit. The compression pipeline is now
almost all of the time; recursion is three proofs (program, leaf, wrap)
against the block route's 59 tree nodes and two wraps.

What would let the leaf be the root: the wrap layout admits it only after a
wrap because the leaf verifies a 16 MB, 56-circuit proof (`Blake3::compress`
1.20x, `G_cold0` 1.55x and five ROM widths over). Admitting it directly needs a
larger wrap layout, which changes the wrap, GL, narrow and PLONK keys shared
with IxVM, so the extra wrap is the cheaper normalising stage.

### The Lean theorem it needs

The step and block routes end in `train_of_deployed_steps` /
`train_of_deployed_blocks`: accepted claims, chained by public IO, give
`IxAICore.train`. A `train_tree` claim carries no batches, so its theorem has
to go through the root:

```lean
theorem train_tree_sound (parity : TreeOnlyParity)  -- shipped preparation's source = treeSource
    (compiled : ModulesArtifact treeOnly) …           -- certified, plan, checkMemo, as in block_sound_deployed
    (arguments : DecodesValues … (entryValues
      [mat fullInit.w1, vec fullInit.b1, mat fullInit.w2, vec fullInit.b2, fxVal fullLr]))
    (decoded : output.decode … = some (.tuple [encDigest R, encModel m']))
    (hR : R = treeRoot blake3 fullBatches fullModels)  -- what aiur_exec_check recomputes
    (blake3 : Blake3Refines)                           -- Aiur's Blake3::hash computes BLAKE3
    (noCollision : CollisionFree blake3 leafAndNodePreimages) :
    m' = IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig
```

Plan, reusing `step_spec` / `chain_spec`:

1. Path lemmas for `FixedTree`. `ObsGen` covers the functions without
   `match` (`enc`, `dec`, the row codecs, `read_batch`, `node`, `leaf`,
   `train_tree`); `half` (14 arms) and `range` (two arms) are written by hand.
2. `range_spec`, by strong induction on `n` along `half`: an observed
   `range(m, lr, i, n)` gives `n` batches `bs` (the hinted bytes, decoded),
   a `StepChain` from `m` over `bs`, and a root equal to the tree of
   observed `Blake3::hash` results over `enc(mₖ₊₁) ++ enc(bₖ)`. No bound on
   the batches is needed here: the step derivations are only carried.
3. Codec lemmas: `dec` and `enc` relate a word to two range-checked bytes,
   injective on `[-32768, 32768)`.
4. With `blake3` and `noCollision`, equal roots give equal leaf lists, so
   the hinted batches are `fullBatches` (hence `BatchOk`) and the
   intermediate models are the spec's; `chain_spec` then gives
   `m' = foldl (Model.step fullLr) fullInit fullBatches = train …`.

Status: not proved. Steps 1–3 are the same kind of work as the existing
refinement; `Blake3Refines` is the open piece (`Library/Blake3/Correctness.lean`
proves word-level facts only, and the stream argument needs the heap-list
representation of `Library/List/Correctness.lean`). Without it, the theorem
can be stated over the circuit's hash function, with `aiur_exec_check`
evidencing that it agrees with BLAKE3 on these inputs.
