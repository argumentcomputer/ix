# Trace sharding: state of the branch and what a GPU box should calibrate

Written 2026-09-10 on the CPU box (Xeon 6975P-C, 64 cores, 495 GB, no
GPU). Everything below is on branch `sb/aiur-distributed-execution`; the
design is [aiur-trace-sharding.md](aiur-trace-sharding.md) (§13 is the
single-claim pipeline), the measurements are
[trace-sharding-results-2026-09-09.md](trace-sharding-results-2026-09-09.md),
and the outside review that led to the estimator fix is
[trace-sharding-performance-audit.md](trace-sharding-performance-audit.md).

## Vocabulary

- **Chunk**: one worker's owned partition of the environment, one shard of
  the `.ixes` manifest. A worker executes the kernel over its chunk and
  produces one execution record.
- **Trace shard** (or shard): a cut of a record's traces that fits the cell
  budget, proven as one STARK under the batch's shared challenges. A record
  yields many shards; the cap applies to shards, never to chunks.
- **Batch**: every shard of every record, one proof, one `CheckEnv` claim
  for the whole environment.
- **Range tree**: Stage 2, the recursion over the batch's shards (range
  leaves, joins, root). These leaves are real tree leaves.

## Dependencies

- multi-stark commit `9322ec062c78a51843f78ea23119ea5a65b19b16` on its
  `sb/trace-sharding` branch (the two-call batch prover: `batch_round_one`
  yields a barrier from a stream of shards, `batch_round_two` finishes from
  it). `Cargo.toml` pins that rev, so the commit must be pushed before this
  branch builds on any other box.
- On a gcc 15 host, `CFLAGS=-std=gnu17` in `~/.cargo/config.toml` (`[env]`)
  keeps the mimalloc C sources linkable against Lean's bundled glibc
  stubs. Not needed on the gcc 13/14 CI image.
- `rustfmt --check` reports about 24 pre-existing diffs on this branch's
  base from a rustfmt version mismatch; none are from this work.

## What is built

1. **Distributed execution** (`ix prove --distributed`): one worker per
   chunk, calls into another worker's constants deferred through the lookup
   argument and absorbed into the owner's multiplicities, records in disjoint
   pointer namespaces, all shards proven as one batch. Ownership is a prover
   hint; soundness is the lookup balance.
2. **Record residency**: workers commit in caller order (Tarjan over the
   static caller graph from byte scopes), execute on demand `--exec-jobs` at
   a time, drop each record once its shards' round-one commitments exist,
   re-execute for round two, and execute the next worker while the current
   one proves (`--no-prefetch` turns that off). Lock-free driver, one atomic
   counter, results through join handles.
3. **Dependency-ordered layout** (`ix shard --ordered --shards N`): chunks as
   contiguous ranges of a dependency order, primitives first, numbered from
   the top down, so the caller graph is acyclic and one record is resident
   plus the prefetched next. `ix prove --distributed --plan-only` prints the
   caller graph and groups for any manifest without executing.
4. **Range-sum recursion** (`ix aggregate --range N`): ix_aggr shapes 10
   (range leaf), 11 (range join), 12 (range root) over one batch; every node
   is itself trace-sharded to the slot.
5. **Fixes along the way**: the inliner hoisted assertion continuations
   (statement frames, `Ix/Aiur/Stages/Source.lean`, regression test
   `assert_before_inline`); the prover peak model read a grouped circuit's
   rows by circuit index (now sums the group's members).

## Reproducing on a box

```
# environment and manifests
ix compile Benchmarks/Compile/CompileInit.lean --out init-ts.ixe
ix shard init-ts.ixe --shards 1 --out init-1.ixes          # verification manifest
ix shard init-ts.ixe --shards 4 --out init-4.ixes          # min-cut chunks
ix shard init-ts.ixe --ordered --shards 8 --out init-ordered-8.ixes

# what the layout implies, no execution
ix prove --ixe init-ts.ixe --ixes init-ordered-8.ixes --distributed --plan-only --no-index

# Stage 1: all Init as one claim, shards planned to 1.8 G committed cells
ix prove --ixe init-ts.ixe --ixes init-ordered-8.ixes --distributed \
  --cells 1800000000 --texray --no-index                    # prints the batch address
ix verify --ixe init-ts.ixe --ixes init-1.ixes <batch>

# Stage 2: range tree, one node at a time, each node planned to the slot
ix aggregate --ixe init-ts.ixe --ixes init-1.ixes --no-cache --jobs 1 \
  --max-ram 100 --trace-shards --range 12 <batch>           # prints the root address
ix verify --aggregate --ixe init-ts.ixe --ixes init-1.ixes <root>
```

`--exec-only` after `--distributed` executes and absorbs every worker and
reports record sizes without proving. The aggregate command has no
`--cells` flag; it plans each node's trace shards to `--max-ram / --jobs`
bytes of host peak, or to a cell budget when
`AIUR_TRACE_SHARD_MAX_CELLS=<cells>` is set in the environment.

## Measured on the CPU box

All Init, one claim, verified roots. Env-shard rows use the same commit.

| Configuration | Stage 1 | Stage 2 | leaf bytes | root |
|---|---|---|---|---|
| 4 min-cut chunks, 1.8 G cells (71 shards) | 28:16, 159 GiB | range tree, one 100 GiB slot: 25:45, 88.5 GiB | 99.8 MiB | 6.95 MiB |
| 8 ordered chunks, 1.8 G cells (95 shards) | 37:25, 113 GiB | not rerun; same tree applies | 159.7 MiB | |
| env shards at 400 GiB slots (9 shards) | 33:21, 347 GiB | wrap-first, 2 wraps at a time: 14:19, 197 GiB | 96.8 MiB | 5.86 MiB |

What the numbers say:

- The trace path's advantage is memory, not bytes or time: it runs inside
  159 GiB (113 with ordered chunks) where the env path needs 347 GiB for
  Stage 1 and 195 GiB per wrap. End to end it is 13 % slower on this box
  because every recursion node is sharded to the slot.
- Residency is set by the layout. Min-cut chunks form one caller group at
  any count, so every record is resident until the first commits. Ordered
  chunks commit one at a time. The cost is duplicated reduction work across
  records (memoization does not cross workers): 8 chunks redo about a
  quarter more execution than 4, hence 95 shards against 71 and 33 % more
  wall. Fewer, larger ordered chunks trade back toward the 4-chunk time at
  the price of larger resident records.
- The stage-two node floor is the recursion verifier itself: a join
  projects at ~205 GB unsharded, so at a 100 GiB slot every node is cut
  into 2–3 shards under Regenerate. Narrower range leaves do not help;
  they add nodes that each pay the same floor.

## What the GPU box should calibrate

The design puts the STARK phases of one shard on the device and keeps the
record on the host. The CPU runs approximated that with a committed-cell
budget; nothing below has been measured on a device.

1. **Cells per byte of device memory.** `--cells 1800000000` was chosen for
   96 GB from the design's model. Measure the device peak of one shard
   against its committed cells (the `[trace-shards]` log lines print each
   shard's projected peak and committed widths) and set the budget from the
   measured ratio. Stage 2 nodes take the same budget through
   `AIUR_TRACE_SHARD_MAX_CELLS`.
2. **Host peak with phases off the host.** On the CPU the peak is records
   plus one shard's phases (about 72 GiB at 1.8 G cells). With phases on
   the device the host holds two records (the one proving, the one executed
   ahead) plus the trace generation of one shard. For Init in 8 ordered
   chunks that is 23 + 18 GB of records; the prefetched record can be
   dropped by `--no-prefetch` at a ~23 % wall cost on the CPU.
3. **Re-execution overlap.** Round two re-executes each worker on the CPU
   while the device proves. Check the execution of the next chunk (60–105 s
   per chunk on 64 cores) still hides behind device proving, which will be
   much shorter than the CPU's.
4. **The recursion verifier's floor** per node and how many shards a node
   needs at the device budget: the same `[trace-shards]` lines during
   `ix aggregate`.
5. **Chunk count.** Measure 4 and 8 ordered chunks: 4 has less duplicated
   work and larger records, 8 the reverse. The per-record cost is the
   `retained` bytes in the `[distributed] worker N: executed` lines.

## Known gaps

- `ix aggregate` needs a `--cells` flag like `ix prove` instead of the
  environment variable.
- Every recursion node parses the whole batch preamble (headers and
  messages of all shards); a compact preamble or a Merkle root over headers
  would cut the per-node fixed cost.
- Workers run as threads of one process. NUMA isolation on a multi-socket
  box needs one process per chunk and the preamble exchanged through files;
  the design already limits the exchange to the preamble.
- Worker 0 carries the claim walk's deferred calls on top of its own chunk,
  so its record is the largest; a small top chunk would shrink the resident
  pair.
- `Retention::Retain` for recursion nodes would remove the doubled stage
  one at the cost of holding the commitments.
