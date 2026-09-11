# The `aiur-hypercube` branch

What this branch builds, how the pieces fit, how to run them, and what the
measurements say. Written for someone (or some agent) picking the branch up
on another machine.

## The goal

Take an Ix proof the rest of the way to something small and cheap to verify:

```
IxVM kernel proofs  ──ix aggregate──►  one aggregate root proof (multi-stark, Goldilocks)
        │
        ▼  ix compress
KoalaBear byte verifier of that proof, executed as an Aiur program,
proven by SP1 Hypercube (sharded)
        │
        ▼
SP1's recursion tail: leaf → compose → shrink → BN254 wrap
        │
        ▼
gnark PLONK proof (~4 KB), with public inputs binding the whole chain
```

Everything above the leaf is SP1 6.6.0's own recursion machinery, used from
the registry crates unmodified. The leaf program and the pipeline that pins
it are ours. Nothing runs inside a RISC-V guest.

## The pipeline, stage by stage

Three proof systems and three fields are involved, and each hop changes
one thing: the number of proofs, the field, or the verifier's cost.

```
Lean env (.ixe)
   │  ix prove                      Aiur/Goldilocks, proven by multi-stark
   ▼
IxVM shard proofs   (CheckEnv claims: "these constants typecheck")
   │  ix aggregate                  Aiur/Goldilocks, proven by multi-stark
   ▼
aggregate root proof   (one multi-stark proof of the ix_aggr verifier program)
   │  ix compress, stage 2          Aiur/KoalaBear, proven by SP1 Hypercube (sharded)
   ▼
Hypercube shard proofs of the byte verifier   (113 shards for Nat.add_comm)
   │  SP1 recursion: leaf → compose → … → shrink → wrap    KoalaBear, then BN254 commitments
   ▼
one wrap proof
   │  gnark PLONK over BN254
   ▼
~4 KB PLONK proof, 5 public inputs
```

**1. IxVM on multi-stark.** The IxVM is the Lean kernel written as an Aiur
program over Goldilocks. `ix prove` executes it on a shard of the
environment and multi-stark proves the execution; the claim is a `CheckEnv`
of that shard. For Nat.add_comm this is one shard, proven in 1.3 s.

**2. The aggregator on multi-stark.** `ix_aggr` is a multi-stark verifier
written in Aiur, also over Goldilocks, also proven by multi-stark. It wraps
each IxVM shard proof by verifying it in-circuit and joins pairs of wrapped
proofs recursively into a tree. Its public input carries an allowlist blob
binding the IxVM verifying key and its own, so the root proof is a
statement about a fixed pair of systems. The output is one multi-stark root
proof (for Nat.add_comm: one wrap, no joins).

This stage stays in the Goldilocks world. Multi-stark proofs are large
(8.6 MB at 100 queries) and Goldilocks FRI verification is expensive for
anything downstream, which is why the next hop changes ecosystems.

**3. The byte verifier on Hypercube.** The same Aiur source of the
multi-stark verifier is compiled to a KoalaBear profile, Goldilocks
arithmetic emulated in 8-bit limbs (`GoldilocksForeign`). It reads the root
proof, the aggregator's vk and the claims as advice through the IO buffer
and verifies the root proof; its public input is the Blake3 digests of the
vk bytes and the claim bytes, so its claim commits to exactly which
aggregator and which Lean claims were verified. This program is proven by
SP1 Hypercube. It is the expensive stage — every Goldilocks operation is
tens of byte-limb rows — so the execution is split into shards, each
balanced locally, with the cross-shard lookups routed through the adapter
chips and a septic-curve digest (section 3 below). The reason to pay this
is that it lands the proof in SP1's KoalaBear ecosystem, where SP1's
recursion circuits and its gnark circuit are reused unmodified.

**4. SP1's recursion tail.** Each Hypercube shard proof is verified by a
leaf program (`AiurRecursiveVerifier`, the one custom program) that maps
Aiur's public values onto SP1's recursion public values. SP1's stock
compose program folds leaves two at a time until one proof remains, shrink
reduces it to a small fixed-shape proof, and wrap re-proves it on the outer
configuration, whose Merkle commitments use Poseidon2 over BN254. Every
program is pinned to a fixed shape and every program's verifying key sits
in a Merkle allowlist whose root travels in the public values, so a prover
cannot substitute a program of its own (section 4).

**5. gnark PLONK.** A gnark circuit verifies the wrap proof and emits a
BN254 PLONK proof of 4160 bytes. Its five public inputs are the digest of
the byte verifier's Hypercube vk (which stage-3 machine ran), the digest
of the byte verifier's claim (which aggregator vk and which Lean claims it
verified), the recursion allowlist root, an exit code of zero, and a nonce.

**What the final proof binds.** Follow the digests back: the PLONK proof
commits to the wrap circuit; the wrap proof commits to the allowlist of
recursion programs; the leaves verified Hypercube shards against the byte
verifier's vk; the byte verifier's claim commits to the aggregator vk and
the claims; the aggregator's claim commits to the IxVM vk through the
allowlist blob and to the `CheckEnv` claims; those name the
content-addressed Lean constants. A 4 KB proof, checked in BN254
arithmetic, says that a specific set of Lean constants typechecked under a
specific kernel.

**Where the time goes** (Nat.add_comm on the GPU, see the measurements):
IxVM 1 s, aggregation cached, byte verifier 32 min (15 min partitioning on
the CPU, 17 min for 113 GPU shard proofs at 9 s each), recursion 2.7 min,
PLONK 2.8 min. Recursion cost is per shard, so the adapter width and the
crossing count (next steps 1 and 2) are the levers on the byte verifier.

## Layers, bottom up

### 1. Field-generic Aiur and the KoalaBear profile

Aiur (the circuit DSL and its synthesis) was made generic over the field
(`crates/aiur`, commits `28c0a5af`…`d57c632b`). The IxVM kernel and the
multi-stark verifier are written against a field-width interface
(`Ix/IxVM/Width/{Goldilocks,KoalaBear}.lean`, `Ix/MultiStark/Field`), so the
same DSL source compiles to a Goldilocks toplevel (production, proven by
multi-stark) or a KoalaBear toplevel (proven by Hypercube).

### 2. The byte verifier (stage 2)

`Ix/MultiStark/` is the multi-stark verifier written in Aiur. Its KoalaBear
build (`MultiStark.multiStarkKoalaBear`, entry `verify_multi_stark_proof`)
verifies a Goldilocks multi-stark proof with Goldilocks arithmetic emulated
in 8-bit limbs (`GoldilocksForeign`, `Ix/MultiStark/Field`). Public input:
Blake3 digests of the verifying key and of the claims (`verifierPubInput2`,
2-byte packing). Advice, through the IO buffer: channel 0 the proof bytes,
1 the vk bytes, 2 the claims in `serializeClaims`'s wire format. FRI
parameters are read in-circuit from the digest-bound vk, so one verifier
serves any parameter set.

This is the expensive part of the pipeline: every Goldilocks operation is
tens of rows of byte-limb circuits, and the work scales with the proven
system's committed width × FRI queries plus the constraint evaluation of all
its circuits.

### 3. `crates/aiur-hypercube`: the Hypercube backend

Interprets Aiur's symbolic circuits inside SP1 Hypercube's `AirBuilder`
(`air.rs`, `expr.rs`): every Aiur circuit becomes a chip, lookups become
LogUp-GKR interactions. Non-affine lookup arguments are materialized into
extra columns; constraints are row-local. The claim enters through the
public values (`record.rs`, `CLAIM_WIDTH = 64`).

**Sharding** (`shard.rs`, `global.rs`). Hypercube's LogUp-GKR is strictly
per shard, so an execution is split into shards that each balance locally,
and the *boundary* is committed to a septic-curve digest (Poseidon2
hash-to-curve, the same construction as SP1's global interactions):

- the partitioner slices the splittable circuits' rows by execution epoch,
  evaluates every interaction to find each shard's residual (tuples it
  requires but does not provide, or provides in excess), absorbs what the
  per-shard tables can, and duplicates memoized rows whose lookups only hit
  per-shard tables (splitting their multiplicity);
- every remaining residual tuple becomes one row of an adapter chip
  (`AiurGlobalN`, `N` = 8-limb chunks of the tuple), which balances the
  tuple locally and adds `lift(mult, tuple)` to an accumulator chain; the
  chain end is exposed in the shard's public values; the top-level verifier
  checks the shards' digests sum to the identity;
- atomic circuits (those with preprocessed traces: byte tables, memory
  boundary, constants) are replicated into every shard;
- shards are refined adaptively until each fits the jagged PCS area bound
  (both commitment rounds ≤ 2^29 cells) and the row cap (2^20 rows per
  chip).

Adapter rows are wide (two Poseidon2 permutations for an 11-limb memory
tuple), so cross-shard traffic is the dominant overhead on large
executions; see the measurements.

**Shape catalogue** (`shape.rs`). SP1's recursion programs are compiled per
proof *shape*: the chip set, the stacked area of each commitment round, and
the padding-column count — but not row counts, which the jagged PCS
witnesses. For a fixed pipeline every shard must land in a finite,
machine-determined catalogue:

- the chip set is always the whole machine (`MachineShape::all`; a chip
  without rows is committed at zero area);
- the preprocessed round is a constant of the machine;
- the main round is padded to a class — powers of two from the stacking
  height up to 2^28, plus a top class just under the 2^29 bound on both
  rounds — by the `AiurPad` chip (512 zero columns, one trivial constraint,
  one inert lookup: the GKR prover rejects interaction-free chips).

`prove()` pads every record; `shape_of_proof` reads the class back off a
proof; `AiurMachine::fingerprint()` keys caches of machine-derived
artifacts.

**GPU** (`cuda.rs`, feature `cuda`, `IX_HC_GPU=1`): the open-source
`sp1-gpu` prover, machine-generic; two of its crates are vendored under
`crates/vendor/` with capacity fixes. Its trace buffer is sized to the top
catalogue class (2^29 cells) so every padded shard fits without measuring
the records up front.

**Memory** (`shard.rs`, `Partition`, `View`). A splittable circuit's rows
in a shard are a *view* into the execution's trace of that circuit — row
ranges (the epoch slice, or a load-affinity circuit's blocks), the
multiplicity reductions of rows duplicated elsewhere, and the rows
duplicated into the shard with their multiplicity — never a copy, so a
refinement round costs a few words per row edit instead of a second copy
of the execution; only the replicated atomic tables are owned per shard.
`prover::prove_source` has a couple of producer threads (`IX_HC_ASSEMBLERS`)
materialize, assemble and pad records ahead of the prover, in shard order,
so assembly (the adapter chips' hash-to-curve is parallel per row; the
septic accumulator chain is the sequential part, ~1 s for 700 k rows)
overlaps proving. Assembly is where a shard becomes big (wide adapter
chips, alignment and class padding), so the resident traces are the
execution's plus a few shards'.

**Refinement rounds** (`shard.rs`, the loop in `partition_shards`). A
round's cost was the tuple bookkeeping: every lookup of every row
evaluated, allocated and hashed into tuple-keyed maps, twice per round,
for five rounds. Now the first round is the only full scan:

- the provide and affinity indexes are bucketed maps built in parallel
  (`TupleIndex`);
- per interval (a shard's epoch slice), the demand-derived lists — the
  affinity votes and the rows to replicate — are cached, and the demand
  itself is computed only for new intervals and dropped;
- per interval, the *base* residual (every chunk's interactions before the
  tables absorb anything, balanced tuples dropped) is cached and, when
  only the edits moved — other shards' demands reduced more home rows in
  the slice, affinity blocks came or went — updated by those differences
  (`update_base`) instead of rescanned;
- home-row reductions are summed in a dense per-circuit array; flow
  matching runs in parallel over hash buckets of the residual tuples;
- an overflowing interval is split into as many parts as its overflow
  calls for, aiming 10 % under the bounds, and shards within 3 % of a
  bound are split too, since a neighbour's split moves crossings and
  affinity blocks; the round cap is generous because late rounds are cheap.

`IX_HC_TIMING=1` reports every stage and round step with the process RSS;
`IX_HC_DUMB=1` disables replication and affinity (a baseline: on the
6-shard stage-2 input it triples the shards and needs four rounds instead
of one — the optimizations are not what makes rounds expensive).

### 4. `crates/aiur-recursion`: the fixed recursion pipeline

`normalize.rs` — the leaf. `AiurRecursiveVerifier` verifies one Aiur shard
proof with SP1's generic in-circuit shard verifier (`recursive_verifier`
over our machine) and maps Aiur's public values onto `RecursionPublicValues`:
septic chain digest → `global_cumulative_sum`, claim flag →
`contains_first_shard`, Poseidon2(padded claim) as 32 bytes →
`committed_value_digest`, shard ordinal → timestamps, Aiur vk hash →
`sp1_vk_digest`. SP1's compose/shrink/wrap invariants then mean exactly what
the native Aiur verifier checks (one claim shard, digests cancel).

The leaf runs on its own machine configuration, `leaf_params() = (21, 23)`
(stacking height, row cap), because a 181-chip Aiur machine's leaf outgrows
SP1's compress cap of 2^21 rows.

`pipeline.rs` — the programs. Every program is compiled from a dummy input
of a known shape and pinned to a recursion shape (`program.shape`), so the
set is finite and the verifying keys are fixed:

| `ProgramKind`        | Verifies                          | Proven on        | Pinned to      |
|----------------------|-----------------------------------|------------------|----------------|
| `Leaf(shape)`        | one Aiur shard of that class      | leaf machine     | leaf shape     |
| `ComposeLeaf(n)`     | `n` leaf proofs                   | compress machine | compress shape |
| `Compose(n)`         | `n` compress proofs               | compress machine | compress shape |
| `Shrink`             | one compress proof                | shrink machine   | —              |
| wrap                 | one shrink proof                  | wrap (BN254)     | —              |

A single shard goes leaf → `ComposeLeaf(1)` → shrink → wrap. Fan-in
(`arity`) is 2 in the CLI and tests.

`shapes.rs` — the pinned shapes. `PinnedShapes { leaf, compress, … }`,
shipped in `shapes/pinned.json`, computed from the stage-2 verifier machine
(the largest machine supported): the leaf shape is the per-chip maximum
over the catalogue's leaf programs; the compress shape is the fixed point
over the compose programs, as SP1 computes its reduce shape. Shapes are
measured on *unpinned* programs (measuring a pinned one panics deep in trace
generation). A machine whose leaf programs do not fit is rejected at setup
with a message pointing at `IX_REC_SHAPES=compute`.

`vks.rs` — the allowlist. The verifying keys of every program form a Merkle
tree of fixed height `VK_TREE_HEIGHT = 8` (the compose programs bake in the
path length). Compose verifies each child's key against it; the root rides
in the public values to the PLONK proof. Leaf keys depend on the machine and
are cached per machine under `~/.ix/cache/recursion/<key>.vks`; everything
above the leaves is common to every machine that fits the shapes, so the
wrap key and the PLONK circuit are the same for every toplevel (tested:
`different_toplevels_share_the_wrap_vk`).

`prove()` checks that the key of the program it actually proved equals the
allowlisted one, which catches any drift between dummy-compiled and real
programs.

`cuda.rs` — the GPU (feature `cuda`, on with `IX_HC_GPU=1`, off again with
`IX_REC_GPU=0`). SP1's recursion chips already have device trace
generation in `sp1-gpu-tracegen`, so the four recursion machines are proven
by the same `CudaShardProver` as the Hypercube stage, with two component
selections: KoalaBear Poseidon2 Merkle trees and the duplex challenger for
leaf, compress and shrink (`CompressAir` and `ShrinkAir` are one AIR type;
the three levels differ in PCS parameters and get one prover each), and
Poseidon2 over BN254 with the multi-field challenger for the wrap. A CUDA
`TaskScope` only lives inside one `run_in_place` closure, so `GpuRecursion`
is a worker thread that enters one scope for its whole life and serves
setup and prove jobs over a channel; provers are built lazily per level
and grown when a program needs a larger trace buffer. Setup also runs on
the GPU, and the allowlist check in `prove` holds across backends: the
keys a GPU setup produces equal the CPU ones.

`plonk.rs` — gnark. `sp1-recursion-gnark-ffi` with the `native` feature (Go
compiled in-process; needs Go with `GOTOOLCHAIN=auto`, exported by the
lakefile, and libclang). SP1's Docker image builds the circuit but its
prover output fails to verify at this pin, so Docker is not used. Artifacts
(~5 GB, ~7 min to build) are cached under
`~/.ix/cache/plonk-bn254/<sha256(wrap vk)>-native-plonk-dev`; with pinned
shapes the wrap vk is stable, so this is a one-time cost.

PLONK public inputs: `vkey_hash` = Poseidon2 digest of the Aiur machine's
Hypercube vk, `committed_values_digest` = Poseidon2 digest of the claim,
`vk_root` = the allowlist root, `exit_code = 0`, `proof_nonce = 0`.

### 5. Lean/FFI surface and the CLI

- `Ix/Aiur/Hypercube.lean`: `HypercubeSystem.build/prove/verify`, and behind
  the `sp1-recursion` feature `wrap`, `plonk`, `recursionShapes`.
- `crates/ffi/src/aiur/hypercube.rs`: the externs. `ProverParams` and
  `ShardingParams` come from the environment (`IX_HC_*`).
- `Ix/Cli/Compress.lean`: `compressAggregateRoot` — load the root wrapper
  from the store, verify natively, build the byte verifier's Hypercube
  system, prove, verify, wrap, PLONK.
- `ix compress <root-proof-address>` (`--wrap-only`, `--out`, `--wrap-out`,
  `--blob` cache of the Hypercube blob) and `ix aggregate --compress`
  (`--plonk-out`, `--hypercube-blob`).

## Building and running

```sh
# Rust crates alone
cargo test -p aiur-hypercube
cargo test -p aiur-recursion --test roundtrip   # ~20–40 min each in debug: computes shapes, sets up all programs

# Lean + FFI with the recursion tail (Go toolchain and libclang required)
IX_SP1_RECURSION=1 lake build ix IxTests
# ... and with the GPU provers (nvcc; CUDA_ARCHS for the GPU generation)
IX_CUDA=1 IX_SP1_RECURSION=1 CUDA_ARCHS=120 lake build ix IxTests

# On the GPU, both stages: prefix any run below with IX_HC_GPU=1

# Stage-2 verifier end to end (ignored suite); IX_S2_RECURSION=wrap|plonk|shapes
IX_S2_QUERIES=3 IX_S2_RECURSION=plonk .lake/build/bin/IxTests --ignored stage2-hypercube
IX_S2_QUERIES=100 IX_S2_FORCE=1 IX_HC_SHARD_CELLS=100000000 IX_S2_RECURSION=wrap .lake/build/bin/IxTests --ignored stage2-hypercube

# Regenerate the pinned shapes from the stage-2 machine (arity 2)
IX_S2_QUERIES=3 IX_S2_RECURSION=shapes IX_REC_ARITY=2 IX_REC_SHAPES_OUT=shapes.json .lake/build/bin/IxTests --ignored stage2-hypercube
cp shapes.json crates/aiur-recursion/shapes/pinned.json   # Lake tracks crates/**/*.json

# The full pipeline on a small environment
ix shard extract --consts Nat.add_comm --out small.ixe init.ixe
ix shard --shards 1 --out small.ixes small.ixe
ix prove --ixe small.ixe --ixes small.ixes              # prints the shard proof address
ix aggregate --ixe small.ixe --ixes small.ixes <shard-proof> --compress --plonk-out small.plonk.json
```

Environment knobs:

| Variable | Meaning |
|---|---|
| `IX_HC_SHARD_CELLS`, `IX_HC_MAX_LOG_ROWS`, `IX_HC_LOG_STACKING`, `IX_HC_LOG_BLOWUP` | Hypercube prover/sharding parameters (defaults: single shard budget with automatic refinement, 2^20 rows, 2^21, blowup 1) |
| `IX_HC_DEBUG` | partitioner, shape and recursion-program diagnostics, per-record LogUp balance checks; `IX_HC_PLAN_ONLY` stops after the shape report |
| `IX_HC_TIMING` | stage, round-step and per-shard wall times with RSS |
| `IX_HC_ASSEMBLERS` | record producer threads ahead of the prover (default 2) |
| `IX_HC_DUMB` | plain epoch slices, no replication or affinity (baseline) |
| `IX_HC_GPU=1` | route Hypercube proving and the recursion tail through `sp1-gpu` (needs the `cuda` build) |
| `IX_REC_GPU=0` | with `IX_HC_GPU`, keep the recursion tail on the CPU |
| `IX_REC_SHAPES=compute\|<file>`, `IX_REC_SHAPES_OUT` | pinned-shape override / regeneration |
| `IX_REC_LEAF_LOG_STACKING`, `IX_REC_LEAF_MAX_LOG_ROWS` | leaf machine configuration (must match the pinned shapes) |
| `IX_S2_QUERIES`, `IX_S2_FORCE`, `IX_S2_RECURSION` | stage-2 test suite controls |
| `IX_NO_FUNCTION_GROUPS` | disable Aiur function grouping process-wide |

## Measurements (CPU, 64 cores, 495 GB)

Stage-2 verifier over a factorial proof:

| Input | Hypercube | Recursion tail | PLONK |
|---|---|---|---|
| 3 queries, 1 shard (32 stacked columns) | 54–115 s | wrap 325 s cold (all program setups), 198 s cached | 520 s incl. cold artifacts; 2 min warm |
| 100 queries, 6 shards | 761 s | wrap 276 s | — |

Full pipeline on the closure of `Nat.add_comm` (1 shard proof, root = one
lift proof of 8.6 MB at 100 queries):

| Stage | Result |
|---|---|
| Hypercube, 114 shards | 2.6 h, 537 MB of shard proofs (~4.7 MB each), peak RSS 373 GB |
| wrap tail | 46 min |
| PLONK | 2 min, 4 KB |

### GPU (RTX PRO 6000 Blackwell, 96 GB; 32 cores, 249 GB), 2026-09-11

`IX_HC_GPU=1`, both stages on the GPU. The wall times include the CPU work
around the provers (execution, witness, partitioning, recursion program
compilation, gnark).

| Input | Hypercube | Recursion tail | PLONK |
|---|---|---|---|
| stage 2, 3 queries, 1 shard | 5.3 s (54–115 s CPU) | wrap 6.7 s (160 s CPU): leaf 0.65 s, compose 0.14 s, shrink 0.12 s, wrap 1.5–8 s | 637 s cold artifacts, 4160 bytes, verified |
| stage 2, 100 queries, 6 shards | 36–45 s (761 s CPU) | wrap 18 s (six leaves, three composes, shrink, wrap) | — |

With the proving keys cached per program (`MAX_CACHED_KEYS`), the leaf
proofs after the first of a class take 0.21 s and the compose proofs 0.09 s;
setup is the rest. Peak RSS of the 6-shard run is 12.3 GB with records
assembled one at a time (15.9 GB before). The GPU-computed recursion keys
equal the CPU-computed ones: the allowlist check in `prove` passes against a
`~/.ix/cache/recursion` seeded by a CPU run, and the gnark circuit accepts
the GPU wrap proof.

Full pipeline on the closure of `Nat.add_comm` (`ix aggregate --compress`,
the same root proof as the CPU table above: 8.6 MB at 100 queries), the
compress stage over the session's iterations:

| Stage | first GPU run | shards as views | + incremental rounds, parallel matching, producers | + delta residuals, dense reductions, parallel indexes |
|---|---|---|---|---|
| execute + witness + extend traces | ~4 min | 143 + 8 + 70 s | 116 + 8 + 70 s | 110 + 8 + 69 s |
| partitioning | ~11 min, 5 rounds | ~10 min, 5 rounds | 562 s, 9 rounds (69, 90, 56 … 25 s) | 395 s: indexes 24 s, rounds 75, 76, 57, 17, 15, 14, 15, 16 s |
| shard proofs | 113 × ~20 s | 113 × ~9 s | 156 in ~130 s | 160 in ~130 s: GPU 0.52 s per shard (83 s total), waiting on assembly 0.25 s (40 s) |
| Hypercube stage | 2444 s | 1921 s | 890 s | 712 s |
| wrap tail | 221 s | 162 s | 238 s | 241 s |
| PLONK (warm) | 183 s | 170 s | 173 s | 185 s |
| total `ix compress` | 48 min | 38 min | 22.5 min | 19.9 min |
| peak RSS | 242 GB | 182 GB | 213 GB | 132 GB |

The CPU run of the same input took 2.6 h for Hypercube and 46 min for the
tail at a 373 GB peak. The GPU now proves a full 2^29-cell shard in about
half a second; what is left in the Hypercube stage is the interpreter
(110 s), trace extension (69 s), the first two partition rounds (the only
full scans, ~75 s each), and the ~80 s between "traces extended" and the
first round that is not yet timed. The shard count grew from 113 to 160 with
the split target and slack (each shard costs ~1.5 s here plus a leaf), which
the wrap tail's 241 s reflects.

Where the 114 shards come from: the verifier's own cells amount to ~30
shards; the rest is cross-shard plumbing — 71 M adapter rows and 117 M
duplicated rows. The largest crossing channel is memory loads of the proof
bytes from later epochs against the rows that stored them (22 M
crossings), followed by two memoized functions.

Shard proof size is close to constant (the per-chip opened values, the GKR
proof and the FRI folding transcript dominate; the per-column part is 4
bytes per column per query), and leaf cost is nearly flat in the shard's
fill (every chip is verified at the row cap; the 1-column and 255-column
leaf programs differ by ~2.5%). So recursion cost is per shard, and shard
count is the number to drive down.

## Known limits and next steps

1. **Cross-shard adapter cost.** An 11-limb memory tuple lands in the
   two-chunk adapter class, two Poseidon2 permutations wide. Narrowing the
   adapter row (one permutation per tuple, SP1's global-chip layout) is the
   biggest lever and is workload-independent. Replicating memory rows
   instead is *not* sound as is: a memory row's values are free witnesses
   bound only by its single store, so a copy in another shard could fork
   memory (memoized function rows can be replicated because their tuples
   are self-certifying).
2. **Crossing count.** The verifier reads proof data across epochs; placing
   the stores with the reads, or partitioning by query for this workload,
   would make most of those crossings local.
3. **Recursion FRI parameters.** `RecursionParameters` isolates the
   aggregate stage's FRI from the IxVM parameters; verifier work is linear
   in queries and the byte verifier reads the parameters from the vk.
4. **Function groups on `ix_aggr`** shrink its committed width, hence the
   proof and the verifier's work (`Ix/Aggr/FunctionGroups.lean` is empty on
   this branch; `Ix/MultiStark/VerifierFunctionGroups.lean` is populated
   only on `gb/recursion-function-groups`).
5. **Arity 4** needs the compress shape recomputed and checked against
   SP1's 2^21 row cap; the arity-2 compose-over-leaves program already
   needs ~590k rows on its largest chip.
6. **Memory.** Shards are views and records are assembled a few at a time
   (see the `Partition` paragraph above), so the resident traces are the
   execution's plus a few shards'. What remains is the partitioner's index
   working set — the provide and affinity indexes and the cached base
   residuals, maps keyed by tuples — which still scales with the execution
   (132 GB peak on Nat.add_comm).
7. **Chip clusters.** Light shards still pay the leaf for all 181 chips; a
   catalogue with a few chip clusters would make them cheaper.
8. **GPU.** Both stages run on the GPU and the proving phase is
   GPU-bound (see the measurements). The CPU work around it is now the
   bottleneck: the Aiur interpreter (110 s for the byte verifier), trace
   extension (69 s) and the two full partition scans (~75 s each). The
   partitioner is semantics-free and rediscovers every provider by
   evaluating and hashing every lookup tuple; recording the provider row of
   each lookup during witness generation would turn partitioning into
   integer graph work and remove the tuple maps from memory. A cleaner
   `ix` entry that skips the aggregate cache when only compression is
   wanted is still missing.

## Commit map

- `28c0a5af`…`7dc592a7` field-generic Aiur, inlining.
- `11ff4d7b` Hypercube backend; `14bde07a`, `b4cf06f8`, `2c027ef7` sharding.
- `d79eb651`…`637436d6` multi-stark field/PCS/transcript interfaces, the
  foreign (byte-limb) Goldilocks, stage 2 on Hypercube.
- `6d168a3a`, `3c4d9a43`, `d4f22bdd` IxVM width profiles, Nat.add_comm on
  Hypercube; `76183732`, `eb66d935` sp1-gpu.
- `b39ed130`…`c1cfc32c` the SP1 recursion tail and native gnark.
- `94e5e052` fixed-shape pipeline (shard catalogue, pinned shapes, vk
  allowlist).
- `2d84089b` `ix compress`.
