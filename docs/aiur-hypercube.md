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
`crates/vendor/` with capacity fixes. Not exercised in this session.

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
| `IX_HC_DEBUG` | partitioner, shape and recursion-program diagnostics; `IX_HC_PLAN_ONLY` stops after the shape report |
| `IX_HC_GPU=1` | route proving through `sp1-gpu` (needs the `cuda` build) |
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
6. **Memory.** The Hypercube prover holds every shard record; a streaming
   prove would cut the 373 GB peak.
7. **Chip clusters.** Light shards still pay the leaf for all 181 chips; a
   catalogue with a few chip clusters would make them cheaper.
8. GPU proving for the byte verifier, and a cleaner `ix` entry that skips
   the aggregate cache when only compression is wanted.

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
