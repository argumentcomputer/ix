# Ix Flock Stage 3

This workspace implements the no-RISC-V Stage 3 compressor:

```text
Stage 2 Aiur recursive-FRI root
  -> Flock proof of statement + AIR/logUp + PCS + FRI verification
  -> Stage 4 terminal SNARK
```

The backend uses Flock `Fast128` over `F128`, BLAKE3 Merkle commitments, and
chained-BLAKE3 Fiat-Shamir. The upstream revision is pinned to
`b310f35f35f68095537150a1c8c0a43caca9a29e`; changing it is a protocol change.

## Flock Stage 2 development

The same workspace now hosts the first stage-neutral verifier leaf for the
`jcb/flock-stage2` development path. `FlockStage2Backend` accepts a canonical
ten-word IxVM P3 claim, performs native fail-fast verification, lowers the
complete eleven-phase P3 verifier, and proves it under the distinct
`ix:flock-stage2:p3-leaf-verifier:v1` transcript domain.

This boundary has its own `FlockStage2ConfigV1` and canonical
`P3VerifierRelationManifestV1`; it does not reuse the Stage 3 configuration or
relation identity. The current leaf proves the exact P3 statement. It does not
yet constrain the `CheckEnv` preimage, publish the uniform Flock aggregate
claim, or recurse, so it is a Phase 1 artifact rather than an aggregate root.

The debug q=2 ten-word fixture now produces a 371,083-byte proof bundle and
passes proof generation, valid verification, and corrupted-proof rejection in
37.22 seconds total. Its first relation build takes 12.62 seconds and Flock
proving after compilation takes 2.337 seconds; the remainder includes the
independent wrong-domain and corrupted-proof relation rebuilds. These figures
validate the new path but are not evidence about a real q=100 IxVM shard. This
fixture is synthetic and should not be confused with the matched kernel proof
below.

`bench-flock-stage2` now generates or imports an exact shard wrapper and runs
one backend per fresh process. A real q=2 IxVM kernel proof over the frozen
one-constant shard yields 2,114,302 Flock rows at `nu=20`. Three alternating
samples on a Ryzen 9 7950X3D put the production P3 shape-0 lift at a 14.399 s
median and the verifier-only/same-witness Flock lower bound at 24.287 s. Flock
also used 26.43 GiB median peak RSS versus P3's 14.62 GiB and emitted a
516,563-byte proof versus P3's 438,620-byte median. That matched small result
is unfavorable to Flock, but it is not a q=100 scaling measurement and the
Flock arm still proves less. Full ranges and fixture identities are in
`plans/flock-stage2-benchmark-plan.md`.

The first persisted q=100 input is a valid 4,432,373-byte raw IxVM proof. It
passes canonical decode, native verification, advice expansion, transcript
replay, native PCS/FRI checks, complete relation construction, and evaluated
Flock preflight. Its exact Stage 2 relation is:

| Quantity | Measured value |
| --- | ---: |
| P3 circuits | 760 (76 active) |
| FRI queries / rounds | 100 / 16 |
| relation inputs / public values | 2,566,088 / 2,567,682 |
| total table rows | 56,237,892 |
| largest table | Goldilocks add, 16,353,512 rows |
| exact uniform domain | `nu=24`, 16,777,216 rows/table |
| compiled relation digest | `c1163b83b88ddd8462ca9adad70e67c06d3d5f3f36ecb5a769b92045393a5b72` |
| accounted commit-phase allocations | 296.65 GiB |
| accounted plus 25% arithmetic margin | 370.81 GiB |

The original lowering spent 651.119 seconds in AIR emission and had not
completed PCS construction after more than 25 minutes. Directed four-way zero
assertions removed Flock's quadratic shared-wire-class behavior, and folding
output canonicality into the add/multiply residual words reduced the initial
144,128,918-row / `nu=27` relation to the shape above. The final sizing pass
emitted all q=100 constraints in 45.56 seconds; AIR itself took 0.11 seconds.

Cold evaluated preflight now succeeds, but it still takes about 12.9 minutes:
the two emission passes and validation account for about 92.8 seconds, while
`ShapeBuilder::finish` alone takes 680.4 seconds. Evaluation after compilation
takes about 1.4 seconds. A production path therefore needs a pinned compiled-
shape cache or an upstream serializable/linear-time shape representation. The
current Flock `CircuitShape` is not directly serializable because it contains
type-erased gate implementations and private compiled fill state. No q=100
Flock proof has been attempted yet.

The preliminary performance assessment is high-risk but unresolved. BLAKE3
contributes only 92,526 rows, or 0.16% of the complete relation; non-native
Goldilocks arithmetic and its assertions contribute more than 96%. The small
synthetic proved leaf is `nu=12`, the real matched q=2 kernel input is `nu=20`,
and the production shard is `nu=24`. The exact q=100 memory model accounts for
296.65 GiB before circuit/wiring/opening scratch and retained pools, making a
1 TiB node the appropriate first-run target. Compiled-shape caching could
remove the 12.9-minute cold setup, but only a q=100 Flock proof can measure the
remaining prover workload. Until that matched W0 benchmark runs the P3 lift
and Flock verifier core over the same shard, hardware, and revision, keep P3
for Stage 2 and defer Flock Stage 2 recursion.

Run the evaluated leaf preflight and the explicitly ignored proof round trip:

```sh
cargo test -p flock-stage3-host \
  real_ixvm_claim_lowers_to_the_complete_stage2_leaf_relation -- --nocapture
cargo test -p flock-stage3-host \
  real_ixvm_stage2_leaf_flock_round_trip -- --ignored --nocapture
```

With an `IX_FLOCK=1` build, ingest a persisted raw shard directly. `profile`
performs native validation, `pcs-size` and `size` emit exact row censuses
without finalizing the circuit, and `preflight` compiles and evaluates it:

```sh
ix flock-leaf PROOF_ADDRESS --mode profile
ix flock-leaf PROOF_ADDRESS --mode pcs-size --queries 10
ix flock-leaf PROOF_ADDRESS --mode size
IX_FLOCK_TIMING=1 ix flock-leaf PROOF_ADDRESS --mode preflight
```

Build and run the paired harness (or generate a parameter-matched local input):

```sh
IX_FLOCK=1 lake build bench-flock-stage2
bench-flock-stage2 --ixe ENV.ixe --ixes MANIFEST.ixes --shard 0 \
  --queries 2 --generate-proof proof.ixp
bench-flock-stage2 --ixe ENV.ixe --ixes MANIFEST.ixes --shard 0 \
  --proof-file proof.ixp --queries 2 --backend p3-lift --json p3.json
bench-flock-stage2 --ixe ENV.ixe --ixes MANIFEST.ixes --shard 0 \
  --proof-file proof.ixp --queries 2 --backend flock-verifier-core \
  --json flock.json
```

## Current status

`FlockStage3Backend::prove_stage2` now generates a complete Stage 3 proof.
The production path:

1. validates canonical Aiur verifier-key, claim, and proof encodings;
2. expands the compact multiproof into the typed verifier witness;
3. compiles the specialised fixed-shape Flock relation;
4. proves it under the production Stage 3 transcript domain;
5. binds the compiled circuit, Flock configuration, Stage 2 key, witness
   layout, capacity, and completed phase mask in `Stage3RelationManifestV1`;
6. returns a strict, versioned `Stage3ArtifactV1`.

`FlockStage3Backend::verify_stage2` requires an externally expected
`Stage3StatementV1`. It reconstructs the relation from the canonical Stage 2
transport, checks the expected root and relation-manifest digest, and verifies
the Flock bundle. The relation digest therefore has to be pinned by the
deployment; accepting a relation digest supplied only by the prover would not
specialise the verifier key.

The single relation constrains all eleven registered verifier phases:

- typed witness shape, sparse activation, and active trace heights;
- specialised Aiur verifying-key/AIR metadata;
- all 18 canonical Goldilocks claim words and the 224-byte Stage 2 statement;
- lookup-message inversion, intermediate logUp accumulators, and final balance;
- exact chained-BLAKE3 transcript replay;
- Goldilocks and degree-two extension arithmetic;
- first/last/transition selectors and compiled AIR DAG evaluation;
- alpha-folded OOD composition and quotient recombination;
- every multi-matrix, multi-height PCS opening and BLAKE3 MMCS path;
- every binary FRI beta, grinding draw, query index, fold, roll-in, and final
  polynomial check; and
- one published BLAKE3 Stage 2 root shared by the statement and proof checks.

PCS leaves use the full BLAKE3 tree hasher, including rows wider than one block
and messages beyond one 1,024-byte chunk. Transcript field sampling follows
Plonky3 rejection sampling across the current digest plus one constrained
chained refill. The bounded circuit fails closed only if fewer than two values
are canonical among eight candidates, or among seven after a raw commit-PoW
draw. The latter probability is below roughly `2^-189`.

## Measured complete proof

The production regression fixture is a real canonical multi-STARK proof with
an inactive leading circuit, active circuits at heights 8 and 4, an active
preprocessed matrix, an 18-word claim lookup, nontrivial first-row/transition
constraints, and two FRI queries.

On the debug profile, the instrumented complete production round trip produced:

- Stage 3 artifact: **326,019 bytes**;
- encoded production payload: **325,893 bytes**;
- fixture setup: **0.010 seconds**;
- complete `prove_stage2` path: **491.624 seconds**;
- artifact encode and decode: **less than 0.001 seconds each**;
- valid cryptographic verification: **16.245 seconds**;
- rejection of a wrong relation statement: **0.000011 seconds**;
- rejection of a corrupted proof: **16.437 seconds**; and
- complete round trip: **524.315 seconds**.

The complete prove-path timing includes native validation, witness lowering,
relation construction, Flock proving, and artifact packaging. Proving accounts
for 93.8% of the round trip. The negative-check time is almost entirely a
second full cryptographic verifier run against the corrupted proof; the wrong
relation digest fails before cryptography in 11 microseconds. This size is
expected: Stage 3 is the off-chain proof whose small fixed verifier is
compressed by Stage 4. It is not the sub-kilobyte Ethereum proof.

Run the exact regression with:

```sh
cargo test -p flock-stage3-host real_stage2_production_artifact_round_trip -- --ignored --nocapture
```

The ordinary suite exercises relation construction and native/circuit
differential checks without paying the full proving cost:

```sh
cargo test -p flock-stage3-host --lib
cargo clippy -p flock-stage3-host --all-targets -- -D warnings
```

Print the selected Flock configuration and digest with:

```sh
cargo run -p flock-stage3-host --bin flock-stage3-config
```

## Production aggregate preflight

Build the optional root connector and compile/evaluate the complete Stage 3
relation for a persisted `ix_aggr` root without starting the Flock prover:

```sh
IX_FLOCK=1 nix develop --command lake exe ix flock-root ROOT_ADDRESS \
  --mode preflight
```

Preflight natively verifies and expands the compact Stage 2 proof, constructs
the typed AIR/PCS/FRI witness, evaluates every Flock gate, and prints the Stage
2 advice geometry, `nu`, table capacity, relation/public sizes, per-gate row
counts, and content-addressed relation/statement digests. It is the mandatory
gate before a production-sized proof.

Once preflight succeeds, retain the expensive verified artifact explicitly:

```sh
IX_FLOCK=1 nix develop --command lake exe ix flock-root ROOT_ADDRESS \
  --mode prove --output root.stage3.flock
```

The output is installed atomically. The binary-FRI lowering supports the full
height-derived schedule: the prior eight-round implementation ceiling is gone,
with evaluated regressions at 9, 16, and the current 30-round maximum.

## Scope and remaining work

The current relation is deliberately specialised to the configuration used by
Ix: 18 claim words, binary FRI, cap height zero, and an exact activation/height
shape. Host deserialization is witness generation rather than trusted
acceptance; every lowered value reaches a verifier constraint. Native
prevalidation remains an ergonomics and cost guard.

Before freezing a production deployment, Stage 3 still needs:

- capacity measurements over the intended aggregate-proof corpus rather than
  one small fixture;
- differential vectors for production-sized Aiur roots and nonzero grinding;
- an independent review of the local Boolean R1CS tables and pinned Flock
  soundness profile; and
- a canonical export of the fixed Flock verifier inputs for Stage 4 witness
  generation.

The next implementation boundary is Stage 4: compile verification of this
fixed relation into the universal-setup FFLONK development backend, measure its
constraint/gas costs, and retain the option to switch the same statement to a
circuit-specific Groth16 endpoint once the relation is stable.
