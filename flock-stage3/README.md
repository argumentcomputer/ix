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

On the debug profile, the complete production round trip produced:

- Stage 3 artifact: **326,019 bytes**;
- encoded production payload: **325,893 bytes**; and
- prove + decode + valid verify + negative checks: **529.55 seconds**.

The negative checks reject a different relation digest and a corrupted proof.
This size is expected: Stage 3 is the off-chain proof whose small fixed
verifier is compressed by Stage 4. It is not the sub-kilobyte Ethereum proof.

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
