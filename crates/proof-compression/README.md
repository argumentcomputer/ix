# Proof compression foundations

This crate provides a BLS12-381 KZG polynomial commitment scheme implementing
the `multi-stark` field, evaluation-domain, transcript, and PCS interfaces,
along with a proving configuration, Goldilocks circuit translation, and
arithmetic and transcript gadgets for FRI verification.

- `Scalar` provides canonical scalar-field serialization and arithmetic.
- `Radix2Coset` defines evaluation domains and their selector polynomials.
- `Srs` loads and validates proving parameters; `VerifierParams` retains only
  the public parameters required for verification.
- `KzgPcs` commits polynomial columns, batches openings by evaluation point,
  and enforces each polynomial's declared degree bound with shifted commitments.
- Coefficients can be resident, constant, or stored in checksummed local files.
- `KzgConfig` binds the protocol parameters and SRS into the transcript and
  implements multi-stark proving with streamed lookup and quotient processing.
- `FixedProofCodec` encodes proofs against a fixed, trusted system and trace
  layout, omitting metadata that the verifier already knows.
- `GoldilocksCircuit` translates Goldilocks constraints into scalar-field
  constraints, preserving public values and enforcing canonical integer bounds.
- `KzgCircuitExt` chooses lookup groups within the quotient and SRS bounds.
- `QuadraticValue` constrains quadratic-extension arithmetic, and
  `constrain_algebraic_checks` enforces the inner system's constraint and
  lookup equations against supplied openings and challenges.
- `Blake3Challenger` matches native Goldilocks/BLAKE3 sampling, including
  canonical field rejection sampling with a fixed retry budget.
- `constrain_transcript` binds the system shape, claims, commitments, and
  intermediate accumulators to the algebraic challenges.

The FRI helpers do not yet verify a complete proof: openings still require
PCS authentication. The complete verifier is introduced in the next patch.

The caller must authenticate the SRS provenance. Point and consistency checks
cannot establish that its trapdoor is unknown. `Srs::unsafe_dev_setup` generates
known-trapdoor parameters for tests only. The caller also binds its protocol and
parameters into the BLAKE3 transcript before committing and opening polynomials.

The crate currently exposes this backend as a library. Certificate
compression and CLI integration are introduced by subsequent patches.

## Tests

The inline tests cover canonical encodings, domain selectors, SRS validation,
transcript observations, degree-bound rejection, verifier-only parameters, and
equivalence of constant, resident, and disk-backed polynomial operations.
Backend tests also cover foreign-field bounds, compact encoding, transcript
binding, streamed/dense proving equivalence, and copy constraints across shards.
FRI gadget tests compare arithmetic and transcript results with native
implementations, exercise BLAKE3 block and tree boundaries and forced field
sampling retries, and reject altered claims, openings, roots, and challenges.
A fixed parity fixture checks call/return relations and unused rows independently
of the proof protocol.

Run them on a machine with sufficient resources:

```sh
cargo test --release -p ix-proof-compression
cargo test --release -p ix-proof-compression --no-default-features
```
