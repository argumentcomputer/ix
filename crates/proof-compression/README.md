# Proof compression foundations

This crate provides a BLS12-381 KZG polynomial commitment scheme implementing
the `multi-stark` field, evaluation-domain, transcript, and PCS interfaces.

- `Scalar` provides canonical scalar-field serialization and arithmetic.
- `Radix2Coset` defines evaluation domains and their selector polynomials.
- `Srs` loads and validates proving parameters; `VerifierParams` retains only
  the public parameters required for verification.
- `KzgPcs` commits polynomial columns, batches openings by evaluation point,
  and enforces each polynomial's declared degree bound with shifted commitments.
- Coefficients can be resident, constant, or stored in checksummed local files.

The caller must authenticate the SRS provenance. Point and consistency checks
cannot establish that its trapdoor is unknown. `Srs::unsafe_dev_setup` generates
known-trapdoor parameters for tests only. The caller also binds its protocol and
parameters into the BLAKE3 transcript before committing and opening polynomials.

The crate currently exposes these foundations as a library. Certificate
compression and CLI integration are introduced by subsequent patches.

## Tests

The inline tests cover canonical encodings, domain selectors, SRS validation,
transcript observations, degree-bound rejection, verifier-only parameters, and
equivalence of constant, resident, and disk-backed polynomial operations.

Run them on a machine with sufficient resources:

```sh
cargo test --release -p ix-proof-compression
cargo test --release -p ix-proof-compression --no-default-features
```
