# Experimental Stage 4 native core

This independent Cargo workspace contains the reusable trace, R1CS circuit,
and KZG-FFLONK components imported from `jcb/flock-stage4` at `8fdb3eab`.
`IMPORT-PROVENANCE.json` records the original revision and SHA-256/Git blob
identities of all 47 imported source/manifests. It describes the import
baseline, not a promise that subsequent changes have those hashes.

The workspace is excluded from the ordinary Ix Cargo build. It has no native
Stage 2 or Flock dependency and does not alter the root dependency pins.

```sh
cargo test --release --locked --manifest-path flock-stage4/Cargo.toml --workspace
cargo fmt --manifest-path flock-stage4/Cargo.toml --all -- --check
```

The import regression on 2026-09-12 passed 149 tests (88 FFLONK, 18 trace,
43 circuit); one pre-existing heavyweight circuit projection is ignored.
Tests include strict scalar/curve/subgroup decoding, invalid SRS/key rejection,
nonzero blinding admission, authenticated scratch corruption, and identical
proof/key results across memory and file backends for fixed test randomness.
Small proofs use development setup and randomness, not production security.

## Boundary that is not yet closed

`Stage4RelationPublicInputsV1` is the historical **root-conditional** relation.
Its matrix, structure, and jagged evaluations require external trusted-table
discharge. Its statement mapping is still the historical Stage 3 mapping.
The public-input-binding tests prove only their small binding circuits.
Neither is a complete generic IxBy execution proof.

The existing FFLONK body is exactly 992 bytes. The historical full terminal
statement also carries 600 scalar fields (19,200 bytes). A 992-byte body does
not establish the compact-proof goal: the generic execution adapter and all
terminal root checks must be constrained inside the final relation, followed
by an actual complete proof and isolated verification without root sidecars.
The old Stage 2 exporter, CLI, fixture scheduler, and billion-row census are
deliberately not imported as an IxBy backend.
