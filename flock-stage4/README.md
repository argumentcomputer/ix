# Experimental Stage 4 native core

This independent Cargo workspace contains the reusable trace, R1CS circuit,
and KZG-FFLONK components imported from `jcb/flock-stage4` at `8fdb3eab`.
`IMPORT-PROVENANCE.json` records the original revision and SHA-256/Git blob
identities of all 47 imported source/manifests. It describes the import
baseline, not a promise that subsequent changes have those hashes.

The workspace is excluded from the ordinary Ix Cargo build. Its `exec` crate
now uses the generic `ixby-flock` backend and the same pinned Flock revision;
the three original crates remain Flock-independent. No crate depends on the
native Stage 2 verifier, and the root dependency pins are unchanged.

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
The generic replay addition passes 164 ordinary tests (88 FFLONK, 20 trace,
46 circuit, 10 replay/setup); three heavyweight tests remain opt-in.

## Generic Exec replay

`exec::compile_exec_replay` takes only an approved `CompiledExec` and produces
an immutable replay topology before any guest or proof exists. Its `replay`
method consumes commitment components and the strict `IXBYEX00` bundle;
`exec::replay_exec` is a compile-and-replay convenience wrapper.
It never reconstructs a native Stage 2 proof,
guest image, input bytes, or execution trace. The complete native verifier,
recorded transcript, algebra, Product-GKR, merged PCS, multipoint/untwisted
assist, inner Ligerito/Merkle, and all accumulator folds are exercised on
three real generic executions under one setup. Native replay topology is
identical across two programs and both branch outcomes.

The new circuit binding constrains `S = H4(P,B,I,O)` and public `Q = H5(P,B,O)`.
The input commitment is private; the public claim remains an explicit
application input from which the approved image/profile and canonical output
determine Q. The final application verifier has not been implemented yet.
The complete replay composition is deliberately named
`constrain_exec_root_conditional`; its roots still require closure.

Proof-free symbolic compilers reconstruct wiring, zerocheck, lincheck, merged
PCS, multipoint/anchor assist, inner Ligerito, and all three accumulator folds,
plus both complete transcript operation trees and their BLAKE3 compression
topology. Native replay must match their exact structures, not just operation
counts. Component identities remain distinct. These are replay blueprints,
not a proof-free R1CS/key compiler. No terminal key or full FFLONK proof is
produced here.

```sh
ulimit -v 33554432
RAYON_NUM_THREADS=4 timeout 180 cargo test --release --locked \
  --manifest-path flock-stage4/Cargo.toml -p ixby-stage4-exec \
  native::tests::different_guests_have_identical_complete_replay_topology \
  -- --ignored --test-threads=1 --nocapture
```

The full matrix-free census is separately opt-in via
`native::tests::complete_generic_exec_constraint_census`. It reports phase
progress, process peak memory counters, canonical R1CS/PLONK counts, and
capacity minima. A sizing report is not a satisfying-assignment check or a
proof. The completed run took 1,161.51 seconds including setup and counted
590,712,359 R1CS constraints and 989,490,840 PLONK rows. It still carries 42,464
public scalar bytes, needs a `2^30` base domain, and models a 420.9 GB
file-key/SRS/FFT resident payload minimum before several excluded costs.
The [retained report](census/exec-scalar-root-conditional-v0.json) records exact
counts and scope. Cost reduction and root closure are required; no expensive
terminal-prover or SRS job has been launched.

See [generic replay and remaining gates](../docs/IxbyStage4Replay.md).
`EXEC-REPLAY-PROVENANCE.json` records the donor hashes before this port,
excluded legacy interfaces, and semantic changes separately from M1.

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
The old Stage 2 exporter entry point, CLI, fixture scheduler, and billion-row
census are deliberately not used as an IxBy backend or its cost estimate.
