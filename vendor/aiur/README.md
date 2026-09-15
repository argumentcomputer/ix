# Pinned pure Aiur target reference

Unchanged files from argumentcomputer/ix at `a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`.
`upstream.json` records the exact SHA-256 inventory and both licenses.
`Ix/Aiur.lean` is a local import root. No Rust executor, FFI stub,
prover, or verifier is imported. The bytecode evaluator is deferred
until its pure IO types have an independent upstream module.

Compilatrix builds these sources with its pinned Lean 4.33.0 toolchain;
the upstream toolchain is recorded independently. Vendored cycle lemmas
have their stated abstract-row premises; they do not certify the
upstream bytecode checker or extract facts from AIR constraints.
