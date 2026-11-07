# Pinned pure Aiur target reference

Files from argumentcomputer/ix at `a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`,
vendored under the `IxCC.Vendor` module prefix: upstream module `Ix.M` is
`IxCC.Vendor.Ix.M` here, so no vendored module shares a name with ix's own
packages. That prefix in their imports is the only change. `upstream.json`
records the upstream SHA-256 of each file and both licenses; `check-aiur`
restores each file's upstream imports and compares the result with it. The
`IxCC` library imports all eleven modules. No Rust executor, FFI stub,
prover, or verifier is imported. The bytecode evaluator is deferred
until its pure IO types have an independent upstream module.

IxCC builds these sources with its pinned Lean toolchain;
the upstream toolchain is recorded independently. Vendored cycle lemmas
have their stated abstract-row premises; they do not certify the
upstream bytecode checker or extract facts from AIR constraints.
