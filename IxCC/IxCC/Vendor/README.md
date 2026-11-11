# Pinned pure Aiur target reference

Files from argumentcomputer/ix at `a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`, an
upstream revision of another line of ix's Aiur that is not in this
repository's history (vendor provenance, like a fixture's upstream origin;
the snapshot, these citations and the reference exports under `tools/aiur-*`
are to be retired with the legacy Aiur model after pull request #678 lands,
roadmap RL-3), vendored under `IxCC.Vendor` so that neither a module nor a declaration name
is shared with ix's own packages: upstream module `Ix.M` is `IxCC.Vendor.Ix.M`
here, and upstream declaration `D` (`Aiur.Bytecode.Toplevel`, `IndexMap`,
`List.mapM_except_ok`, …) is `IxCC.Vendor.D`. Two mechanical edits are the
only changes: the prefix of each `Ix` import, and a `namespace IxCC.Vendor`
line right after each file's first `public section` with its
`end IxCC.Vendor` right before the file's final `end`. `upstream.json`
records the upstream SHA-256 of each file and both licenses; `check-aiur`
undoes both edits and compares the result with it. The `IxCC` library
imports all eleven modules. No Rust executor, FFI stub, prover, or verifier
is imported. The bytecode evaluator is deferred until its pure IO types have
an independent upstream module.

IxCC builds these sources with its pinned Lean toolchain;
the upstream toolchain is recorded independently. Vendored cycle lemmas
have their stated abstract-row premises; they do not certify the
upstream bytecode checker or extract facts from AIR constraints.
