# Experimental IxBy / Flock native workspace

This independent workspace starts the generic IxBy execution backend. Its
current implementation contains reusable primitive gates and labelled native
gadget proof regressions, not an IxBy interpreter or certified Stage 2 verifier.
It is excluded from the root Cargo workspace and has no `aiur`, `multi-stark`,
or `ix-terminal` dependency. Test-only Plonky3 field crates provide arithmetic
differential oracles at the same revision used by the original tests.

Flock is pinned to `b310f35f35f68095537150a1c8c0a43caca9a29e`; no experimental
m37 patch/profile is enabled. `IMPORT-PROVENANCE.json` records the donor HEAD
and each working-source hash, including the uncommitted sizing changes.
Visibility/import/formatting adaptations are separate from the original
table/witness identities. The source worktree was not modified.

## What is imported

- Shared Boolean R1CS builder, initialized witness generation, F128 equality,
  canonical Goldilocks/add/multiply/extension gates, lane repacking, and byte
  windows; count/emit parity and bounded assertion-group wiring regressions.
- Generic BLAKE3 compression and byte/word/parameter packing extracted from
  the old statement-binding file, without its Stage 2 relation or decoder.
- Arithmetic and Merkle conformance proof/verification/strict artifact codecs.
  Their historical configuration identity lives under `conformance/config`;
  it is not the new generic execution protocol identity. These artifact types
  must never be accepted as Exec proofs through fallback decoding.

Ordinary tests include direct P3 differentials, noncanonical field elements,
wrong quotient/result/direction bits, all byte-window offsets, dummy-row zero
initialization (including the BLAKE3 constant pin), and circuit/schema drift.
New BLAKE3 regressions compare the compression gate with native hashes at
single-block boundaries and reject tampered R1CS output bits.

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml --workspace
cargo fmt --manifest-path flock-stage3/Cargo.toml --all -- --check
cargo clippy --release --locked --manifest-path flock-stage3/Cargo.toml --workspace --all-targets -- -D warnings
```

The current ordinary suite passed 30 tests. The two real conformance proofs
are opt-in and also passed locally on 2026-09-12, including their serialized
round trips and malicious operand/path/root/proof mutations:

| Label | Flock proof bundle bytes | Scope |
| --- | ---: | --- |
| Goldilocks arithmetic conformance | 129,251 | Base/extension arithmetic gadget circuit |
| BLAKE3 Merkle conformance | 108,171 | Four-level authentication-path gadget circuit |

These byte counts exclude the conformance artifact's public operands and
framing. They are neither generic Exec proof sizes nor terminal FFLONK sizes.
Tests ran with eight Rayon workers, a 32 GiB virtual-address limit, and a
300-second timeout per test; this is a bounded regression, not peak-RSS or
production capacity evidence.

```sh
RAYON_NUM_THREADS=8 cargo test --release --locked --manifest-path flock-stage3/Cargo.toml --workspace conformance:: -- --ignored --test-threads=1
```

The new backend must instantiate the proof-free setup contract in
`Ix/Ixby/Flock/Contract.lean`, use a distinct Exec domain/public template, and
compile one fixed interpreter topology per approved capacity/primitive class.
Guest code, branch outcomes, private input, Stage 2 keys, and witness geometry
must not determine its setup. See `docs/IxbyExec.md` for the theorem boundary.
