# Compression stage boundaries

Ix is migrating default proof compression to the **Lean-compiled Aiur
compression stages** (`ix compress run-stages`, `crates/proof-compression/src/aiur_backend/`,
documented in [Aiur compression architecture](aiur-compression-architecture.md)),
retiring the legacy hand-written `pipeline::compress` Rust circuits (hand-written
Stage-0 FRI, `foreign.rs`, and `recursive/` gadgets).

From a Protocol `v6` (`Fp^3`) aggregate root proof, Ix targets three
cryptographic endpoints (see
[STARK parameters and concrete endpoint security](stark-parameters.md#concrete-security-analysis-across-all-three-endpoints)):

1. **Endpoint 1 — Native `Fp^3` STARK Shrinker (`--stark-128` / `--stark-128-zk`,
   `crates/stark-shrinker`):** wraps the aggregate root in a single high-blowup
   Goldilocks `Fp^3` STARK proof (`v6` transparent or `v6-zk` hiding PCS), with
   zero trusted setup: about 128-bit classical security (an estimate, limited
   by the production 32-byte `BLAKE3-256` digest at `127.7b`; no machine-checked
   theorem covers this verifier) and about `85.3b` BHT post-quantum collision
   resistance. Post-quantum soundness is not established: no theorem considers a
   quantum adversary. A 64-byte RFC 7693 `BLAKE2b-512` profile (512-bit internal
   state: `255.7b` classical BCS / `170.7b` BHT / `204.8b` CNS / `256b` Grover)
   exists only as a Lean specification and parameter study, used by no prover or
   verifier (`BLAKE3-XOF48`/`XOF64` are excluded from it due to BLAKE3's 256-bit
   internal `cv`).
2. **Endpoint 2 — BLS12-381 KZG → Recursive KZG → EIP-2537 Final PLONK
   (`--bls12-381`):** uses Filecoin Phase 1 `challenge_19` (`2^27` trace prefix /
   `2^28 - 2` public degree) with mandatory `G1` prime-order subgroup checks for
   ~126–128-bit classical security (0-bit post-quantum) and Pectra EIP-2537
   on-chain verification.
3. **Endpoint 3 — BN254 KZG → Recursive KZG → Final PLONK / optional Groth16
   (`--bn254`, opt-in pre-Pectra EVM compatibility):** uses Aztec Ignition
   parameters (~100-bit classical exTNFS security, 0-bit post-quantum).

## Lean-compiled Aiur stages vs. retiring hand-written `pipeline::compress`

In the target **Aiur compression pipeline** (`ix compress run-stages`), every
verifier circuit is compiled from Lean Aiur sources and exported by the Lean
exporters (`stark-export export-trace --compress-wrap`,
`stark-export export-trace --compress-gl`, `wide_export`, `tiling_export2`,
`plonk_export`):

```text
IxVM aggregate root (Protocol v6 Goldilocks Fp^3 / BLAKE3 STARK)
  -> CompressWrap        normalized wrap of the root (Goldilocks FRI)
  -> CompressGL          FRI verifier over curve Fr, packed-SHPLONK KZG proof
  -> CompressNarrowFixed fixed-key narrow tiled stage, packed-SHPLONK KZG proof
  -> CompressFinalNarrow terminal Aiur relation (Lean-checked SCS)
  -> Native Rust PLONK   final proof & Solidity verifier (EIP-2537 BLS12-381 or opt-in BN254)
```

Because `CompressWrap` and `CompressGL` take verifying keys as authenticated
data rather than hard-coding per-circuit Rust constraints, upgrading IxVM or
aggregation circuits only updates authenticated statement digests rather than
re-authoring Rust verifier circuits.

The legacy hand-written `pipeline::compress` pipeline (hard-coded Stage-0 FRI →
first KZG → hand-written recursive KZG → final Rust PLONK/Groth16) is retained only
during the transition to `ix compress run-stages` and is scheduled for
retirement once curve-parameterized `aiur_backend/` (BLS12-381 + BN254) replaces
default `ix compress`. Within that legacy pipeline, the recursive KZG stage
reduces the first stage's many commitments and openings before translating its
verifier into PLONK/Groth16 constraints; measurements of the recursive Init wrapper do
not establish the cost of wrapping the first stage directly.

## Execution and trust boundaries

`ix compress run-stages` runs the Lean-compiled Aiur stages in-process from an
independently BLAKE3-pinned `ix-aiur-stages-v1` manifest (`Ix/Cli/AiurStages.lean`),
invoking `wide_export` and `tiling_export2` in dedicated Lean tasks without
Rust calling back into Lean. Legacy `pipeline::compress` runs its hand-written
stages in-process with checked stage checkpoints. Final PLONK and Groth16
provers run natively in Rust (`crates/proof-compression`, zero Go/CGo
dependencies); a loaded prover retains its circuit, keys and optional device
allocations across calls.

KZG and PLONK CUDA kernels build against sppark (`libix_bn254_cuda.so` and
BLS12-381 PLONK GPU kernels). Groth16 CUDA uses installed ICICLE libraries.
Cargo reports each runtime artifact to Lake for packaging alongside the
executable.

BN254 PLONK uses admitted Aztec Ignition parameters; BLS12-381 KZG and PLONK use
admitted Filecoin `challenge_19` parameters. The hand-written recursive KZG
circuit enforces prime-order `G1` subgroup membership in constraints
(`recursive/native_curve.rs`; the check is proved correct for the Lean model in
`Ix/Cert/Compression/Bls12381/CurveMsm.lean`); the Aiur compression backend
checks it only while decoding untrusted advice, not in constraints. Groth16
needs its own circuit-specific Phase 2 setup (the bundled Groth16 key is
development-only and requires explicit `--dev-srs` / `--dev-final-srs`). All
final proof types require independently authorized verifier keys; a generated
candidate catalog does not grant that authorization. Explicit KZG verification
requires a pinned key and expected statement.

## Parameter research

Inspect keys through the Rust decoder before calculating candidate security
bounds:

```sh
cargo run --release -p ix-proof-compression --no-default-features \
  --features parallel --example fri_sizing -- --statistics outer-vk.bin | \
  lake exe fri-security -
```

The `fri_sizing` example estimates candidate frontend layouts. Materializing the
full lowering with `FRI_SIZING_LOWER=1` can require tens of GiB. Candidate query
counts and trace layouts are research inputs; performance comparisons must retain
the same Protocol `v6` 128-bit security requirement. The calculator reports
individual terms and the assumptions of each regime.

[STARK parameters and endpoint security](stark-parameters.md),
[Aiur compression architecture](aiur-compression-architecture.md),
[compiler and zero-Go compression guide](ixcc-aiur-compiler.md),
[operational setup and commands](../crates/proof-compression/README.md), and
[revision-labelled measurements](proof-benchmark-comparison.md) are maintained
separately. Detailed stage-collapse experiments are preserved in Git history at
`7b9a7f21`.
