# Proof compression

Compress the aggregated Init root through FRI → KZG → recursive KZG.
The supported Init profile uses a **known-trapdoor development SRS**:
`--dev-srs` is required, and the proofs are **not production-secure**.

```sh
ix compress ROOT_PROOF_ADDRESS --dev-srs
ix verify COMPRESSED_PROOF_ADDRESS --dev-srs
```

Compression preserves the claim address and prints a new proof address.
It registers the portable verifier locally and resumes checkpoints under
`~/.ix/compression/PROOF_ADDRESS/HEIGHT`. Use `--out DIR --resume` for custom
checkpoints, `--resident` to trade RAM for less disk I/O, and `--log-height 25`
for fewer partitions (default: 24). Checkpoints must be trusted local files.
`--root-vk PATH` selects a trusted root key instead of the current aggregate key.
Staging requires `zstd`; full proving needs hundreds of GiB of RAM.

A separate verifier machine imports `final-kzg/verifier.bin` once, using a
BLAKE3 digest obtained independently of the prover:

```sh
ix verifier import verifier.bin --digest TRUSTED_DIGEST --dev-srs
ix verify COMPRESSED_PROOF_ADDRESS --dev-srs
```

Accepted verifiers are stored under `~/.ix/verifiers/development/`.
Unknown profiles, altered keys and conflicting registrations are rejected.
Verification checks the proof, degree bounds and external pairing equations
using the portable verifier; it does not load the proving SRS.

The measured Init packet is 2,757 bytes, including its public claim and pairing
operands. Its stored ix wrapper is 2,803 bytes; the portable verifier is
5,847 bytes, distributed separately. These sizes exclude QR encoding overhead.

## Code and tests

`fri` constrains FRI verification, `foreign` translates Goldilocks arithmetic
into scalar-field constraints, `kzg` implements the commitment backend, and
`recursive` constrains KZG verification with public pairing operands.
`pipeline` runs the stages through the Plonkish API. The `init_fri`,
`init_fri_kzg` and `init_kzg_wrap` binaries expose individual stages.

```sh
cargo test --release -p ix-proof-compression
lake build ix compression-cli-tests
lake exe compression-cli-tests
```

Tests cover small proving, tampering, CLI validation and proof identity.
The saved Init FRI fixture checks the fixed public statement.
