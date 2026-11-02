# BN254 final gnark backends

This Go module implements the final Ix verifier circuit and calls stock
gnark. Cargo builds it as a C archive linked into `ix`;
`pipeline/gnark.rs` owns the Rust bindings and loaded prover handles.
Two release commands sit beside the archive: `cmd/ignition` converts the
Ignition ceremony to a gnark SRS, and `cmd/solidity` exports gnark's Solidity
verifier for a serialized PLONK or Groth16 key.
Go builds without backend tags include both CPU backends. Selecting just
`plonk` or `groth16` excludes the other implementation and C exports; Cargo
supplies these tags from its feature selection.

The circuit binds the expected claim digest, outer pairing and deferred pairing
obligations. Its schema explicitly describes accumulator counts, claim rows and
public-input mappings.

## Build and use

Compression runs inside `ix`. `IX_PLONK=1` and `IX_GROTH16=1` select the
`plonk` and `groth16` features for the `ix` executable only; both are off by
default, and only builds with one of them link Go. CPU builds need Go and a C
compiler, but no CUDA toolkit:

```sh
IX_PLONK=1 IX_GROTH16=1 lake build ix
```

Install the released Ignition SRS as described in the
[compression setup guide](../../crates/proof-compression/README.md), then run:

```sh
ix compress ROOT_PROOF_ADDRESS --plonk --out /path/to/empty-output
```

Rust authenticates the setup and inner proof, selects the cache, calls gnark,
and publishes the native proof, Solidity payload, key and verifier contract.
The proof envelope is written last, after verification succeeds. Rerunning the
command with the same output directory reuses every stage whose proof still
verifies.

## CUDA

Enabling both `plonk` and `cuda` Cargo features enables GPU MSMs, FFTs and numerator
evaluation through gnark's upstream `Accelerator` interface. Gnark retains
quotient division, witness solving, randomness, transcript challenges, opening
construction, and verification. CPU and CUDA use the same module graph and
proof encodings.

```sh
export CUDA_HOME=/usr/local/cuda
export IX_KZG_CUDA_ARCHS=120
IX_CUDA=1 IX_PLONK=1 lake build ix
```

The KZG and PLONK kernels share `libix_bn254_cuda.so`, built against the configured
sppark dependency. Rust and cgo link that library; no source patching, private
sppark copy, or separate PLONK builder is involved. Cargo reports the runtime
libraries to Lake for installation beside `ix`.

`IX_KZG_CUDA_ARCHS` overrides `MULTI_STARK_CUDA_ARCHS`; otherwise the shared Rust
build helper detects GPU architectures and checks nvcc support.

PLONK proving uses CUDA when built with `IX_CUDA=1`; CPU-only builds use CPU.
`IX_PLONK_CUDA_DEVICE` selects the visible GPU ordinal; the default is zero.
`IX_PLONK_CUDA_MEMORY_GIB` sets the budget, defaulting to 64 GiB with 8 GiB
additional headroom. `IX_PLONK_CUDA_MSM_STRATEGY` accepts `split` (default) or
`mask`. `IX_CUDA` enables CUDA for Aiur, FRI, KZG, and final PLONK.

A loaded prover retains its keys and optional accelerator across calls. Rust
requires exclusive access for each proof and releases the Go handle on drop.
CUDA failures abort the proof; they do not select CPU fallback. Metrics on
stderr report arithmetic calls, transfers and memory use when the accelerator
closes. `IX_PLONK_CUDA_TRACE=1` enables callback diagnostics; DMA event timing
uses `IX_KZG_CUDA_PROFILE=1`.

The [stock gnark comparison](../../docs/proof-benchmark-comparison.md#stock-gnark-comparison)
records why the backend uses the upstream interface without fused extensions.

## Trust and artifacts

Rust owns artifact and Lagrange-cache metadata. Circuit caches bind the cache
format, verifier description, released setup and gnark's `go.sum`. Lagrange caches bind the setup,
domain and monomial receipt. Go checks the sizes and digests of decoded native
artifacts and rejects a witness whose claim differs from the independent digest
supplied by Rust. Retaining a prover avoids loading its circuit and keys again.

Default verification uses the bundled PLONK verifying key and its fixed Ignition anchors
(`crates/proof-compression/verifying-keys/`); a proof whose key identifier
names any other key is rejected. Verification requires neither a proving SRS
nor a GPU.

Circuit release tooling is library code: `pipeline::plonk::export` writes
the verifier description and witness for a recursive KZG packet, and
`pipeline::plonk::export_parameters` writes the selected final setup's SRS prefix.
Default `ix verify` uses the release keys; local final keys require an explicitly
pinned development verifier bundle.

Regenerate internal artifact metadata through the Rust preparation APIs when
changing implementations.

## Tests

```sh
cd tools/gnark
go test -tags plonk,groth16 ./...
```

Go tests cover circuit tampering, canonical encodings, exceptional MSM inputs,
small PLONK proofs, SRS/basis conversion and cache corruption. Rust FFI tests use
the authenticated Init proof and exercise bad claims, keys, proofs, buffers and
handles:

```sh
cargo test --release -p ix-proof-compression --no-default-features \
  --features parallel,plonk --lib pipeline::gnark::tests
```

The full compile and retained-prover tests are ignored by default. The latter
requires `IX_GNARK_INIT_ARTIFACTS`, `IX_GNARK_INIT_MANIFEST_SHA256`, and
`IX_GNARK_INIT_WITNESS`; run it explicitly only after budgeting memory and time.
The [contract guide](../../contracts/plonk/README.md) covers
Solidity verification of the unchanged proof encoding and regenerating its
verifier from the release key with `cmd/solidity`.

## BN254 Groth16 final

The `groth16` feature implements Groth16 over the same KZG verifier circuit and
witness schema. It compiles R1CS instead of PLONK's sparse constraints. The two
public inputs remain the little-endian 128-bit halves of the expected BLAKE3
claim digest. The circuit retains the outer and deferred KZG pairing checks.

The checked-in Init fixture compiles to 4,340,068 R1CS constraints, a `2^23`
QAP domain, and one commitment. Its native proof is 196 bytes, its Ix envelope
is 236 bytes, and its uncompressed Solidity payload is 384 bytes. The extra
commitment and its proof are part of the verified encoding. Development
verifying keys and a proof of this fixture are retained in
`crates/proof-compression/tests/fixtures/groth16`; they are not production keys.

### TODO: Reduce Groth16 commitment verification cost

Evaluate a commitment-free Groth16 circuit. The current gnark commitment
extension adds a separate two-pair pairing check costing **113,000 gas** and
128 bytes to the Solidity proof payload (384 bytes instead of the ordinary
256-byte A/B/C proof). The ordinary four-pair Groth16 equation costs another
181,000 gas. SHA-256's precompile cost in the measured proof is only 84 gas.

Anvil validation of normalized Nat.add_comm, Init and Mathlib under one key per
backend measured 320,286 execution gas for the Groth16 adapter and 275,438 for
PLONK. Total transaction gas was 348,262–348,298 and 311,070–311,118,
respectively. These measurements use Solidity 0.8.33, via-IR, 200 optimizer runs
and Prague; Groth16 uses development keys and PLONK uses Ignition. The adapters
receive a claim digest, so these costs exclude hashing raw claim bytes.
Receipts, traces and proof vectors are retained in
`target/final-solidity-20261029-xso7clim/` at the repository root.

SP1's Groth16 path uses direct bit constraints for range checks and an ordinary
A/B/C verifier. Ix also uses gnark's emulated BN254 arithmetic for KZG pairings,
whose deferred checks use commitments; replacing range checks alone may not
eliminate the extension. Any alternative must preserve both inner KZG pairing
obligations and claim binding. It needs new circuit-specific keys and Solidity
validation, with measurements of constraint count, proving cost and verification
gas. This optimization is deferred; the commitment checks remain required by
the current circuit and verifier.

### Preparing and using development keys

With `--dev-final-srs`, compression prepares and caches local keys automatically.
The underlying library functions can also prepare keys explicitly. Export an
already verified recursive KZG packet with the shared exporter
(`pipeline::plonk::export`), compile the Groth16 circuit from its `vk.json`
with `pipeline::groth16::compile`, then create development keys with
`pipeline::groth16::setup_development`.

The exporter takes the BLAKE3 digest that authenticates the serialized KZG
verifier file and the independently expected statement. It checks the selected
setup's released Ignition anchors or development class and verifies the inner proof.
Compilation writes a fresh circuit into an empty
artifact directory.

`IX_GROTH16_ARTIFACTS` optionally reuses the release circuit's prepared artifacts,
which must match its pins. For a different inner verifier, or without those
artifacts, development keys are generated and cached automatically:

```sh
ix compress /path/to/aggregate-proof.bin --groth16 \
  --dev-kzg-srs --dev-final-srs --out ./development-groth16
ix verify COMPRESSED_PROOF --dev-srs \
  --verifier-bundle ./development-groth16/groth16/development-verifier.json \
  --verifier-bundle-blake3 TRUSTED_BLAKE3_DIGEST
```

`--groth16` selects the proof system; `--dev-final-srs` permits its development
outer keys. `--dev-kzg-srs` is a separate inner-setup choice. Together the flags
need no Ignition parameters; the combination also works with `--plonk`.
PLONK's final powers and Lagrange parameters are independent of the inner KZG
verifier's parameters. A proof-file
input contains a serialized `Ixon.Proof`, including its claim, and is read without
importing it into the store. Verification's `--dev-srs` permits development proofs,
but an unknown final key also requires a separately pinned development bundle.
See [local development compression](../../docs/development-compression.md).
Rerunning `ix compress` into an output directory whose recursive KZG stage is
complete proves only the Groth16 stage.

Groth16 uses envelope tag `IXBN\0\0\0\x03`, followed by the 32-byte approved
verifying-key SHA-256 and canonical native proof. Verification is CPU-only and
requires neither proving parameters nor a visible GPU.

### Ceremony verification and key import

Production keys require a Groth16-compatible phase-one setup and a
circuit-specific phase two. Ignition's KZG SRS is not a Groth16 setup.

`pipeline::groth16::setup_mpc(artifacts, ceremony, trusted_sha256)` verifies each
phase-one and phase-two contribution against its predecessor, binds phase two
to the R1CS digest, applies the recorded beacons, and writes the resulting keys.
The descriptor includes the curve, domain, circuit digest, two 32-byte beacons,
and contribution paths with byte counts and SHA-256 receipts. Its exact schema
is defined by `groth16Ceremony` in `groth16_setup.go`.

`pipeline::groth16::import(artifacts, release, trusted_sha256)` imports an already
reviewed key bundle. The release binds both keys, the circuit and verifier-schema
hashes, the commitment hash, and the ceremony digest. Import relies on the
independently trusted release digest; it does not re-run the contribution chain.

A production key from such a ceremony replaces the bundled development key in
`crates/proof-compression/verifying-keys/`. The circuit, setup transcript
provenance, and resulting key must be independently reviewed first.
Contributions generated by one local test process are useful tests of the
setup machinery, not a production ceremony.

### CUDA

Groth16 uses stock gnark's BN254 ICICLE implementation, pinned to
`icicle-gnark` v3.2.2 (`b62bbbe518a73214da10ece26969ad55e6fa0cd0`). It accelerates
G1/G2 MSMs and QAP polynomial work. CPU and CUDA use the same serialized keys,
proof format, SHA-256 commitment hash, and CPU verifier.

```sh
export IX_GROTH16_BACKEND=cuda
export IX_GROTH16_DEVICE=0
```

ICICLE loads proving-key vectors on demand and frees their device memory after
use. Compression produces one proof per prover handle, so retaining the entire
key in VRAM would not save transfers across proofs and would increase its
persistent memory footprint.
Each prover handle stays on one device; operations and cleanup are serialized
per device. `ix` does not warm other GPUs or silently fall back to CPU.

Install ICICLE separately using the pinned revision above, with BN254, MSM,
NTT and G2 enabled. Lake and Cargo default to `/usr/local`, with core libraries
in `/usr/local/lib` and CUDA modules under `/usr/local/lib/backend`.
`IX_GROTH16_ICICLE_ROOT` optionally selects another installation prefix.
Then build with `IX_CUDA=1 IX_GROTH16=1 lake build ix` or Cargo features
`parallel,groth16,cuda`. Lake checks and tracks the library files, then copies
the libraries and backend plugins into `.lake/build/lib` beside `ix`; it does not
compile ICICLE. `ix` discovers the packaged backend first, with the
installation's `lib/backend` as a fallback; `ICICLE_BACKEND_INSTALL_DIR`
overrides that runtime selection. `.#icicle-bn254` builds the pinned ICICLE
with Nix. Verification remains CPU-only and does not initialize a device.

Rust parses device selection and key-pinning options and passes them explicitly
through FFI. The retained handle owns its native circuit, keys and device memory.
Artifact manifests are internal metadata; regenerate them with the library's
compile and setup functions when changing the implementation.

### Solidity and tests

`Groth16Verifier.sol` is generated from the exact verifying key, during key
preparation or with `go run ./cmd/solidity -system groth16 -key KEY -out FILE`.
The adapter in
`contracts/groth16/src/IxGroth16Verifier.sol` fixes its address and code hash,
converts the independently expected digest, and returns false for malformed
proofs. Verification calls have a bounded gas budget. The contract fixtures
cover plain Groth16 and the commitment-augmented Init wrapper.
The commitment hash must remain SHA-256 in proving, native verification and
Solidity export.

```sh
go test -tags groth16 -run '^TestGroth16(BackendInterop|BackendSelection|MPCAndAdmission)$' .
IX_GROTH16_CUDA_TEST=1 go test -tags groth16,icicle -run '^TestGroth16CUDAInterop$' .
cd contracts/groth16 && forge test
```

Rust tests verify the checked-in Init proof through FFI by default. The ignored
`pipeline::groth16::native_tests::compiles_init_without_changing_constraints`
checks the full circuit identity. `retained_init_prover_reuses_keys` uses prepared
keys in `IX_GROTH16_ARTIFACTS`, proves twice, checks independent verification,
and tests rejection and cleanup; it requires several GiB of memory.

The [performance record](../../docs/proof-benchmark-comparison.md) contains
the matched Init measurements and the stock-gnark decision.
