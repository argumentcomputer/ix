# BN254 terminal gnark backends

This Go module implements the terminal Ix verifier circuit and calls stock
gnark. Cargo builds it as a C archive inside `ix-compression-worker`;
`pipeline/gnark.rs` owns the Rust bindings and loaded prover handles.
There is no separate Go executable.

The circuit binds the expected claim digest and checks outer and deferred
pairing obligations. It uses classic GLV, separate pairing checks, and explicit
`accumulatorCount`, `claims`, and `publics` in the verifier description.

## Build and use

`lake build ix` builds the Lean CLI and native Rust compression worker. The
worker enables `plonk` and `groth16`; the Lean-facing `ix-ffi` library does not. CPU
builds need Go and a C compiler, but no CUDA toolkit. A direct worker build is:

```sh
cargo build --release -p ix-proof-compression --bin ix-compression-worker \
  --no-default-features --features parallel,plonk,groth16
```

Configure the four Ignition environment variables from the
[compression setup guide](../../crates/proof-compression/README.md), then run:

```sh
ix compress ROOT_PROOF_ADDRESS --plonk --out /path/to/empty-output
```

Rust authenticates the setup and inner proof, selects the cache, calls gnark,
and publishes the native proof, Solidity payload, key, verifier contract,
admission, and candidate catalog. The proof envelope is written last, after
verification succeeds. `IX_COMPRESSION_WORKER` overrides the worker location.
Nix provides `.#compression-worker`, `.#compression-worker-cuda`, and
`.#ix`.

## CUDA

Enabling both `plonk` and `cuda` Cargo features enables GPU MSMs, FFTs and numerator
evaluation through gnark's upstream `Accelerator` interface. Gnark retains
quotient division, witness solving, randomness, transcript challenges, opening
construction, and verification. CPU and CUDA use the same module graph and
proof encodings.

```sh
export CUDA_HOME=/usr/local/cuda
export IX_PLONK_CUDA_ARCHS=120
IX_CUDA=1 lake build ix
```

Cargo obtains the pinned sppark and BLST sources from its `cuda` dependencies. `IX_PLONK_SPPARK_SOURCE` and
`IX_PLONK_BLST_SOURCE` optionally override those roots. Alternatively,
`IX_PLONK_CUDA_LIBRARY` names an already-built `libix_plonk_bn254_cuda.so`.
Lake installs that library beside the worker in `../lib`. Nix supplies its
pinned native library directly. Primitive source ownership and build details
are in `crates/proof-compression/cuda/plonk`.

Select execution separately with `IX_PLONK_BACKEND=cpu` or `cuda`.
`IX_PLONK_CUDA_DEVICE` selects the visible GPU ordinal; the default is zero.
`IX_PLONK_CUDA_MEMORY_GIB` sets the budget, defaulting to 64 GiB with 8 GiB
additional headroom. `IX_PLONK_CUDA_MSM_STRATEGY` accepts `split` (default) or
`mask`. `IX_CUDA` enables CUDA for Aiur, FRI, KZG, and terminal PLONK.

A loaded prover retains its keys and optional accelerator across calls. Rust
requires exclusive access for each proof and releases the Go handle on drop.
CUDA failures abort the proof; they do not select CPU fallback. Metrics on
stderr report arithmetic calls, transfers and memory use when the accelerator
closes. `IX_PLONK_CUDA_TRACE=1` enables callback diagnostics; DMA event timing
uses `IX_KZG_CUDA_PROFILE=1`.

The [stock gnark comparison](../../docs/proof-benchmark-comparison.md#stock-gnark-comparison)
records why the backend uses the upstream interface without fused extensions.

## Trust and artifacts

Rust owns artifact and Lagrange-cache metadata. Circuit caches bind the worker
build, verifier description and admitted setup. Lagrange caches bind the setup,
domain and monomial receipt. Go checks the sizes and digests of decoded native
artifacts and rejects a witness whose claim differs from the independent digest
supplied by Rust. Retaining a prover avoids loading its circuit and keys again.

`IX_PLONK_VERIFIER_CATALOG` selects an independently authorized catalog. A proof's
candidate catalog is not automatically trusted. Entries bind the verifying-key
SHA-256, inner verifier identity, program prefix, circuit hash, and Ignition
admission. Verification requires neither a proving SRS nor a GPU.

The worker retains the `plonk export`, `export-first`, `srs`, `wrap`, and
`verify` commands. For example:

```sh
ix-compression-worker plonk verify proof.envelope.bin claim.bin
```

Internal metadata has no helper-executable identity. Rebuild old artifact caches
and regenerate candidate catalogs instead of editing or translating them.

## Tests

```sh
cd tools/plonk-wrapper
go test ./...
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
The Go `TestBN254CUDAInit` remains an opt-in arithmetic integration/profiling
entry point. The [contract guide](../../contracts/plonk/README.md) covers
Solidity verification of the unchanged proof encoding.

## BN254 Groth16 terminal

The worker also implements `groth16` over the same KZG verifier circuit and
witness schema. It compiles R1CS instead of PLONK's sparse constraints. The two
public inputs remain the little-endian 128-bit halves of the expected BLAKE3
claim digest. The circuit retains the outer and deferred KZG pairing checks.

The checked-in Init fixture compiles to 4,340,068 R1CS constraints, a `2^23`
QAP domain, and one commitment. Its native proof is 196 bytes, its Ix envelope
is 236 bytes, and its uncompressed Solidity payload is 384 bytes. The extra
commitment and its proof are part of the verified encoding. Development
verifying keys and a proof of this fixture are retained in
`crates/proof-compression/tests/fixtures/groth16`; they are not production keys.

### Preparing and using development keys

Export an already verified recursive KZG packet with the existing shared
exporter, then compile the Groth16 circuit:

```sh
ix-compression-worker groth16 export verifier.bin packet.bin TRUSTED_VERIFIER_BLAKE3 expected-statement.json input
ix-compression-worker groth16 compile input/vk.json groth16-keys
ix-compression-worker groth16 setup-development groth16-keys
ix-compression-worker groth16 prove groth16-keys input/witness.json EXPECTED_CLAIM_DIGEST proof
```

`TRUSTED_VERIFIER_BLAKE3` authenticates the serialized KZG verifier file.
`EXPECTED_CLAIM_DIGEST` is obtained independently of the witness. The exporter
requires admitted Ignition parameters for the inner KZG proof; local Groth16
setup does not change the inner setup policy. Compilation writes a fresh
circuit into an empty artifact directory.

The CLI uses prepared keys and an independently approved catalog:

```json
{
  "format": "ix-bn254-groth16-verifiers-v1",
  "keys": [{
    "sha256": "SHA256_OF_GROTH16_VERIFYING_KEY",
    "path": "groth16-keys/verifying-key.bin",
    "inner_vk_id": "VK_ID_FROM_EXPORTED_vkId",
    "inner_schema_sha256": "SHA256_OF_EXPORTED_vk.json",
    "statement_prefix": [0, 293, 0, 0, 0, 0, 0, 0, 0, 0],
    "circuit_sha256": "SHA256_OF_circuit.bin",
    "setup": "development"
  }]
}
```

The hashes above are placeholders. Copy the complete ten-word `prefix` from
the exported verifier description; the example prefix is not an approved
program. `inner_vk_id` is the description's `vkId`, which differs from the
BLAKE3 digest of the serialized verifier file. Relative key paths resolve against
the catalog directory. A proof or generated manifest never authorizes its own
verifying key.

```sh
export IX_GROTH16_ARTIFACTS=/path/to/groth16-keys
export IX_GROTH16_VERIFIER_CATALOG=/path/to/approved-catalog.json
ix compress ROOT --groth16 --dev-groth16
ix verify COMPRESSED_PROOF --dev-srs
```

`--dev-groth16` permits development outer keys and requires `--groth16`.
`--dev-srs` on verification is the existing permission for development proofs.
A saved recursive packet can be wrapped directly, avoiding earlier stages:

```sh
ix-compression-worker groth16 wrap verifier.bin packet.bin TRUSTED_VERIFIER_BLAKE3 expected-statement.json output --allow-development
ix-compression-worker groth16 verify output/proof.envelope.bin claim.bin --allow-development
```

Groth16 uses envelope tag `IXBN\0\0\0\x03`, followed by the 32-byte approved
verifying-key SHA-256 and canonical native proof. Verification is CPU-only and
requires neither proving parameters nor a visible GPU.

### Ceremony verification and key import

Production keys require a Groth16-compatible phase-one setup and a
circuit-specific phase two. Ignition's KZG cache is not a Groth16 setup.

`groth16 setup-mpc <artifacts> <ceremony.json> <trusted-sha256>` verifies each
phase-one and phase-two contribution against its predecessor, binds phase two
to the R1CS digest, applies the recorded beacons, and writes the resulting keys.
The descriptor includes the curve, domain, circuit digest, two 32-byte beacons,
and contribution paths with byte counts and SHA-256 receipts. Its exact schema
is defined by `groth16Ceremony` in `groth16_setup.go`.

`groth16 import <artifacts> <release.json> <trusted-sha256>` imports an already
reviewed key bundle. The release binds both keys, the circuit and verifier-schema
hashes, the commitment hash, and the ceremony digest. Import relies on the
independently trusted release digest; it does not re-run the contribution chain.

Production catalog entries use `"setup": "mpc"` and a `ceremony_sha256` field.
The circuit, setup transcript provenance, and resulting key must be independently
admitted before adding that entry. Contributions generated by one local test
process are useful tests of the setup machinery, not a production ceremony.

### CUDA

Groth16 uses stock gnark's BN254 ICICLE implementation, pinned to
`icicle-gnark` v3.2.2 (`b62bbbe518a73214da10ece26969ad55e6fa0cd0`). It accelerates
G1/G2 MSMs and QAP polynomial work. CPU and CUDA use the same serialized keys,
proof format, SHA-256 commitment hash, and CPU verifier.

```sh
nix build .#compression-worker-cuda
export IX_COMPRESSION_WORKER="$PWD/result/bin/ix-compression-worker"
export IX_GROTH16_BACKEND=cuda
export IX_GROTH16_DEVICE=0
export IX_GROTH16_PIN_KEY=1
```

`IX_GROTH16_PIN_KEY` defaults to `0`, streaming key vectors as needed. Set it to
`1` only when persistent key vectors and working memory fit on the selected GPU.
Each prover handle stays on one device; operations and cleanup are serialized
per device. The worker does not warm other GPUs or silently fall back to CPU.

For a manual ICICLE installation, build only BN254 with MSM, NTT and G2 enabled,
using the pinned revision above. Set `IX_GROTH16_ICICLE_ROOT` to its installation
prefix, then build with `IX_CUDA=1 lake build ix` or Cargo features
`parallel,plonk,groth16,cuda`. The native build checks the libraries and packages
both the core libraries and CUDA backend modules beside the worker. Nix supplies
these dependencies in `.#compression-worker-cuda`; `.#icicle-bn254` builds ICICLE
alone. Verification remains CPU-only and does not initialize a device.

Rust parses device selection and key-pinning options and passes them explicitly
through FFI. The retained handle owns its native circuit, keys and device memory.
Artifact manifests are internal metadata; regenerate them with the worker's
compile/setup commands when changing the implementation.

### Solidity and tests

`Groth16Verifier.sol` is generated from the exact verifying key. The adapter in
`contracts/groth16/src/IxGroth16Verifier.sol` fixes its address and code hash,
converts the independently expected digest, and returns false for malformed
proofs. Verification calls have a bounded gas budget. The contract fixtures
cover plain Groth16, commitment-augmented Groth16, and the actual Init wrapper.
The commitment hash must remain SHA-256 in proving, native verification and
Solidity export.

```sh
go test -run '^TestGroth16(BackendInterop|BackendSelection|MPCAndAdmission)$' .
IX_GROTH16_CUDA_TEST=1 go test -tags icicle -run '^TestGroth16CUDAInterop$' .
cd contracts/groth16 && forge test
```

Rust tests verify the checked-in Init proof through FFI by default. The ignored
`pipeline::groth16::native_tests::compiles_init_without_changing_constraints`
checks the full circuit identity. `retained_init_prover_reuses_keys` uses prepared
keys in `IX_GROTH16_ARTIFACTS`, proves twice, checks independent verification,
and tests rejection and cleanup; it requires several GiB of memory.
The matched performance harness is `TestBN254TerminalComparison`. It accepts
`IX_TERMINAL_COMPARE=1`, `IX_TERMINAL_COMPARE_OUT`,
`IX_TERMINAL_GROTH16_ARTIFACTS`, and optionally
`IX_TERMINAL_PLONK_ARTIFACTS` plus `IX_TERMINAL_PLONK_MANIFEST_SHA256` to reuse
an authenticated PLONK cache for the identical verifier schema. Select systems
and devices with `IX_TERMINAL_COMPARE_SYSTEMS` and
`IX_TERMINAL_COMPARE_DEVICES`; `IX_TERMINAL_COMPARE_REPEATS` defaults to three.
It separates opening the retained key/circuit, the first proof, warm proofs,
and verification. Proving includes gnark's witness solving; earlier Ix/KZG
stages and witness export are excluded. Compare CPU and GPU proofs by acceptance
and statement, not by bytes, because proofs are randomized.

### Matched Init terminal measurements

Measured on 2026-10-29 with Go 1.26.8, 32 logical CPUs and an RTX PRO 6000
Blackwell Server Edition. Both systems use exactly the same checked-in Init
verifier description and witness. Values are medians of three warm proofs in
separate processes at default parallelism; no other GPU compute process was
present when either CUDA run started.

| Backend | CPU proving | CUDA proving | Native proof | Ix envelope | Solidity payload |
| --- | ---: | ---: | ---: | ---: | ---: |
| Groth16 | 7.35 s | 2.61 s | 196 B | 236 B | 384 B |
| PLONK | 66.07 s | 11.59 s | 584 B | 624 B | 864 B |

Groth16 CUDA uses ICICLE with pinned key vectors; PLONK CUDA uses the existing
sppark adapter and retained bases. Proving includes gnark witness solving.
Opening the key/circuit takes about 27 seconds for Groth16 and 22 seconds for
PLONK, separately from the table. Earlier compression stages and witness export
are excluded. Groth16 uses development keys; PLONK reuses its pinned Ignition
cache. These are one-workload measurements, not predictions for every circuit.
Raw samples, file identities, opening times and peak process RSS are recorded
in `testdata/terminal-comparison.json`. The actual Groth16 Init proof also passes
the Solidity adapter test, at 318,490 execution gas excluding transaction
intrinsic gas and calldata.
