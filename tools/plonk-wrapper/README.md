# BN254 PLONK wrapper

This helper proves the exported Ix KZG verifier using BN254 PLONK. It binds
the expected claim digest and checks both outer and deferred pairing
obligations. The checked-in verifier witness comes from an authenticated
Ignition Init proof.

## Build and use through ix

`lake build ix` builds the CLI, compression worker, and
`ix-bn254-plonk-wrapper`. The Go module builds BN254 unconditionally;
the optional `cuda` tag enables GPU arithmetic. Nix provides
`.#plonk-wrapper`, `.#plonk-wrapper-cuda`, and the complete `.#ix` CLI.

Configure `IX_KZG_IGNITION_CACHE`, `IX_KZG_IGNITION_CACHE_BLAKE3`,
`IX_KZG_IGNITION_ADMISSION`, and `IX_KZG_IGNITION_ADMISSION_BLAKE3` using the
[compression setup guide](../../crates/proof-compression/README.md).

```sh
ix compress ROOT_PROOF_ADDRESS --plonk --out /path/to/empty-output
```

Terminal PLONK requires authenticated ceremony parameters. The output's
`plonk` directory contains native/Solidity proofs, the generated verifier,
verifying key, admission, and candidate verifier catalog. `IX_PLONK_HELPER`
can override the executable location.

## Optional BN254 CUDA backend

CPU is the default. The experimental CUDA helper supports BN254 domains through
`2^24`, including the current Init circuit, with GPU MSMs, FFTs and PLONK
numerator evaluation through stock gnark's `Accelerator` interface. CPU and CUDA
builds use the same pinned `go.mod` and `go.sum`. Gnark retains quotient division,
witness solving, randomness, transcript challenges, opening construction and
verification. Proof encoding and the verifying key are independent of the
selected arithmetic backend.

The source build uses explicit copies of sppark revision
`114feb69ebfe029e2caa5e6c2d372c695e5d4da8` and blst 0.3.16. The blst source root
must contain `src/server.c` and `build/assembly.S`. No Rust build archive is
required. Provide these source roots and a CUDA toolkit supporting the chosen
GPU architecture:

```sh
export IX_PLONK_SPPARK_SOURCE=/path/to/pinned-sppark
export IX_PLONK_BLST_SOURCE=/path/to/blst-0.3.16/blst
export CUDA_HOME=/usr/local/cuda
export NVCC="$CUDA_HOME/bin/nvcc"
export IX_PLONK_CUDA_ARCHS=120
IX_PLONK_CUDA=1 lake build ix_plonk_wrapper
```

The standalone equivalent is:

```sh
python3 tools/plonk-wrapper/build_cuda.py \
  --out .lake/build/bin/ix-bn254-plonk-wrapper \
  --build-dir .lake/build/plonk-cuda \
  --sppark "$IX_PLONK_SPPARK_SOURCE" --blst "$IX_PLONK_BLST_SOURCE"
```

The native build checks source receipts and applies the tracked sppark patch
to a private build copy. The helper uses ordinary `go build -tags=cuda` against
the pinned upstream modules and records executable/library hashes. The native
library is installed in `../lib` relative to the helper. Keep both artifacts together when installing; `lake run install`
does this when `IX_PLONK_CUDA=1`. The optional Nix package is
`.#plonk-wrapper-cuda`, targeting SM120. CPU packages remain independent of
the CUDA toolkit.

Select the runtime backend separately from building it:

```sh
CUDA_VISIBLE_DEVICES=0 IX_PLONK_BACKEND=cuda \
  .lake/build/bin/ix-bn254-plonk-wrapper prove artifacts input/witness.json proof-output
```

`IX_PLONK_CUDA_DEVICE` selects the visible ordinal (default 0), and
`IX_PLONK_CUDA_MEMORY_GIB` sets the allocation budget (default 64 GiB), with
8 GiB additional device headroom. Use one visible physical GPU per helper.
`IX_PLONK_CUDA` does not imply the inner prover's `IX_CUDA`, or vice versa.
Requesting CUDA from a CPU-only helper fails explicitly. CUDA errors abort that
proof; they do not silently switch its arithmetic to CPU.

The helper emits callback times, dispatch counts, transferred bytes, allocation
accounting and CUDA pool high-water marks. Callback times include transfers;
numerator timing includes its internal transforms and host restoration. Pool
high-water marks exclude allocations outside the pool. Complete-process timing
also includes artifact authentication/loading and backend setup.
Queue wait and nested native timings overlap callback timings; they are not
independent stages to add to the total.
Set `IX_PLONK_CUDA_TRACE=1` for operation start/end diagnostics without scalar
values. Transfer counters cover explicit adapter transfers; internal sppark
result transfers may add traffic.

Transfer metrics report per-callback byte/call deltas and separate inclusive
transfer wall time, host staging and DMA event time. Wall time can include
previously queued kernels; host staging and DMA overlap. DMA timings are valid
only when `TransferTimingEnabled` is true. The shared transfer implementation
currently enables those events with `IX_KZG_CUDA_PROFILE=1`.

The opt-in full Init test supports `IX_PLONK_CUDA_INIT_MODES=cpu,cuda`,
`IX_PLONK_CUDA_INIT_REPEATS` and `IX_PLONK_CUDA_INIT_CPU_PROFILE=1`, in addition
to its required artifact/claim pins. CPU sampling covers only the first selected
proof. Reports separate backend setup and profiler startup/shutdown from core
proving.

`IX_PLONK_CUDA_MSM_STRATEGY=split` is the default: large Pippenger buckets are
split into bounded tasks while retaining the zero and ±1 fast paths. The
explicit `mask` comparison strategy computes `MSM(s+r)-MSM(r)` and caches its
correction points by registered range. Neither path applies whole-scalar
affine normalization. Both preserve the original commitment exactly.

Artifact manifests still bind their producer executable. Compile and prepare
artifacts with the frozen helper used for proving; CPU/CUDA mode changes within
that helper do not require different keys. A changed helper does not authorize
editing an old manifest. The full Init test harness accepts an independently
pinned existing manifest without changing production loading rules.

The [stock gnark comparison](../../docs/proof-benchmark-comparison.md#stock-gnark-comparison)
records the Init measurements behind the upstream integration choice.

The persistent worker protocol, immutable selector caching across proofs,
shared admission with KZG workers, and cancellation/restart policy remain
future service work.

## Authorize verification keys independently

`IX_PLONK_VERIFIER_CATALOG` names an independently trusted JSON catalog.
Generating a proof does not authorize its candidate catalog. The format is
`ix-bn254-plonk-verifiers-v1`; entries use `setup: "ignition"` and pin the
verifying-key SHA-256, inner verifying-key identity, program prefix, circuit
hash, helper hash, and Ignition admission BLAKE3 digest. Relative paths are
resolved beside the catalog. Verification needs neither a proving SRS nor a
GPU, and derives the expected public digest from the caller's claim.

## Standalone operations

`ix-compression-worker plonk export` authenticates a portable BLAKE3 verifying key,
verifies its packet against an independently expected statement, and exports
the fixed scalar program and canonical witness:

```sh
ix-compression-worker plonk export \
  vk.bin packet.bin TRUSTED_VERIFIER_BLAKE3 expected-statement.json input
ix-bn254-plonk-wrapper compile input/vk.json artifacts
ix-bn254-plonk-wrapper check-witness artifacts input/witness.json
```

`check-witness` is an assignment diagnostic, not a proof. It uses diagnostic
commitment challenges. Production `prove` uses gnark's real KZG commitment
computation and verifies the resulting PLONK proof before publishing it.

Read the padded `Domain` from `artifacts/manifest.json`, then export the required
parameters through ix:

```sh
ix-compression-worker plonk srs DOMAIN parameters.bin
ix-bn254-plonk-wrapper prepare artifacts parameters.bin TRUSTED_EXPORT_BLAKE3
ix-bn254-plonk-wrapper prove artifacts input/witness.json proof-output
ix-bn254-plonk-wrapper verify \
  artifacts/verifying-key.bin TRUSTED_KEY_SHA256 \
  proof-output/proof.bin EXPECTED_CLAIM_DIGEST
```

The parameter export receipt is written beside `parameters.bin` as
`parameters.json`. Obtain `TRUSTED_EXPORT_BLAKE3` from that authenticated Rust
operation, independently of an untrusted parameter file. Gnark requires `N+3`
monomial powers and `N` Lagrange points; the adapter requests the next power of
two from ix and retains the ceremony's full public degree. Its current maximum
PLONK domain is `2^26` when a sufficient authenticated parameter prefix is available.

Circuit and key artifacts bind the verifying key, executable and parameter receipt.
The helper checks hashes before reuse. Lagrange points are cached separately
by setup, domain and monomial receipt; `IX_PLONK_LAGRANGE_CACHE` can
select the shared directory. A changed executable needs a new artifact
directory. Corrupt artifacts fail closed.

## BN254 Ignition parameters

Export requires `IX_KZG_IGNITION_CACHE`, `IX_KZG_IGNITION_CACHE_BLAKE3`,
`IX_KZG_IGNITION_ADMISSION` and `IX_KZG_IGNITION_ADMISSION_BLAKE3`, as described
in the [compression setup documentation](../../crates/proof-compression/README.md).
The provisioned `2^26` monomial cache supports PLONK domain `2^25`, which
requires `2^25+3` powers. The Init wrapper uses classic GLV and separate pairing
checks: 14,689,440 constraints plus two public rows fit a `2^24` domain.
`prepare` derives and caches its Lagrange basis from the authenticated monomial
powers. The exported verifier must explicitly supply `accumulatorCount`,
`claims`, and `publics`.

## Tests

```sh
cd tools/plonk-wrapper
go test ./...
```

The ordinary tests cover Blake3 boundaries, canonical point encodings,
the actual Init verifier witness and tampering, exceptional MSM inputs,
small PLONK proofs, explicit verifier schemas, and parameter-cache integrity.
The opt-in full Init test above is the common CPU/CUDA profiling and integration
entry point. Its loader validates the supplied artifact dimensions instead of
assuming a fixed historical constraint count.

Current Init proofs use a `2^24` PLONK domain. Recorded native, envelope, and
Solidity proof sizes are 584, 624, and 864 bytes. See the
[benchmark comparison](../../docs/proof-benchmark-comparison.md) for hardware,
timings, and measurement boundaries, and the
[contract guide](../../contracts/plonk/README.md) for on-chain validation.

## BN254 Groth16 terminal

The helper also implements `groth16` over the same KZG verifier circuit and
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
ix-bn254-plonk-wrapper groth16 compile input/vk.json groth16-keys
ix-bn254-plonk-wrapper groth16 setup-development groth16-keys
ix-bn254-plonk-wrapper groth16 prove groth16-keys input/witness.json EXPECTED_CLAIM_DIGEST proof
```

`TRUSTED_VERIFIER_BLAKE3` authenticates the serialized KZG verifier file.
`EXPECTED_CLAIM_DIGEST` is obtained independently of the witness. The exporter
requires admitted Ignition parameters for the inner KZG proof; local Groth16
setup does not change the inner setup policy. Explicit compilation checks a
fresh circuit digest before reusing an existing artifact directory.

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
nix build .#groth16-wrapper-cuda
export IX_GROTH16_HELPER="$PWD/result/bin/ix-bn254-plonk-wrapper"
export IX_GROTH16_BACKEND=cuda
export IX_GROTH16_DEVICE=0
export IX_GROTH16_PIN_KEY=1
```

`IX_GROTH16_PIN_KEY` defaults to `0`, streaming key vectors as needed. Set it to
`1` only when persistent key vectors and working memory fit on the selected GPU.
Each prover handle stays on one device; operations and cleanup are serialized
per device. The helper does not warm other GPUs or silently fall back to CPU.

For a manual ICICLE installation, build only BN254 with MSM, NTT and G2 enabled,
and use the native source revision above. Then:

```sh
python3 tools/plonk-wrapper/build_groth16_cuda.py --out /path/to/bin/ix-bn254-plonk-wrapper --icicle-root /persistent/icicle-installation
```

The installation remains a runtime dependency. `IX_GROTH16_ICICLE_ROOT` supplies
it to Lake when `IX_GROTH16_CUDA=1`. The terminal CUDA choice is independent of
`IX_CUDA` and `IX_PLONK_CUDA`. `.#terminal-wrapper-cuda` includes both terminal
accelerators; `.#icicle-bn254` builds the native dependency alone. These CUDA
packages target Linux x86-64 and SM 120. CPU-only builds require no CUDA libraries.

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

The full CPU fixture check is opt-in with `IX_GROTH16_WRAPPER_TEST=1` and
`IX_GROTH16_WRAPPER_PROVE=1`; it includes local setup and takes several minutes.
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
