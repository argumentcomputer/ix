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
