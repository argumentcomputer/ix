# BLS12-381 and BN254 PLONK wrappers

This helper proves verification of an ix BLAKE3 KZG packet, including its
outer opening equation and its deferred pairing equation. Its only public
inputs are the expected claim digest, packed as two little-endian 128-bit
limbs. The trusted circuit fixes the inner verifying key and aggregation-program
prefix.

The implementation is experimental. The BLS conformance packets exercise small
circuits; the BN254 fixture comes from an authenticated Ignition Init proof.
Production verification keys need review of the complete circuit and its
measurements before authorization.

## Build and use through ix

Go 1.26.8 or newer is required for source builds. `lake build ix` builds the
native helper beside ix and its compression worker; `lake run install` installs
all three. `nix build .#ix` packages them, and `nix build .#plonk-wrapper` builds
and tests only this helper. Runtime proving and verification do not need Go or
Cargo installed.

`IX_KZG_CURVE=bn254 lake build ix` selects BN254 for the CLI, compression
worker and `ix-bn254-plonk-wrapper` helper. Set the same selection for
`lake run install`. Both helpers share this module; the `bn254` Go build tag
selects BN254, and the default build selects BLS12-381. The standalone Nix
helper package is `.#plonk-wrapper-bn254`; the default `.#ix` remains BLS.

```sh
export IX_KZG_FILECOIN_CACHE=/path/to/filecoin-prefix-2p27.bin
ix compress ROOT_PROOF_ADDRESS --plonk --out /path/to/empty-output
```

The existing ix setup configuration owns Filecoin selection and authentication.
`IX_KZG_FILECOIN_MANIFEST` selects an explicitly pinned cache receipt when using
a cache other than the standard `2^27` cache. Terminal PLONK rejects `--dev-srs`.
Key generation and Lagrange conversion are deterministic operations on these
public powers; they do not require a circuit-specific trusted ceremony.

The output's `plonk` directory contains the native proof, Solidity proof bytes,
generated verifier, public key and a candidate verifier catalog. `ix compress`
preserves the claim and stores a new proof address. Override the helper location
with `IX_PLONK_HELPER` if it is not beside the CLI/worker.

## Optional BN254 CUDA backend

CPU is the default. The experimental CUDA helper supports BN254 domains through
`2^24`, including the current Init circuit, with GPU MSMs, FFTs and a fused
PLONK quotient. Gnark retains witness solving, randomness, transcript challenges,
opening construction and verification. Proof encoding and the verifying key
are independent of the selected arithmetic backend.

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
IX_KZG_CURVE=bn254 IX_PLONK_CUDA=1 lake build ix_plonk_wrapper
```

The standalone equivalent is:

```sh
python3 tools/bls-plonk-wrapper/build_cuda.py \
  --out .lake/build/bin/ix-bn254-plonk-wrapper \
  --build-dir .lake/build/plonk-cuda \
  --sppark "$IX_PLONK_SPPARK_SOURCE" --blst "$IX_PLONK_BLST_SOURCE"
```

The build checks source receipts, applies the tracked gnark and sppark patches
to private build copies, and records executable/library hashes. It leaves
`go.mod` and the dependency caches unchanged. The native library is installed
in `../lib` relative
to the helper. Keep both artifacts together when installing; `lake run install`
does this when `IX_PLONK_CUDA=1`. The optional Nix package is
`.#plonk-wrapper-bn254-cuda`, targeting SM120. CPU packages remain independent of
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
quotient timing includes its internal transforms and host restoration. Pool
high-water marks exclude allocations outside the pool. Complete-process timing
also includes artifact authentication/loading and backend setup.
Queue wait and nested native timings overlap callback timings; they are not
independent stages to add to the total.
Set `IX_PLONK_CUDA_TRACE=1` for operation start/end diagnostics without scalar
values. Transfer counters cover explicit adapter transfers; internal sppark
result transfers may add traffic.

ABI7 reports per-callback transfer byte/call deltas and separates inclusive
transfer wall time, host staging and DMA event time. Wall time can include
previously queued kernels; host staging and DMA overlap. DMA timings are valid
only when `TransferTimingEnabled` is true. The shared transfer implementation
currently enables those events with `IX_KZG_CUDA_PROFILE=1`.

The opt-in full Init test supports `IX_PLONK_CUDA_INIT_MODES`,
`IX_PLONK_CUDA_INIT_REPEATS`, `IX_PLONK_CUDA_INIT_STAGE_PROFILE=1` and
`IX_PLONK_CUDA_INIT_CPU_PROFILE=1`, in addition to its required artifact/claim
pins. CPU sampling covers only the first selected proof; stage observation
covers every selected proof. Reports separate backend setup and profiler
startup/shutdown from core proving and record overlapping stage intervals.

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

The persistent worker protocol, immutable selector caching across proofs,
shared admission with KZG workers, and cancellation/restart policy are subsequent
service work.

## Authorize verification keys independently

Set `IX_PLONK_VERIFIER_CATALOG` to an independently trusted JSON catalog before
verifying a PLONK proof with `ix verify`. Generating a proof does not activate
its candidate catalog. Approving a key approves the circuit and fixed program
prefix represented by that key.

The generated `verifier-catalog.candidate.json` has the catalog schema and uses
a path relative to its directory for `verifying-key.bin`. It records the key's
SHA-256, inner verifying key, program prefix, circuit hash and helper hash. Review and
install accepted entries as trusted application configuration. Proof envelopes
carry only a key identifier and proof bytes; they cannot supply a trusted key.

Verification checks the selected key's digest and Filecoin G1/G2 anchors and
derives the expected public digest from the independently supplied ix claim.
It requires no proving SRS or GPU.

For BN254, the catalog format is `ix-bn254-plonk-verifiers-v1` and each key
has `setup: "ignition"`, an `admission` path and its independently trusted
`admission_blake3`. Verification authenticates that admission and checks the
key's Ignition anchors without loading the proving powers. Relative key and
admission paths resolve beside the catalog. The BN254 envelope is separately
tagged and cannot be accepted as a BLS proof.

## Standalone operations

`ix-compression-worker plonk export` authenticates a portable BLAKE3 verifying key,
verifies its packet against an independently expected statement, and exports
the fixed scalar program and canonical witness:

```sh
ix-compression-worker plonk export \
  vk.bin packet.bin TRUSTED_VERIFIER_BLAKE3 expected-statement.json input
ix-bls-plonk-wrapper compile input/vk.json artifacts
ix-bls-plonk-wrapper check-witness artifacts input/witness.json
```

`check-witness` is an assignment diagnostic, not a proof. It uses diagnostic
commitment challenges. Production `prove` uses gnark's real KZG commitment
computation and verifies the resulting PLONK proof before publishing it.

Read the padded `Domain` from `artifacts/manifest.json`, then export the required
parameters through ix:

```sh
ix-compression-worker plonk srs DOMAIN parameters.bin
ix-bls-plonk-wrapper prepare artifacts parameters.bin TRUSTED_EXPORT_BLAKE3
ix-bls-plonk-wrapper prove artifacts input/witness.json proof-output
ix-bls-plonk-wrapper verify \
  artifacts/verifying-key.bin TRUSTED_KEY_SHA256 \
  proof-output/proof.bin EXPECTED_CLAIM_DIGEST
```

The parameter export receipt is written beside `parameters.bin` as
`parameters.json`. Obtain `TRUSTED_EXPORT_BLAKE3` from that authenticated Rust
operation, independently of an untrusted parameter file. Gnark requires `N+3`
monomial powers and `N` Lagrange points; the adapter requests the next power of
two from ix and retains the ceremony's full public degree. Its current maximum
PLONK domain is `2^26` with the provisioned `2^27` cache.

Circuit and key artifacts bind the verifying key, executable and parameter receipt.
The helper checks hashes before reuse. Lagrange points are cached separately
by setup, domain, receipt and helper identity; `IX_PLONK_LAGRANGE_CACHE` can
select the shared directory. A changed executable needs a new artifact
directory. Corrupt artifacts fail closed.

## BN254 Ignition parameters and Lagrange import

BN254 uses the same commands with `ix-bn254-plonk-wrapper`. Export requires
`IX_KZG_IGNITION_CACHE`, `IX_KZG_IGNITION_CACHE_BLAKE3`,
`IX_KZG_IGNITION_ADMISSION` and `IX_KZG_IGNITION_ADMISSION_BLAKE3`, as described
in the [compression setup documentation](../../crates/proof-compression/README.md).
The provisioned `2^26` monomial cache supports PLONK domain `2^25`, which
requires `2^25+3` powers. The normal helper's classic-GLV Init wrapper has
14,689,440 constraints plus two public rows, fitting `2^24` with 2,087,774
rows to spare. The completed full proof benchmark below used the earlier
17,996,081-constraint configuration and domain `2^25`.

SP1 v6.1.0 publishes a legacy gnark `plonk_pk.bin` containing a `2^25`
Lagrange basis for the same Ignition anchors. It is an untrusted source of
candidate points. After compilation and authenticated monomial export, import
it before `prepare`:

```sh
ix-bn254-plonk-wrapper import-lagrange-sp1 \
  artifacts parameters.bin TRUSTED_EXPORT_BLAKE3 /path/to/plonk_pk.bin
ix-bn254-plonk-wrapper prepare artifacts parameters.bin TRUSTED_EXPORT_BLAKE3
```

The importer bounds lengths, validates point encodings, compares the setup
anchors and domain, and checks the complete candidate basis against the
authenticated monomial powers with a transcript-bound random linear relation.
That relation requires a scalar inverse FFT and two MSMs. The cache is
published only after it passes, with the candidate-vector digest and validation
evidence in `validation.json`. The error bound for a fixed incorrect basis is
at most `(N-1)/Fr` in the random-oracle model. SP1 circuit keys are discarded;
`prepare` generates ix's own proving and verifying keys. A basis for `2^25`
cannot be truncated into a `2^24` basis.

The import command requires an exact domain match. For the current `2^24`
circuit, `prepare` computes and caches a matching basis from the authenticated
monomial powers unless an independently validated matching cache is present.

Ordinary BN254 tests run with `go test -tags bn254 ./...`. They cover the real
Init verifier witness and tampering, Arkworks-compatible transcript encodings,
exceptional MSM inputs, small PLONK proofs, parameter caches and rejection of
incorrect imported bases and malformed SP1 key containers.

## Tests and sizing

```sh
cd tools/bls-plonk-wrapper
go test ./...
IX_PLONK_SIZE=1 go test -run TestComponentSizing -v
```

The ordinary tests cover BLAKE3 block/chunk/XOF boundaries, canonical curve
encodings, subgroup rejection, complete verifier witnesses, cached-parameter
integrity, basis conversion and small PLONK proofs using real Filecoin powers.
The small PLONK backend proof tests exercise `N=8`, separately from the full
verifier circuit.

The measured BLS full conformance verifier has 20,665,582 constraints, a `2^25`
domain and one extra committed polynomial. Point validation and public binding
account for about 3.21 million constraints, BLAKE3 adds 6.29 million, scalar
identities add 441, opening MSMs add 7.77 million, and the pairing checks add
about 1.70 million each. These are cumulative-compilation differences; shared
range checks can affect component accounting.

For that BLS fixture, even eliminating the second pairing check for free would
leave more than `2^24` constraints. BLS retains classic GLV; its tested
alternative increased the full count to 25,429,821.

BN254 also selects classic GLV, reducing its actual Init wrapper to
14,689,442 total rows while retaining separate pairings. The randomized
batching measurement variant reaches 13,810,186 rows with classic GLV; batching
with BN254's previous multiplication path reaches 17,530,148 rows. Batching
is experimental and is not selected by the normal helper. Reproduce sizing
with `IX_PLONK_SIZE=1 go test -tags bn254 -run TestOptimizationSizing -v`;
`IX_PLONK_SIZE_VK` selects a verifying key and `IX_PLONK_SIZE_REPORT` saves JSON.
`IX_PLONK_SIZE_VARIANT` can select `baseline`, `batched`, `classic-glv` or
`batched-classic-glv`. These are compilation results, separate from the
completed 2^25 proof benchmark.
`TestComponentSizing` accepts `baseline` or `classic-glv` for the component
breakdown; its default follows the normal helper's classic-GLV selection.

The backend is native CPU gnark at `262cf453c107d147a228b6b7418c5cf791c3b79b`.
Upstream experimental WebGPU/WASM PLONK acceleration exists, but this helper
does not activate it. The packaged native ICICLE/CUDA integration is for
Groth16.

## Full Init proof measurement

A full Filecoin/BLAKE3 Init packet was wrapped and verified on October 16,
2026, using 48 logical CPUs of a Xeon Platinum 8559C and 499 GiB RAM. The
actual Init wrapper has 21,184,618 constraints, a `2^25` domain, two public
inputs and one extra commitment.

With keys prepared, `plonk.Prove` took **127.17 seconds**; the fresh prove
process took **293.87 seconds**, including artifact authentication/loading,
verification and output. Peak prover RSS was **53.63 GiB**. In-memory native
verification took **2.75 ms**. Across seven fresh verifier processes,
decode/public-witness/verification took a median **4.20 ms** and complete
process wall time was **25.51 ms**. Wrong claims and a modified proof were
rejected.

The native proof is **744 bytes**, its ix envelope **784 bytes**, and the
Solidity encoding **1,184 bytes**. Solidity transaction gas was not measured.
One-time parameter/key preparation took **20m 17s**, including **18m 59s**
for Lagrange conversion and cache publication. Those costs, compilation,
SRS export and inner KZG proving are excluded from the proving figure.

The matching circuit, keys, parameter representations, frozen tools and proof
are archived in `s3://argument-kzg-params-063002298335-us-east-1-an/`
(`us-east-1`) under
`bls12-381/plonk/init/2p25/73d8ebbad3df955310fcf7c8b7d35cf04f6ecd5be513f55af25036b7349e5299/`.
Its `MANIFEST.json` has SHA-256
`6be357f686599d283acca68e6eb4a9aa9f29c31d0010e7c8190f5767a04daaee`; the
archive's `verify_bundle.py --manifest-sha256` authenticates a restored copy.

The earlier 2^25 configuration of the actual Ignition/BLAKE3 Init packet
proved and verified with BN254:
**104.33 seconds** core proving, **143.59 seconds** for the fresh prover process,
**47.18 GiB** peak RSS and **1.20 ms** in-memory native verification. Seven fresh
verifier processes had medians of **1.92 ms** for decode/public-witness/verify
and **21.70 ms** including startup and key loading. The native proof is
**584 bytes**, its ix envelope **624 bytes**, and the Solidity encoding
**864 bytes**. Prepared keys were excluded from these proof timings.

Full validation and cache publication of SP1's `2^25` Lagrange basis took
**27.70 seconds**, followed by **63.55 seconds** for parameter loading and ix
circuit-key preparation. This avoids computing the group FFT locally; the
setup-time difference from the BLS run is not a curve-speed comparison.

The current **2^24 classic-GLV configuration**, retaining separate pairing
checks, proves the same Init packet in **53.79 seconds** for core proving and
**73.70 seconds** for the complete fresh process. Peak prover RSS is
**25.19 GiB**. Native in-memory verification took **1.49 ms**; seven fresh
verifier processes had medians of **1.81 ms** for decode/public-witness/verify
and **22.52 ms** including startup and key loading. Proof sizes remain
**584 bytes native**, **624 bytes enveloped** and **864 bytes for Solidity**.

Local 2^24 parameter/key preparation took **5m 58s**, including **5m 25s** for
Lagrange conversion/cache publication. These artifacts are now cached; all
preparation is excluded from proof timings. The proof and independent native
and catalog verification passed, including negative-input checks.

The same BN254 proof passes Solidity verification on local Anvil using SP1's
v6.1.0 verifier with only its 23 circuit-key constants changed. Total receipt
gas is **316,003** directly or **320,103** through ix's expected-claim adapter,
including transaction intrinsic/calldata gas. All 47 compatibility and
negative-input checks passed. See the
[Anvil reproduction and gas breakdown](../../contracts/plonk/README.md#actual-bn254-init-proof-on-anvil).
