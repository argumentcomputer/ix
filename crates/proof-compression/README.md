# Ix proof compression

The pipeline is Goldilocks/Blake3 FRI → BN254 KZG → recursive BN254 KZG,
with an optional final BN254 PLONK or Groth16 proof. FRI uses Goldilocks and its
quadratic extension with Blake3 Merkle commitments. Curve arithmetic starts
when the FRI verifier is translated into BN254 scalar-field constraints.

BN254 is unconditional, including builds with `--no-default-features`.
The main Cargo features are `parallel`, `plonk`, `groth16`, and `cuda`. Either
final feature builds one shared gnark C archive. Combining a final
feature with `cuda` enables its GPU backend.
Compression runs inside `ix`. Lake enables the final features only for the
`ix` executable, so other executables and tests never compile Go.

```sh
lake build ix
IX_CUDA=1 lake build ix
IX_CUDA=1 IX_PLONK=1 IX_GROTH16=1 lake build ix
```

Lake's switches select these Cargo features: `IX_PLONK` and
`IX_GROTH16` (both off by default, so compression ends at the ~2.1 KB
recursive KZG proof and the default build needs no Go) select the final
backends, and `IX_CUDA`
enables CUDA for Aiur, FRI, KZG, and each selected final backend. Native
BN254 arithmetic uses shared sppark/BLST support, and Rust calls stock gnark
through its C archive. Groth16 CUDA links a separately installed, pinned ICICLE.
Lake and Cargo default to `/usr/local`; `IX_GROTH16_ICICLE_ROOT` overrides the
installation prefix. Core libraries belong in `<prefix>/lib` and CUDA modules
in `<prefix>/lib/backend`. Lake validates and copies those libraries into
`.lake/build/lib` beside `ix`. Provision ICICLE before building Ix; Lake does
not compile it. Nix builds the pinned installation as `.#icicle-bn254`.
Those libraries may contain other curves; Ix exposes only BN254.

KZG uses authenticated Ignition parameters or explicit known-trapdoor
development parameters. Final setup is independent: PLONK defaults to Ignition,
while `--dev-final-srs` prepares local keys for either PLONK or Groth16. With
`--dev-kzg-srs` as well, neither stage needs Ignition.
Default verification pins one version of the verifying keys,
[`0.1`](verifying-keys/0.1): one key per proof system, with the root layout,
statement prefix and Ignition parameters they were derived for. `ix verify` selects the key by the proof's tag and requires
the packet's key identifier to name it; there is no catalog of alternatives.
Bundled recursive KZG and PLONK proofs verify under Ignition. The release Groth16 key
comes from a development setup, so Groth16 proving requires `--dev-final-srs`
and verification requires `--dev-srs`. Use
`ix compress PROOF --groth16 --dev-final-srs`, where `PROOF` is a
store address or a serialized `Ixon.Proof` file containing its claim. File
inputs are read without importing them into the store. See the
[final backend guide](../../tools/gnark/README.md#bn254-groth16-final).
The library's `verify_with_vk` can
verify recursive KZG proofs under an independently pinned key and statement.
Local final keys use `verify_with_development_verifier`. The CLI requires
`--verifier-bundle`, its independent `--verifier-bundle-blake3` pin, and
`--dev-srs`; see [local development compression](../../docs/development-compression.md).

BN254 supports radix-2 domains through `2^28`; traces and quotient domains
must both fit. Existing BN254 proof and verifier encodings are retained.

## Ignition setup

The released recursive KZG and PLONK verifying keys fix the approved Ignition
parameters. Verification needs no SRS file, source manifest or admission JSON.
Proving loads a prefix of the release's standard gnark `SRS.WriteRawTo` file:

```sh
ix compress setup
ix compress ROOT_PROOF_ADDRESS --out /path/to/new-run
```

`ix compress setup` downloads the file if it is missing and checks it against
its pinned SHA-256, then publishes every stage's fixed preprocessing to the
fixed cache; entries already present are only checked. The file is
`bn254-ignition-main-197/srs.bin` under `IX_PARAMS_DIR` (default
`~/.ix/compression/params`). `IX_KZG_SRS` can select another local copy of the
same release SRS; it is not pin-checked. Its G1/G2 anchors must match the
released key. Provenance comes from release preparation and distribution;
these runtime checks do not replay the ceremony or verify participant
signatures.

`--dev-kzg-srs` selects known-trapdoor inner parameters and bypasses Ignition
loading. Use `--dev-final-srs` as well for development final PLONK/Groth16 keys.
`verify_with_vk` verifies an independently pinned recursive key and expected
statement, requiring `allow_development` when its parameters differ from the
release. The default verifier accepts only the bundled keys.

### Preparing a parameter release

The offline tool uses the same `gnark-ignition-verifier` revision and final two
contributions as SP1: MAIN IGNITION manifest indices 174 and 175, positions 196
and 197. It checks both complete contributions and their link, performs a KZG
opening sanity check, and writes the retained prefix using gnark serialization.
It does not verify contributor signatures. Authenticate the ceremony source as
part of release review, and distribute the approved SRS alongside the release.

```sh
cd tools/gnark
go run ./cmd/ignition -cache /path/to/transcripts -out /path/to/srs.bin
```

This is a release operation: it downloads both complete contributions if absent
and holds their point arrays in memory. It is not run during builds or proving.
The output retains the shifted basis beginning at `tau * G1`; the release key
carries the full ceremony's public degree independently of the retained prefix.

The parameter publisher must upload `srs.bin` to the existing
`bn254/ignition/main-197/` release location before `ix compress setup` can
install it.

## Proving and verification

`ix compress ROOT` and `ix prove ... --compress kzg|plonk|groth16` automatically
normalize the aggregate root using the versioned
[version 0.1 layout](verifying-keys/0.1/layout.json).
`--fixed-root` is an optional layout override. The default layout is the one
shared by the saved Nat.add_comm, Init and Mathlib normalization runs; it has
101 circuit heights, 18 claim elements and no additional headroom beyond those
measured bounds. Its root verifier BLAKE3 is
`f0c635f096bb2b9ff8fbeaf947c406978c11ce3bc447df94e43d6e9fe3cc6fbc`.
The default rejects another backend key, and normalization rejects executions
that exceed the fixed bounds before allocating traces. A larger supported
layout is a new release profile; compression does not resize it per proof.
The profile supplies normalization bounds, not a bundled compression verifier.

`ix compress` and `ix prove ... --compress` run every stage in the `ix`
process through `pipeline::compress(CompressInput, &CompressConfig)`: FRI
compression of the normalized root, first KZG, recursive KZG and, when
selected, the final proof. Real inputs require tens of millions of rows
and substantial RAM; use the measurements above when choosing a host and
place outputs and caches on fast local storage.

Stages are kept under the output directory, `~/.ix/compression/<root>` by
default or `--out`: `root/`, `fri/`, `first-kzg/`, `final-kzg/` (including
`vk.bin`), then `plonk/` or `groth16/`, and the returned `compressed.bin`.
Rerunning the same command resumes: a stage is reused when the proof in its
directory verifies for the expected statement and setup (and, for this
version's backend under Ignition, the bundled keys), the same check that
follows proving; the first stage that fails, and every later one, is proved
again. A non-empty directory whose `root/` does not match the proof, layout
and statement is refused unchanged. The first KZG stage's partition height is
fixed at 2^24, the height the bundled keys were derived for. Fixed-preprocessing and
development SRS caches are shared under `~/.ix/compression/cache`;
`IX_KZG_FIXED_CACHE` and `IX_KZG_SRS_CACHE` override them.

`ix verify` checks recursive KZG proofs under the bundled key. To verify
under an independently pinned key instead, `verify_with_vk` takes the independently reviewed BLAKE3
digest of `final-kzg/vk.bin`, the original claim and independently expected
root claims. It needs no proving SRS or cache, and checks the verifying key
digest, development opt-in, claim digest, all expected statement words, outer
KZG proof and deferred pairing; the verifier never obtains its trusted pin
from the proof.

### Validation and sizing entry points

`fri_sizing --statistics <outer-vk.bin>` exports key statistics through the
Rust decoder without building a circuit. Pipe its JSON to
`tools/compression/fri_security_estimate.py -` for parameter estimates.
`fri_sizing` also retains opt-in frontend sizing.

Focused entry points include the field primitives and complete verifier
witness, with additional curve, transcript, MSM and public-pairing modules:

```sh
cargo test -p ix-proof-compression --no-default-features --features parallel \
  --lib recursive::native_field::
cargo test -p ix-proof-compression --no-default-features --features parallel \
  --lib recursive::native_verifier::reuse_tests::recursive_witness_rejects_tampering_without_native_preverification -- --exact
```

## Final PLONK

```sh
ix compress ROOT_PROOF_ADDRESS --plonk --out /path/to/empty-output
```

Install the released SRS or select a local copy with `IX_KZG_SRS`. The result
includes the proof envelope, native and Solidity proof encodings, generated
Solidity verifier and verifying key, which must equal the bundled key for
`ix verify` to accept the proof. See the [gnark backend guide](../../tools/gnark/README.md)
for Rust FFI tests, CUDA configuration, and artifact cache rules. On-chain verification uses the final PLONK verifier
and [claim adapter](../../contracts/plonk/README.md).

## CUDA and profiling

### Backend configuration

The `cuda` feature compiles the KZG kernels with nvcc and runs
interpolation, commitments, coset evaluation, lookup and quotient
construction and opening divisions on NVIDIA GPUs. It needs the CUDA
toolkit at build time and a visible GPU at runtime; a CPU-only build
neither compiles sppark nor links CUDA.

```sh
IX_CUDA=1 MULTI_STARK_CUDA_ARCHS=120 lake build ix
cargo test --release -p ix-proof-compression --features cuda
```

`IX_CUDA=1` enables both multi-stark's Goldilocks backend for the Aiur
prover and the KZG backend here; there is no separate switch. The KZG and
PLONK kernels build into one `libix_bn254_cuda.so` (one sppark, a private C++
runtime, C exports only), which Lake copies into `.lake/build/lib` beside
multi-stark's `libmulti_stark_cuda.so`.

`IX_NO_PAR=1` builds without the `parallel` feature, and
`IX_CUDA_TRACE_CODEGEN=1` adds the generated CUDA trace kernels described in
[the GPU proving guide](../../docs/aiur-gpu-proving.md), implying `cuda`.

See [the GPU proving guide](../../docs/aiur-gpu-proving.md) for shared CUDA
backend packaging and host-toolchain requirements. When deploying `ix`,
copy both libraries from `.lake/build/lib` into `../lib` relative to the
executable.

With the feature compiled, every proving operation above the size
thresholds in the prover runs on the devices and a rejected memory
admission is an error; tune the residency limit or chunk size below rather
than expecting a host fallback. A CUDA build keeps every committed column
in memory; a CPU build serves the fixed columns from their cache files and
produces identical proof bytes. `ix` reads these settings from the
environment and installs them once, before the first KZG stage:

| Variable | Values | Default |
| --- | --- | --- |
| `IX_KZG_CUDA_DEVICES` | CUDA ordinals, comma separated, in preference order | `0`; the library itself defaults to every supported device |
| `IX_KZG_MSM_CHUNK_POINTS` | `1..=2^28` | `2^24` |
| `IX_KZG_CUDA_RESIDENT_GIB` | device bytes kept for resident coefficients, in GiB | first stage: up to half the device memory; recursive stage: `8` |
| `IX_KZG_CUDA_SRS_CACHE` | `0`, `1` | `0` |
| `IX_KZG_CUDA_PASSES` | `0`, `1`, `force` | `1`: constraint passes when the dense working set does not fit |
| `IX_KZG_CUDA_PROFILE` | set to record NVTX ranges and transfer timings | unset |

With several devices selected, each runs one native operation at a time
and the work spreads by job: partitions prove concurrently, FFT queues and
MSM chunks split across the devices, and resident coefficients are retained
on whichever device has the most room. A lookup, quotient or constraint
pass runs whole on one device that admits its working set, preferring the
device holding most of its resident columns and uploading the others from
the host; the first free admitted device is taken rather than waiting for
the preferred one. Devices never exchange data directly, so there is no
peer access to configure. The pipeline selects device `0` by default;
set `IX_KZG_CUDA_DEVICES` to use additional devices.

`IX_KZG_CUDA_ARCHS` selects the SM architectures at build time and falls
back to `MULTI_STARK_CUDA_ARCHS`, so one variable configures both CUDA
backends of a Lake build. Without either variable, the build detects the
installed GPUs; set explicit targets for headless CI or cross builds.
Device discovery admits only GPUs compatible with a compiled kernel image;
an architecture excluded by the toolkit or an explicit selection is rejected
before proving. The feature-compiled test suite
needs a GPU host; device unit tests are marked ignored and run with
`--ignored`. CPU/GPU proof-byte parity is checked by comparing the two builds' outputs.

### Profiling

The global `IX_TEXRAY=1` switch enables TeXRay for proving, aggregation,
compression, and the Typecheck benchmark. On `ix compress` it reports
coarse phase timings and RSS summaries on stderr, with one root per stage:
`compression/fri`, `compression/kzg`, `compression/wrap`, and
`compression/plonk` or `compression/groth16`. The tree covers circuit
construction, witness generation, lowering, setup, preprocessing caches,
commitments, proving, verification, and output. The inherited `stark/*`
lookup, quotient, and opening phases are included; `stark/fri_open` also
names KZG openings in the generic prover. Prefetched trace generation can
overlap commitment, so child durations should not be summed as wall time.

`IX_KZG_CUDA_PROFILE=1` independently enables fine-grained NVTX ranges and
per-device transfer/kernel timings. Use both switches to relate whole-stage
costs to CUDA execution; GPU operation detail stays out of the TeXRay tree.

## Library interfaces and tests

The library also exposes `pipeline::prepare_root` for aggregate roots with
multiple Aiur trace shards, `FixedRoot` for a bounded normalized root, and
`pipeline::setup` to construct a verifier from trusted parameters without a
proof witness. `Prepared::prove_fri`, `prepare_kzg`, `Prepared::prove_kzg` and
`prepare_recursive` compose the stages with caller-selected bounds and SRS.
These APIs return verifier-only metadata and keep the expected claim separate
from the proof; they do not change the bundled keys. The CLI uses
`pipeline::compress` and the bundled verifying keys described above.

`fri` constrains FRI verification, `foreign` translates Goldilocks arithmetic
into scalar-field constraints, `kzg` implements the commitment backend, and
`recursive` constrains KZG verification with public pairing operands.
`pipeline` runs the stages through the Plonkish API.

Focused CPU checks use the small BN254 fixtures:

```sh
cargo test --release --locked -p ix-proof-compression --test integration \
  -- kzg::
```

`tests/kzg_backend_parity.py` compares independent CPU/CUDA builds on small
ordinary KZG proofs. Complete Init proofs, GPU tests, and sizing runs have
substantial resource costs and are run separately from the small checks.
The CLI tests cover setup selection, claim type checks, unsupported proof
versions, and rejection of untrusted verifying keys.

Sizing and benchmark context is retained in the
[benchmark comparison](../../docs/proof-benchmark-comparison.md) and
[stage construction notes](../../docs/compression-stage-collapse.md).
