# Proof compression

Compress the aggregated Init root through FRI → KZG → recursive KZG.

The KZG stages prove under the Filecoin phase-one powers of tau when
`IX_KZG_FILECOIN_CACHE` names a prefix cache produced by the authenticated
import in `kzg::srs::filecoin` (`examples/kzg_filecoin_import.rs` drives it
from the 72 GiB `challenge_19`). The cache is pinned by the manifest receipt
its import printed: the receipt of the complete `2^27` cache is built in, and
`IX_KZG_FILECOIN_MANIFEST` names the receipt of a cache with another prefix.
The recursive stage needs the `2^27` prefix, about 12 GiB.

```sh
IX_KZG_FILECOIN_CACHE=/data/filecoin/filecoin-prefix-2p27.bin ix compress ROOT_PROOF_ADDRESS
ix verify COMPRESSED_PROOF_ADDRESS
```

The provisioned parameters live in the S3 bucket
`argument-kzg-params-063002298335-us-east-1-an`: the `2^27` prover cache
`filecoin-prefix-2p27.bin` and the complete 72 GiB `challenge_19` it was
imported from. Neither download needs to be trusted: the importer checks the
source against the ceremony's published BLAKE2b-512 digest, and loading
checks the cache against its built-in receipt and the pinned tau anchors. A
256-power cache from the same import is checked in at
`tests/fixtures/filecoin-prefix-2p8.bin` for tests of the real format.

| Artifact | Size | Pin |
| --- | ---: | --- |
| `challenge_19` | 77,309,411,488 bytes | BLAKE2b-512 `5a26015b…4df76b`, `FILECOIN_CHALLENGE_19_BLAKE2B` |
| `filecoin-prefix-2p27.bin` | 12,884,919,006 bytes | BLAKE3 receipt `14423860…37f10a`, `FILECOIN_PREFIX_2P27_MANIFEST_BLAKE3` |
| `tests/fixtures/filecoin-prefix-2p8.bin` | 25,342 bytes | BLAKE3 receipt `185c556e…a0507d`, `FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3` |

Without a Filecoin cache, `--dev-srs` selects a **known-trapdoor development
SRS**. Its proofs are **not production-secure**, and `ix verify` and
`ix verifier import` accept them only with `--dev-srs`.

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

Accepted verifiers are stored under `~/.ix/verifiers/filecoin/` or
`~/.ix/verifiers/development/` by the class of their public setup, and a
verifier's class is checked again on every use. A profile is Filecoin only
when its identity, public degree and all four anchor points equal the
ceremony values pinned in `kzg::srs::filecoin`; verification needs no cache. Unknown profiles, altered
keys and conflicting registrations are rejected.
Verification checks the proof, public setup binding and external opening
pairing equation using the portable verifier; it does not load the proving SRS.

The packet carries the 18-word public claim, a profile ID, two compressed G1
opening-pairing operands and the compact KZG proof. The independently accepted
portable verifier supplies the circuit and public setup parameters.

Every setup declares its complete public polynomial degree. Loading a shorter
proving prefix or only verifier anchors preserves that degree and the setup
identity. The Filecoin identity derives from the ceremony digest and its
`2^28 - 2` public degree, so every prefix cache of it binds the same
checkpoints and verifier profiles. Development identities derive from the
seed and declared degree; the trapdoor remains known.

## Final proof transcript

New recursive KZG proofs use Keccak-256 in portable verifier profile v5.
The FRI proof, first KZG proof and the recursive circuit's verification of
that first proof retain BLAKE3. The compact proof layout and SRS are unchanged.
Portable v4 verifiers continue to verify their BLAKE3 proofs; the profile
version selects the transcript, without trying alternatives. New outer
checkpoint bindings include the transcript choice, so v4 checkpoints require
a fresh output directory. Metadata checksums and registry digests remain BLAKE3.

The Keccak transcript starts with a zero 32-byte state. For counters 0, 1 and
2 it computes Keccak-256 over
`"multi-stark/kzg/keccak256/v1" || counter:u8 || state:bytes32 || observations`.
The first two digests concatenate into a 512-bit **big-endian** integer reduced
modulo the BLS12-381 scalar field; the third digest becomes the next state.
All three hashes use the old state, then the observation buffer is cleared.
Observations keep the existing canonical field/point and vector encodings.
The parameter seed has its own Keccak protocol domain and binds the same
public setup anchors and degree limits as the BLAKE3 configuration.

This profile makes a custom Ethereum verifier's transcript use native Keccak;
it does not change the proof into a standard PLONK format or implement a
Solidity verifier.

## GPU proving

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
prover and the KZG backend here; there is no separate switch.

With the feature compiled, every proving operation above the size
thresholds in the prover runs on the devices and a rejected memory
admission is an error; tune the residency limit or chunk size below rather
than expecting a host fallback. A CUDA build keeps every checkpoint in
memory, as the original pipeline did, so `--resident` changes nothing
there; a CPU build proves disk-backed checkpoints with identical proof
bytes. The worker installs its settings from the environment before the
first proving operation:

| Variable | Values | Default |
| --- | --- | --- |
| `IX_KZG_CUDA_DEVICES` | CUDA ordinals, comma separated | every supported device |
| `IX_KZG_MSM_CHUNK_POINTS` | `1..=2^28` | `2^24` |
| `IX_KZG_CUDA_RESIDENT_GIB` | device bytes kept for resident coefficients, in GiB | `8`, leaving the rest of the device for lookup and quotient working sets |
| `IX_KZG_CUDA_SRS_CACHE` | `0`, `1` | `0` |
| `IX_KZG_CUDA_PASSES` | `0`, `1`, `force` | `1`: constraint passes when the dense working set does not fit |
| `IX_KZG_CUDA_PROFILE` | set to record NVTX ranges and transfer timings | unset |

### Measured proving time

One RTX PRO 6000, 24 host cores, a 230 GiB cgroup limit without swap,
sequential stages, the fused `run` and `stage-and-prove` entries, trace cap
2^24, witness prefetch off, and the caches shared through
`IX_KZG_FIXED_CACHE` and `IX_KZG_SRS_CACHE` from a fresh output directory.
The cold trial generates both development SRS files and all fixed
preprocessing; the warm trial reuses them.

| Stage | Cold | Warm | multi-stark `sb/kzg` warm |
| --- | ---: | ---: | ---: |
| FRI compression, GPU | 62 s | 61 s | 60 s |
| First KZG stage | 307 s | 178 s | 164 s |
| Recursive KZG stage | 307 s | 121 s | 113 s |
| Pipeline | 676 s | 360 s | 336 s |

The warm trial hashed every cached checkpoint at restore; the restore now
hashes only the metadata files, since checkpoints verify their own recorded
digest on every read, and has not been re-measured. The final packet is
2,181 bytes in every run.

`IX_KZG_CUDA_ARCHS` selects the SM architectures at build time and falls
back to `MULTI_STARK_CUDA_ARCHS`, so one variable configures both CUDA
backends of a Lake build. The feature-compiled test suite needs a GPU host;
the device unit tests are marked ignored and run with `--ignored`. CPU/GPU
proof-byte parity is checked by comparing the two builds' outputs.

## Stage entries and caches

`init_fri_kzg run <saved-fri-dir> <output-dir> <log-height> [--resident]`
stages and proves the first KZG stage in one process, feeding generated
traces straight into commitment; `ix compress` uses it for a fresh run and
falls back to `stage` then `prove` when resuming a staged directory.
`init_fri_kzg serve <responses.jsonl> [log-height] [--resident]` keeps a
prepared worker resident across requests. The recursive stage has the same
fused entry, `init_kzg_wrap stage-and-prove <first-stage-dir> <output-dir>`,
which `ix compress` uses for a fresh run; it caps device residency at 8 GiB
so the constraint passes of the 2^27 trace are admitted, unless
`IX_KZG_CUDA_RESIDENT_GIB` is set.

| Variable | Meaning | Default |
| --- | --- | --- |
| `IX_KZG_FIXED_CACHE` | directory of fixed-preprocessing checkpoints, bound to the executable digest, plan and setup identity | `<dir>/kzg/fixed-cache` |
| `IX_KZG_FILECOIN_CACHE` | receipt-pinned Filecoin prefix cache; selects the Filecoin setup for every stage | unset: development setup, requiring `--dev-srs` |
| `IX_KZG_FILECOIN_MANIFEST` | BLAKE3 manifest receipt of that cache | the built-in receipt of the complete `2^27` cache |
| `IX_KZG_SRS_CACHE` | directory holding block-checksummed development SRS files shared across stages | per-stage `kzg/dev-srs.bin` |
| `IX_KZG_PREFETCH_GIB` | bound on the next partition's witness prefetched during proving | `32` |
| `IX_KZG_TRACE_CODEC` | `pzstd` or `zstd` for staged trace files | `pzstd` when installed |

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
