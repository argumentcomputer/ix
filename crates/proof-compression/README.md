# Proof compression

Compress an aggregate `CheckEnv` root proof through FRI → KZG → recursive
KZG. The statement the compressed proof exposes is the root's public claim
row, derived from the aggregation backend as `ix verify --aggregate` derives
it and bound to the claim by its packed digest; nothing in the pipeline or
its caches depends on which environment was proved.

The KZG stages prove under the Filecoin phase-one powers of tau when
`IX_KZG_FILECOIN_CACHE` names a prefix cache produced by the authenticated
import in `kzg::srs::filecoin` (`examples/kzg_filecoin_import.rs` drives it
from the 72 GiB `challenge_19`). The cache is pinned by the manifest receipt
its import printed: the receipt of the complete `2^27` cache is built in, and
`IX_KZG_FILECOIN_MANIFEST` names the receipt of a cache with another prefix.
The recursive stage needs the `2^27` prefix, about 12 GiB.

The provisioned parameters live in the S3 bucket
`argument-kzg-params-063002298335-us-east-1-an` in `us-east-1`, under their
file names: the `2^27` prover cache `filecoin-prefix-2p27.bin` and the
complete 72 GiB `challenge_19` it was imported from. Fetch the cache onto
fast local storage (see [Disk placement](#disk-placement)) and point
the pipeline at it; `challenge_19` is only needed to re-run the import.

```sh
IX_COMPRESSION_DATA=/path/to/local-nvme/ix-compression
mkdir -p "$IX_COMPRESSION_DATA/parameters" "$IX_COMPRESSION_DATA/runs"
export IX_KZG_FILECOIN_CACHE="$IX_COMPRESSION_DATA/parameters/filecoin-prefix-2p27.bin"
export IX_KZG_FIXED_CACHE="$IX_COMPRESSION_DATA/cache/fixed-preprocessing"
export IX_KZG_SRS_CACHE="$IX_COMPRESSION_DATA/cache/development-srs"
aws s3 cp s3://argument-kzg-params-063002298335-us-east-1-an/filecoin-prefix-2p27.bin \
  "$IX_KZG_FILECOIN_CACHE"
ix compress ROOT_PROOF_ADDRESS --out "$IX_COMPRESSION_DATA/runs/run-001"
ix verify COMPRESSED_PROOF_ADDRESS
```

Choose an existing local NVMe mount for `IX_COMPRESSION_DATA`; these commands
create directories on its filesystem. `--out` changes the run directory only.
The explicit cache variables keep preprocessing off the default home volume.
`IX_KZG_SRS_CACHE` is used only for development parameters. See
[KZG benchmarking](#kzg-benchmarking) for cold/warm runs and timing boundaries.

Neither download needs to be trusted: the importer checks the
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
SRS**. Its proofs are **not production-secure**. Compression checks each proof
and writes its verifier artifact. The application bundles only the Filecoin
profile listed below.

```sh
unset IX_KZG_FILECOIN_CACHE IX_KZG_FILECOIN_MANIFEST
ix compress ROOT_PROOF_ADDRESS --dev-srs --out "$IX_COMPRESSION_DATA/runs/dev-001"
```

Compression preserves the claim address and prints a new proof address.
It runs the three stages in sequence, each as a child process, into an empty
directory, `~/.ix/compression/PROOF_ADDRESS/HEIGHT` unless `--out DIR` names
one. Each stage writes its proof and verifying metadata; a rerun starts over.
Fixed preprocessing and development SRS files are cached across runs under
`~/.ix/compression/cache`. Use `--log-height 25` for fewer partitions
(default: 24) and `--root-vk PATH` for a trusted root key instead of the
current aggregate key. Full proving needs hundreds of GiB of RAM.

Verification uses the profiles compiled into the application from `profiles/`.
`ix verify` selects a profile by the packet's ID and derives the expected
statement from that profile's pinned aggregation-program prefix and the hash
of the caller's serialized claim. It checks the compact proof and both
pairing obligations without a verifier file, registry, proving SRS or GPU.

External verifier imports are not supported, and local files under
`~/.ix/verifiers` have no effect. Unknown profile IDs are rejected; adding an
accepted profile requires an application update. The bundled profiles are:

| Profile | Setup | First-stage log-height |
| --- | --- | --- |
| `aggregate-filecoin-v5.bin` | Filecoin | 24 |

The adjacent JSON files record the setup, root key and artifact identities.
The verifier catalog pins each profile and its aggregation-program prefix.
The public claim is supplied by the caller rather than copied from the packet, so a bundled profile verifies
any aggregate root proved by the same recursive circuit. `ix compress` derives
the statement from the aggregation backend instead and fails if a bundled
profile pins a different program than the build it runs in, so a stale
bundle is caught where the backend is available.

Compression does not require a profile to be bundled before proving. It
constructs its circuit, verifies its output and writes `final-kzg/verifier.bin`
as an output of the run. That file can be reviewed and bundled in a later
application release; generating it does not register it for verification.

The packet carries the 18-word public claim, a profile ID, two compressed G1
opening-pairing operands and the compact `KQP4` KZG proof. Generic Serde
serialization of complete KZG proofs is unsupported; callers use
`FixedProofCodec` with the expected profile. Internal commitment metadata
retains its canonical encoding and checks nested counts before allocating.

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
The profile version selects the transcript without trying alternatives;
application verification also requires that exact profile to be bundled.
Setup bindings include the transcript choice. Metadata checksums and profile
identities remain BLAKE3.

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
prover and the KZG backend here; there is no separate switch. KZG-specific
kernels are compiled into `ix-compression-worker`, the stage executable
built beside `ix`. Both executables use multi-stark's shared CUDA backend.

`IX_NO_PAR=1` builds without the `parallel` feature, and
`IX_CUDA_TRACE_CODEGEN=1` adds the generated CUDA trace kernels described in
[the GPU proving guide](../../docs/aiur-gpu-proving.md), implying `cuda`.

See [the GPU proving guide](../../docs/aiur-gpu-proving.md) for shared CUDA
backend packaging and host-toolchain requirements. When deploying the worker,
copy `.lake/build/lib/libmulti_stark_cuda.so` into `../lib` relative to its
executable, as for the CUDA-enabled Lean binaries.

With the feature compiled, every proving operation above the size
thresholds in the prover runs on the devices and a rejected memory
admission is an error; tune the residency limit or chunk size below rather
than expecting a host fallback. A CUDA build keeps every committed column
in memory; a CPU build serves the fixed columns from their cache files and
produces identical proof bytes. The worker installs its settings from the
environment before the first proving operation:

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
compression, and the Typecheck benchmark. On `ix compress` or a direct
worker invocation it reports coarse phase timings and RSS summaries on
stderr. Each worker installs TeXRay before loading inputs and examines a `compression/fri`,
`compression/kzg`, or `compression/wrap` root. The tree covers circuit
construction, witness generation, lowering, setup, preprocessing caches,
commitments, proving, verification, and output. The inherited `stark/*`
lookup, quotient, and opening phases are included; `stark/fri_open` also
names KZG openings in the generic prover. Prefetched trace generation can
overlap commitment, so child durations should not be summed as wall time.

`IX_KZG_CUDA_PROFILE=1` independently enables fine-grained NVTX ranges and
per-device transfer/kernel timings. Use both switches to relate whole-stage
costs to CUDA execution; GPU operation detail stays out of the TeXRay tree.

## Disk placement

The recorded GPU runs used local NVMe. Other filesystems are supported, but
parameter loading, checkpoint writes, integrity scans, and cache publication
are part of proving wall time. Put stage output and fixed preprocessing on
the **same filesystem** so cache publication and restoration can hard-link
the files. Across filesystems the implementation copies them, adding I/O and
duplicate storage even if both filesystems are on NVMe.

| Data | Location | Storage behavior |
| --- | --- | --- |
| Filecoin parameters | `IX_KZG_FILECOIN_CACHE` | Each KZG worker reads and authenticates its required prefix from the provisioned file. |
| Fixed coefficients and circuit metadata | `<out>/first-kzg/kzg/` and `<out>/final-kzg/kzg/`; reused through `IX_KZG_FIXED_CACHE` | Cold runs write and sync checkpoints, then hash and publish them after proof verification. Warm runs hash the cached files before linking or copying them into the new run. |
| Development parameters | `IX_KZG_SRS_CACHE` | Generated and cached on a miss; loaded and checked on reuse. Unused with Filecoin. |
| Stage proofs, claims, verifier metadata, and reports | `--out` | Retained between worker processes and after the run. |
| Stored `Ixon.Proof` containing the final proof and claim | `~/.ix/store` | Written by `ix compress`; `--out` does not relocate the store. |

CUDA proving retains committed coefficients in host RAM and selected columns
in VRAM. Witness columns stay in memory. Fixed checkpoints are still written
on a cold run; a warm CUDA worker loads them into RAM after the cache integrity
scan. CPU workers instead index fixed checkpoints and stream their columns
during proving. OS page-cache hits can reduce physical reads, so a warm
preprocessing cache does not imply zero storage work.

### Capacity and retention

The 12 GiB Filecoin file is only one part of the footprint. Fixed checkpoint
payloads use 32 bytes per coefficient:

```text
fixed coefficient bytes = 32 × sum(preprocessed_width × trace_height)
```

For the bundled v5 recursive profiles, the computation trace has 15 fixed
columns at `2^27` rows and the table trace has four at `2^17` rows. Their
combined coefficient payload is **60.015625 GiB**, excluding checkpoint
metadata. Together with the Filecoin file, this already exceeds 72 GiB before
first-stage preprocessing, intermediate artifacts, and filesystem headroom.
This is a calculation from those profiles, not a measured disk high-water mark
for the current code. First-stage size depends on the layout; record the
actual checkpoint sizes when provisioning a new profile.

On one filesystem, cache entries and run checkpoints share storage through
hard links. Deleting one directory does not free those bytes while another
link remains. Cache keys include the worker executable digest, plan, and setup;
a changed executable creates a new cache lineage. There is no automatic
eviction of old runs or cache entries. Retire them explicitly once no worker
uses them. Use `df -h` on the selected mount to check available space.

Before discarding ephemeral storage, preserve the stored proof with its claim
and `final-kzg/verifier.bin` on durable storage. Keep intermediate proofs and
caches when they are useful for later runs. The 72 GiB `challenge_19` source
is needed only for parameter import; normal proving uses the prefix cache.

## Stage entries and caches

`ix compress` invokes `ix-compression-worker <stage> <args>` for each stage.
Each invocation runs one stage and exits, releasing its host memory and
CUDA state. The separate executable keeps the KZG CUDA runtime outside
Lean's process. Reuse between invocations comes from the disk caches below.
The worker must be installed beside `ix`, or named by `IX_COMPRESSION_WORKER`.
Maintainers can invoke a stage directly when diagnosing a saved input:

```sh
ix-compression-worker fri root/ fri/ --prove-outer
ix-compression-worker kzg run fri/ first-kzg/ 24
ix-compression-worker wrap stage-and-prove first-kzg/ final-kzg/
```

The KZG stages generate traces directly into commitment and proving.
Every KZG stage requires `--dev-srs` when no Filecoin cache is configured.

`ix compress` sets the fixed-preprocessing and development SRS cache
directories under `~/.ix/compression/cache` unless the environment already
names them. Direct stage invocations use the defaults below.

| Variable | Meaning | Default |
| --- | --- | --- |
| `IX_KZG_FIXED_CACHE` | directory of fixed-preprocessing checkpoints, bound to the executable digest, plan and setup identity | `<stage>/kzg/fixed-cache` |
| `IX_KZG_FILECOIN_CACHE` | receipt-pinned Filecoin prefix cache; selects the Filecoin setup for every stage | unset: development setup, requiring `--dev-srs` |
| `IX_KZG_FILECOIN_MANIFEST` | BLAKE3 manifest receipt of that cache | the built-in receipt of the complete `2^27` cache |
| `IX_KZG_SRS_CACHE` | directory holding block-checksummed development SRS files shared across stages | unset: regenerated per stage |
| `IX_KZG_PREFETCH_GIB` | bound on the next partition's witness generated while the current one is committed | `32` |
| `IX_ROOT_GENERIC_HASHES` | set to build the FRI stage's circuit with generic rather than compact BLAKE3; `ix compress` rejects it | unset |

## KZG benchmarking

State the input boundary with every timing:

| Scope | Command boundary | Included work |
| --- | --- | --- |
| Aggregate root → compressed packet | Whole `ix compress` process | Backend setup, root-to-FRI compression, both KZG workers, verification, cache publication, and final store write. Initial proving and aggregation are excluded. |
| Saved compressed FRI → KZG packet | Both sequential KZG worker processes | First KZG stage and recursive KZG stage, including parameter loading, verification, output, and cache publication. Root-to-FRI compression is excluded. |

Use whole-process wall time for either scope. Internal
`kzg/prove-report.json.total_seconds` starts inside the proving phase and is
captured before fixed-cache publication; it excludes some preparation and
storage work. `IX_TEXRAY=1` provides the phase breakdown described under
[Profiling](#profiling). Do not sum overlapping child spans.

For a Filecoin cold/warm pair, use the NVMe layout and provisioned parameters
from the quickstart. `IX_FRI_INPUT` must contain `outer-vk.bin`,
`outer-proof.bin`, and `outer-claims.bin` from the saved FRI stage. Keep the
input, binary, features, setup, and runtime settings identical between runs:

```sh
set -eu
IX_FRI_INPUT=/path/to/saved-fri
IX_KZG_WORKER=.lake/build/bin/ix-compression-worker
IX_KZG_BENCH=$(mktemp -d "$IX_COMPRESSION_DATA/runs/kzg-bench.XXXXXX")
export IX_KZG_FIXED_CACHE="$IX_KZG_BENCH/fixed-preprocessing"
: "${IX_KZG_FILECOIN_CACHE:?set the provisioned Filecoin cache path}"
sha256sum "$IX_KZG_WORKER" "$IX_FRI_INPUT/outer-vk.bin" \
  "$IX_FRI_INPUT/outer-proof.bin" "$IX_FRI_INPUT/outer-claims.bin" \
  > "$IX_KZG_BENCH/inputs.sha256"
findmnt -T "$IX_KZG_BENCH" > "$IX_KZG_BENCH/storage.txt"
df -h "$IX_KZG_BENCH" >> "$IX_KZG_BENCH/storage.txt"
for mode in cold warm; do
  run="$IX_KZG_BENCH/$mode"
  mkdir -p "$run"
  /usr/bin/time -v -o "$run/first-kzg.time" \
    "$IX_KZG_WORKER" kzg run "$IX_FRI_INPUT" "$run/first-kzg" 24 \
    > "$run/first-kzg.log" 2>&1
  /usr/bin/time -v -o "$run/recursive-kzg.time" \
    "$IX_KZG_WORKER" wrap stage-and-prove "$run/first-kzg" "$run/final-kzg" \
    > "$run/recursive-kzg.log" 2>&1
done
```

The first run populates the initially empty fixed cache; the second reuses it
with fresh output directories and fresh worker processes. Sum the two elapsed
worker times for each saved-FRI-to-packet result. Parameter download and import
happen before timing. For development runs, report the development SRS cache
state separately: generating parameters changes the measured workload.

Record the revisions, hardware and driver, environment settings, parameter
receipt, filesystem/device placement, checkpoint sizes, and each process's
exit status alongside these logs. Report OS page-cache state separately from
preprocessing-cache state; if uncontrolled, say so. Rebuilding the worker
between the pair invalidates preprocessing reuse. For full compression from
an aggregate root, time `ix compress` with a fresh `--out` directory and the
same explicit cache placement instead.

### Recorded Init KZG run

One cold/warm pair used a saved compressed Init FRI proof, Filecoin parameters,
one RTX PRO 6000 Blackwell with 96 GB VRAM, 32 vCPUs, 256 GiB RAM, and local
NVMe. Cold means empty fixed preprocessing; warm means reused preprocessing.
Both used fresh worker processes and already-provisioned parameters. OS caches
were uncontrolled. This is a historical result for the saved Init artifacts;
rerun after changing binaries or profiles.

| Stage | Cold | Warm |
| --- | ---: | ---: |
| Compressed FRI → KZG | 300.33 s | 189.93 s |
| Recursive KZG | 171.51 s | 119.11 s |
| **Total** | **471.87 s** | **309.04 s** |

The recorded scope includes SRS loading/authentication and verification, and
excludes builds, parameter download, initial aggregation, and root-to-FRI
compression. No SRS generation was performed. Warm was **1.53× faster**;
both runs produced identical **2,181-byte packets**. Verification including
pairings took **6.67 ms**, excluding loading and startup; peak host RSS was
**236.51 GiB**. The record does not give a total disk high-water mark or a
comparison against another storage device.

## Shared stage construction

The public stage API and the worker use the same production circuit builders,
statement schemas, lowering namespaces, and recursive Keccak transcript.
The file adapters load artifacts, select setup and cache locations, and report
results. Multi-shard roots and the normalized `FixedRoot` remain supported;
`setup` constructs its verifier without a proof or witness.

KZG commitment consumes the lowered circuit and assignment before proving.
The remaining phase owns committed columns and verifier metadata, allowing
frontend memory to be released before lookup and quotient allocation.
Bundled and library recursive verification share validation and pairing checks.
A bundled profile retains its prepared system, pairing keys and compact codec.

The library's `IXKZGV02` key encoding binds the transcript explicitly.
The bundled v5 profile and packet encodings are unchanged.

## Code and tests

The library also exposes `pipeline::prepare_root` for aggregate roots with
multiple Aiur trace shards, `FixedRoot` for a bounded normalized root, and
`pipeline::setup` to construct a verifier from trusted parameters without a
proof witness. `Prepared::prove_fri`, `prepare_kzg`, `Prepared::prove_kzg` and
`prepare_recursive` compose the stages with caller-selected bounds and SRS.
These APIs return verifier-only metadata and keep the expected claim separate
from the proof. They do not register a verifier in the application's bundled
catalog. The CLI uses the worker and trusted profiles described above.

`fri` constrains FRI verification, `foreign` translates Goldilocks arithmetic
into scalar-field constraints, `kzg` implements the commitment backend, and
`recursive` constrains KZG verification with public pairing operands.
`pipeline` runs the stages through the Plonkish API, exposed by
`ix-compression-worker`.

```sh
cargo test --release -p ix-proof-compression
lake build ix compression-cli-tests
.lake/build/bin/compression-cli-tests
```

The lakefile compiles Cargo's C units as C17 so they stay compatible with
Lean's bundled libc on hosts whose C compiler defaults to C23, and tracks
that flag and the embedded profile bytes when deciding whether to rebuild
the Rust archive.

Tests cover small proving, tampering, CLI validation and proof identity.
The saved Init FRI fixture checks native verification and verifier planning.
The CLI test verifies the checked-in Filecoin packet in a fresh home without a proving SRS
or verifier import, rejects modified claims and profile IDs, and confirms
that a local verifier registry cannot override the application's profiles.
