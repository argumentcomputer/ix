# Proof compression

## Experimental BN254 CPU backend

The `bn254` feature selects BN254 for the KZG library, including scalar
arithmetic, FFTs, commitments, batched openings, BLAKE3 transcripts, compact
proof encoding, recursive verifier gadgets and the standalone compression
worker. Use it independently of the BLS12-381 terminal-backend features:

```sh
cargo test -p ix-proof-compression --no-default-features \
  --features bn254,parallel --test bn254_kzg
```

This target proves small circuits with an explicitly known-trapdoor development
SRS. BN254 has no authenticated production parameter loader yet. Its worker
requires `--dev-srs` even if Filecoin environment variables are configured.
The ordinary `ix` executable, Solidity exporter, gnark wrapper and CUDA backend
remain BLS12-381. Combining `bn254` with the default features,
`bls12-381`, `solidity`, `plonk` or `cuda` is unsupported and rejected.

BN254's scalar field permits radix-2 domains through `2^28`; the trace size
multiplied by the quotient factor must fit that limit. Compressed G1/G2 points
occupy 32/64 bytes in arkworks' canonical encoding. Proofs, checkpoints,
portable verifier parameters, transcript seeds and development setup/cache
identities distinguish the curve. Existing BLS12-381 formats retain their
identities.

Curve selection is per build. Separate target directories, such as
`--target-dir target/bls12-381` and `--target-dir target/bn254`, keep both
executables available for comparison. The shared `kzg_transcripts`,
`kzg_sharding` and `kzg_streaming` test targets run on either curve; enable
`parallel` for both. These are correctness checks, not performance benchmarks.

The recursive source port uses four 80-bit base-field limbs for BN254, a
257-bit biased quotient and the existing bounded carry construction. G1
validation uses BN254's cofactor-one property after enforcing the curve
equation. Its canonical 32-byte point encoding is exposed as two 128-bit
little-endian public limbs per deferred pairing operand; BLS retains two
192-bit limbs per point. The native assignment path checks that these public
values match the constrained points and verifies the deferred pairing.

Focused debug validation with Rust 1.98.1 passed 132 BN254 tests and 114 BLS
regression tests using locked, offline dependencies. Coverage includes KZG
proofs, recursive field/curve/transcript/MSM constraints, malformed witnesses,
deferred pairings, profile authentication, worker selection and existing BLS
catalog fixtures. BN254 also passed verifier reuse, FRI-to-KZG stage checks,
saved Init FRI input verification and the small root-stage integration tests.
Clippy with `-D warnings` passed for both configurations, including the sizing
example. These are targeted checks, not the complete repository suite.

Init's first BN254 KZG proof and its full recursive witness passed native
checks. Full recursive proving, CUDA and terminal BN254 PLONK remain
unvalidated. Ignored proving/benchmark tests and the larger KZG component
cases were excluded. Complete pipeline results are pending.

### Real-input measurements

The saved mathlib aggregate FRI proof was verified and compressed through one
additional Goldilocks FRI layer using the existing CUDA worker. The run took
60.0 seconds end to end, including 50.2 seconds for outer proving and
verification, with 186.3 GiB peak host RSS. The raw input proof was 5,554,329
bytes and the compressed FRI proof was 1,441,095 bytes. These measurements
used a 48-logical-CPU Xeon Platinum 8559C host with two RTX PRO 6000 Blackwell
Server GPUs; they measure FRI, not BN254 KZG.

For the same saved Init FRI proof and first-stage log-height 24, the BN254
frontend and padded main traces match the historical BLS12-381 run exactly:

| First KZG metric | BN254 and BLS12-381 |
| --- | ---: |
| Gates | 113,913,480 |
| Lookups | 31,689,479 |
| Witness values | 132,837,040 |
| Partitions | 19 |
| Padded main-trace cells | 1,071,842,048 |
| Main scalar storage only | 31.943 GiB |

The mathlib frontend has eight more gates and four more values than Init,
with the same lookup count. Main-trace storage excludes the frontend, fixed,
lookup and quotient columns, and scratch space. The historical BLS recursive
verifier and measured BN254 verifier compare as follows:

| Recursive verifier metric | BLS12-381 reference | BN254 Init |
| --- | ---: | ---: |
| Gates | 85,902,077 | 44,895,563 |
| Lookups | 32,487,842 | 16,255,419 |
| Frontend rows | 118,389,942 | 61,151,005 |
| Witness values | 115,263,448 | 59,590,881 |
| Padded computation height | `2^27` | `2^26` |
| Opening MSM terms | 583 and 9 | 583 and 9 |

BN254 has about 48% fewer recursive frontend rows and halves the padded
computation trace. Its full recursive witness and external pairing checks
passed against the real Init first KZG proof. That first proof is 32,869 bytes,
or 33,045 bytes including its packet header and statement. The recursive
outer proof is still pending.

At the recursive frontend boundaries, point validation accounts for 36.47
million BLS rows versus 0.41 million BN254 rows; BN254's cofactor-one G1
removes the BLS subgroup-check machinery. The two opening MSMs add 62.80
million versus 45.45 million rows. Transcript processing adds 19.12 million
versus 15.28 million rows, with shorter point encodings on BN254. These
increments include newly exposed public values and are not operation counts
or gnark PLONK constraint counts.

These are structural comparisons. Historical BLS timings use CUDA, Filecoin
parameters and an older build with a Keccak final transcript; current BN254
runs use CPU, development parameters and BLAKE3. A curve-speed comparison
requires matching those conditions.

### Saved Init pipeline

The worker has two entry points for a complete KZG run. `pipeline run` reads
`root-vk.bin`, `root-proof.bin` and `root-claims.bin`, performs FRI compression,
then runs first and recursive KZG stages. `pipeline run-fri` starts from an
existing `outer-vk.bin`, `outer-proof.bin` and `outer-claims.bin`; it verifies
that saved FRI proof and compares all eighteen statement words with the
separately supplied root claims before starting the KZG workers.

Build and execute these commands only when machine time is available. Real
inputs require tens of millions of rows and substantial RAM; use the
measurements above when choosing a host and place outputs and caches on fast
local storage.

```sh
cargo build --release --locked -p ix-proof-compression --bin ix-compression-worker \
  --no-default-features --features bn254,parallel --target-dir target/bn254
export IX_COMPRESSION_WORKER="$PWD/target/bn254/release/ix-compression-worker"
"$IX_COMPRESSION_WORKER" fri capabilities

"$IX_COMPRESSION_WORKER" pipeline run \
  /path/to/root /path/to/claim.bin /path/to/bn254-run 24 --dev-srs
```

Alternatively, reuse an already saved FRI proof in a separate empty output
directory:

```sh
"$IX_COMPRESSION_WORKER" pipeline run-fri \
  /path/to/fri /path/to/claim.bin /path/to/root/root-claims.bin \
  /path/to/bn254-from-fri 24 --dev-srs
```

To verify the saved FRI input and count the translated frontend before
proving, use:

```sh
"$IX_COMPRESSION_WORKER" kzg size \
  /path/to/fri /path/to/kzg-size.json --dev-srs
```

This retains the source Goldilocks circuit and translation wire map, without
allocating the translated circuit, proving traces or SRS. Its exact gate,
lookup and value counts do not estimate total prover memory or padded trace
sizes. The saved Init and mathlib inputs each used about 8.13 GiB peak RSS
and 20 seconds wall time for this preflight on the measurement host.

`claim.bin` contains the canonical serialized claim whose digest appears in
the root statement. The top-level driver admits first-stage log-heights 24
and 25, matching the saved recursive layout policy. Workers run in separate
processes and are checked for the selected curve before proving. Each run
writes `proof.envelope.bin`, `final-kzg/verifier.bin`,
`expected-root-claims.bin` and `pipeline-report.json`; failed stages retain
their checkpoints. Shared cache environment variables override the default
per-run `cache/` directory.

BN254 has no bundled verifier catalog entry. Its packet/profile versions are
separate from BLS, and generating a profile does not authorize it. For local
verification, set `BN254_PROFILE_DIGEST` to the independently reviewed BLAKE3
digest of `final-kzg/verifier.bin`, then supply that pin, the original claim,
and independently expected root claims:

```sh
"$IX_COMPRESSION_WORKER" pipeline verify \
  /path/to/bn254-run/proof.envelope.bin /path/to/claim.bin \
  /path/to/root/root-claims.bin /path/to/bn254-run/final-kzg/verifier.bin \
  "$BN254_PROFILE_DIGEST" --dev-srs
```

Verification needs no proving SRS or cache. It checks the profile digest,
development opt-in, claim digest, all expected statement words, outer KZG
proof and deferred pairing. The generated report records the profile digest
for inspection; the verifier never obtains its trusted pin from the proof.
The library equivalents are `compress`, `compress_fri` and
`verify_with_profile`. Ordinary `ix verify` continues to use its BLS catalog.

### Validation and sizing entry points

Focused entry points include the field primitives and complete verifier
witness, with additional curve, transcript, MSM and public-pairing modules:

```sh
cargo test -p ix-proof-compression --no-default-features --features bn254,parallel \
  --lib recursive::native_field::
cargo test -p ix-proof-compression --no-default-features --features bn254,parallel \
  --lib recursive::native_verifier::reuse_tests::recursive_witness_rejects_tampering_without_native_preverification -- --exact
```

The sizing example uses the same four-row inner circuit on both curves. It
proves that small development fixture, then counts the recursive frontend
without retaining the full recursive IR, generating its witness or producing
an outer proof:

```sh
cargo run -p ix-proof-compression --no-default-features --features parallel \
  --example recursive_size > target/recursive-bls12-381.json
cargo run -p ix-proof-compression --no-default-features --features bn254,parallel \
  --example recursive_size > target/recursive-bn254.json
```

The reports contain cumulative and incremental gates, lookups and values at
the curve-input, transcript, scalar-check and opening-MSM boundaries. Shared
tables and scalar preparation contribute to these phases; these frontend
counts are not gnark PLONK constraint counts. The real Init comparison above
uses saved pipeline artifacts; this smaller example provides another
controlled input for comparing the two curves.

The remaining migration steps are:

1. Complete the Init and mathlib development compression runs and matched
   backend comparisons. Compare circuit reports before choosing production
   resource requirements or authorizing profiles.
2. Adapt the gnark circuit to that profile and BN254 Fr, preserving both
   pairing obligations and the two public claim-digest limbs; prove a complete
   small wrapper with the standard BN254 PLONK backend.
3. Add authenticated BN254 ceremony provisioning, profile/catalog authorization
   and regenerated fixtures before enabling production proving.
4. Follow the [BN254 GPU integration plan](../../docs/compression-architecture-options.md#bn254-gpu-integration-plan): port layouts and kernels, establish CPU/GPU
   parity, then measure resources before real Init and multi-GPU benchmarks.

See the [architecture options](../../docs/compression-architecture-options.md)
for the proposed pipeline and unmeasured performance expectations.

## BLS12-381 compression pipeline

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

`--dev-srs` selects a **known-trapdoor development SRS**, including when a
Filecoin cache is configured. Its proofs are **not production-secure**.
Verification requires the corresponding bundled development profile and
explicit `--dev-srs` opt-in; proof, claim and pairing checks still apply.

```sh
ix compress ROOT_PROOF_ADDRESS --dev-srs --out "$IX_COMPRESSION_DATA/runs/dev-001"
ix verify COMPRESSED_PROOF_ADDRESS --dev-srs
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

Ordinary `ix verify` does not import external profiles, and local files under
`~/.ix/verifiers` have no effect. Unknown profile IDs are rejected; adding an
accepted profile requires an application update. The standalone worker's
`pipeline verify` command instead requires an explicit profile pin and expected
statement, as described above. The bundled BLS profiles are:

| Profile | Setup | First-stage log-height |
| --- | --- | --- |
| `aggregate-filecoin-v5.bin` | Filecoin | 24 |
| `aggregate-development-v5.bin` | Development, requires `--dev-srs` | 24 |

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
it does not change the proof into a standard PLONK format. The optional
[Solidity verifier prototype](../../contracts/kzg/README.md) provides a native
profile exporter and local EVM conformance tests.

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
| `IX_KZG_FILECOIN_CACHE` | receipt-pinned Filecoin prefix cache, used unless `--dev-srs` selects development parameters | unset: `--dev-srs` required |
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
were uncontrolled. This historical result used the Init FRI fixture from
`40c990ca`; the current fixture is regenerated by the current CLI. Use identical
input fixtures when comparing binaries or profiles.

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
The CLI test verifies both checked-in packets in a fresh home without a proving
SRS or verifier import. Development proofs require `--dev-srs`; that flag also
selects development parameters when a Filecoin cache is configured. Tests reject
modified claims, proofs and pairing data even with development opt-in, and
confirm that a local verifier registry cannot override the application's profiles.
