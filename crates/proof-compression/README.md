# Ix proof compression

The pipeline is Goldilocks/Blake3 FRI → BN254 KZG → recursive BN254 KZG,
with an optional terminal BN254 PLONK proof. FRI uses Goldilocks and its
quadratic extension with Blake3 Merkle commitments. Curve arithmetic starts
when the FRI verifier is translated into BN254 scalar-field constraints.

BN254 is unconditional, including builds with `--no-default-features`.
The remaining Cargo features are `parallel`, `plonk`, and `cuda`.
Lake builds the CLI, worker, and matching `ix-bn254-plonk-wrapper` together.
An explicit `IX_KZG_CURVE=bn254` is accepted; other values are rejected.

```sh
lake build ix
IX_CUDA=1 lake build ix
IX_PLONK_CUDA=1 lake build ix
```

`IX_CUDA` selects the Aiur/FRI and KZG CUDA backends. `IX_PLONK_CUDA`
independently selects the terminal PLONK CUDA helper. Native BN254 arithmetic
uses shared sppark/BLST support, and the Go helper uses gnark. Those libraries
may contain other curves; Ix exposes only BN254.

KZG uses authenticated Ignition parameters or explicit known-trapdoor
development parameters. Terminal PLONK requires authenticated Ignition.
The BN254 KZG release catalog is empty: local verification requires an
independently pinned verifying key and expected statement. PLONK verification
requires an independently authorized `IX_PLONK_VERIFIER_CATALOG`.

BN254 supports radix-2 domains through `2^28`; traces and quotient domains
must both fit. Existing BN254 proof, verifier, and SRS encodings are retained.

## Ignition setup

### Ignition parameter import

The BN254-only `kzg_ignition_import` example provides local transcript
inspection, import and authenticated prefix loading. The real `2^26` import
and authenticated cache loads passed on 2026-10-16. To build the tool:

```sh
cargo build --release --locked -p ix-proof-compression \
  --no-default-features --features parallel --example kzg_ignition_import
IGNITION_IMPORTER="$PWD/target/release/examples/kzg_ignition_import"
"$IGNITION_IMPORTER" info
"$IGNITION_IMPORTER" inspect \
  /path/to/ignition-downloads /path/to/source-manifest.candidate.json
```

`inspect` reads the complete local contributions 196 and 197, in the
`NNN_0xaddress/transcript00.dat` through `transcript19.dat` directories. It
checks framing and embedded checksums and produces an **untrusted candidate**
inventory with complete-file BLAKE2b-512 hashes. This importer-specific source
manifest is different from Aztec's downloaded `manifest.json`. Inspection
does not authenticate participants or replay the ceremony.

Independently authenticate the selected ceremony bytes before pinning the
exact source-manifest JSON's BLAKE3 digest in trusted configuration. Then:

```sh
"$IGNITION_IMPORTER" import \
  /path/to/ignition-downloads /path/to/source-manifest.json \
  "$IGNITION_SOURCE_MANIFEST_BLAKE3" /path/to/new-ignition-prefix.bin 26
"$IGNITION_IMPORTER" verify \
  /path/to/new-ignition-prefix.bin "$IGNITION_CACHE_MANIFEST_BLAKE3" 26
```

Import reports `cache_manifest_blake3`; retain it separately from the cache
for subsequent loads. It authenticates all source files, including unused
suffixes, by hash. It checks canonical coordinates and curve/subgroup
membership for retained G1 points and G2 anchors, the shifted first power,
every retained adjacency and the selected predecessor link. The link check
is not full participant-signature or ceremony verification. Prefixes must be
powers of two from 2 through `2^26`.
The default inspection inventory includes both contributions; library
callers can supply a separately pinned manifest without predecessor evidence.

The importer preserves the sequence beginning at `tau * G1`; it never
inserts the canonical generator. A complete 100,800,000-entry source declares
public polynomial degree 100,799,999 even when fewer points are retained.
Import memory is bounded by chunks, and cache publication is atomic and
refuses existing destinations. Normalized G1 payloads occupy 64 bytes per
point (about 4 GiB for `2^26`), plus metadata. Cache loads authenticate whole
overlapping chunks; a two-point verifier load reads just the authenticated
manifest and anchors.

Library entry points are `kzg::srs::ignition::{inspect_ignition_source,
read_source_manifest, import_ignition_transcripts, load_ignition_cache}`.
`load_ignition_cache_with_identity` also returns the source receipt metadata.
No ceremony pin is built in. The import follows SP1's PLONK setup path,
Aztec Ignition's `MAIN IGNITION` transcripts through participants 196 and
197; this selects a candidate, not an authorized production setup.

The validated source snapshot contains all forty transcript files from
participants 196 and 197, matching the SP1-selected participant snapshot.
All forty per-file signatures verified using EIP-191 over the SHA256 of the
complete transcript. Both participants' first G1 and contribution G2 points
also matched the historical records in
[Aztec's verification repository at `c333ec47`](https://github.com/AztecProtocol/ignition-verification/tree/c333ec4775045139f86732abfbbd65728404ab7f).
The source inventory's complete-file BLAKE2b-512 hashes were then matched
against that signature evidence before import. This authenticates the files
to the documented participant keys; it does not replay the entire ceremony
or establish erasure of their secret randomness. The separate `sealed`
snapshot has different anchors and is not part of this import.

The prepared cache, all forty source transcripts, admission and authentication
evidence are stored in the S3 bucket:
`s3://argument-kzg-params-063002298335-us-east-1-an/bn254/ignition/main-197/`.
All 116 objects (17,197,946,185 bytes) passed size and SHA-256 verification
after upload, including multipart checksum verification. The local validation
copy is at `/opt/dlami/nvme/ix-bn254/parameters/ignition/`:

- `source-authentication.json` binds `source-manifest.json` to the signature
  evidence and its pinned upstream revision.
- `authentication/verified-signatures.json` records every digest, signature
  and recovered address; `authentication/verify_signatures.py` reproduces
  those checks against the downloaded transcripts.
- `import-receipt.json` and `admission-receipt.json` record the
  independent source, cache and admission pins and the complete setup identity.

Proving needs the prepared cache and admission; the source transcripts are
needed only to reproduce the import. Restore them onto fast local storage:

```sh
IGNITION_DATA=/path/to/local-nvme/parameters/ignition
IGNITION_S3=s3://argument-kzg-params-063002298335-us-east-1-an/bn254/ignition/main-197
mkdir -p "$IGNITION_DATA"
export IX_KZG_IGNITION_CACHE="$IGNITION_DATA/ix-prefix-26.bin"
export IX_KZG_IGNITION_ADMISSION="$IGNITION_DATA/admission.json"
aws s3 cp "$IGNITION_S3/ix-prefix-26.bin" "$IX_KZG_IGNITION_CACHE" --region us-east-1
aws s3 cp "$IGNITION_S3/admission.json" "$IX_KZG_IGNITION_ADMISSION" --region us-east-1
export IX_KZG_IGNITION_CACHE_BLAKE3=6b4a939d863d026ab045d3da2c8175abb9224889a58ccbf26bacb92f74248e6b
export IX_KZG_IGNITION_ADMISSION_BLAKE3=4e16f069766667b6f5b9710b23bbf4fce067053967666db78f34ff058b48ff46
```

The host-specific `setup.env` and `setup.json` were excluded from S3; the
commands above configure replacement local paths with the verified pins.

| Validated operation | Time | Peak process RSS |
| --- | ---: | ---: |
| Import `2^26` powers, checking contributions 196 and 197 | 211.88 s | 0.134 GiB |
| Authenticate and load the complete `2^26` cache | 5.54 s | 4.532 GiB |
| Load two verifier anchors from the authenticated cache | 4.31 ms | — |

Times are the tool's operation timings; resource logs are under
`/opt/dlami/nvme/ix-bn254/logs/ignition-{import,verify}-26/`. CPU crate tests
passed for the imported Ignition parameters; see the historical measurement records for the exact revisions and test counts.
The complete cold and warm Init runs under Ignition also passed; see
[the real-input validation](#real-init-with-ignition).

### Admitted Ignition pipeline

An `IgnitionAdmission` carries the exact source-manifest JSON, its pin,
source-derived setup identity and degree, and four verifier anchors. Its
independent BLAKE3 pin authorizes those parameters. It contains no proving
cache path or cache-prefix receipt, so verification can use it without a
proving cache and different authenticated prefixes can share an admission.
The source-derived identity prevents relabeling an existing development
setup as Ignition. Source provenance still depends on the caller's trust in
the descriptor; creating this file does not independently authenticate a
ceremony or authorize a verifying key.

Produce the descriptor from already trusted source and cache pins:

```sh
"$IGNITION_IMPORTER" admission \
  /path/to/ignition-prefix.bin "$IGNITION_CACHE_MANIFEST_BLAKE3" \
  /path/to/source-manifest.json "$IGNITION_SOURCE_MANIFEST_BLAKE3" \
  /path/to/new-admission.json
```

Retain the reported `admission_blake3` independently. To select these
parameters for proving, configure all four settings:

```sh
export IX_KZG_IGNITION_CACHE=/path/to/ignition-prefix.bin
export IX_KZG_IGNITION_CACHE_BLAKE3="$IGNITION_CACHE_MANIFEST_BLAKE3"
export IX_KZG_IGNITION_ADMISSION=/path/to/new-admission.json
export IX_KZG_IGNITION_ADMISSION_BLAKE3="$IGNITION_ADMISSION_BLAKE3"

"$IX_COMPRESSION_WORKER" pipeline run-fri \
  /path/to/fri /path/to/claim.bin /path/to/root/root-claims.bin \
  /path/to/new-ignition-run 24
```

On the validation host, the retained configuration supplies all four settings:

```sh
source /opt/dlami/nvme/ix-bn254/parameters/ignition/setup.env
```

It selects `ix-prefix-26.bin` and `admission.json`, using the pins recorded in
the receipts above. It does not select or authorize a verifying key.

Partial configuration, incorrect pins, changed anchors/source receipts and
insufficient prefixes fail closed. `--dev-srs` explicitly selects development
parameters instead. The worker checks Ignition capability before starting
stages and binds both KZG stages to the same admitted setup; the recursive
verifying key must also retain its admitted deferred pairing keys.

For local verification, supply the independently trusted verifying key digest
as well as the original claim, expected root statement and admitted setup:

```sh
"$IX_COMPRESSION_WORKER" pipeline verify-ignition \
  /path/to/run/proof.envelope.bin /path/to/claim.bin \
  /path/to/root/root-claims.bin /path/to/run/final-kzg/vk.bin \
  "$BN254_VK_DIGEST" /path/to/new-admission.json \
  "$IGNITION_ADMISSION_BLAKE3"
```

This command reads no proving cache or setup environment and rejects
`--dev-srs`. The library equivalent is `verify_with_ignition_admission`,
with an `IgnitionAdmission` authenticated using `read` or `from_bytes`.
Ordinary application verification continues to use its release-bundled
verifying key catalog. A future BN254 production entry must bundle both
the verifying key digest and the admitted setup pin; generating either
artifact does not add that entry. The BN254 catalog remains empty and admits
no development entries.

## Proving and verification

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
  --no-default-features --features parallel --target-dir target/bn254
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
writes `proof.envelope.bin`, `final-kzg/vk.bin`,
`expected-root-claims.bin` and `pipeline-report.json`; failed stages retain
their checkpoints. Shared cache environment variables override the default
per-run `cache/` directory.

BN254 has no bundled verifying key catalog entry. Its packet and verifying
key formats identify BN254; generating a key does not authorize
it. For local verification, set `BN254_VK_DIGEST` to the independently
reviewed BLAKE3 digest of `final-kzg/vk.bin`, then supply that pin,
the original claim and independently expected root claims:

```sh
"$IX_COMPRESSION_WORKER" pipeline verify \
  /path/to/bn254-run/proof.envelope.bin /path/to/claim.bin \
  /path/to/root/root-claims.bin /path/to/bn254-run/final-kzg/vk.bin \
  "$BN254_VK_DIGEST" --dev-srs
```

Verification needs no proving SRS or cache. It checks the verifying key
digest, development opt-in, claim digest, all expected statement words, outer
KZG proof and deferred pairing. The generated report records the verifying
key digest for inspection; the verifier never obtains its trusted pin from
the proof.
The library equivalents are `compress`, `compress_fri` and
`verify_with_vk`. `ix verify` uses the catalog for its compiled curve;
BN254 has no authorized entries yet, so use the worker command above with an
explicit verifying key for development verification.

### Validation and sizing entry points

Focused entry points include the field primitives and complete verifier
witness, with additional curve, transcript, MSM and public-pairing modules:

```sh
cargo test -p ix-proof-compression --no-default-features --features parallel \
  --lib recursive::native_field::
cargo test -p ix-proof-compression --no-default-features --features parallel \
  --lib recursive::native_verifier::reuse_tests::recursive_witness_rejects_tampering_without_native_preverification -- --exact
```

## Terminal PLONK

```sh
ix compress ROOT_PROOF_ADDRESS --plonk --out /path/to/empty-output
```

Use the four Ignition environment variables described above. The result
includes the proof envelope, native and Solidity proof encodings, generated
Solidity verifier, verifying key, admission, and candidate verifier catalog.
The candidate must be reviewed independently before configuring it for
`ix verify`. See the [helper guide](../../tools/plonk-wrapper/README.md)
for standalone proving, validated Lagrange import, CUDA configuration, and
artifact cache rules. On-chain verification uses the terminal PLONK verifier
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

## Library interfaces and tests

The library also exposes `pipeline::prepare_root` for aggregate roots with
multiple Aiur trace shards, `FixedRoot` for a bounded normalized root, and
`pipeline::setup` to construct a verifier from trusted parameters without a
proof witness. `Prepared::prove_fri`, `prepare_kzg`, `Prepared::prove_kzg` and
`prepare_recursive` compose the stages with caller-selected bounds and SRS.
These APIs return verifier-only metadata and keep the expected claim separate
from the proof. They do not register a verifier in the application's bundled
catalog. The CLI uses the worker and trusted verifying keys described above.

`fri` constrains FRI verification, `foreign` translates Goldilocks arithmetic
into scalar-field constraints, `kzg` implements the commitment backend, and
`recursive` constrains KZG verification with public pairing operands.
`pipeline` runs the stages through the Plonkish API, exposed by
`ix-compression-worker`.

Focused CPU checks use the small BN254 fixtures:

```sh
cargo test --release --locked -p ix-proof-compression --test bn254_kzg
cargo test --release --locked -p ix-proof-compression --test kzg_transcripts
python3 tests/check_compression_build.py \
  --toolchain /path/to/lean-4.34.1-linux --out /tmp/ix-build-config
```

`tests/kzg_backend_parity.py` compares independent CPU/CUDA builds on small
ordinary KZG proofs. Complete Init proofs, GPU tests, and sizing runs have
substantial resource costs and are run separately from the small checks.
The CLI tests cover setup selection, claim type checks, unsupported proof
versions, and rejection of untrusted verifying keys.

Sizing and benchmark context is retained in the
[benchmark comparison](../../docs/proof-benchmark-comparison.md) and
[stage construction notes](../../docs/compression-stage-collapse.md).
The retired BLS implementation is preserved on `sb/bn254-bls-preserved`.
