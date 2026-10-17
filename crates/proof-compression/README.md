# Proof compression

## Experimental BN254 backend

The `bn254` feature selects BN254 for the KZG library, including scalar
arithmetic, FFTs, commitments, batched openings, BLAKE3 transcripts, compact
proof encoding, recursive verifier gadgets and the standalone compression
worker. Use it independently of the BLS12-381 terminal-backend features:

```sh
cargo test -p ix-proof-compression --no-default-features \
  --features bn254,parallel --test bn254_kzg
```

BN254 supports an explicit known-trapdoor development SRS and caller-admitted
Ignition parameters. The importer, admission and pipeline passed crate tests,
real transcript authentication/import, and cold/warm Init GPU proofs with
independent CPU verification. No production ceremony pin or BN254 verifying
key is bundled yet. Filecoin environment variables cannot select a BN254
setup. Admission of parameters and authorization of a verifying key are
separate trust decisions.
The `ix` library and its worker select the same curve through Lake's
`IX_KZG_CURVE=bls12-381|bn254` setting; BLS12-381 remains the default.
The Solidity exporter and gnark wrapper remain BLS12-381. Combining `bn254`
with the default features, `bls12-381`, `solidity` or `plonk` is unsupported
and rejected. The `bn254,cuda` integration passes CUDA component checks and
ordinary KZG proof-byte parity on a small fixture. Saved Init development
GPU proofs match CPU output; Ignition GPU proofs pass independent CPU
verification and produce identical bytes with cold/warm fixed preprocessing.

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

The CPU baseline at `52c61479` records focused debug validation with Rust
1.98.1 passing 132 BN254 tests and 114 BLS regression tests using locked,
offline dependencies. Coverage includes KZG
proofs, recursive field/curve/transcript/MSM constraints, malformed witnesses,
deferred pairings, verifying key authentication, worker selection and existing BLS
catalog fixtures. BN254 also passed verifier reuse, FRI-to-KZG stage checks,
saved Init FRI input verification and the small root-stage integration tests.
Clippy with `-D warnings` passed for both configurations, including the sizing
example. These baseline checks excluded ignored proving/benchmark tests and
larger KZG component cases; they were not the complete repository suite.

Init's complete BN254 development pipeline passed, including independent
envelope verification and rejection of substituted claims, statements,
verifying key digests and missing development opt-in. Mathlib passed native FRI,
sizing and source/translated witness checks; no complete mathlib KZG proof
was produced. The complete saved Init CUDA pipeline now passes with both
development and admitted Ignition parameters. Terminal BN254 PLONK is
available with admitted Ignition parameters: CPU and CUDA Init proofs pass
independent native verification and the adapted Solidity verifier. See the
[current PLONK results and bottleneck profile](../../docs/bls-plonk-wrapper-status.md#bn254-cuda-plonk-implementation-and-actual-witness-msms).

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
or 33,045 bytes including its packet header and statement. The final recursive
proof is 1,669 bytes, its packet is 1,909 bytes and the complete envelope is
1,917 bytes. Independent verification against the original Init claim and
root statement passed without a proving SRS or cache. Negative checks rejected
the mathlib claim, its root statement, both together, an incorrect profile
pin and omitted development opt-in. The profile pin came from the locally
generated run; it is not an independently authorized production profile.

At the recursive frontend boundaries, point validation accounts for 36.47
million BLS rows versus 0.41 million BN254 rows; BN254's cofactor-one G1
removes the BLS subgroup-check machinery. The two opening MSMs add 62.80
million versus 45.45 million rows. Transcript processing adds 19.12 million
versus 15.28 million rows, with shorter point encodings on BN254. These
increments include newly exposed public values and are not operation counts
or gnark PLONK constraint counts.

The complete Init CPU run took 3,193.0 seconds (53.2 minutes) and peaked at
96.0 GiB host RSS. Fixed preprocessing was cold and both development SRS
prefixes were generated during the run. Stage spans from TeXRay are rounded:

| Init CPU phase | First KZG | Recursive KZG |
| --- | ---: | ---: |
| Preparation and main commitments | 16.17 min | 6.44 min |
| Lookup construction | 7.04 min | 2.35 min |
| Quotient construction | 11.02 min | 4.11 min |
| Openings | 1.98 min | 1.27 min |
| Complete stage | 38.34 min | 14.87 min |

Complete stages also include input handling, circuit/witness construction,
parameter preparation, verification and output. Nested spans and prefetched
work overlap; do not sum arbitrary child spans. Native final packet
verification took 3.96 ms inside the prover; the separate verification process
took 15.5 ms including startup and file loading. Main trace shapes and phase
logs do not provide complete FFT-call, field-operation or prover-MSM totals.

These are structural comparisons. Historical BLS timings use CUDA, Filecoin
parameters and an older build with a Keccak final transcript; current BN254
runs use CPU, development parameters and BLAKE3. A curve-speed comparison
requires matching those conditions.

### Ignition parameter import

The BN254-only `kzg_ignition_import` example provides local transcript
inspection, import and authenticated prefix loading. The real `2^26` import
and authenticated cache loads passed on 2026-10-16. To build the tool:

```sh
cargo build --release --locked -p ix-proof-compression \
  --no-default-features --features bn254,parallel --example kzg_ignition_import
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
No ceremony pin is built in. See the
[setup research](../../docs/compression-architecture-options.md#bn254-trusted-setup-research-2026-10-16).

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
evidence are stored in the same S3 bucket as the BLS parameters:
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
passed: 249 for BN254 and 238 for BLS12-381, with five ignored on each.
The CUDA module suites also passed all thirty checks on each curve.
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
  /path/to/root/root-claims.bin /path/to/run/final-kzg/verifier.bin \
  "$BN254_PROFILE_DIGEST" /path/to/new-admission.json \
  "$IGNITION_ADMISSION_BLAKE3"
```

This command reads no proving cache or setup environment and rejects
`--dev-srs`. The library equivalent is `verify_with_ignition_admission`,
with an `IgnitionAdmission` authenticated using `read` or `from_bytes`.
Ordinary application verification continues to use its release-bundled
verifying key catalog. A future BN254 production entry must bundle both
the verifying key digest and the admitted setup pin; generating either
artifact does not add that entry. The BN254 catalog remains empty and admits
no development entries. Existing BLS interfaces/catalogs are unchanged.

### Real Init with Ignition

The saved Init FRI proof completed both KZG stages using admitted Ignition
parameters, first with cold fixed preprocessing and then with it reused.
The ceremony import was already prepared and is excluded from these timings.
Independent CPU verification passed for both runs after removing
proving-cache and setup environment variables. Seven negative checks per run
rejected a corrupt proof, wrong claim, wrong expected statement, wrong
verifying key digest, wrong admission pin, corrupt admission and a development
verifying key. Each verification report includes a CPU capability check as
its ninth check.

| Measurement | Cold fixed preprocessing | Warm fixed preprocessing |
| --- | ---: | ---: |
| First KZG wall time | 210.89 s | 135.94 s |
| Recursive KZG wall time | 72.69 s | 44.56 s |
| Complete pipeline wall time | 284.30 s | 181.13 s |
| First KZG peak process RSS | 175.283 GiB | 175.287 GiB |
| Recursive KZG peak process RSS | 81.155 GiB | 63.161 GiB |
| First KZG sampled peak GPU memory | 28,954 MiB | 28,952 MiB |
| Recursive KZG sampled peak GPU memory | 60,696 MiB | 58,648 MiB |

Both stages use the same admitted setup identity and full public degree
100,799,999. The first stage retains nineteen circuits, 113,913,480 gates and
31,689,479 lookups. The recursive frontend has 61,151,377 rows, 372 more than
the development setup, and still pads to `2^26`. These are single runs with
uncontrolled OS page cache. Different binaries and setup parameters prevent
attributing differences from the development benchmark to the ceremony.

The envelope is **1,917 bytes** and the portable verifying key is **1,542
bytes**. Both are byte-identical between the cold and warm runs, as are the
compact proofs from both KZG stages. The verifying key uses the same
structure as BLS12-381, implemented by `VerifierProfile`, with BN254 version 7,
circuit metadata and both opening equations. Its locally pinned BLAKE3
digest is
`a4cf1b3b2489af6c939847d5060452bccb1f87ed8cff0fb90658e477549eafcd`.
This key has not been added to the verifying key catalog.

Artifacts are under `/opt/dlami/nvme/ix-bn254/ignition-validation/`:
`experiment.json` records both runs and byte comparisons; `cold/run/` and
`warm/run/` contain their envelopes and verifying keys. Each run's
`verification/verification-report.json` records all independent checks and
`stages/` contains resource logs. The admitted parameter settings
remain in `/opt/dlami/nvme/ix-bn254/parameters/ignition/setup.env`.

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

BN254 has no bundled verifying key catalog entry. Its packet and verifying
key versions are separate from BLS, and generating a key does not authorize
it. For local verification, set `BN254_PROFILE_DIGEST` to the independently
reviewed BLAKE3 digest of `final-kzg/verifier.bin`, then supply that pin,
the original claim and independently expected root claims:

```sh
"$IX_COMPRESSION_WORKER" pipeline verify \
  /path/to/bn254-run/proof.envelope.bin /path/to/claim.bin \
  /path/to/root/root-claims.bin /path/to/bn254-run/final-kzg/verifier.bin \
  "$BN254_PROFILE_DIGEST" --dev-srs
```

Verification needs no proving SRS or cache. It checks the verifying key
digest, development opt-in, claim digest, all expected statement words, outer
KZG proof and deferred pairing. The generated report records the verifying
key digest for inspection; the verifier never obtains its trusted pin from
the proof.
The library equivalents are `compress`, `compress_fri` and
`verify_with_profile`. `ix verify` uses the catalog for its compiled curve;
BN254 has no authorized entries yet, so use the worker command above with an
explicit verifying key for development verification.

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

CPU/GPU parity and real Init pipeline measurements are recorded below. The
BN254 gnark wrapper now proves and verifies the actual Ignition Init packet,
including both pairing obligations and the two public claim-digest limbs.
The classic-GLV helper with separate pairing checks uses 14,689,442 rows and
domain 2^24. Core proving took 53.79 seconds, the fresh prover process took
73.70 seconds, and peak RSS was 25.19 GiB. The native proof is 584 bytes, or
624 bytes with its ix envelope. The matching basis and keys are now cached;
their 5m 58s preparation cost is excluded from proof timing. Independent native
and catalog verification passed. See the
[PLONK measurement and setup record](../../docs/bls-plonk-wrapper-status.md#bn254-224-full-init-proof-benchmark).

The same proof passes local Anvil verification through a constants-only SP1
verifier adaptation and ix's claim adapter at 320,103 total transaction gas.
See the [Solidity result](../../contracts/plonk/README.md#actual-bn254-init-proof-on-anvil).
Remaining work includes complete CLI packaging.
Review the authenticated BN254
ceremony provisioning, verifying key/catalog authorization and regenerated
fixtures before enabling production releases.

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
Verification requires the corresponding bundled development verifying key and
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

Verification uses the verifying keys compiled into the application from
`profiles/`. `ix verify` selects a verifying key by the packet's ID and derives
the expected statement from that key's pinned aggregation-program prefix and
the hash of the caller's serialized claim. It checks the compact proof and
both pairing obligations without an external key file, registry, proving SRS
or GPU.

Ordinary `ix verify` does not import external verifying keys, and local files
under `~/.ix/verifiers` have no effect. Unknown verifying key IDs are rejected;
adding an accepted key requires an application update. The standalone
worker's `pipeline verify` command instead requires an explicit verifying key
digest and expected statement, as described above. The bundled BLS verifying
keys are:

| Verifying key | Setup | First-stage log-height |
| --- | --- | --- |
| `aggregate-filecoin-v5.bin` | Filecoin | 24 |
| `aggregate-development-v5.bin` | Development, requires `--dev-srs` | 24 |

The adjacent JSON files record the setup, root key and artifact identities.
The verifying key catalog pins each key and its aggregation-program prefix.
The public claim is supplied by the caller rather than copied from the
packet, so a bundled key verifies any aggregate root proved by the same
recursive circuit. `ix compress` derives the statement from the aggregation
backend instead and fails if a bundled key pins a different program than
the build it runs in, so a stale bundle is caught where the backend is available.

Compression does not require a verifying key to be bundled before proving. It
constructs its circuit, verifies its output and writes `final-kzg/verifier.bin`
as an output of the run. That file can be reviewed and bundled in a later
application release; generating it does not register it for verification.

The packet carries the 18-word public claim, a verifying key ID, two compressed G1
opening-pairing operands and the compact `KQP4` KZG proof. Generic Serde
serialization of complete KZG proofs is unsupported; callers use
`FixedProofCodec` with the expected proof shape. Internal commitment metadata
retains its canonical encoding and checks nested counts before allocating.

Every setup declares its complete public polynomial degree. Loading a shorter
proving prefix or only verifier anchors preserves that degree and the setup
identity. The Filecoin identity derives from the ceremony digest and its
`2^28 - 2` public degree, so every prefix cache of it binds the same
checkpoints and verifying keys. Development identities derive from the
seed and declared degree; the trapdoor remains known.

## Final proof transcript

Portable BLS verifying key version 5 uses Keccak-256 for recursive KZG proofs.
The FRI proof, first KZG proof and the recursive circuit's verification of
that first proof retain BLAKE3. The compact proof layout and SRS are unchanged.
The verifying key version selects the transcript without trying alternatives;
application verification also requires that exact key to be bundled.
Setup bindings include the transcript choice. Metadata checksums and key
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

This transcript lets a custom Ethereum verifier use native Keccak;
it does not change the proof into a standard PLONK format. The optional
[Solidity verifier prototype](../../contracts/kzg/README.md) provides a native
verifying key exporter and local EVM conformance tests.

## GPU proving

### Curve selection and validation status

Lake uses `IX_KZG_CURVE=bls12-381|bn254` for both `ix` and the single
`ix-compression-worker` target. `IX_CUDA=1` enables the selected KZG CUDA
backend and Goldilocks CUDA. BN254 builds its matching PLONK helper and selects
explicitly admitted Ignition parameters or `--dev-srs`. Curve features
participate in the Cargo arguments and
Lake artifact traces, so switching the curve rebuilds both the CLI library
and worker. Keep complete builds in separate worktrees for side-by-side
comparisons; both curves use the usual executable names and runtime layout.

The source changes select sppark's BN254 field instantiation, use four-limb
MSM outputs and 72-byte affine uploads, derive SRS-cache allocation estimates
from the selected point types, and limit BN254 FFT domains to `2^28`.
Rust and C++ layout assertions cover the bridge. A host-only check compares
Fq/Fr moduli, Montgomery one and R-squared before CUDA device discovery.

The lookup, quotient and constraint-pass descriptors have paired Rust/C++
layout assertions. Dense and pass execution retain their existing supported
trace ranges. `IX_KZG_CUDA_PASSES=force` requires the pass path for an eligible
kernel invocation and fails if it cannot run; it cannot silently use the
dense path. Unsupported lookup/quotient shapes and storage report CPU
construction in the logs. MSM scratch keeps the conservative 384-byte
per-point allowance on both curves, with separate bucket headroom and native
cache estimates; it does not scale every buffer by the point-size reduction.
Pinned transfer rings remain bounded at 256 MiB per device when both lanes
are used. FFT batches publish resident handles only after every job succeeds;
native destruction checks device ownership, and transfer rings clean up in
their owning context.

Small or disk-backed FFT, MSM and opening work reports CPU dispatch at debug
level; use `RUST_LOG=ix_proof_compression=debug` when collecting parity logs.

On October 16, 2026, the BN254 CUDA library test target compiled with Rust
1.98.1, CUDA 13.3.73 and NVIDIA driver 595.91.07 for SM 120. The focused
`kzg::cuda::tests::cuda_base_and_scalar_arithmetic_match_arkworks` test passed
on GPU 0, an RTX PRO 6000 Blackwell Server Edition. It checks six device
operations on 32 inputs in each of Fq and Fr against Arkworks, including zero,
modulus-boundary and high-limb values. The host field-representation guard
also passed during device initialization. Compilation took 1m 02s and the
test runner took 0.34s; these are test timings, not proving benchmarks.

The command used the working-tree CUDA port atop CPU baseline `52c61479`:

```sh
CARGO_HOME="$PWD/target/cargo-home" CUDA_HOME=/usr/local/cuda-13.3 \
NVCC=/usr/local/cuda-13.3/bin/nvcc IX_KZG_CUDA_ARCHS=120 \
MULTI_STARK_CUDA_ARCHS=120 CUDA_VISIBLE_DEVICES=0 \
cargo test --locked -p ix-proof-compression --no-default-features \
  --features bn254,parallel,cuda --lib \
  kzg::cuda::tests::cuda_base_and_scalar_arithmetic_match_arkworks \
  -- --exact --ignored --nocapture
```

Follow-up validation on the same source completed every CUDA-module test on
both curves, using normal build and test parallelism:

| Configuration | Host/ABI checks | GPU checks | Failures |
| --- | ---: | ---: | ---: |
| `bn254,parallel,cuda` | 12 | 18 | 0 |
| `bls12-381,parallel,cuda` | 12 | 18 | 0 |

The 60 checks cover native field parameters and their rejection cases, every
supported NTT root and inverse-size factor, oversized-domain rejection,
point transport, subgroup/coset FFTs, zero-padding and batched order. MSM and
polynomial cases cover exceptional points, chunk tails, structured-scalar
normalization, resident inputs, evaluation and division. Cached MSM checks
cover offsets, owner isolation, eviction/re-upload and rejected requests.
Dense and forced-pass lookup/quotient output matches CPU calculations on
1,024-row host and 65,536-row resident fixtures, including next-row access,
constant columns, zero denominators and quotient cosets.

The single-device concurrency checks also passed, including the `2^20`-point
MSM case. Each curve's two-device admission check passed separately with
`CUDA_VISIBLE_DEVICES=0,1`; other GPU checks used device 0. This validates
resident-buffer selection, not multi-GPU proving performance. The BLS CUDA
test target compiled in 42.90s. Test timings are not curve-speed benchmarks.
Local per-run commands, logs and source hashes are recorded in
`target/gpu-parity/cuda-component-parity.json`.

The [proof fixture](examples/kzg_backend_parity.rs) also passed exact byte
comparison between separate CPU and CUDA binaries on both curves. It proves
two ordinary KZG circuits with 4,096 and 8,192 rows, five grouped lookups,
next-row openings and a quotient-factor cap of four, using an 8,192-power
development SRS. The CPU, dense GPU, forced-pass GPU and cached-SRS GPU modes
produce identical proof and verifier bytes within each curve:

| Curve | Compact proof bytes | Modes with identical bytes |
| --- | ---: | --- |
| BN254 | 1,861 | CPU, dense GPU, forced passes, cached SRS |
| BLS12-381 | 2,197 | CPU, dense GPU, forced passes, cached SRS |

GPU dispatch is checked in the logs. CPU binaries independently verify every
mode with the CPU-generated, digest-pinned verifier; CUDA binaries also
verify the CPU proofs with no GPU visible. Changed claims, evaluations,
verifier pins and proofs from the other curve are rejected. These checks
exclude FRI compression, recursive KZG proving and production setup trust.
Peak process RSS across the fixture runs was under 480 MiB; peak VRAM was
not recorded. This is not a production resource or performance measurement.
The [runner](../../tests/kzg_backend_parity.py) retains separate binaries,
native libraries, proofs, verifier pins, command logs and resource records.
The local result is `target/gpu-parity/proof-matrix-v2/report.json`, with
strict rejection checks in `strict-negative-report.json` alongside it.

The complete Lake configuration typechecked with Lean 4.34.1.
[`tests/check_compression_build.py`](../../tests/check_compression_build.py)
passed seven argument-selection cases covering both curves, CPU/CUDA,
trace-codegen implying CUDA, the default, and the nonparallel configuration;
an invalid curve is rejected. These evaluate build arguments without
starting a project build or constraining the parallelism of proving runs.
Cargo feature-tree inspection also confirms the matching curve selection in
`ix-ffi`. The local configuration report is
`target/gpu-parity/cli-config/report.json`. Narrow Clippy checks with
`-D warnings` passed for the parity example under BN254/CUDA and BLS/CPU.

The full saved Init first-KZG and recursive-KZG stages also pass on both
curves. BN254 produces exactly the CPU run's proof bytes at both boundaries,
and its final envelope passes the original CPU worker's verifier. The
[matched Init measurement](#matched-init-gpu-comparison) records timings,
memory, setup and cache conditions. GPU FRI compression, full-size BLS
CPU/GPU byte comparison, injected asynchronous failure recovery, complete
CLI linking and larger inputs still require the gates in the
[GPU plan](../../docs/compression-architecture-options.md#bn254-gpu-integration-plan).

After authorizing machine time, reproduce the small proof comparison with
the CUDA toolkit and locked Cargo dependencies available:

```sh
python3 tests/kzg_backend_parity.py --out target/kzg-proof-parity
python3 tests/check_compression_build.py \
  --toolchain /path/to/lean-4.34.1-linux --out target/kzg-build-config
```

After machine time is authorized, the BN254 build selection is:

```sh
IX_KZG_CURVE=bn254 IX_CUDA=1 MULTI_STARK_CUDA_ARCHS=120 lake build ix
```

Omit `IX_CUDA=1` for a CPU build. Direct Cargo builds select
`--no-default-features --features bn254,parallel,plonk` for both `ix-ffi` and
`ix-proof-compression`; add `cuda` to each for the GPU configuration.
KZG kernels remain in the worker, while `ix-ffi/cuda` enables Aiur CUDA.
Default Cargo and Lake builds retain BLS12-381 and its terminal backends.
Terminal BN254 PLONK requires authenticated Ignition parameters and an
independently authorized verifier catalog. See the
[helper documentation](../../tools/bls-plonk-wrapper/README.md) for parameter
export, validated SP1 Lagrange import and the selected helper executable.

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
Every KZG stage requires an admitted production setup or explicit `--dev-srs`.
BLS uses Filecoin configuration; BN254 uses the four Ignition settings above.

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

### Matched Init GPU comparison

On October 16, 2026, both optimized CUDA workers completed the same saved
Init compressed FRI input, using the working tree above CPU baseline
`52c61479`. Both used BLAKE3 transcripts and known-trapdoor development
parameters, one RTX PRO 6000 Blackwell Server Edition, all 48 logical CPUs
of the Xeon Platinum 8559C host, 499 GiB RAM, and local NVMe. Toolchain:
Rust 1.98.1, CUDA 13.3.73, driver 595.91.07, SM 120.

These are **cold fixed-preprocessing** measurements with **prepared SRS
caches** and fresh worker processes. Each curve started with an empty fixed
cache. OS page caches were uncontrolled. Whole-process wall times include
SRS loading, frontend construction, witness generation, fixed preprocessing,
proving, verification, output and cache publication. Builds, SRS generation,
FRI compression and gaps between worker invocations are excluded. There is
one cold measurement per curve. A subsequent warm BN254 rerun is recorded
below; BLS warm timing has not been measured for these builds.

| Stage | BN254 | BLS12-381 | BLS time / BN254 time |
| --- | ---: | ---: | ---: |
| First KZG | 206.66 s | 225.18 s | 1.09× |
| Recursive KZG | 69.34 s | 153.01 s | 2.21× |
| **Total** | **276.00 s** | **378.19 s** | **1.37×** |

BN254 used 27.0% less total wall time in this run. Its recursive computation
trace has `2^26` rows, versus BLS's `2^27`; this measures the complete
curve-specific pipelines, not an isolated field or MSM speedup. Both used
`IX_KZG_CUDA_DEVICES=0`, `CUDA_VISIBLE_DEVICES=0`,
`IX_KZG_CUDA_RESIDENT_GIB=8`, `IX_KZG_MSM_CHUNK_POINTS=16777216`,
`IX_KZG_CUDA_PASSES=1`, `IX_KZG_CUDA_SRS_CACHE=0`, and `IX_TEXRAY=1`.
Neither run capped CPU thread counts. First-stage constraints ran densely;
both recursive lookups used GPU passes. The BN254 recursive quotient fit
densely, while BLS used passes.

| Curve / stage | Peak process RSS | Sampled peak GPU memory |
| --- | ---: | ---: |
| BN254 first | 175.28 GiB | 27.73 GiB |
| BN254 recursive | 81.16 GiB | 58.73 GiB |
| BLS first | 175.80 GiB | 27.73 GiB |
| BLS recursive | 164.52 GiB | 64.70 GiB |

GPU memory was sampled every two seconds and includes allocator
reservations. Both stages verified natively, including the deferred
pairings. BN254's compact proofs, packets and profile match the completed
CPU run byte for byte; its 1,917-byte envelope also verifies with that CPU
worker and its prior profile pin. The BLS envelope is 2,189 bytes and its
profile matches the existing bundled development-v6 profile. Both portable
envelopes verify with no GPU visible, and wrong profile pins and missing
development opt-in are rejected.

The local record is `target/gpu-parity/init-comparison.json`. Frozen workers,
native libraries, proofs, fixed caches, command logs and resource samples
are under `/opt/dlami/nvme/ix-gpu-compare-52c61479/`; `experiment.json` records
input and source hashes, and `report.json` contains the comparison.
The [stage supervisor](../../tests/run_gpu_stage.py) measures whole-process
wall time and memory. [SRS preparation](examples/kzg_dev_srs.rs) can be run
before timing, and the [metadata inspector](examples/kzg_stage_resources.rs)
estimates column/pass memory without allocating proving matrices.

BN254's fixed checkpoints total 114.79 GiB (84.77 GiB first stage and
30.02 GiB recursive). Generating and writing them took 122.39 seconds in
the fixed-preparation spans. These figures favor local generation and reuse
on this hardware; downloading that volume is not necessarily cheaper.
The current cache is trusted local data keyed by executable and profile.
Distributing checkpoints would additionally require authenticated manifests
and an explicit compatibility contract. Ceremony SRS distribution is a
separate concern.

### Warm BN254 Init rerun

A second BN254 run reused the exact frozen worker, native library, input,
GPU settings, SRS cache and fixed-preprocessing entries from the matched
comparison. Both stages used fresh processes and output directories, and
both logged a fixed-cache hit. OS page caches remained uncontrolled.

| Stage | Cold | Warm | Saved |
| --- | ---: | ---: | ---: |
| First KZG | 206.66 s | 153.16 s | 53.49 s |
| Recursive KZG | 69.34 s | 48.48 s | 20.86 s |
| **Total** | **276.00 s** | **201.64 s** | **74.36 s** |

Warm proving used 26.9% less total wall time (1.37× speedup). Simply
subtracting the cold fixed-preparation spans predicted 153.61 seconds,
48.03 seconds below the measured warm total. Cache validation and restore
took 10.60 seconds for the first stage and 5.32 seconds for recursion;
loading the saved coefficients during preparation adds further work.

The compact proofs, packets, profiles and final 1,917-byte envelope match
the cold run exactly. The original CPU worker independently verifies the
warm envelope with the original claim, expected root claims and profile
pin, with no GPU visible. Peak process RSS was 175.28 GiB for the first
stage and 63.17 GiB for recursion.

The local report is `target/gpu-parity/init-bn254-warm.json`; the NVMe copy
is `/opt/dlami/nvme/ix-gpu-compare-52c61479/bn254/warm-report.json`. Proofs
are under that curve's `warm/` directory, with stage logs and resource
samples in `logs/warm-first-kzg/` and `logs/warm-recursive-kzg/`. These
measurements use the same saved-FRI-to-KZG scope as the cold comparison.

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
