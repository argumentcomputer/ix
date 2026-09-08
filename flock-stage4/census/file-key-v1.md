# File-backed proving-key polynomials and memory

This report records the fixed-key storage pass with the memory prover
workspace. The subsequent [file prover workspace](file-workspace-v1.md)
replaces the temporary-polynomial schedule, and the
[owned-input pass](owned-inputs-v1.md) provides the current RAM assessment.
The key's storage layout and circuit census are unchanged.

The FFLONK preprocessor can now write its fixed polynomials directly to
authenticated scratch storage, and the same prover consumes either key backend.
On the 65,536-row synthetic fixture, this reduces total proving heap from
**168.4 MB to 118.1 MB (29.88%)** and preprocessing heap from
**118.1 MB to 63.6 MB (46.17%)**, with essentially unchanged proving time.

At the complete fixture's size, the new key replaces **768 GiB** of retained
polynomials with **608 GiB of scratch storage** and a **9.5 MiB authentication
index**. Combined with the preceding file-SRS implementation, the retained
SRS/key minimum falls from **1,032 GiB to about 264 GiB**.

**A complete proof on 512 GB RAM remains unsupported.** The current witness
and temporary polynomial schedule still exceeds that budget. The reduced
retained-key minimum is not a peak-RAM estimate.

Implementation: `50377fd200a4c96200067e9307bb9aef9fccca40`, following
`9de2fd3531419ce3e8dd0d72c437157d548e8dbc`.
The circuit and arithmetization are unchanged; the complete
[circuit census](stage2-integration-v3.md) remains current and was not rerun.
The separate 100-query Stage 2 profile still needs its own census.
See also the [preceding SRS measurements](file-srs-v1.md) and
[machine-readable results](file-key-v1.json).

## What changed

`preprocess_fflonk_to_file(srs, arithmetization, storage)` constructs
`FflonkFilePreprocessedCircuitV1<R>` directly. With `R = std::fs::File`,
polynomial data lives on disk; a caller-supplied buffered reader can retain
additional memory. The existing `preprocess_fflonk` API still returns the
materialized development key.

The new preprocessor computes one selector IFFT at a time. Sigma construction
keeps one column plus the domain's omega powers, stores the evaluations, then
transforms that same column in place. C0 is packed in bounded batches from
the stored coefficient columns and committed through the new
`commit_polynomial_source` API. Preprocessing never constructs the complete
materialized polynomial key or an 8n-field C0 vector.

`prove_fflonk` now accepts `FflonkProvingKeyV1`. Fixed-polynomial evaluation,
scaled additions, and C0 reads stream through bounded buffers. Sigma
evaluation reads cache one chunk per column across the smaller inversion
batches. Multiplication loads one fixed coefficient polynomial when needed;
the underlying polynomial FFTs and temporary proof polynomials remain
materialized. In-memory keys expose borrowed slices through the same interface.

Both built-in SRS backends commit streamed coefficients with at most 65,536
scalar fields per read. The streamed API requires the declared length,
including trailing zeros, to fit the SRS. The existing slice commitment API
keeps its trailing-zero trimming behavior. Custom SRS implementations must
implement streamed commitment support to use direct file preprocessing; the
default reports an explicit unsupported-operation error.

Preprocessing digests, verifier keys, transcript challenges, and the fixed
992-byte proof transport are unchanged. Direct comparison tests cover both
key backends, all three SRS storage configurations, and zero/nonzero blinding.

## Measured heap and time

Every sample uses the same authenticated, **uncompressed file SRS**, synthetic
multiplication fixture, witness, and nonzero blinding as the previous report.
Only the key storage mode changes between paired runs.

| Domain | Key | Retained heap | Additional peak | Total proving peak | Prove time |
| ---: | :--- | ---: | ---: | ---: | ---: |
| 16,384 | Memory | 21,234,931 | 41,028,288 | 62,263,219 | 5.435 s |
| 16,384 | File | 8,652,617 | 41,028,288 | 49,680,905 | 5.597 s |
| 65,536 | Memory | 84,936,147 | 83,495,616 | 168,431,763 | 21.644 s |
| 65,536 | File | 34,605,289 | 83,495,616 | 118,100,905 | 21.617 s |

The retained heap falls by **59.26%** at 65,536 rows. Additional peak heap
is unchanged in both pairs: these fixtures still peak in the materialized
temporary-polynomial/MSM schedule. Total peak falls by **20.21%** at
16,384 rows and **29.88%** at 65,536 rows.

Preprocessing is now measured separately, beginning after the SRS and
arithmetization have been constructed:

| Domain | Key | Initial live heap | Total preprocessing peak | Preprocess time |
| ---: | :--- | ---: | ---: | ---: |
| 16,384 | Memory | 8,652,019 | 49,680,435 | 0.847 s |
| 16,384 | File | 8,652,081 | 37,622,409 | 0.863 s |
| 65,536 | Memory | 34,604,499 | 118,100,243 | 3.412 s |
| 65,536 | File | 34,604,561 | 63,575,081 | 3.338 s |

The polynomial scratch files contain 9,961,472 bytes at 16,384 rows and
39,845,888 bytes at 65,536 rows. Their authentication indexes use 416 and
608 bytes, respectively. Small initial/retained-count differences include
command-line and fixed bookkeeping allocations.

All four proofs verified. Their BLAKE3 proof digests match each other and
the previous file-SRS report:

| Domain | Proof digest |
| ---: | :--- |
| 16,384 | `65d7ed465f8a91fa6b057ed6c61a2eec853537147788847473f38152d3fc86c5` |
| 65,536 | `c23b58fa94b8f4d88508a376323850fce2837e949262155b58b7e458eb683ff7` |

These are requested live heap allocations, not RSS. They exclude allocator
overhead, transient allocation inside realloc, stack, filesystem cache, and
other process memory. The proving measurement includes all setup, R1CS, and
witness allocations that remain live during proving. The preprocessing
measurement excludes SRS creation/import and initial relation construction.
Timings are single sequential runs on a shared host, with background load
and filesystem cache uncontrolled; they do not establish full-fixture
throughput or disk performance.

## Storage and authentication

The file stores canonical 32-byte little-endian Fr values with no header.
Offsets below are measured in field elements; multiply by 32 for byte offsets.

| Polynomial data | Start | Length |
| :--- | ---: | ---: |
| QL coefficients | 0 | n |
| QR coefficients | n | n |
| QM coefficients | 2n | n |
| QO coefficients | 3n | n |
| QC coefficients | 4n | n |
| Sigma1 evaluations | 5n | n |
| Sigma1 coefficients | 6n | n |
| Sigma2 evaluations | 7n | n |
| Sigma2 coefficients | 8n | n |
| Sigma3 evaluations | 9n | n |
| Sigma3 coefficients | 10n | n |
| C0 coefficients | 11n | 8n |

Five selector evaluation columns retained by the materialized key are unused
by proving and omitted from disk storage. Total payload is **19n × 32 bytes**.
C0 retains the original QL, QR, QO, QM, QC, Sigma1, Sigma2, Sigma3 interleaving.

Each polynomial is divided into chunks of at most 65,536 fields. A retained
32-byte BLAKE3 digest binds the domain
`ix:stage4:fflonk-polynomial-chunk:bls12-381:v1`, absolute chunk byte offset,
byte length, and exact encoded values. Offsets and lengths use u64 little-endian
encoding. Hashes are computed from generated values before writing. Every read
authenticates a complete local chunk before canonical decoding, including when
the caller requests only part of that chunk. Modified or truncated data,
I/O failures, and poisoned locks produce errors.

The authentication index costs:

```text
32 × (11 × ceil(n / 65,536) + ceil(8n / 65,536)) bytes
```

This is **scratch storage**, with trusted key metadata and hashes held in
memory. Reopening the raw file does not import a proving key. The caller
provides an empty readable/writable/seekable file and controls its lifetime,
cleanup, and durability. Failed preprocessing can leave a partial file.
The library rejects nonempty storage and never truncates an existing file.

Polynomial I/O uses a 2 MiB encoded chunk. Streaming consumers normally use
another 2 MiB field buffer; the permutation step caches up to 6 MiB across
three sigma columns. C0 packing uses up to 16 MiB of interleaved fields plus
bounded column and encoding buffers. These coexist with other workspaces;
none is an aggregate process-memory limit.

## Capacity at the complete fixture

For the unchanged n = 2^30 domain on this 64-bit build:

| Quantity | Bytes | Binary units |
| :--- | ---: | ---: |
| Previous retained polynomial data | 824,633,720,832 | 768 GiB |
| New polynomial scratch payload | 652,835,028,992 | 608 GiB |
| Polynomial authentication index | 9,961,472 | 9.5 MiB |
| Gates and copy cells still retained | 283,467,841,536 | 264 GiB |
| File-SRS authentication index | 4,718,624 | 4.50 MiB |
| Previous file-SRS/materialized-key minimum | 1,108,106,280,992 | 1,032 GiB |
| New file-SRS/file-key minimum | 283,482,521,632 | 264.014 GiB |

The native capacity model uses 216 bytes per gate, 16 bytes per copy cell,
and 32 bytes per Fr. These minima exclude R1CS, the original witness, spare
vector capacity, allocator overhead, reader state, filesystem cache, temporary
polynomial/MSM/FFT buffers, and other process memory.

There is still a concrete allocation obstacle before the first commitment:
the prover retains three wire evaluation columns, three wire coefficient
columns, and both public-input forms during the public-input IFFT.
Those eight columns add **256 GiB** to the retained key/index minimum.
That already reaches **558,360,428,576 bytes
(520.014 GiB)**, before the excluded allocations and later proof rounds.

The RAM target remains 512,000,000,000 bytes (476.84 GiB), with a proposed
64 GiB reserve and no implemented aggregate memory cap. Remaining work is
spillable witness and temporary polynomial buffers, external FFTs,
streamed gate/witness processing and copy-permutation construction, and an
enforced budget across all of them. A full production proof and peak-RSS
measurement are still required.

## Validation and reproduction

All **135 Stage 4 tests**, **63 regular host tests**, and **13 serial
cryptographic vectors** passed, together with formatting and Clippy in both
workspaces. Storage tests cover partial and multiple chunks, short I/O,
truncation, external mutations in early and late proof rounds, I/O and lock
failures, coefficient-stream bounds, C0 interleaving, and cross-chunk sigma
processing. The full circuit projection was not repeated because the
circuit and arithmetization did not change.

To reproduce a pair at 65,536 rows, use an existing matching test SRS archive
or let the example create one, then provide a **new** polynomial scratch path:

```sh
cargo run --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-fflonk --example prover_memory -- \
  16 /tmp/ix-test-16-uncompressed.srs uncompressed

cargo run --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-fflonk --example prover_memory -- \
  16 /tmp/ix-test-16-uncompressed.srs uncompressed /tmp/ix-test-16-key.bin
```

The example uses public test-only tau 29. Existing SRS files are validated
and reused only when the fixture settings match. Polynomial scratch files
are created with `create_new`; choose a fresh path for each run.
