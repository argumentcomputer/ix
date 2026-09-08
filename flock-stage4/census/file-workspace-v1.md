# File-backed prover workspace and memory

This report records the file-workspace pass with borrowed circuit inputs.
The subsequent [owned-input pass](owned-inputs-v1.md) releases the canonical
R1CS and original assignment at their last use and provides the current RAM
assessment. The polynomial schedule, storage format, and circuit census below
remain unchanged.

The FFLONK prover can now store wire values and temporary polynomials in an
authenticated scratch file. On the 65,536-row synthetic fixture, the file
workspace reduces total proving heap from **116.0 MB to 63.6 MB (45.19%)**.
Additional peak heap falls from **81.4 MB to 29.0 MB (64.41%)**. The paired
runs take 20.99 and 21.31 seconds and produce the same verified proof digest.

**A complete proof on 512 GB RAM remains unsupported.** At the complete
fixture's size, the largest transform needs one **128 GiB** field array and
a **2 MiB** roots cache. Fixed polynomials and other proof polynomials live
on disk, but the canonical R1CS, original witness, gates, and copy cells
remain resident. Those retained inputs plus witness lowering already require
at least **596.3 GB (555.37 GiB)** before allocator overhead and other buffers.

Implementation: `09a2b80bc91c7a27ac9b2cf3354972543cd1f636`, following
`6c09d06b`. The circuit and arithmetization are unchanged, so the complete
[circuit census](stage2-integration-v3.md) remains current and was not rerun.
The separate 100-query Stage 2 profile still needs its own census. See the
[preceding key report](file-key-v1.md) and
[machine-readable results](file-workspace-v1.json).

## What changed

`prove_fflonk_with_file_workspace(srs, key, r1cs, witness, blinding, storage)`
uses the same proof rounds as `prove_fflonk`. The latter retains the memory
workspace for existing callers. Both support memory or file keys and SRS
backends. With `storage: std::fs::File`, the new workspace stores wire
evaluations, A/B/C, the permutation grand product, quotient polynomials,
C1/C2, F/W1, W2, and intermediate arithmetic results on disk.

Polynomial multiplication uses this schedule:

1. Read and transform the first operand, store its evaluations, and release
   its transform array.
2. Read and transform the second operand. Multiply it by the first operand's
   evaluations through bounded authenticated reads.
3. Release the stored first evaluations and inverse-transform the second
   array in place, then write the resulting coefficients.

The file workspace uses a radix-2 FFT with bit reversal and at most 65,536
cached roots. This avoids arkworks' domain/2 roots table. The transform array
itself remains resident; this is not an external FFT. The original memory
workspace continues using arkworks' FFT implementation.

Exact division by `X^d - beta` generates quotient coefficients in ascending
order using `p_i = q_(i-d) - beta*q_i`. It keeps at most
`min(d, quotient_length)` quotient values, then checks every remaining high
coefficient to establish exact division. For `beta = 0`, it checks the low
coefficients and streams the higher coefficients directly. Thus packed
opening quotients never require an 8n- or 9n-field resident array.

Additions, scaling, shifts, evaluations, and KZG coefficient reads use bounded
chunks. C1/C2 packing consumes a complete source chunk per column in each
batch to avoid repeatedly reading the same authenticated bytes. The
permutation step caches at most one chunk from each of its six wire/sigma
columns and retains the existing 16,384-row inversion batches. Public-input
interpolation now transforms its evaluation vector in place. Z blinding
reserves its three extra coefficients explicitly.

## Measured heap and time

Every final sample uses the same synthetic multiplication fixture, public
test-only tau 29, nonzero blinding, authenticated **uncompressed file SRS**,
and authenticated **file key** as the preceding report. Only the prover
workspace mode changes within each pair.

| Domain | Workspace | Retained heap | Additional peak | Total proving peak | Prove time |
| ---: | :--- | ---: | ---: | ---: | ---: |
| 16,384 | Memory | 8,652,627 | 40,504,288 | 49,156,915 | 5.330 s |
| 16,384 | File | 8,652,757 | 28,972,850 | 37,625,607 | 5.409 s |
| 65,536 | Memory | 34,605,299 | 81,398,752 | 116,004,051 | 20.988 s |
| 65,536 | File | 34,605,429 | 28,973,042 | 63,578,471 | 21.308 s |

Total proving peak falls by **23.46%** at 16,384 rows and **45.19%** at
65,536 rows. These small fixtures still peak in bounded commitment work;
the nearly constant additional peak does not imply constant RAM use as n
grows. The FFT array and witness-lowering buffers still scale with n.
The memory workspace also improves slightly from the preceding report's
49.7/118.1 MB total peaks because of the shared allocation changes.

Preprocessing is unchanged except for recording each stored polynomial's
last nonzero index. Its total peak is about 37.6 MB at 16,384 rows and
63.6 MB at 65,536 rows; exact figures are in the JSON report. Small retained
heap differences include argument paths and fixed bookkeeping.

| Domain | Key scratch bytes | Prover scratch high-water bytes | Proof digest |
| ---: | ---: | ---: | :--- |
| 16,384 | 9,961,472 | 24,641,056 | `65d7ed465f8a91fa6b057ed6c61a2eec853537147788847473f38152d3fc86c5` |
| 65,536 | 39,845,888 | 98,565,664 | `c23b58fa94b8f4d88508a376323850fce2837e949262155b58b7e458eb683ff7` |

All four proofs verified, and their digests match both preceding storage
reports. Proof format, transcript challenges, verification keys, and
preprocessing digests are unchanged. These scratch sizes describe the
synthetic fixture; full-fixture scratch high-water usage has not been measured.

The heap metric counts requested live allocations. It excludes allocator
overhead, transient allocation inside realloc, stack, filesystem cache, and
other process memory; it is not RSS. The proving measurement includes all
relation, witness, key, and SRS allocations that remain live during proving.
Preprocessing excludes SRS creation/import and initial relation construction.
Timings are single sequential runs on a shared host with background load and
filesystem cache uncontrolled. They do not establish production throughput
or full-fixture disk performance.

## Scratch storage and failure handling

The workspace reuses the fixed-key storage's canonical 32-byte little-endian
Fr encoding and authenticated chunks. Retained BLAKE3 digests bind the
`ix:stage4:fflonk-polynomial-chunk:bls12-381:v1` domain, absolute chunk byte
offset, byte length, and exact encoded values. Offsets and lengths use u64
little-endian encoding. Hashes are computed before writing, and a read checks
a complete local chunk before decoding any requested fields.

Stored metadata also records the last nonzero index. This preserves full
length for evaluation columns and permits trimmed coefficient sources without
rereading entire zero-padded polynomials just to choose an FFT size.

Each live polynomial owns its reserved file region. Dropping it returns that
region to a best-fit allocator, which coalesces adjacent free regions.
Failed writes or generation also return their reservation. File and allocation
locks are not held while a generator reads other polynomials, so source reads
can share the same file without deadlock. A poisoned allocator stops further
allocation and never recycles regions using uncertain state.

The caller supplies an empty readable/writable/seekable file. The library
rejects nonempty storage and never truncates it; the physical file retains
its high-water size. Reopening raw bytes does not import a workspace: trusted
lengths and authentication hashes remain in memory. The caller controls file
protection, cleanup, and durability. **The file contains private witness data**,
and a failed proof can leave partial data behind. Supplying an in-memory
reader/writer instead of a `File` retains its data in RAM.

Normal I/O uses a 2 MiB encoded chunk plus bounded field buffers. C1 packing
uses up to 8 MiB of generated fields, C2 up to 6 MiB, plus bounded source and
encoding buffers. Permutation reads cache up to 12 MiB across six columns.
These coexist with other workspaces; none enforces an aggregate process limit.

## Capacity at the complete fixture

For the unchanged n = 2^30 integration fixture on this 64-bit build:

| Quantity | Bytes | Binary units |
| :--- | ---: | ---: |
| Retained file SRS/key minimum | 283,482,521,632 | 264.014 GiB |
| Largest file-workspace FFT array | 137,438,953,472 | 128 GiB |
| FFT roots cache | 2,097,152 | 2 MiB |
| Largest quotient rolling buffer | 34,359,738,368 | 32 GiB |
| Three wire columns and auxiliary-value cache during lowering | 119,779,513,424 | 111.553 GiB |
| Retained key/indexes plus largest FFT array and roots | 420,923,572,256 | 392.016 GiB |
| Canonical R1CS minimum | 172,685,269,960 | 160.826 GiB |
| Original witness minimum | 20,376,502,048 | 18.977 GiB |
| Retained relation/witness/SRS/key minimum | 476,544,293,640 | 443.816 GiB |
| Witness-lowering minimum including retained inputs | 596,323,807,064 | 555.370 GiB |
| Largest FFT stage including retained inputs | 613,985,344,264 | 571.818 GiB |

The R1CS minimum uses the census's 642,332,970 constraints at 80 bytes each
and 3,032,465,809 nonzero terms at 40 bytes each. The original witness uses
636,765,689 fields, including the constant-one slot and public fields, at
32 bytes each. Witness lowering still retains three n-field columns plus
417,507,458 auxiliary `Option<Fr>` values at 40 bytes each. Gate and copy-cell
sizes remain 216 and 16 bytes. The example reports these target-specific
resident widths so the arithmetic is reviewable.

These are allocation minima, not measured full-fixture peaks. They exclude
spare vector capacity, allocator overhead, I/O/MSM buffers, workspace indexes,
reader state, filesystem cache, and other process memory. The largest FFT
stage uses the algorithm's maximum 4n transform size; quotient and lowering
buffers are used in separate phases and are not added to that stage.

The target remains **512,000,000,000 bytes (476.84 GiB)** with a proposed
64 GiB reserve. The next major work is streaming or releasing the canonical
R1CS before later phases, streamed witness processing and copy-permutation
construction, and an enforced aggregate memory budget. External FFTs remain
an option for further headroom. A complete production proof and peak-RSS
measurement are still required.

## Validation and reproduction

All **144 Stage 4 tests**, **63 regular host tests**, and **13 serial
cryptographic vectors** passed, together with formatting and Clippy in both
workspaces. New coverage includes FFT comparisons through multiple roots
cache tiles, polynomial and packing identities, exact division across chunk
boundaries with zero/nonzero divisor constants and rejected remainders,
permutation equality at every row, complete proof equality across backends,
and first/middle/final proof-read corruption and I/O failures. Storage tests
also cover partial writes, late generator failure, extent reuse, truncation,
overflow, poisoned locks, and preservation of still-live polynomials.

Append a new prover scratch path to the existing file-key benchmark command:

```sh
cargo run --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-fflonk --example prover_memory -- \
  16 /tmp/ix-test-16-uncompressed.srs uncompressed \
  /tmp/ix-test-16-key.bin /tmp/ix-test-16-workspace.bin
```

Omit the last argument for the memory workspace. Existing matching test SRS
archives are validated and reused. Both polynomial scratch paths use
`create_new`; choose fresh paths for every run and remove them when finished.
