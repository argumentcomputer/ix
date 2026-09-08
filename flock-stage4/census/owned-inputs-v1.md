# Owned circuit inputs and compact copy cycles

The prover can release the canonical R1CS during gate lowering and release
the original assignment before polynomial work. The new ownership path uses
the same canonical gates, copy cycles, keys, and proof rounds as the borrowed
APIs. It removes the full relation from preprocessing and proving without
changing the statement proved.

On the 65,536-row synthetic fixture, owned inputs reduce total proving heap
from **63.6 MB to 46.3 MB (27.21%)** and preprocessing heap from **63.6 MB to
50.5 MB (20.62%)**. Paired prove times are 21.484 and 21.498 seconds. Both
proofs verify and match the preceding report's proof digest.

The complete fixture's native payload minimum for witness lowering falls
from **596.3 GB to 423.6 GB**. The maximum FFT stage falls from **614.0 GB to
420.9 GB**. These figures are below the 512 GB target, but **a complete proof
and its peak RAM have not been measured**. They exclude spare capacity,
transient reallocation, allocator overhead, and other buffers; there is no
enforced aggregate memory budget.

The [circuit census](stage2-integration-v3.md) remains current. This change
preserves canonical lowering and copy-permutation order, so the full census
was not rerun. The separate 100-query Stage 2 profile still needs its own
census. See the [previous workspace report](file-workspace-v1.md) for the
unchanged polynomial algorithms and storage format, and the
[machine-readable results](owned-inputs-v1.json) for exact measurements.

Implementation: `75cc586c9e5661ab59151f76e847168ecbb61dc4`, following
`13dea95dd88a6fb04c6b167285f08dd72cf0da16`.

## Input ownership and validation

The owned pipeline is:

```rust
let checked = FflonkCheckedWitnessV1::new(&r1cs, witness)?;
let arithmetization = arithmetize_r1cs_owned(r1cs)?;
let key = preprocess_fflonk_to_file(&srs, arithmetization, key_storage)?;
let output = prove_fflonk_checked_with_file_workspace(
    &srs, &key, checked, blinding, prover_storage,
)?;
```

`FflonkCheckedWitnessV1::new` checks the assignment length, constant-one slot,
and every R1CS constraint, then records the canonical relation digest. It
moves the existing assignment allocation into an immutable wrapper. Read
access exposes only shared slices. Recovering a mutable `Witness` consumes
the checked state, so subsequent checked proving requires another validation.

`arithmetize_r1cs_owned` consumes constraints in canonical order. Each
constraint's sparse terms are freed after it is lowered. The outer constraint
array is released when that iteration ends, before padding and copy-cycle
construction. It does not stream relation construction: the caller first
builds the materialized R1CS, and the final gates and copy cells remain in RAM.

The checked prover compares the relation digest, assignment length, and
public-input count with the preprocessed arithmetization. Witness lowering
still solves auxiliary values and checks every PLONK gate and copy equality.
After lowering and copying the public inputs, the prover drops the original
assignment before storing wire columns or performing FFTs.

`prove_fflonk_checked` provides the same ownership behavior with the memory
workspace. Both new entry points accept either SRS/key backend. The existing
`prove_fflonk` and `prove_fflonk_with_file_workspace` signatures retain their
borrowed behavior and share the proof implementation. Errors also consume
owned inputs; callers that need a retry must retain a copy or reconstruct the
assignment. Explicitly retaining clones also retains their memory.

## Compact copy-permutation construction

The builder now keeps one encoded last-cell pointer per wire instead of
collecting every occurrence in a separate vector. The last cell's current
successor is the first cell of its cycle. Inserting a new occurrence redirects
the last cell to the new one and the new cell to the first one. Traversing
gates in row/column order therefore preserves the previous forward cycles,
including singleton cycles and repeated occurrences within one gate.

R1CS and auxiliary identifiers occupy disjoint ranges. The dense cache uses
eight bytes per declared wire, including the constant-one slot. If the
declared slot count exceeds three times the number of gates, a sparse map
keeps one pointer per used wire. This avoids a large dense allocation for
circuits with many unused variables. Count overflow and undeclared wire
identifiers are rejected.

For the complete fixture, the dense tail array uses
`8 * (636,765,689 + 417,507,458)` = **8,434,185,176 bytes (7.855 GiB)**.
The three output copy-cell columns still use 48 bytes per domain row.
The old occurrence-list algorithm's heap and time were not separately
benchmarked in this report; both ownership modes below use the compact cache.

## Measured heap and time

Every sample uses the unchanged synthetic multiplication fixture, public
test-only tau 29, nonzero blinding, and authenticated uncompressed file SRS,
file key, and file prover workspace. Only input ownership changes within
each pair. All heap figures below are bytes of requested live allocations.

| Domain | Inputs | Relation-lowering peak | Preprocessing peak | Proving peak | Prove time |
| ---: | :--- | ---: | ---: | ---: | ---: |
| 16,384 | Borrowed | 8,913,860 | 37,622,636 | 37,625,705 | 5.404 s |
| 16,384 | Owned | 6,882,412 | 34,346,301 | 33,300,983 | 5.388 s |
| 65,536 | Borrowed | 35,652,548 | 63,575,308 | 63,578,569 | 21.484 s |
| 65,536 | Owned | 27,526,252 | 50,468,573 | 46,277,719 | 21.498 s |

Proving peak falls by **11.49%** at 16,384 rows and **27.21%** at 65,536 rows.
Relation-lowering peak falls by about **22.79%** at both sizes. Before proving
at 65,536 rows, retained heap falls from 34,605,516 to 21,498,781 bytes because
the R1CS has already been released. The checked prover then releases the
original assignment before its largest temporary allocations.

Owned mode checks and binds the assignment during the relation-lowering
measurement; borrowed mode performs that check during proving. Summing
relation-lowering, preprocessing, and proving times gives 6.238/6.233 seconds
at 16,384 rows and 24.799/24.825 seconds at 65,536 rows. SRS creation/import
and initial relation construction are outside those intervals.

All four proofs verify. Their digests match across ownership modes and match
the preceding SRS, key, and workspace reports. Key scratch sizes remain
9,961,472 and 39,845,888 bytes; prover scratch high-water sizes remain
24,641,056 and 98,565,664 bytes, respectively. Exact proof digests, retained
heap, incremental peaks, and timings are recorded in the JSON report.

The heap metric includes all inputs that remain live during each measured
phase. It excludes allocator overhead, transient realloc internals, stack,
filesystem cache, and other process memory; it is not RSS. These small
fixtures still peak in bounded commitment work. Their savings percentages
and additional heap cannot be extrapolated to the complete circuit.
Timings are single sequential runs on a shared host with background load and
filesystem cache uncontrolled; they do not establish production throughput.

## Full-fixture memory assessment

For n = 2^30 on this 64-bit build:

| Allocation or stage | Bytes | Binary units |
| :--- | ---: | ---: |
| Retained gates/copy cells and file SRS/key indexes | 283,482,521,632 | 264.014 GiB |
| Original assignment, until witness lowering finishes | 20,376,502,048 | 18.977 GiB |
| Three wire columns and auxiliary cache during lowering | 119,779,513,424 | 111.553 GiB |
| Owned witness-lowering minimum | 423,638,537,104 | 394.544 GiB |
| Owned maximum FFT-stage minimum, including key/indexes | 420,923,572,256 | 392.016 GiB |
| Canonical R1CS payload released before preprocessing | 172,685,269,960 | 160.826 GiB |

The lowering minimum adds the retained key/indexes, original assignment,
three n-field columns, and 417,507,458 auxiliary `Option<Fr>` values. The
maximum FFT stage adds the key/indexes, one 128 GiB transform array, and its
2 MiB roots cache. Lowering, quotient, and FFT buffers belong to different
phases and are not summed as simultaneous allocations.

The previous borrowed path still has its previous memory costs: it keeps the
canonical relation and original assignment live through proving. Using file
storage alone does not opt into the new ownership behavior.

The target is **512,000,000,000 bytes (476.84 GiB)**. After a proposed 64 GiB
reserve, the working budget is 443,280,523,264 bytes. The owned lowering
minimum leaves **19.64 GB (18.29 GiB)** below that working budget. This margin
has not been validated against actual vector capacities, transient allocation
during growth, I/O/MSM buffers, workspace indexes, allocator behavior, or OS
cache. Relation construction and gate lowering also need complete allocation
accounting. The reported stage minima do not bound the full pipeline.

Further work is enforcing a budget across those allocations and validating a
complete proof with peak RSS. Streaming witness lowering, external gate/copy
storage, or external FFTs could provide additional headroom. A small synthetic
proof does not establish full-fixture memory use or disk performance.

## Validation and reproduction

All **149 Stage 4 tests**, **63 regular host tests**, and **13 serial
cryptographic vectors** passed. Formatting and Clippy passed in both
workspaces. New tests compare owned/borrowed gates and witness columns;
reject malformed assignments and relation mismatches; compare dense/sparse
copy cycles with an independent occurrence-list implementation; and check
count overflow and undeclared wires. Complete proofs match with memory/file
keys and workspaces under zero and nonzero blinding. Real-file tests cover
both compressed and uncompressed SRS encodings. Existing corruption and I/O
failure tests still pass through the shared proof rounds.

Append `owned` after the two scratch paths:

```sh
cargo run --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-fflonk --example prover_memory -- \
  16 /tmp/ix-test-16-uncompressed.srs uncompressed \
  /tmp/ix-test-16-key.bin /tmp/ix-test-16-workspace.bin owned
```

Use `borrowed` or omit the sixth argument for the baseline ownership mode.
Existing matching test SRS archives are validated and reused. Both scratch
paths use `create_new`; choose fresh paths for each run. The prover scratch
file contains private witness values, and the caller controls protection and
cleanup. The example uses a public test-only tau and a synthetic circuit.
