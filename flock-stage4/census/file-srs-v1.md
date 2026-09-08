# File-backed SRS and proving memory

This report records the SRS-only storage pass. The subsequent
[file-backed polynomial key implementation](file-key-v1.md) supersedes its
materialized-key assumptions and reduces the retained SRS/key minimum further.

The existing FFLONK preprocessor and prover can now use an authenticated SRS
file without retaining all G1 powers in memory. At the
[current complete fixture's size](stage2-integration-v3.md), this replaces
**936 GiB of resident G1 points** with a **4.50 MiB authentication index**
and bounded decoding/MSM buffers. The SRS/key resident-memory lower bound
falls from **1.92 TiB to 1.01 TiB**.

**A complete proof on 512 GB RAM is still not supported.** The proving key,
R1CS, witness, and polynomial operations remain materialized. This pass
implements SRS storage; a polynomial store, streamed gate/witness processing,
external copy-permutation construction, and an aggregate memory budget remain.
No full Flock FFLONK proof or full-circuit peak-RAM measurement was produced.

The implementation is recorded at
`111512e9be44bd7651afdb9a0b5a4ebe028de512`. The circuit and lowering are
unchanged from the v3 census at `1d3a0e4a21e8936cd74f4428c87f4173ea09cc89`:
1,059,840,428 constraint rows and a size-2^30 base domain. Its census covers
the complete two-query Stage 2 integration fixture; the separate 100-query
profile still needs its own census. The complete census was not repeated
for this storage-only change.

The [machine-readable report](file-srs-v1.json) contains the exact capacity
figures, benchmark measurements, and proof fingerprints.

## Measured proofs

The synthetic multiplication fixture uses public test-only tau 29 and the
same witness, key, and nonzero blinding for each backend. All measured proofs
verified and had matching proof digests. A separate end-to-end test compares
the complete proof bytes and preprocessed keys from a real file with the
in-memory backend, for both file encodings.

Heap columns below are requested allocation bytes. The total peak includes
the retained setup and additional live allocations during proving.

| Domain | SRS storage | Retained heap | Additional peak | Total peak | Prove time |
| --- | --- | ---: | ---: | ---: | ---: |
| 16,384 | Memory | 36,571,972 | 27,921,088 | 64,493,060 | 5.298 s |
| 16,384 | Compressed file | 21,234,916 | 37,882,560 | 59,117,476 | 16.611 s |
| 16,384 | Uncompressed file | 21,234,895 | 41,028,288 | 62,263,183 | 5.448 s |
| 65,536 | Memory | 146,279,236 | 79,724,512 | 226,003,748 | 22.329 s |
| 65,536 | Compressed file | 84,936,132 | 80,349,888 | 165,286,020 | 67.148 s |
| 65,536 | Uncompressed file | 84,936,111 | 83,495,616 | 168,431,727 | 22.001 s |

File storage reduces retained heap by approximately **41.94%** in both
samples. At 65,536 rows, the uncompressed file reduces total peak heap by
**25.47%**, with approximately the same proving time as the memory backend.
Compressed storage reduces that peak by **26.87%**, but proving takes about
three times as long because each read decompresses the curve points.
The example therefore defaults to uncompressed working files and offers
compressed storage when disk capacity is more important.

File reads require additional point and byte buffers. For the smaller
fixture these offset much of the retained-setup saving: the uncompressed
total peak falls by only 3.46%. The buffers stay bounded as the SRS grows.

These are single runs on the development host, measured on 2026-09-08 UTC
with Rust 1.98.0. Background load and filesystem cache were not controlled;
the timings do not predict full-circuit disk throughput. Heap counts include
benchmark bookkeeping and arguments, and exclude allocator overhead,
transient reallocation internals, stack, process RSS, and filesystem cache.
Archive creation, SRS validation, and preprocessing peaks and times are
excluded because the counter and timer are reset immediately before proving.

## Validation and file format

`KzgCommitmentSourceV1` supplies commitments and verifier material to the
existing preprocessing and proving functions. `KzgUniversalSrsV1` remains
the in-memory implementation. `KzgFileSrsV1<R>` accepts a seekable reader;
using `std::fs::File` keeps point data on disk.

Opening an archive checks the exact file length, canonical generators,
nonidentity powers, canonical coordinates, curve membership, and prime-order
subgroup membership. It computes the existing canonical SRS digest over
compressed points, even when the archive stores uncompressed points.
A second pass applies the same digest-derived challenge and batched pairing
consistency equation as the memory backend. Global challenge exponents and
the adjacency between chunks are preserved.

The first pass records one BLAKE3 digest for each chunk of at most 65,536
points. Every subsequent read checks its complete chunk, including any
unused suffix of a partially consumed chunk, before decoding or MSM. Thus
the decoder can skip repeating curve/subgroup checks on authenticated bytes.
Changes between validation passes or after opening are rejected when the
affected chunk is read. The reader cursor is protected by a mutex, and
commitments sharing one source run serially.

Both encodings preserve the original SRS digest, verifier key, polynomial
commitments, and proof bytes. Switching storage formats requires no circuit
or proving-key regeneration. The uncompressed file representation uses
96-byte G1 records; the proof's EIP-2537 transport continues to use 128-byte
G1 records and an unchanged 992-byte total proof.

The v1 file has a fixed 216-byte header:

| Offset | Bytes | Contents |
| ---: | ---: | --- |
| 0 | 13 | ASCII `IX-KZG-SRS-V1` |
| 13 | 1 | G1 encoding: 0 compressed, 1 uncompressed |
| 14 | 2 | Reserved zeros |
| 16 | 8 | Little-endian unsigned power count |
| 24 | 96 | Canonical compressed G2 generator |
| 120 | 96 | Canonical compressed tau-G2 |
| 216 | count × 48 or count × 96 | Canonical G1 powers in ascending exponent order |

Trailing bytes, unknown encodings, and nonzero reserved bytes are rejected.
`write_kzg_srs_file` writes an exact-count point iterator through a bounded
buffer, without collecting the powers. It is an encoder; the completed file
must be opened and validated before use. The caller owns file creation,
durability, and publication, and selects trusted setup material as before.

## Full-fixture capacity

For the unchanged size-2^30 domain, the SRS contains 9,663,676,434 G1 powers.
The capacity model reports:

| Item | Exact bytes | Binary size |
| --- | ---: | ---: |
| In-memory G1 powers | 1,005,022,349,136 | 936 GiB |
| Compressed SRS file, including header | 463,856,469,048 | 432 GiB |
| Uncompressed SRS file, including header | 927,712,937,880 | 864 GiB |
| Retained authentication index | 4,718,624 | 4.50 MiB |
| Maximum decoded G1 buffer | 6,815,744 | 6.5 MiB |
| Maximum compressed read buffer | 3,145,728 | 3 MiB |
| Maximum uncompressed read buffer | 6,291,456 | 6 MiB |
| Materialized proving key minimum | 1,108,101,562,368 | 1,032 GiB |
| File SRS index plus key minimum | 1,108,106,280,992 | 1.01 TiB |

The index occupies `32 * ceil((9*n + 18) / 65_536)` bytes. A commitment
retains one decoded-point buffer and one encoded-byte buffer at a time,
in addition to the bounded Arkworks MSM workspace. SRS consistency validation
also uses one bounded scalar buffer. A caller-supplied buffered reader can
retain additional storage.

The key lower bound remains `n * (216 + 3*16 + 24*32)` bytes on this x86-64
build. It excludes the R1CS, witness, temporary polynomial and MSM buffers,
reader state, spare vector capacity, allocator overhead, and operating
system. The 16 retained preprocessing field columns alone occupy 512 GiB.
They, the 256 GiB packed C0 polynomial, and the materialized gate/permutation
data are the next major storage targets.

The RAM target remains 512,000,000,000 bytes (476.84 GiB), with the previously
proposed 64 GiB reserve leaving 412.84 GiB for proving. This is not an
implemented memory cap. The full polynomial, FFT, witness, permutation, and
I/O schedule still needs to enforce a shared budget and be measured under an
actual RAM limit.

## Reproduction

Run the memory baseline with:

```sh
cargo run --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-fflonk --example prover_memory -- 14
```

Use a file-backed SRS with:

```sh
cargo run --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-fflonk --example prover_memory -- 14 /tmp/ix-test-uncompressed.srs
cargo run --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-fflonk --example prover_memory -- 14 /tmp/ix-test-compressed.srs compressed
```

Use `16` and separate archive paths for the larger sample. The example
creates missing archives from a streaming public test-only power generator.
It validates and reuses matching existing archives, checks their degree,
test tau, and encoding, and never overwrites an existing file.

Validation passed 126 Stage 4 tests, 63 regular host tests, and all 13 serial
cryptographic vectors. Both workspaces passed formatting and Clippy. Tests
cover both production-size chunk boundaries and their tails, independent
commitment/opening comparisons, a real-file proof comparison, invalid
encodings, off-curve and torsion points, inconsistent powers, short reads,
truncation, write/flush errors, and changes during or after validation. A
cancellation regression rejects errors that would evade the consistency
check if challenge exponents restarted at each chunk.
