# Optimized complete census and 512 GB RAM assessment

The complete fixture now uses **1,330,644,479 PLONK constraint rows**, an
**87.17% reduction** from [the original baseline](stage2-integration-v1.md).
Its base domain fell from **2^34 to 2^31**. The full circuit projection and
every native root comparison passed.

The measured circuit and lowering are recorded at revision
`a29aaefa5a9e9c8cdcd7cdeddb36322591dd726c`.

**A full proof on 512 GB RAM is not yet supported.** The materialized SRS
and proving key alone require at least **4,226,247,821,136 bytes (3.84 TiB)**.
The prover also needs a size-2^33 polynomial FFT for this circuit, whereas
the field supports at most 2^32. Reaching the RAM target requires a disk-backed
prover, including blocked polynomial products within the field limit.

The [machine-readable measurements](stage2-integration-v2.json) distinguish
canonical storage payloads, resident-memory lower bounds, and small-prover
heap measurements. No full Flock FFLONK proof was generated.

This is the complete `real_stage2_integration_artifact_round_trip` fixture,
using two Stage 2 FRI queries, log blowup 1, cap height 0, binary folds, a
final polynomial of length one, and no Stage 2 proof of work. The pinned
native Flock revision is `b310f35f35f68095537150a1c8c0a43caca9a29e`.
The separate 100-query Stage 2 profile still needs its own full census.
Both transcripts, statement binding, Boolean PIOP, wiring, merged PCS,
multipoint assist, inner Ligerito, and all three accumulator folds are included.

| Metric | Original baseline | Optimized |
| --- | ---: | ---: |
| Public variables | 600 | 600 |
| Private variables | 969,365,103 | 803,337,595 |
| R1CS constraints | 988,096,814 | 809,681,727 |
| Nonzero R1CS terms | 12,367,726,634 | 3,810,984,144 |
| PLONK constraint rows | 10,374,565,573 | 1,330,644,479 |
| PLONK auxiliary wires | 9,386,468,759 | 520,962,752 |
| Base domain | 17,179,869,184 | 2,147,483,648 |

The optimized lowering expands R1CS constraints by 1.64x, down from 10.50x.
It reduces R1CS constraints by 18.06% and nonzero terms by 69.19%.
The domain contains 816,838,569 padding rows, including the two reserved
blinding rows. Public inputs remain 600 scalars (19,200 bytes), accompanying
the unchanged 992-byte proof format and native terminal root verification.

| Phase | R1CS constraints | PLONK constraint rows |
| --- | ---: | ---: |
| Statement | 32,734 | 61,990 |
| Transcript | 60,569,360 | 113,924,625 |
| Zerocheck | 4,494,754 | 7,268,284 |
| Lincheck | 5,127,937 | 8,287,638 |
| Wiring | 42,699,548 | 70,231,896 |
| PCS | 662,325,707 | 1,074,728,062 |
| MatrixFold | 34,431,687 | 56,141,984 |
| Total | 809,681,727 | 1,330,644,479 |

`Transcript` includes both tapes; `MatrixFold` includes the matrix,
structure, and jagged accumulators. The fingerprints are:

```text
R1CS projection: 5ae6408ed0124aa8afb7d6fff3b6bd257771e9891edf688ba717828d1fdd00bd
Gate stream:    fb492055e8b8af6bd91d84d74bdeee4e55481a6f93c671d1e091cc00d42b2d5c
```

The hash domains and canonical record/footer encodings are unchanged from
v1. The circuit and lowering have changed, so circuit digests and proving
keys must be regenerated. Deterministic tie-breaking makes the new shared
XOR networks independent of hash-map iteration order.

The implemented circuit optimizations are:

- Fold linear occurrences of either multiplication input into the same
  three-wire gate. A Boolean XOR now lowers to one PLONK row.
- Replace the flattened F128 multiplication tensor with three Karatsuba
  levels and 27 packed 16-bit polynomial products. Radix-32 digits cannot
  carry between coefficients; both integer sides are below 2^160 and below
  the scalar modulus. Boolean digit decompositions therefore recover the
  exact binary product. A fresh-input multiplication falls from 92,510 to
  9,516 PLONK rows, and from 7,921 to 5,952 R1CS constraints.
- Share XOR subexpressions across constant multiplication and Frobenius
  maps. Symbolic tests check every input basis vector of representative maps.
- Bind packed BLAKE3 words once and reuse them across additions. A raw
  compression uses 31,112 PLONK rows; the R1CS grows slightly because these
  bindings eliminate repeated wide linear combinations during lowering.

The implemented prover optimizations move witness columns instead of
cloning them, invert permutation denominators in bounded batches, remove the
full roots-of-unity vector, cancel the Lagrange boundary quotient before
multiplication, perform polynomial FFTs without redundant coefficient
clones, divide monic polynomials in place, and reuse packed buffers for W2.
Unused buffers are released after their last use. The prover rejects an
unsupported polynomial FFT domain before lowering its witness.

Two synthetic circuits were proved using the original prover source at
`e09f48253f3a` and the optimized prover, with the same key, witness, public
test SRS, and nonzero blinding. Both versions verified and emitted
byte-identical proofs:

| Base domain | Original additional peak heap | Optimized additional peak heap | Reduction |
| --- | ---: | ---: | ---: |
| 16,384 | 99,880,688 bytes | 61,082,160 bytes | 38.84% |
| 65,536 | 378,015,184 bytes | 222,824,720 bytes | 41.05% |

These count requested live heap allocations above the retained setup at the
start of proving. Retained setup was 36,571,972 and 146,279,236 bytes,
respectively, in the comparison harness. Allocator overhead, transient
reallocation internals, stack, and RSS are excluded. These small synthetic
measurements do not establish peak RAM for the full Flock circuit.

At the full optimized domain, the capacity model gives:

| Payload | Exact bytes | Binary size |
| --- | ---: | ---: |
| Constraint gate stream | 255,483,739,968 | 237.94 GiB |
| One field column | 68,719,476,736 | 64 GiB |
| Three witness evaluation columns | 206,158,430,208 | 192 GiB |
| Retained preprocessing polynomials | 1,099,511,627,776 | 1 TiB |
| Packed C0 polynomial | 549,755,813,888 | 512 GiB |
| Largest packed polynomial bound | 618,475,291,200 | 576 GiB |
| Compressed G1 SRS | 927,712,936,800 | 864 GiB |
| G1 SRS in EIP-2537 encoding | 2,473,901,164,800 | 2.25 TiB |

The required SRS degree is 19,327,352,849, with 19,327,352,850 G1 powers.
On this x86-64 build, `Fr` is 32 bytes, `G1Affine` is 104 bytes,
`PlonkGateV1` is 216 bytes, and `PlonkCellV1` is 16 bytes. Consequently the
resident SRS and retained key require at least
`(9*n + 18)*104 + n*(216 + 3*16 + 24*32)` bytes. This is the 3.84 TiB lower
bound above, before the R1CS, witness, temporary buffers, spare vector
capacity, allocator overhead, or operating system. Serialized SRS point
widths cannot be used to estimate the existing in-memory SRS.

For the 512 GB target, this assessment uses **512,000,000,000 bytes
(476.84 GiB)** and assumes local disk is available. Reserving 64 GiB for the
operating system and runtime leaves **412.84 GiB** for the proving working
set. This is a proposed budget, not an implemented or measured memory cap.
Even one full C0 or C2 buffer exceeds that working budget.

The remaining implementation needs to:

1. Generate witness rows and copy-permutation records from the canonical
   stream without retaining the complete R1CS or gate graph, then sort the
   copy records using bounded memory.
2. Store preprocessing and packed polynomials on disk, schedule their
   lifetimes, and stream validated SRS points into bounded MSM batches.
3. Use external FFTs and blocked polynomial convolution. Splitting I/O does
   not create a size-2^33 root of unity: each convolution block must use a
   supported domain of at most 2^32. Alternatively, another 19.31% gate
   reduction would reach a size-2^30 base domain and its size-2^32 product FFT;
   disk-backed storage would still be required for 512 GB RAM.
4. Enforce the aggregate memory budget across FFT, sorting, MSM, witness,
   and I/O buffers, then measure a complete proof and its verification under
   an actual RAM limit. Disk scratch requirements and full prover runtime
   remain unmeasured; the SRS and polynomial payloads already require
   terabytes of storage.

Measured on 2026-09-08 UTC with Rust 1.98.0 (`88d9e12ae`). Projection,
lowering, and hashing took 1,640.840 seconds; the complete integration test
passed in 1,652.89 seconds, including all circuit/native root comparisons.
The final regression checks passed 109 Stage 4 tests, 63 regular host tests,
and all 13 serial cryptographic vectors. Formatting and Clippy are checked
in both workspaces.

Reproduce the complete census with:

```sh
IX_STAGE4_PROJECT_R1CS=1 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml --all-features \
  real_stage2_integration_artifact_round_trip -- --ignored --nocapture
```

Reproduce the current synthetic memory profile with:

```sh
cargo run --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-fflonk --example prover_memory -- 14
```

Use `16` for the larger sample. The example contains the fixture and
allocation counter, verifies the resulting proof, and prints its digest.
For the original baseline, copy the same example into an isolated checkout
of `e09f48253f3a` and run it there. It uses a public test-only tau exclusively
for this synthetic measurement.
