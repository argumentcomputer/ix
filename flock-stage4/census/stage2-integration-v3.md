# Second optimization pass and 512 GB RAM assessment

The circuit census below remains current. The subsequent
[file-backed SRS](file-srs-v1.md), [fixed-key polynomial storage](file-key-v1.md),
[file prover workspace](file-workspace-v1.md), and
[owned-input pass](owned-inputs-v1.md) supersede the RAM assumptions in this
historical assessment. The ownership report contains the current measurements
and remaining memory-budget and full-proof validation work.

The complete fixture now uses **1,059,840,428 PLONK constraint rows**,
**20.35% fewer** than the [preceding version](stage2-integration-v2.md) and
**89.78% fewer** than the [original baseline](stage2-integration-v1.md).
The base domain falls from **2^31 to 2^30**, so the prover's required
**size-2^32 polynomial FFT now fits the field limit**. The complete circuit
projection and every native root comparison passed.

The measured circuit is recorded at revision
`1d3a0e4a21e8936cd74f4428c87f4173ea09cc89`.

**A full proof on 512 GB RAM is still not supported.** The materialized SRS
and proving key require at least **2,113,123,911,504 bytes (1.92 TiB)**,
half the preceding lower bound. Bounded MSM batches reduce temporary proving
allocations, but the current backend still retains its SRS and key in memory.
Disk-backed storage and an enforced aggregate memory budget remain necessary.
No full Flock FFLONK proof was generated.

The [machine-readable measurements](stage2-integration-v3.json) distinguish
storage payloads, resident-memory lower bounds, and synthetic prover heap
measurements. This is the complete
`real_stage2_integration_artifact_round_trip` fixture: two Stage 2 FRI
queries, log blowup 1, cap height 0, binary folds, a final polynomial of length
one, and no Stage 2 proof of work. The pinned native Flock revision is
`b310f35f35f68095537150a1c8c0a43caca9a29e`. The separate 100-query Stage 2
profile still needs its own census. Both transcripts, statement binding,
Boolean PIOP, wiring, merged PCS, multipoint assist, inner Ligerito, and all
three accumulator folds are included.

| Metric | Preceding version | This pass |
| --- | ---: | ---: |
| Public variables | 600 | 600 |
| Private variables | 803,337,595 | 636,765,088 |
| R1CS constraints | 809,681,727 | 642,332,970 |
| Nonzero R1CS terms | 3,810,984,144 | 3,032,465,809 |
| PLONK constraint rows | 1,330,644,479 | 1,059,840,428 |
| PLONK auxiliary wires | 520,962,752 | 417,507,458 |
| Base domain | 2,147,483,648 | 1,073,741,824 |
| Required polynomial FFT | 8,589,934,592 | 4,294,967,296 |

R1CS constraints fall by 20.67% and nonzero terms by 20.43%. The domain is
16 times smaller than the original baseline. It contains 13,900,796 padding
rows, including the two reserved blinding rows: only 1.29% of the domain.
Future circuit growth could cross the power-of-two boundary again.
Public inputs remain 600 scalars (19,200 bytes), accompanying the unchanged
992-byte proof format and native terminal root verification.

| Phase | R1CS constraints | PLONK constraint rows |
| --- | ---: | ---: |
| Statement | 32,734 | 61,990 |
| Transcript | 60,569,360 | 113,924,625 |
| Zerocheck | 4,389,929 | 7,099,307 |
| Lincheck | 4,849,112 | 7,859,125 |
| Wiring | 42,600,582 | 70,115,110 |
| PCS | 496,020,304 | 805,473,453 |
| MatrixFold | 33,870,949 | 55,306,818 |
| Total | 642,332,970 | 1,059,840,428 |

`Transcript` includes both tapes; `MatrixFold` includes the matrix,
structure, and jagged accumulators. The fingerprints are:

```text
R1CS projection: f49125dbe2067cdb5db8f437a6b6ae6a2391ba3330801aa6f1f2a457ca0cc7ea
Gate stream:    cf662c1a6ad3ac959c24172a8828e77fa65892abadf384ace8aefa399cb476d3
```

Hash domains and canonical record/footer encodings remain unchanged. The
relation's implementation has changed, so circuit digests and proving keys
must be regenerated.

The circuit changes in this pass are:

- Propagate known, constrained F128 constants through field operations.
  Multiplication by zero or one is simplified, constant multipliers use
  linear maps, and multiplying a wire by itself uses Frobenius squaring.
  Private zero and one values retain the same circuit layout as all other
  private values; simplification never depends on a private witness value.
- Build equality tables with one product per split: the high branch is
  `weight * x`, and the low branch is `weight + high` in characteristic two.
- Sum weighted opened rows in F128 before applying their F256 lane weights.
  This removes repeated extension-field work for each opened word while
  preserving zero padding for ragged rows.
- Contract final residuals directly against the interleaved F128 words,
  treating each pair as one F256 coefficient. Equality-basis and monomial
  Horner folds replace explicit residual vectors; fixed-coordinate factors,
  induced-query normalization, and transcript bindings are preserved.

Independent native tests expand the literal tensor bases and residual
vectors, including full-width extension-field values, ragged rows, and
empty evaluation points. They compare actual witness bits and reject
tampering with derived outputs. Projection tests check that private zero
and one values produce identical counts and fingerprints.

The prover now commits polynomials in MSM batches of at most 65,536 points.
SRS validation generates challenge powers in the same bounded batches,
carrying the exponent across batch boundaries. All curve, subgroup, digest,
and consistency checks remain, with one final batched pairing equation.
Tests cover the batch boundary and its tail with distinct points and an
independent scalar-sum oracle. The SRS point vector itself is still resident.

The verified synthetic prover measurements compare this pass with
`ceb41f265778`, using the same key, witness, public test SRS, and nonzero
blinding:

| Base domain | Previous additional peak heap | Current additional peak heap | Further reduction |
| --- | ---: | ---: | ---: |
| 16,384 | 61,082,160 bytes | 27,921,088 bytes | 54.29% |
| 65,536 | 222,824,720 bytes | 79,724,512 bytes | 64.22% |

Retained setup remains 36,571,972 and 146,279,236 bytes, respectively.
Both proofs verified and matched the preceding proof digests. A direct
byte comparison also passed at 16,384 rows. Relative to the original
`e09f48253f3a` prover, additional peak heap has fallen by 72.05% and 78.91%.
Batching may trade computation time for memory; no throughput improvement
is claimed.

These measurements count requested live heap allocations above the retained
setup at the start of proving. They exclude allocator overhead, transient
reallocation internals, stack, and RSS. They also exclude SRS-validation
temporaries because the peak is reset immediately before proving. They do
not establish peak RAM for the full Flock circuit.

At the full optimized domain, the capacity model gives:

| Payload | Exact bytes | Binary size |
| --- | ---: | ---: |
| Constraint gate stream | 203,489,362,176 | 189.51 GiB |
| One field column | 34,359,738,368 | 32 GiB |
| Three witness evaluation columns | 103,079,215,104 | 96 GiB |
| Retained preprocessing polynomials | 549,755,813,888 | 512 GiB |
| Packed C0 polynomial | 274,877,906,944 | 256 GiB |
| Largest packed polynomial bound | 309,237,645,888 | 288 GiB |
| Compressed G1 SRS | 463,856,468,832 | 432 GiB |
| G1 SRS in EIP-2537 encoding | 1,236,950,583,552 | 1.125 TiB |

The required SRS degree is 9,663,676,433, with 9,663,676,434 G1 powers.
On this x86-64 build, `Fr` is 32 bytes, `G1Affine` is 104 bytes,
`PlonkGateV1` is 216 bytes, and `PlonkCellV1` is 16 bytes. The materialized
SRS/key lower bound is
`(9*n + 18)*104 + n*(216 + 3*16 + 24*32)` bytes. It excludes the R1CS,
witness, temporary buffers, spare vector capacity, allocator overhead, and
operating system. Serialized SRS widths do not represent resident point sizes.

The RAM assessment uses **512,000,000,000 bytes (476.84 GiB)** and assumes
local disk is available. A proposed 64 GiB reserve leaves **412.84 GiB**
for the proving working set. The largest packed polynomial now fits that
budget individually, but the complete retained setup and simultaneous
working buffers do not. This budget is neither implemented nor measured.

The remaining implementation needs to:

1. Generate witness rows and copy-permutation records from the canonical
   stream without retaining the complete R1CS or gate graph, then sort
   copy records using bounded memory.
2. Store preprocessing and packed polynomials on disk, schedule their
   lifetimes, and stream validated SRS points into the bounded MSM kernel.
3. Implement external FFTs and polynomial operations under an aggregate
   budget for FFT, sorting, MSM, witness, and I/O buffers. The required
   size-2^32 transform is now supported by the field; this census no longer
   requires blocked convolution to work around an unavailable root of unity.
4. Generate and verify a complete proof under an actual RAM limit. Disk
   scratch requirements and full prover runtime remain unmeasured; the SRS
   and polynomial payloads still imply terabytes of storage.

Measured on 2026-09-08 UTC with Rust 1.98.0 (`88d9e12ae`). Projection,
lowering, and hashing took 1,324.572 seconds. The complete integration test
passed in 1,336.40 seconds, including all circuit/native root comparisons.
The final regression checks passed 116 Stage 4 tests, 63 regular host
tests, and all 13 serial cryptographic vectors. Formatting and Clippy passed
in both workspaces.

Reproduce the complete census with:

```sh
IX_STAGE4_PROJECT_R1CS=1 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml --all-features \
  real_stage2_integration_artifact_round_trip -- --ignored --nocapture
```

Reproduce the synthetic memory profile with:

```sh
cargo run --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-fflonk --example prover_memory -- 14
```

Use `16` for the larger sample. The example verifies the proof and prints
its digest. Run the same example at `ceb41f265778` to reproduce the preceding
version. The SRS uses a public test-only tau exclusively for this synthetic
measurement.
