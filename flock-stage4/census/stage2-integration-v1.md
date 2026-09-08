# Complete Stage 2 integration fixture census

This is the historical baseline at revision `e09f48253f3a`. The
[optimized census](stage2-integration-v2.md) supersedes it.

The original three-wire FFLONK lowering exceeded the BLS12-381 scalar field's
FFT domain limit for this fixture. It required a domain of **2^34**, while
the field supports at most **2^32**. That backend could not preprocess or
prove the complete fixture.

The measured gate stream has **10,374,565,573 constraint rows**.
Together with 600 public-input rows and two mandatory blinding rows, it needs
10,374,566,175 active/reserved rows and a power-of-two domain of
17,179,869,184. That domain would contain 6,805,303,011 padding
rows, including the blinding rows. The supported maximum domain has
4,294,967,296 rows.

At least **58.60%** of the constraint
rows must be removed just to fit the existing field-domain limit. Prover
design should address this size before implementing the external FFT,
permutation, and MSM pipeline.

The census covers `real_stage2_integration_artifact_round_trip` in
[`fri.rs`](../../flock-stage3/host/src/fri.rs), using the complete
`constrain_stage4_relation` API. It includes statement binding, both
transcripts, Boolean PIOP, wiring, merged PCS, multipoint assist, inner
Ligerito, and the matrix, structure, and jagged folds. Every derived root is
compared with the native exporter and independently checked against trusted
static tables.

The fixture uses two Stage 2 FRI queries, log blowup 1, cap height 0, binary
folds, a final polynomial of length one, and zero Stage 2 proof-of-work bits.
Flock uses its pinned native proving path at revision
`b310f35f35f68095537150a1c8c0a43caca9a29e`. The separate 100-query Stage 2
production profile needs its own census. These figures describe this complete
fixture.

The complete projection produced the following counts:

| Metric | Count |
| --- | ---: |
| Public variables | 600 |
| Private variables | 969,365,103 |
| R1CS constraints | 988,096,814 |
| Nonzero R1CS terms | 12,367,726,634 |
| PLONK auxiliary wires | 9,386,468,759 |

| Phase | R1CS constraints | PLONK constraint rows |
| --- | ---: | ---: |
| Statement | 31,812 | 109,658 |
| Transcript | 58,839,691 | 201,627,619 |
| Zerocheck | 6,006,946 | 71,173,564 |
| Lincheck | 6,864,595 | 81,657,818 |
| Wiring | 56,010,084 | 641,582,824 |
| PCS | 814,452,419 | 8,836,712,370 |
| MatrixFold | 45,891,267 | 541,701,720 |
| Total | 988,096,814 | 10,374,565,573 |

`Transcript` includes both tapes, and `MatrixFold` includes the matrix,
structure, and jagged accumulators. PCS contributes **85.18%** of the
PLONK constraint rows. The lowering expands the R1CS count by **10.50x**.

The complete fingerprints are:

```text
R1CS projection: 638798523f43c5380db6769a18b589f0cf66cf9cb35cae965a9ac20e64e21023
Gate stream:    c1a6c385399d1a94b381d42c47363546669049e9b7b017622babf6306b1e887f
```

The R1CS fingerprint is produced by `R1csBuilder::finish_projection` under
the BLAKE3 domain `ix:stage4:r1cs-projection:bls12-381:v1`. The gate-stream
fingerprint uses the record and footer encoding described below.

The following payload estimates apply the current storage formulas to the
**unsupported required domain**. They are hypothetical sizes, not usable
FFLONK setup parameters or peak-memory measurements. They exclude FFT/sort
scratch space, indexes, filesystem overhead, and implementation buffers.

| Payload | Exact bytes | Binary size |
| --- | ---: | ---: |
| Constraint gate stream | 1,991,916,590,016 | 1.81 TiB |
| One field column | 549,755,813,888 | 512.00 GiB |
| Three witness evaluation columns | 1,649,267,441,664 | 1.50 TiB |
| Retained preprocessing polynomials | 8,796,093,022,208 | 8.00 TiB |
| Packed C0 polynomial | 4,398,046,511,104 | 4.00 TiB |
| Largest packed polynomial | 4,947,802,325,568 | 4.50 TiB |
| Compressed G1 SRS | 7,421,703,488,352 | 6.75 TiB |
| G1 SRS in EIP-2537 encoding | 19,791,209,302,272 | 18.00 TiB |

The corresponding hypothetical SRS degree is 154,618,822,673,
requiring 154,618,822,674 G1 powers. The 600 public scalars occupy
19,200 bytes in canonical 32-byte encoding, accompanying the 992-byte proof.
The native terminal verifier also checks their deferred root evaluations.

Measured on 2026-09-06 UTC with Rust 1.98.0 (`88d9e12ae`). The relation
projection, lowering, and hashing pass took 3,601.488 seconds on this host.
The complete integration test passed in 3,613.32 seconds, including every
circuit-to-native root comparison. Prover timing remains unmeasured.

Reproduce the full sizing pass with:

```sh
IX_STAGE4_PROJECT_R1CS=1 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml --all-features \
  real_stage2_integration_artifact_round_trip -- --ignored --nocapture
```

The sizing path retains the required domain when it exceeds the field limit.
Normal arithmetization and preprocessing retain their domain checks. The
measurement hashes each canonical 192-byte constraint-gate record in emission
order; buffering records changes update boundaries only. Its BLAKE3 domain is
`ix:stage4:plonk-gate-stream:v1`, followed by the gate bytes and five
little-endian `u64` counts: public-input rows, constraint rows, padding rows,
domain size, and auxiliary wires. Public and padding rows are implicit.
