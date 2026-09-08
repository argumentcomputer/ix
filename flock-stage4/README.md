# Ix Flock Stage 4

This isolated workspace implements the terminal compression boundary:

```text
Flock Stage 3 proof
  -> canonical BLS12-381 Fr relation
  -> universal-setup KZG-FFLONK proof
```

The optimized integration fixture has **1,059,840,428 PLONK constraint rows**,
down **89.78%** from the original baseline and **20.35%** from the preceding
version. Its base domain is now **2^30**, and its polynomial products' size-2^32
FFT fits the field limit. The prover now supports an authenticated file-backed
SRS, replacing **936 GiB** of resident points with a **4.50 MiB** index and
bounded working buffers. The remaining materialized proving key still requires
at least **1,032 GiB (about 1.01 TiB)**, so a complete proof on 512 GB RAM
remains unsupported.
See the [circuit census](census/stage2-integration-v3.md) and
[file-SRS measurements](census/file-srs-v1.md) for the remaining storage work.

The `ix-terminal-circuit` crate owns the backend-independent R1CS. Its first
landed slice fixes the two-limb public-input encoding for the 256-bit Stage 3
statement digest and emits a deterministic circuit digest plus a constraint
census. The `ix-fflonk` crate fixes the v1 proof transport at four EIP-2537 G1
points plus fifteen canonical BLS12-381 scalar-field values: exactly 992
bytes. It strictly checks field encodings, curve membership, and subgroup
membership while decoding. Universal powers-of-tau validation checks every
G1 power and tau-G2 point for curve and subgroup membership before the batched
pairing check. The backend lowers canonical R1CS constraints to three-wire
PLONK rows, computes selector and copy-permutation preprocessing, commits and opens polynomials with
KZG, generates blinded C1/C2/W1/W2 proofs, replays the five-round Keccak
transcript, and checks the complete native FFLONK interpolation and two-pairing
equation. A nonzero-blinded end-to-end vector round-trips through the fixed
992-byte proof transport.

The Stage 3 host also exposes `prepare_stage4_verifier_witness`. It runs the
real pinned Flock verifier with a transparent recording challenger and exports
the accepted proof bundle, public F128 values, exact transcript-operation tree,
observations, byte payloads, and challenges. The production regression fixture
currently records 2,281 transcript operations and 1,120 challenges; a rejected
proof yields no export.

The replay counts on this page refer to the complete
`real_stage2_integration_artifact_round_trip` fixture. Its Stage 2 transport
uses two FRI queries, log blowup 1, cap height 0, binary folds, and no Stage 2
proof of work. Flock itself uses the pinned native proving path. The separate
100-query Stage 2 production profile needs its own Stage 4 census; these
fixture counts do not size every production layout.

The next landed slice normalizes that tape into a backend-neutral trace and
compiles it into BLS12-381 Fr R1CS. The trace pins stream-word provenance,
compression parameters and chaining links, squeeze sources, fork seed/digest
links, and fused-PoW predicates. A raw BLAKE3 compression currently costs
16,292 private variables, 16,628 R1CS constraints, and 31,112 PLONK rows.
Packed 32-bit words are bound once and reused across additions. The production verifier has
1,608 compression rows across three chains and 455 fused-PoW predicates. Its
streaming projector retains no assignment or constraint matrices.

The next slice bridges Flock's GHASH-basis `GF(2^128)` arithmetic into Fr.
One general field multiplication uses three Karatsuba levels and 27 packed
16-bit polynomial products. Boolean radix-32 digits recover the exact binary
convolution without scalar-field wraparound. It costs 5,952 R1CS constraints
and 9,516 PLONK rows including two fresh 128-bit inputs; the original lowering
used 92,510 PLONK rows. Constant multiplication and Frobenius maps share a
deterministic network of XORs. Known circuit constants are propagated through
field operations, and multiplication of a wire by itself uses the linear
Frobenius map. Private witness values of zero and one retain the same circuit
layout as other private values. The production
zerocheck exports a value-free DAG of 1,416 operations whose leaves name exact
transcript observation or challenge indices.

The production union lincheck is replayed through its challenge-bound sumcheck
and reported-evaluation equation. The combined Boolean-PIOP DAG has 2,960
operations and two equality assertions. It exports 22 registry-keyed
static-matrix claims (A and B for each of 11 Boolean tables); the ordinary
circuit API rejects unresolved claims, while the explicitly named deferred API
returns their constrained wires to the matrix accumulator.

The matrix-accumulator slice now generates and verifies Flock's real aggregate
transcript with 128-bit per-challenge grinding. Its backend-neutral trace binds
every input coordinate and evaluation, replays 496 degree-two Boolean-matrix
sumcheck rounds, checks the column bridges and row roots, and preserves the
registry identity of all 22 matrices. A native differential check discharges
those roots against the registry matrices.

The same auxiliary transcript folds the three Product-GKR structure claims
under Flock's digest-keyed sigma group. This rectangular fold binds 87 claim
observations, samples 32 challenges, replays 26 rounds, and emits one plain
structure-table root. That root contributes 27 injectively embedded public
`Fr` values and has an explicit native terminal discharge against the circuit
named by its digest. Redundant Boolean-pin helpers are excluded because the
canonical Boolean algebra already recomputes them from fixed circuit counts.

The statement-wiring slice connects Flock's circuit statement to the terminal
public input. It allocates all 828 Flock public words once, reproduces Flock's
13-leaf/12-parent BLAKE3 commitment to them, and binds that result plus the
fixed Flock circuit digest to the exact byte payloads absorbed before any
Fiat--Shamir challenge. Public-vector words 217 and 218 are constrained to the
Stage 2 root inside the 104-byte Stage 3 statement. The circuit then hashes
that full statement and binds the result to two injective public `Fr` limbs.

The circuit-wiring slice now replays Flock's complete batched Product-GKR over
the 23-variable cell space. It constrains all 253 degree-two rounds, both
terminal input equations, equality of the two surfaced witness evaluations,
and the gather-factorization recombination against the same 828 public words.
All 395 digest-fixed public words are pinned to their circuit constants. The
production wiring DAG contains 9,113 operations and 28 equality assertions and
returns 64 transcript-bound packed-direct gather claims. Its three remaining
`live * id`, `live`, and `live * sigma` evaluations are explicit conditional
claims against the digest-keyed circuit-structure matrix and now feed the
structure accumulator above; they are not trusted verifier advice.

The merged-PCS frontend now derives the exact Boolean AB and C opening points
from the zerocheck/lincheck wires and binds them beside all 64 wiring gathers.
It checks both succinct DP24 ring switches (256 observed slices and 14 sampled
randomizers), replays the 66-way mixed batching, and constrains all 20 rounds
of the dense degree-two sumcheck for the production `m = 27` commitment. The
original Merkle CAP remains connected to the byte payload absorbed by the main
transcript. The frontend returns the constrained assist endpoint `running`
and inner-opening claim `q_hat(rho) = q_eval`.

The multipoint-twisted slice now derives both family-H coefficient vectors from
the constrained ring challenges, recombines all 256 dual-form observations and
the 64-member scalar group, checks `running = q_eval * v`, and replays the
20-round product sumcheck plus its 42-round untwisted anchor. Its exact
four-state boundary recurrence exports three constrained claims on Flock's
count-dependent jagged layout rather than trusting their raw evaluations.

Those three claims now enter Flock's native jagged aggregate class. The Stage 4
circuit binds the digest, layout shape, equality/combo row descriptions, and
all transcript challenges; replays 52 column/row fold rounds; and binds the
resulting root to 53 public `Fr` values. The host independently discharges that
root against `JaggedParams`. The complete production auxiliary tape now has
2,742 transcript operations, 4,640 observed values, 626 byte payloads (5,073
bytes), 630 challenges, 2,150 BLAKE3 compression rows, and 622 fused-PoW
constraints. Its jagged component binds 283 claim observations and three
bridges, samples 58 challenges, and emits one root.

The 22 Boolean-matrix roots add 518 public `Fr` values, the circuit-structure
root adds 27, and the jagged root adds 53. Together with the two statement
limbs, the current relation therefore has 600 public variables. Each
`GF(2^128)` value uses one injective little-endian field embedding, and the
circuit constrains every derived bit decomposition to its public field.
At 32 bytes per scalar these public values occupy 19,200 bytes, in addition
to the 992-byte proof; terminal root verification remains part of acceptance.

`constrain_stage4_relation` is the shared composition API for every phase,
including inner Ligerito and all three accumulators. It accepts a fresh
`R1csBuilder`, `Stage4RelationPublicInputsV1`, and a borrowed
`Stage4RelationWitnessV1`. A materialized builder and an observed projection
therefore compile the same relation in the same order. The public encoder is
checked against circuit allocation order, including the maximum F128 value.
The returned `Stage4RelationCircuitOutputV1` retains phase outputs so the full
projection can compare every derived root with the native exporter.

Enable the Stage 3 host's `stage4` feature to use
`Stage4FlockVerifierWitnessV1::terminal_public_inputs`,
`terminal_relation_witness`, and `verify_stage4_terminal`. The terminal
verifier takes an externally expected Stage 3 statement, the trusted FFLONK
key, and a `Stage4TerminalContextV1` containing the registry, circuit, and
jagged parameters from that same setup. It checks the statement digest,
the exact root identities, order, dimensions, and table evaluations, then
verifies FFLONK over the shared public encoding. Those tables and the key
are verifier configuration, not data selected by the proof.

The production fixture exercises all 600 public fields and rejects altered,
reordered, omitted, and malformed roots and a different expected statement.
A small public-binding proof over that real root vector tests the complete
terminal acceptance wrapper, including corrupted FFLONK proofs and changed
roots whose table evaluations are still correct. It also rejects a valid
public-binding proof whose root evaluation is incorrect. These tests do not
generate a proof of the full Flock relation.

The complete relation projects to 636,765,088 private variables,
642,332,970 R1CS constraints, and 3,032,465,809 nonzero terms.
Its three-wire lowering emits **1,059,840,428 constraint rows**.
After public inputs and blinding rows, the required power-of-two domain is
1,073,741,824, sixteen times smaller than the
[original baseline](census/stage2-integration-v1.md).
The [optimized census](census/stage2-integration-v3.md) records every phase,
both fingerprints, storage sizes, and the 512 GB RAM assessment.

The Flock replay now closes the inner Ligerito opening against the
transcript-bound CAP. The production trace has four recursive levels and 406
authenticated queries, covering 10,644 opened F128 values and 3,213 Merkle
path digests. It binds 28 extension-field messages, 18 fold challenges, 27
sumcheck challenges, seven OOD claims, and 64 final residual words. The circuit
replays the extension sumchecks, derives every stratified query index,
authenticates multi-block BLAKE3 leaves through the capped Merkle trees, folds
the novel-basis coordinates, and checks the final interleaved F128/F256 inner
product. Opened rows are combined in F128 before applying F256 lane weights.
The final residual is evaluated directly against the interleaved words using
Horner folding, avoiding a full extension-field residual vector per query.

The R1CS projection mode now accepts a streaming backend observer. The
production regression attaches the FFLONK lowering to the same canonical pass,
so one matrix-free replay reports the exact gate count, power-of-two domain,
auxiliary-wire count, and required universal-SRS degree. Affine rank-one
constraints remain one PLONK row, including XOR relations whose right-hand
side contains the multiplication inputs; wide linear combinations introduce only the
deterministic accumulator rows they require. The same lowering can stream every
constraint gate as a canonically validated, versioned 192-byte record with
stable auxiliary-wire identifiers. A checked capacity model converts the final
census into gate-stream, field-column, preprocessing, packed-polynomial, and
compressed/uncompressed SRS payload sizes.

`PlonkGateProjectionV1::finish_for_sizing` reports the required domain even
above the field limit. The normal projection finalizer, materialized lowering,
and preprocessing retain their domain checks.

The development prover now moves witness columns, batches permutation
inversions, reuses polynomial buffers, and cancels the boundary quotient
algebraically. KZG commitments process at most 65,536 points per MSM batch,
and SRS validation generates challenge powers in bounded batches. A synthetic
16,384-row proof uses 27.9 MB of additional peak heap, down from 61.1 MB in
the preceding version and 99.9 MB originally. All versions produce the same
verified proof with the same key, witness, and randomness. This measures the
development backend on a small circuit; the full Flock proof remains unmeasured.

`KzgFileSrsV1<File>` now supplies validated powers directly from disk to the
same preprocessor and prover through `KzgCommitmentSourceV1`. It validates
all points and SRS consistency on opening, then authenticates each bounded
chunk before use. Compressed 48-byte and uncompressed 96-byte G1 storage
produce the same SRS digest, keys, and proofs. The uncompressed format avoids
repeated point decompression. On the 65,536-row synthetic fixture, it reduces
total peak heap from 226.0 MB to 168.4 MB, with approximately the same proving
time. The [storage report](census/file-srs-v1.md) records both formats and
distinguishes retained setup from temporary buffers and process RSS.

The next production step is a disk-backed polynomial store, external FFT and
copy-permutation construction, and streamed gate/witness processing. The
file-backed SRS and bounded MSM kernel are implemented; an aggregate memory
budget across all working buffers is still required. The capacity model reports
the supported size-2^32 polynomial FFT requirement and separate lower bounds
for resident and file-backed SRS configurations. The prover checks the FFT
requirement before allocating its witness columns. Every backend must consume
the canonical relation rather than define another one.

The proof width follows the [FFLONK paper](https://eprint.iacr.org/2021/1167)
and uses [EIP-2537](https://eips.ethereum.org/EIPS/eip-2537) for G1 transport.
The Stage 4 Fiat--Shamir profile hashes those same 128-byte calldata points and
canonical 32-byte big-endian scalars with Keccak-256. The backend now emits the
exact EIP-2537 curve-call plan: one six-term, 960-byte G1 MSM followed by one
two-pair, 768-byte pairing check. Their consensus-priced precompile floor is
156,900 gas. A deployable EVM implementation of the Keccak and scalar-field
portion, plus measured whole-verifier gas, remains to be completed.

Run the focused suite and the native terminal integration vector with:

```sh
cargo test --release --locked --manifest-path flock-stage4/Cargo.toml --workspace
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml --all-features \
  real_stage2_integration_artifact_round_trip -- --ignored --nocapture
```

Both isolated workspaces have CI jobs for formatting, Clippy, and tests; the
Stage 3 job also runs all cryptographic vectors serially. Lake tracks Stage 4
Rust sources and manifests when rebuilding the Rust archive, and Nix includes
the same inputs in its Lake source set.

The complete streaming census is opt-in because of its runtime:

```sh
IX_STAGE4_PROJECT_R1CS=1 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml --all-features \
  real_stage2_integration_artifact_round_trip -- --ignored --nocapture
```

Profile requested heap allocations for a verified synthetic proof with:

```sh
cargo run --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-fflonk --example prover_memory -- 14
```

The argument is the base-two domain logarithm. This example uses a public
test-only SRS and reports retained and additional peak heap bytes separately;
it does not measure allocator overhead or process RSS.

Add an archive path to use an uncompressed file-backed SRS, or append
`compressed` to use compressed points:

```sh
cargo run --release --locked --manifest-path flock-stage4/Cargo.toml \
  -p ix-fflonk --example prover_memory -- 14 /tmp/ix-test-uncompressed.srs
```

The example creates missing archives and validates matching existing ones
without overwriting them. Use separate paths for different domain sizes or
encodings. Archive creation, validation, and preprocessing peaks are excluded
from the reported proving measurement.
