# Ix Flock Stage 4

This isolated workspace implements the terminal compression boundary:

```text
Flock Stage 3 proof
  -> canonical BLS12-381 Fr relation
  -> universal-setup KZG-FFLONK proof
```

The `ix-terminal-circuit` crate owns the backend-independent R1CS. Its first
landed slice fixes the two-limb public-input encoding for the 256-bit Stage 3
statement digest and emits a deterministic circuit digest plus a constraint
census. The `ix-fflonk` crate fixes the v1 proof transport at four EIP-2537 G1
points plus fifteen canonical BLS12-381 scalar-field values: exactly 992
bytes. It strictly checks field encodings, curve membership, and subgroup
membership while decoding. It now also validates universal powers-of-tau
material, lowers canonical R1CS constraints to three-wire PLONK rows, computes
selector and copy-permutation preprocessing, commits and opens polynomials with
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

The next landed slice normalizes that tape into a backend-neutral trace and
compiles it into BLS12-381 Fr R1CS. The trace pins stream-word provenance,
compression parameters and chaining links, squeeze sources, fork seed/digest
links, and fused-PoW predicates. A raw BLAKE3 compression currently costs
15,824 private variables and 16,160 constraints. The production verifier has
1,608 compression rows across three chains and 455 fused-PoW predicates. Its
streaming R1CS projection has 24,569,216 private variables, 25,111,575
constraints, and 136,194,848 nonzero terms. The projector retains no assignment
or constraint matrices.

The next slice bridges Flock's GHASH-basis `GF(2^128)` arithmetic into Fr.
One general field multiplication uses a cached, flattened Karatsuba tensor and
costs 7,921 constraints including two fresh 128-bit inputs. The production
zerocheck exports a value-free DAG of 1,416 operations whose leaves name exact
transcript observation or challenge indices. Transcript plus zerocheck projects
to 30,477,568 private variables, 31,118,521 constraints, and 219,481,186
nonzero terms, with fingerprint
`f6898705fa3a4bdb886743302bd535b29c6c7e94f4c10e26cdef4d89d230300f`.

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

The last fully fingerprinted prefix ended before the multipoint and jagged
slices. It projected to 547 public variables, 170,007,888 private variables,
173,158,769 constraints, and 1,910,076,918 nonzero terms, with fingerprint
`9c6da80e1705ae17bdea0af18013902c09b908706b692fc6591287ee40f16cb7`.
Those numbers are retained as a historical baseline, not as current pins. A
fresh private-variable, constraint, nonzero, and digest census is still needed
for the complete relation; the inner Merkle replay makes that projection
materially more expensive than the historical roughly 90-minute prefix.

The Flock replay now closes the inner Ligerito opening against the
transcript-bound CAP. The production trace has four recursive levels and 406
authenticated queries, covering 10,644 opened F128 values and 3,213 Merkle
path digests. It binds 28 extension-field messages, 18 fold challenges, 27
sumcheck challenges, seven OOD claims, and 64 final residual words. The circuit
replays the extension sumchecks, derives every stratified query index,
authenticates multi-block BLAKE3 leaves through the capped Merkle trees, folds
the novel-basis coordinates, and checks the final interleaved F128/F256 inner
product.

The R1CS projection mode now accepts a streaming backend observer. The
production regression attaches the FFLONK lowering to the same canonical pass,
so one matrix-free replay reports the exact gate count, power-of-two domain,
auxiliary-wire count, and required universal-SRS degree. Affine rank-one
constraints remain one PLONK row; wide linear combinations introduce only the
deterministic accumulator rows they require. The same lowering can stream every
constraint gate as a canonically validated, versioned 192-byte record with
stable auxiliary-wire identifiers. A checked capacity model converts the final
census into gate-stream, field-column, preprocessing, packed-polynomial, and
compressed/uncompressed SRS payload sizes.

The remaining production boundary is to finish the complete relation/gate
fingerprint, connect the canonical stream to external FFT, permutation-sort,
and MSM stages, and measure prover cost. Every backend must consume the
canonical relation rather than define another one.

The proof width follows the [FFLONK paper](https://eprint.iacr.org/2021/1167)
and uses [EIP-2537](https://eips.ethereum.org/EIPS/eip-2537) for G1 transport.
The Stage 4 Fiat--Shamir profile hashes those same 128-byte calldata points and
canonical 32-byte big-endian scalars with Keccak-256. The backend now emits the
exact EIP-2537 curve-call plan: one six-term, 960-byte G1 MSM followed by one
two-pair, 768-byte pairing check. Their consensus-priced precompile floor is
156,900 gas. A deployable EVM implementation of the Keccak and scalar-field
portion, plus measured whole-verifier gas, remains to be completed.

Run the focused suite with:

```sh
cargo test --manifest-path flock-stage4/Cargo.toml
```
