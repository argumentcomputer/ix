# Generic IxBy → Stage 4 replay

Status: native replay and new public/private statement binding are implemented.
This is progress toward M5, not completion of M5–M8. There is no approved
full terminal topology/key, closed-root circuit, or complete FFLONK proof yet.
The native Flock constraint-to-IxBy refinement obligation in M3 remains too.

## Entry and ownership

The isolated `flock-stage4/exec` crate depends on `ixby-flock`, Flock
`b310f35f35f68095537150a1c8c0a43caca9a29e`, and the imported neutral trace,
circuit, and FFLONK crates. It does not depend on a native Stage 2 verifier.
Root Cargo/Lean dependencies and the experimental m37 configuration are
unchanged. The donor file hashes and excluded legacy APIs were recorded in
`flock-stage4/EXEC-REPLAY-PROVENANCE.json` before import.

`compile_exec_replay(approvedExec)` constructs an immutable `CompiledExecReplay`
using only the approved generic setup. It takes no guest image, commitment,
statement, or proof. Its `replay(commitments, completeProofBytes)` method uses
the strict Exec decoder and complete native verifier; `replay_exec` remains
the compile-and-replay convenience entry point. Its read-only `VerifiedExecProof`
input projection is borrowed from that exact approved setup. There is no
legacy decoder, Stage 2 artifact reconstruction, program/input decoding,
host interpreter, or prover-selected public vector in this boundary.

The setup retains distinct protocol, implementation, semantic-profile,
physical-capacity, primitive-registry, concrete-registry, circuit,
public-template, and input-layout identities. The main transcript uses the
same domain plus complete setup digest as the native Exec verifier. The
auxiliary fold transcript has its own generic Exec domain. Fold claim/table
identities are checked against the approved registry, structure, and layout.

Native verification is a witness-generation check, not the circuit's soundness
argument. A replay export is not an acceptance certificate.

## Exact statement connections

`ExecBindingV0` is compiled only from the approved semantic profile, registry,
circuit, row counts, and explicit public-slot template. Fixed zero words stay
fixed; output positions are never inferred by perturbing a witness vector.

`constrain_exec_binding` computes both domain-separated hashes:

- `S = H4(P || B || I || O)` uses the private input commitment.
- `Q = H5(P || B || O)` is connected to the two external 128-bit digest limbs.

P is fixed by setup; B, I, and O are private circuit variables. The same B and
O wires occur in both hashes. The full Flock public vector is reconstructed
from the fixed template and the two computed S limbs; it is not free advice.
Its exact native chunked BLAKE3 digest is recomputed and bound to the main
transcript. Registry digest, all ordered counts including padding, and circuit
digest are also bound to their exact pre-challenge payloads.

The application must still implement
`verify(approvedConfig, publicCanonicalIxonClaim, compactProof)` and derive Q
from the approved profile/image and canonical result for that explicit claim.
Accepting an opaque prover-selected Q is not the final public-claim API.
Hash binding and backend cryptographic soundness remain named assumptions.

## Replay coverage and setup independence

The generic adapter records and exports:

1. Main chained-BLAKE3 transcript, fork/merge links, and fused PoW predicates.
2. Product-GKR wiring, public/gate recombination, and three structure claims.
3. Standard-RS Boolean zerocheck, union lincheck, and every A/B matrix claim.
4. Two ring switches, packed-direct claims, mixed batching, and dense sumcheck.
5. Multipoint/untwisted assist and its complete jagged assertion.
6. Inner Ligerito, F256 messages, OOD checks, queries, rows, and Merkle paths.
7. Matrix, circuit-structure, and jagged accumulator transcripts and folds.
8. The new generic Exec statement connections described above.

The native accumulator outputs are discharged against the actual fixed tables
as a differential. The circuit composition still exposes those roots publicly;
the differential is not a substitute for closing them inside the final proof.

Wiring and Boolean PIOP topology are independently reconstructed by symbolic
compilers rooted in `CompiledExec`. They never invoke a prover or verifier,
construct a guest, or evaluate witness values. They produce exactly the
arithmetic DAG, static constants, deferred claim identities, challenge/
observation indices, gather mappings, and Boolean PCS wires required by the
approved geometry. The merged PCS, multipoint/anchor assist, and complete
inner Ligerito topology are reconstructed too, including the fixed jagged
heights and every private row/path slot. Native replay is compared structurally
against them before it is returned to the caller.

A separate symbolic tape compiler fixes the complete main operation tree,
not just scalar counts: every label, slice width, PoW difficulty, nonce
payload, fork seed, child closure and merge position. It preserves the
distinction between absent grinding and an explicit zero-bit PoW, and between
one-word vector and scalar squeezes. Query values are never sampled during
setup and cannot alter the row/path allocation. All compilers run before the
strict native proof decoder.

The auxiliary compiler fixes every matrix/structure/jagged claim, fold round,
bridge, root slot, and auxiliary transcript operation. Both transcripts are
lowered to exact BLAKE3 stream sources, compression geometry, CV links, squeeze
sources, fork links, and PoW predicates without hashing or inventing dummy
messages/nonces. Native comparison excludes only the concrete CV/message
witness columns; the existing compression constraints must check their values.
Hash-layout differentials cover absorb/XOF/PoW boundaries with 336 native
instances, and 27 structural mutations are rejected.

The compiled object retains fourteen separate setup/component identities,
including domain-separated main and auxiliary operation-tree digests. It is
borrowed from its approved Exec setup and has no public field replacement or
prover-export constructor. The regression compiles it twice before creating
any guest, then reuses the same object for all three executions. Repeated
native equality is additional evidence, not permission to derive a key from
an arbitrary proof. A proof-free R1CS emitter and terminal key compiler still
need to consume the approved topology without relying on a valid assignment;
no such key-generation API is exposed here.

## Current evidence

The direct scalar setup is the same one exercised by Stage 3's 39-program/
primitive proof corpus: 256 code bytes, two functions, four blocks/function,
two operands, four locals, two continuations, two arguments, 64 input/output
bytes, two input values, and 24 transitions. Its setup digest is
`41163b87f03675917ac93824d8b1c11ab0c489c2fc2e03abece34d11fa3255f7`.

The Stage 4 replay regression uses a local-return program and a three-block
Boolean branch program with both branch outcomes. All three complete Exec
bundles are 296,091 bytes, including their 40-byte envelope. Their thirteen
phase/topology digests agree. No Stage 4 key or FFLONK proof is generated.

| Native replay component | Observed size |
| --- | ---: |
| Public words | 52: 50 fixed, 2 computed S limbs |
| Main transcript operations / challenges | 2,099 / 1,326 |
| Main transcript compression rows / PoW predicates | 1,588 / 320 |
| Boolean arithmetic operations / matrix claims | 3,822 / 46 |
| Wiring arithmetic operations / gather claims | 4,223 / 493 |
| Ligerito levels / queries / opened F128 values | 3 / 371 / 12,524 |
| Merkle path digests | 1,484 |
| Accumulator transcript compression rows / PoW predicates | 4,947 / 1,373 |
| Terminal diagnostic root families | 46 matrix roots, 1 structure, 1 jagged |

The 179 ordinary workspace tests pass; nine tests are ignored by default
(the retained large two-ring projection, native replay/census, and the four
decision-diagram native/materialization/optimization tests, plus two
structural BLAKE3 component tests).
The real three-execution replay regression passes under a 32 GiB
address-space cap with four Rayon threads. The complete matrix-free census
finished successfully in 1,161.51 seconds, including setup, under that cap.
The first 900-second timeout is superseded by this completed run. The retained
[exact census](../flock-stage4/census/exec-scalar-root-conditional-v0.json)
pins the relation revision, reproduction command, counts, projection digest,
timing scope, and sampled process memory counters.

| Complete root-conditional sizing | Result |
| --- | ---: |
| R1CS constraints / nonzero terms | 590,712,359 / 2,795,440,842 |
| PLONK constraint rows | 989,490,840 |
| PLONK base / polynomial-FFT domain | `2^30` / `2^32` |
| Public scalar vector (including Q) | 1,327 scalars / 42,464 bytes |
| Required SRS degree | 9,663,676,433 |
| Compressed file-SRS bytes | 463,856,469,048 |
| Modeled file-key/SRS/FFT resident payload minimum | 420,923,572,256 bytes |
| Last sampled process high-water RSS | 3,548,100 KiB |

PCS accounts for 350,773,578 R1CS constraints; all transcript chains for
105,378,574; accumulator arithmetic for 106,032,537. These are full counts,
not estimates extrapolated from a prefix. The matrix-free census does not
store a complete witness or check its satisfaction, and the memory figure is
not a terminal prover's RSS. The capacity payload excludes several buffers,
R1CS/witness storage and runtime overhead. It is not evidence of fitting a
particular host. Root closure is additional work/cost. No terminal SRS, key,
materialization or proving job was started; this geometry requires cost
reduction before an admitted complete proof.

The binding tests materialize and check their R1CS, mutate both public limbs,
fixed public words, S wires, and every bound prefix payload including count
padding, and reject changed P/B/I/O or registry/circuit/counts. Different
component values produce identical binding matrices. Native bundle mutations,
wrong commitment openings, truncation, trailing bytes, and both historical
artifact domains are rejected.

## Exact fixed-table prototype (M6, not root closure)

`compile_exec_root_tables` borrows the approved setup and derives all 46 Boolean
A/B matrices, the circuit-structure matrix, and the jagged matrix from it.
There is no proof input. Source-entry and retained-node limits apply across
all tables together. The program identity includes the replay identity, exact
coordinate order, coefficients, and all diagram nodes. It is not a terminal
verification-key identity.

The neutral diagram compiler normalizes duplicate entries by characteristic-
two cancellation and reduces identical cofactors. Point-coordinate addresses
are LSB-first row coordinates followed by LSB-first column coordinates;
decisions interleave their bits MSB-first. Every decision evaluates
`low + x * (low + high)`, the exact multilinear interpolation on that Boolean
coordinate. Skipped variables contribute no factor. Coefficients, branch
structure, and ordering are setup-owned, not witnesses. The complete structure
table includes constant-pin plane 5, even though the fresh GKR claims initially
select planes 0–2; a folded random point sees the whole matrix.

`constrain_f128_fixed_table` evaluates the immutable program using the existing
F128 gadgets. Materialized synthetic tests compare literal sparse MLEs, reject
every mutated output/claimed-value bit, and retain the same matrices across
different point values. An actual approved slot-19 A table (768 nonzeros,
43 diagram nodes) also matches native bilinear evaluation in materialized R1CS:
229,797 private variables, 230,853 constraints, and 1,068,466 nonzero terms,
including its twenty point coordinates and private claimed value. Its two
point assignments satisfy identical matrices, and claim-bit mutations fail.

The native all-table differential compiles 46,914,681 source entries into
46,913,775 nonzero coefficients and 1,515,960 diagram nodes in 7.434 seconds;
the complete test takes 13.43 seconds. All 48 tables agree with the pinned
native evaluators at two non-Boolean points each. These tests generate no
guest proof or terminal key. The [retained prototype report](../flock-stage4/census/exec-fixed-root-table-prototype-v0.json)
pins source hashes, counts, resource limits, and measurement scope.

Compression is not yet cheap enough for the terminal circuit: the diagram
programs still have 1,501,595 general field-product sites. Multiplying that by
the isolated fresh-input multiplication gadget's 5,696 constraints gives an
8.55-billion-constraint reference cost for products alone, **not** an emitted
closure census or an unconditional lower bound. The dense BLAKE3 slot and
largest decoder dominate. Six variable orders were tested on those matrices;
MSB interleaving was smallest among those candidates. Bounded positive/mixed
cofactor-XOR rewrites preserve exact values when they finish, but usually grow
or reach the node limit. Only limited structure/small-table savings were found;
the default compiler does not adopt the rewrites.

These are reusable exact-evaluation components and cost evidence. The final
relation must still connect every approved table to the corresponding
constrained transcript point and claimed value, remove the root sidecar, and
prove the complete result. The current root-conditional relation, Stage 3
tables/profile, and backend keys are unchanged. Structural formulas and
complete-verifier cost reductions are the next step; no oversized terminal
materialization, SRS generation, or proving run has been started.

### Structural BLAKE3 matrices

The next prototype, `compile_exec_blake3_root_maps`, preserves the approved
Stage 3 BLAKE3 table exactly. It ports only the pinned Option-F linear row
formulas into a shared XOR program: carry prefixes, fused partial sums, lane
rotations, and finalization reuse intermediate expressions. An IV bit is a
coefficient of the constant-pin **input column**, not a literal F128 one.
The setup compiler then expands every output coefficient and compares it
against the actual registry A/B rows, including their constant and padding
rows. Geometry, graph references, sparse-entry count, and coefficient-memory
limits are checked. There is no sampled-match or digest-only admission path.

Both 16,384-square maps match all 44,442,498 nonzero coefficients. A uses
38,756 retained XORs and B uses 47,867; exact compilation/checking takes
0.155 seconds after approved setup. Native multilinear evaluations agree at
three different point pairs per matrix. Altered constant/padding formulas and
insufficient resource bounds fail. No Stage 3 matrix, profile, key, transcript,
or upstream source is changed.

The neutral `constrain_f128_binary_linear_table` gadget generates only the
referenced column basis weights, applies the immutable XOR network, and folds
its output rows at the supplied row point. All inputs are already constrained
point wires, and sharing decisions compare fixed wire identities, not witness
values. Small materialized rectangular examples agree with literal sparse
MLEs, reject all claimed-bit mutations, and preserve identical matrices across
different values. The application must still authorize the map and bind its
point/value wires to the exact deferred claim.

| Structural BLAKE3 component | A | B |
| --- | ---: | ---: |
| R1CS constraints | 139,902,339 | 132,705,987 |
| PLONK constraint rows | 221,560,957 | 209,357,185 |
| Matrix-free census seconds | 248.527 | 237.700 |

These complete component counts include 28 freshly allocated private F128
point coordinates each; they exclude a claimed-value input, transcript/Exec
binding, and every other verifier/root component. The full test completed in
491.59 seconds under a 32 GiB address-space cap, without storing the matrices
or checking a complete satisfying assignment. The source/formula/map hashes,
projection identities, native negatives, commands, and memory scope are in the
[structural report](../flock-stage4/census/exec-structural-blake3-root-v0.json).
This is a substantial improvement over the decision-diagram product-cost
reference, but not a measured full-closure census or an admitted terminal
proving job. Further cost reduction and the original M5–M8 gates remain.

## Remaining gates

Implement proof-free R1CS/key compilation from the approved replay blueprints;
extend phase-specific hostile message tests; close every unresolved table
evaluation in the final relation;
then actually prove and isolate-verify that complete relation with only an
approved terminal configuration, externally expected statement, and compact
proof. Resource admission must use the new complete geometry including root
closure. The 992-byte legacy proof-body codec remains only a transport fact.

The scalable guest operations, native representation/refinement proofs,
certified compiler handoff, and changed-Stage-2-guest upgrade test remain part
of the original plan. This replay port does not discharge them.
