# Generic IxBy → Stage 4 replay

Status: native replay, public/private statement binding, a root-closed
composition prototype and bounded proof-free R1CS emission are implemented.
This is progress toward M5/M6, not
completion of M5–M8. There is no approved full terminal topology/key,
materialized complete closed-root relation, or complete FFLONK proof yet.
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
as a differential. The diagnostic circuit composition exposes those roots
publicly; the separate closed prototype emits their exact table evaluations.
The native differential is not a substitute for those in-circuit constraints
or for a completed full-relation proof.

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
an arbitrary proof. The proof-free R1CS emitter below consumes this topology
without relying on a valid assignment. Complete materialization and terminal
key preprocessing remain unfinished; no terminal key-generation API is exposed.

## Legacy-backend baseline evidence

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

The current ordinary Stage 4 workspace suite passes 208 tests; 23 tests are
ignored by default. These separately labelled opt-in tests cover native
proof/replay, component materialization, and bounded whole-circuit census;
none is a full terminal proving test. This count includes the later packed
backend integration below.
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

### Explicit small generic class

The setup API also admits a separately identified scalar class with 64 program
bytes, one function and one block, one operand/local/continuation/argument,
one input value, 32 input/output bytes, and four transitions. Both capacity
and semantic-profile identities change; the scalar primitive meanings and
pinned implementation remain the same. This is an M6 cost diagnostic, not a
replacement for the baseline or the larger crypto/Stage 2 workloads in M4/M8.

| Setup-owned geometry | Baseline | Small class |
| --- | ---: | ---: |
| Dense witness words | 43,028 | 7,124 |
| Committed words / PCS dimension | 65,536 / `m=23` | 32,768 / `m=22` |
| Live PCS lanes | 43 | 14 |
| Ligerito queries | 371 | 371 |
| Opened F128 words / path digests | 12,524 / 1,484 | 5,448 / 1,113 |
| Boolean matrix root claims | 46 | 46 |
| Matrix-fold rounds | 1,208 | 1,172 |

The smaller class reaches the upstream embedded configuration floor, without
lowering security/query/grinding settings. BLAKE3's 44,442,498 A/B nonzeros
remain exactly unchanged. Its sorted registry index moves from 9 to 7;
the root compiler discovers and exhaustively validates the actual table.
No setup or circuit topology is chosen from guest instructions or proof data.

The small setup digest is
`4fe87f091aef3cd1e54f290874eb5f148c8a31a3bbbafdac5a242b3e2d7081f5`.
Its closed-composition program digest is
`7c4ce17ecb07358d058e45d8f153f2b8ed39e0389b4f5626b4c626935a55c8a1`,
not a full R1CS or verification-key digest. The regression compiles setup
twice before creating a guest and reuses it for local return with false/true
inputs and a distinct image returning literal true. All three complete native
bundles are 165,667 bytes. Every native matrix/structure/jagged root matches
the setup-owned program, and each assigned 4,096-constraint prefix equals
proof-free setup emission. Program/input/output commitment changes and proof
mutation are rejected. Generic execution of a true-returning image does not
authorize that image as an application Stage 2 verifier.

The whole closed-circuit measurement is a separate, bounded, proof-free test:
`small_capacity_complete_root_closed_admission_census`. It uses the real
composition and PLONK observer with the same `2^30` hard cutoff; it does not
infer a full result from component savings or prefix counts. Source hashes,
parameters, native cases and measurement outcomes are in the
[small-class report](../flock-stage4/census/exec-small-class-root-closed-admission-v0.json).
It returned `RejectedBudget` after 1,246.958 seconds of emission (1,257.41
seconds including setup), at 651,198,742 R1CS constraints and 1,073,741,821
PLONK constraint rows in `MatrixFold`. The two public and two blinding rows
require 1,073,741,825 rows, crossing `2^30` before root closure finishes.
This is not the full relation's count, and removing one row would not establish
that it fits. Last sampled process high-water RSS was 2,157,240 KiB, including
native setup; the streamed matrices/witness were not retained. Other tests
overlapped emission, so timing is not a controlled comparison. The smaller
capacity does not solve the current encoding's supported-domain failure.
Neither a native root differential nor a successful sizing result establishes
the full satisfying assignment, terminal key/proof, isolated verification or
larger-profile acceptance gates.

### Explicit packed-word backend integration

`Blake3Backend::PackedWordsV0` is a setup-owned implementation choice supplied
to `compile_exec_profile_with_backend`. The default compiler remains
LegacyOptionF with the unchanged baseline setup digest above. Within either
capacity class, packed setup preserves the same semantic profile, primitive
meanings, capacity and commitment function, but changes the implementation,
registry, circuit/public-template, protocol geometry and transcript identity.
No proof header or guest selects this choice. Native cross-backend substitution
rejects both original proofs and proofs with forged receiver-matching headers.

The packed baseline setup digest is
`e100007d6afc10d3d4e0afcc529a7a1a1c147c7e76d2f1623d83240cf073da11`;
the packed small class is
`e02060020627b285c8c1d13989e9a18cb0f88595ca5bf414f8daaf4b6f713e96`.
These are generic Exec setup identities, not terminal verification keys.

| Packed setup-owned geometry | Baseline | Small class |
| --- | ---: | ---: |
| Outer row log / PCS dimension | 11 / `m=23` | 11 / `m=22` |
| Dense witness words / live lanes | 53,288 / 53 | 15,764 / 31 |
| Ligerito queries | 371 | 371 |
| Opened F128 words / path digests | 14,964 / 1,484 | 9,596 / 1,113 |
| Boolean matrix root claims | 64 | 64 |
| Matrix-fold rounds | 1,512 | 1,476 |
| Logical source-slot payload bytes | 618,953 | 500,041 |

The embedded Fast128 schedule remains `[244,79,48]` queries and `[16,16,16]`
query-grinding bits. Source-slot bytes exclude approved setup, intermediates,
matrix/witness storage, allocator overhead and process-tree RSS. Repeated
proof-free replay/root compilation gives identical identities for each class.
The root compiler dispatches on the approved backend: legacy has exactly two
checked BLAKE3 formula replacements; packed has zero replacements and exact
diagrams for all 64 A/B matrices. Both retain the exact cofactor-basis structure
and jagged programs. The legacy formula API rejects packed setup explicitly;
compilation failures do not trigger a fallback or leave a missing root.

All 39 baseline scalar/control cases have real packed Exec proofs, each with
a 339,563-byte bundle, and fresh-process verification using only fixed approved
setup, externally expected 32-byte S and proof. For the small class, local
return with false/true inputs and a distinct literal-true image reuse one
setup; each bundle is 236,307 bytes. All 66 native roots match exact setup-owned
evaluation, and the first 4,096 assigned constraints equal proof-free emission
for every case. Changed B/I/O commitments and proof bytes reject. These are
native proofs, root differentials and a short exact prefix, not a complete
closed R1CS identity, satisfying assignment or terminal proof.

`packed_small_exec_whole_root_closed_admission_census` separately measures the
whole proof-free closed emitter with the actual PLONK observer and unchanged
`2^30` domain cap, including the four public/blinding reservations. Its outcome,
frozen source hashes, commands and limits are retained in the
[integrated report](../flock-stage4/census/exec-packed-blake3-root-closed-v0.json).
The run returned `RejectedBudget` after 1,349.908 seconds of emission
(1,350.62 seconds including setup), at 643,838,506 R1CS constraints and
1,073,741,859 PLONK rows in `MatrixFold`. Including the four reserved rows
requires 1,073,741,863 rows, beyond the supported domain. That is a refused
prefix, not a full count; the 39-row overrun is only the stopping threshold,
not the savings needed to fit. Last sampled test-process high-water RSS was
1,165,708 KiB, not a terminal-prover or process-tree measurement. No complete
matrix, satisfying assignment, terminal key or proof was generated.
The [earlier compression-component census](../flock-stage4/census/packed-blake3-components-v0.json)
is not a substitute for this whole-relation measurement: denser witnesses,
more matrix folds and changed wiring/PCS can offset root-component savings.
The complete encoding still needs cost reduction before full materialization,
key/SRS/resource admission and isolated terminal proving. Formal refinement
and the larger crypto/certified Stage 2 guest requirements remain unfinished.

## Exact fixed-table components (M6)

`compile_exec_root_tables` borrows the approved setup and derives all Boolean
A/B matrices (46 for legacy, 64 for packed), the circuit-structure matrix, and
the jagged matrix from it.
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
Davio rewrites preserve exact values when they finish, but usually grow or
reach the node limit. Only limited structure/small-table savings were found;
the default compiler does not adopt the rewrites.

These are reusable exact-evaluation components and cost evidence. The new
closed composition below connects the approved tables to their corresponding
constrained transcript points and claims; its complete result still needs to
be proved. The diagnostic root-conditional relation, Stage 3 tables/profile,
and backend keys are unchanged. Structural formulas and complete-verifier
cost reductions remain necessary; no oversized terminal materialization, SRS
generation, or proving run has been started.

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

### Exact structure cofactor bases

`F128FixedTableBasisV0::compile` constructs immutable, layered GF(2) bases
from the exact setup-owned Shannon diagram. At a layer, each source cofactor
is represented by its low/high coefficient vectors in the next layer's basis.
Gaussian elimination records residual basis vectors and an exact XOR decoder
for every source vector. Leaf elimination includes all 128 coefficient bits;
skipped coordinates retain the same cofactor on both sides. Davio input is
rejected rather than expanded into an unbounded set of new cofactors.

This is an algebraic construction, not a randomized rank test: induction on
the layers identifies every Boolean-cube coefficient with the source diagram.
Each layer evaluates `low + x * (low + high)` using fixed XOR coefficients,
and a coordinate occurs only once on each path. Thus it represents the same
multilinear polynomial over F128. The Rust implementation and circuit gadgets
still require their stated implementation/refinement review; these tests are
not a new kernel-checked theorem or cryptographic assumption.

State slots, cumulative dense-word allocations, word operations and retained
coefficient terms have independent hard compilation bounds. These exclude the
source table, container overhead and the rest of setup and are not an RSS or
prover-admission model. No constructor accepts arbitrary unvalidated layers,
table-value advice, guest data, or proof-derived topology. The program digest
binds its source identity, constants, coordinate order and every coefficient.

The first bounded experiment completes 44 of the 48 actual table programs,
each matching the source diagram at four points in native Flock F128. Slots
0 and 9, both sides, exceed the work bound. A larger diagnostic with 4 billion
word operations and 16 million coefficient terms still refuses all four:
three work-limit failures and one term-limit failure. Reducing rank does not
necessarily reduce circuit cost; none of those matrix/jagged candidates is
automatically selected.

The structure component does show a measured reduction:

| Complete structure-table component | Shannon diagram | Cofactor basis |
| --- | ---: | ---: |
| R1CS constraints | 57,687,119 | 15,998,468 |
| R1CS nonzero terms | 267,174,632 | 76,719,487 |
| PLONK constraint rows | 92,024,156 | 21,653,222 |
| Component base domain | `2^27` | `2^25` |

These matrix-free counts include twenty fresh private F128 point coordinates
and the complete table evaluation, but exclude the claim binding and remaining
verifier. Each emission had an independent 200-million-PLONK-row cutoff.
The 70,370,934-row saving is 76.47% of this component, not of the complete
relation. Both runs completed; neither checked a full satisfying assignment
or generated a terminal proof. The [cofactor report](../flock-stage4/census/exec-cofactor-root-basis-v0.json)
records source hashes, program identities, paired runs and measurement scope.

`compile_exec_root_closure` now selects the basis only for structure and requires
an explicit `.structure_basis` budget. Failure propagates without fallback.
Stage 3's tables/profile/transcript remain identical, while the Stage 4
table-program/composition identities change. Materialized tests cover all three
program kinds, every root family and every claim bit, including exact equality
between proof-free matrices and several assignments. The real-Exec regression
recompiles before three guest/outcome proofs and compares every native fold root.
The previous supported-domain refusal occurs in unchanged work before structure
evaluation. This improvement does not produce a feasible whole-relation census,
materialized closed circuit, terminal key or full FFLONK proof.

## Root-closed composition and hard domain budget

`compile_exec_root_closure(approvedReplay, limits)` compiles all 48 exact
programs before any guest/proof exists. Two BLAKE3 matrix diagrams are replaced
by the exhaustively coefficient-checked linear programs; structure uses the
exact cofactor basis above; the 44 other matrix and jagged diagrams remain.
The current compiler temporarily builds the complete diagram set first, so
its global entry/node budgets include those temporary BLAKE3 diagrams.
Linear construction and the
additional exhaustive coefficient pass and structure-basis construction have
separate explicit bounds.

The immutable table set binds ordered matrix IDs, registry/circuit identities,
program kinds/digests, and every row/column dimension. Its neutral constructor
validates identity/geometry, not coefficient provenance; only the approved
Exec compiler derives and validates these programs from the actual setup.
The compiled closure owns the table set and borrows that same approved replay.
Its `constrain` method rejects mismatched setup/topology/binding before any
allocation and takes externally expected public Q explicitly, not from the
replay witness. This is its witness-driven path; the separate setup-only path
below accepts no such witness. Neither is a terminal key or acceptance certificate.

`constrain_exec_root_closed` and the existing root-conditional API share the
same complete replay body. At each original family-binding site, the closed
path evaluates every exact table at the fold's already constrained point wires
and enforces equality with its claim wires. It allocates no new root witness
or public root sidecar. The only public inputs are Q's two limbs. There is no
unchecked/private binding mode or native-discharge callback. The old path's
public allocation and constraint order are preserved by this refactor.

Synthetic materialized tests exercise all three program kinds and all three
root families. All 128 bits of every claim are mutated and rejected; freshly forged
claims reach R1CS satisfaction checking rather than failing a native value
comparison. Matrix identity/order/count and family geometry failures emit no
constraints. Three point assignments retain identical matrices.

The initial native closure regression compiled the complete root set twice before
creating any proof (15.258 seconds), then matched all 48 native folded roots
for a return program and both branch outcomes (25.58 seconds total). Its
original, pre-cofactor composition digest is
`64caf60bc1fe39846d95e195e3ecf598b75a1bcf22820e5ef72836399c868bdc`;
the table-set digest is
`f020d4867674049eb517f7e7be472614f2e34453adaacbb9834374c6783a3199`.
Those are setup-program identities, NOT R1CS or terminal key digests.
The structure-basis version instead has composition digest
`2a5197d95f015ded732322e73a999bb128faab2e8ffd4c873a15a6c759db2d24`
and table-set digest
`2100cce6c5b5aa4136b68217fda000d2a10189f7863c530507e76cfb94e4a073`;
the same distinction from a terminal key applies.
The same test checks setup-identity corruption before allocation, confirms
that the first private transcript bit follows the two Q limbs, and refuses
zero/tiny or above-supported row budgets. This is native differential and
bounded-entry evidence, not a complete closed R1CS check.

The matrix-free admission API counts actual deterministic PLONK lowering and
stops after the first R1CS constraint whose rows, plus the two public and two
blinding rows, exceed the requested cap. It refuses a cap above `2^30`, since
the pinned prover requires a `4n` polynomial FFT over Fr. Observer errors are
sticky across further emission, allocation, and both finish methods. A refused
stream returns a distinct `RejectedBudget` prefix with no complete digest or
domain; only a finished relation can return the complete census variant.
Successful census still does not check a satisfying assignment, approve host
resources/setup, or generate a proof. Use a bounded subprocess for RAM/time
limits in addition to the internal geometry cap.

The initial bounded full-emission test returned `RejectedBudget` in 1,245.361
seconds after setup/proof replay (1,260.47 seconds total test time). At refusal it had
emitted 643,831,813 R1CS constraints, 1,073,741,821 PLONK constraint rows, and
429,910,008 lowering auxiliary wires, in the `MatrixFold` phase. Adding the
four public/blinding reservations requires 1,073,741,825 rows, beyond the
`2^30` supported base domain. Even that prefix requires a `2^31` padded domain
and `2^33` polynomial FFT; those are lower bounds implied by the prefix, not
a completed full-relation capacity census. The first-over-limit stop does not
imply that removing one row would make the complete relation fit.

The last sampled test-process high-water RSS was 3,558,544 KiB and peak virtual
size 4,163,960 KiB. These include approved native setup, not a terminal prover
or whole process tree. The ordinary test suite overlapped the beginning of
emission; timing is not a controlled benchmark comparison. No complete
closed R1CS, full assignment, terminal SRS/key, or proof was generated. The
[retained admission report](../flock-stage4/census/exec-root-closed-admission-v0.json)
pins every changed Rust source hash, native regression, hard bounds, exact
prefix and timing/memory scope. This establishes that the current encoding
needs cost reduction before proving, not that M6's compact-proof gate passed.

## Proof-free R1CS emission from approved setup

`CompiledExecRootClosure::build_setup_r1cs(ExecSetupR1csLimitsV0)` is an
assignment-free matrix emitter. It takes no guest, statement, expected Q,
commitment components, Flock proof, native replay or replacement trace. Its
`emit_setup` counterpart takes a shape-only streaming builder and a source-slot
payload limit. Both call the same complete closed composition, using only the
immutable approved blueprints and coefficient-checked root programs.

The source-slot layout is derived from approved main/auxiliary observation,
challenge and payload counts; Boolean matrix claims; the fixed wiring and
multipoint private slots; and every inner-Ligerito row/path slot. References,
geometry, uniqueness and hash links are validated. Zero scratch arrays supply
only the existing gadgets' host-value computations. They are not a fabricated
native proof or a satisfying assignment, and no scratch output is returned.
B/I/O and the two public Q limbs stay variable in the physical circuit.

The builder has a construction-time shape mode, distinct from materialized
witness generation. It stores no assignment. `finish_shape` returns only
canonical matrices and validates every variable index; the witness-returning
`finish` rejects shape mode. A shape-only projection can return counts/digests,
never an assignment. Native builders keep their original diagnostic checks.

Only early native-value comparisons are suppressed: transcript compression
columns/challenge hints, binding payloads, algebra assertions and fold value
consistency. Structural checks and their actual equalities remain. An unknown
zero inverse slot uses scratch zero but still emits the same private inverse,
multiplication and `x * inverse = 1` constraint. Neither PoW nor root-table
discharge is skipped. Fixed constants and wire identity, never private scratch
values, determine constant folding and circuit shape.

`R1csShapeLimitsV0` caps variables (including ONE), rows and sparse terms before
retaining over-budget data. Observer/matrix refusals are sticky, including on
the last infallible constraint. Source preflight errors occur before source
allocation and must also be propagated. The owned materialization and census
APIs propagate both emitter and builder errors and never return a partial
circuit as a successful whole relation.

The real scalar setup reports 27,611 F128 source words, 1,484 private digest
words, and 1,705 byte payloads totaling 25,185 bytes: 514,449 bytes of logical
heap-backed source payload. The limit excludes Vec/allocator overhead, inline
B/I/O/Q scratch, approved setup/table storage, gadget intermediates and R1CS
matrices. It is not a peak-RAM or whole-pipeline admission claim.

Evidence is deliberately split by scope:

- Materialized setup matrices exactly match several valid assignments for
  transcript, Exec binding, inverse/algebra, matrix/structure/jagged folds,
  two-level Ligerito and all root-program families. Mutation tests use the
  emitted matrices, not only native rejections. Malformed topology still fails.
- The updated real-Exec regression builds setup and performs bounded emission
  before any guest/proof. Its first 4,096 normalized constraints match all three
  native executions exactly; tiny domain caps and source/matrix refusals pass.
  This prefix is not a whole-circuit digest or verification-key identity.
- `census_exec_root_closed_setup_observed` attempts the whole relation without
  constructing a Flock proof. It has the same public/blinding reservations and
  hard supported-domain limit as the witness-driven diagnostic. A rejected
  prefix contains no complete R1CS digest, full census, terminal key or proof.

The initial whole proof-free run, before the structure-basis optimization,
returned `RejectedBudget` after 1,240.765 seconds of emission (1,253.75 seconds
total test time). It reached exactly the previous
witness-driven cutoff: 643,831,813 R1CS constraints, 1,073,741,821 PLONK rows,
429,910,008 auxiliary wires, last phase `MatrixFold`. Including public/blinding
reservations again exceeds the supported domain. This is prefix count agreement,
not a full matrix digest or completed relation. No guest, Flock proof, valid
assignment, terminal key or full R1CS matrices were constructed by this run.
Its test-process high-water RSS was 3,219,264 KiB and peak virtual size
3,516,620 KiB, including approved native setup. These are not process-tree or
terminal-prover measurements. The 11 setup tests also passed with debug
assertions enabled; that run overlapped emission, so the timings are not a
controlled throughput comparison. The [proof-free emission report](../flock-stage4/census/exec-proof-free-root-closed-emission-v0.json)
records the frozen source hashes, commands, actual limits and separate scopes.

## Remaining gates

Complete proof-free materialization/key preprocessing at feasible geometry;
extend phase-specific hostile message tests; reduce and fully measure the
closed prototype; then actually prove and isolate-verify that complete
relation with only an
approved terminal configuration, externally expected statement, and compact
proof. Resource admission must use the new complete geometry including root
closure. The 992-byte legacy proof-body codec remains only a transport fact.

The scalable guest operations, native representation/refinement proofs,
certified compiler handoff, and changed-Stage-2-guest upgrade test remain part
of the original plan. This replay port does not discharge them.
