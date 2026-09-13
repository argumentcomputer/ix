# Experimental Stage 4 native core

This independent Cargo workspace contains the reusable trace, R1CS circuit,
and KZG-FFLONK components imported from `jcb/flock-stage4` at `8fdb3eab`.
`IMPORT-PROVENANCE.json` records the original revision and SHA-256/Git blob
identities of all 47 imported source/manifests. It describes the import
baseline, not a promise that subsequent changes have those hashes.

The workspace is excluded from the ordinary Ix Cargo build. Its `exec` crate
now uses the generic `ixby-flock` backend and the same pinned Flock revision;
the three original crates remain Flock-independent. No crate depends on the
native Stage 2 verifier, and the root dependency pins are unchanged.

```sh
cargo test --release --locked --manifest-path flock-stage4/Cargo.toml --workspace
cargo fmt --manifest-path flock-stage4/Cargo.toml --all -- --check
```

The import regression on 2026-09-12 passed 149 tests (88 FFLONK, 18 trace,
43 circuit); one pre-existing heavyweight circuit projection is ignored.
Tests include strict scalar/curve/subgroup decoding, invalid SRS/key rejection,
nonzero blinding admission, authenticated scratch corruption, and identical
proof/key results across memory and file backends for fixed test randomness.
Small proofs use development setup and randomness, not production security.
The generic replay and root-closure/setup prototypes pass 228 ordinary tests
(89 FFLONK, 43 trace, 79 circuit, 17 replay/setup); thirty-two heavier native,
materialization, and census/optimization tests remain opt-in.

## Generic Exec replay

`exec::compile_exec_replay` takes only an approved `CompiledExec` and produces
an immutable replay topology before any guest or proof exists. Its `replay`
method consumes commitment components and the strict `IXBYEX00` bundle;
`exec::replay_exec` is a compile-and-replay convenience wrapper.
It never reconstructs a native Stage 2 proof,
guest image, input bytes, or execution trace. The complete native verifier,
recorded transcript, algebra, Product-GKR, merged PCS, multipoint/untwisted
assist, inner Ligerito/Merkle, and all accumulator folds are exercised on
three real generic executions under one setup. Native replay topology is
identical across two programs and both branch outcomes.

The new circuit binding constrains `S = H4(P,B,I,O)` and public `Q = H5(P,B,O)`.
The input commitment is private; the public claim remains an explicit
application input from which the approved image/profile and canonical output
determine Q. The final application verifier has not been implemented yet.
The diagnostic replay composition is deliberately named
`constrain_exec_root_conditional`; its roots still require external discharge.
The separate `constrain_exec_root_closed` prototype emits exact table checks
and publishes only Q. It has not produced a full closed-relation proof.

Proof-free symbolic compilers reconstruct wiring, zerocheck, lincheck, merged
PCS, multipoint/anchor assist, inner Ligerito, and all three accumulator folds,
plus both complete transcript operation trees and their BLAKE3 compression
topology. Native replay must match their exact structures, not just operation
counts. Component identities remain distinct. The root-closure setup emitter
below consumes these blueprints directly, without a valid assignment. No
terminal key or full FFLONK proof is produced here.

```sh
ulimit -v 33554432
RAYON_NUM_THREADS=4 timeout 180 cargo test --release --locked \
  --manifest-path flock-stage4/Cargo.toml -p ixby-stage4-exec \
  native::tests::different_guests_have_identical_complete_replay_topology \
  -- --ignored --test-threads=1 --nocapture
```

The full matrix-free census is separately opt-in via
`native::tests::complete_generic_exec_constraint_census`. It reports phase
progress, process peak memory counters, canonical R1CS/PLONK counts, and
capacity minima. A sizing report is not a satisfying-assignment check or a
proof. The completed run took 1,161.51 seconds including setup and counted
590,712,359 R1CS constraints and 989,490,840 PLONK rows. It still carries 42,464
public scalar bytes, needs a `2^30` base domain, and models a 420.9 GB
file-key/SRS/FFT resident payload minimum before several excluded costs.
The [retained report](census/exec-scalar-root-conditional-v0.json) records exact
counts and scope. Cost reduction and root closure are required; no expensive
terminal-prover or SRS job has been launched.

## Exact fixed-root table prototype

`exec::compile_exec_root_tables` derives immutable decision diagrams from the
approved registry, complete eight-plane circuit structure, and jagged layout.
The neutral `constrain_f128_fixed_table` gadget evaluates their exact
multilinear extensions at constrained point wires. It accepts no table-value
hint. This component prototype preserves the diagnostic root-conditional path.
The new closed composition below supplies the point/value/identity connections;
emitting these checks is not a substitute for proving the complete relation.

All 48 tables match the native evaluators at two non-Boolean points. One actual
registry-table gadget was materialized and checked at two points with identical
R1CS matrices; claimed-value mutations fail. Its 230,853 constraints are a
component measurement, not the full relation's cost. The complete diagram
census has 1,515,960 nodes and 1,501,595 general product sites. The bounded
positive/mixed Davio rewrites mostly grow or hit their limits; none is adopted
by the default compiler. See the [prototype census](census/exec-fixed-root-table-prototype-v0.json)
for exact counts, bounds, reproduction commands, and failed alternatives.
Structural formulas and further verifier cost reduction are needed before
full terminal proving can be admitted.

The separate `compile_exec_blake3_root_maps` prototype reconstructs the pinned
BLAKE3 tables as shared XOR programs and checks **every coefficient** against
the approved registry before returning them. It does not modify Stage 3's
matrices or replace coefficient validation with a digest or sample test.
`constrain_f128_binary_linear_table` applies such a map to constrained column
basis weights and interpolates its rows. No matrix-value hint is accepted.
The A/B programs have 38,756/47,867 XORs; both match native MLE evaluation.
The complete component-only matrix-free census totals 272,608,326 R1CS
constraints and 430,918,142 PLONK rows, including fresh private point wires
but excluding the rest of the verifier and terminal claim binding.
This remains an oversized prototype, not a closed-root proof. Its
[separate report](census/exec-structural-blake3-root-v0.json) records the exact
counts, original formula provenance, source/map hashes, bounds, and tests.

The structure table now uses an exact cofactor-basis program. Gaussian
elimination on fixed cofactor coefficient pairs reduces its representation;
the circuit still interpolates every coordinate and enforces the original
folded claim. No sampled-value hint or new commitment replaces the table.
The paired, complete component census falls from 57,687,119 to 15,998,468 R1CS
constraints and from 92,024,156 to 21,653,222 PLONK constraint rows (76.47% fewer).
These counts include twenty fresh private F128 coordinates and table evaluation
only, not the whole verifier or terminal claim binding.

Only structure adopts this representation. Other large-table attempts hit
explicit compiler work/term limits, even in a separately bounded larger trial.
The new `.structure_basis` compilation budget has no fallback on failure.
The [cofactor report](census/exec-cofactor-root-basis-v0.json) records exact
source/program identities, native and materialized tests, paired counts and
bounded failures. Stage 3 matrices/profile/transcript are unchanged; Stage 4's
composition identity changes. This later-phase saving does not remove the
previous domain refusal in the unchanged earlier matrix-root work, and no
complete closed proof or terminal key has been produced.

## Root-closed composition and bounded admission

`compile_exec_root_closure` derives an immutable, complete root program set
from the approved replay setup alone: the two exhaustively checked BLAKE3
linear maps, 44 other matrix diagrams, a structure cofactor basis, and a jagged
diagram. No guest, point, value, statement, or proof is an input. The shared replay composition
binds each deferred root to its exact table evaluation using the already
constrained transcript point and claim wires. There is no new root witness,
unchecked acceptance bit, or native table-discharge callback in this path.
Its public input is the caller's externally expected Q, exactly two limbs.
These program identities are not terminal R1CS/verification-key identities.

The real native test compiles the complete table set twice before creating
any proof, then checks all 48 evaluations against the native fold roots of
three executions. It also tests malformed setup identities and tiny row caps.
Materialized synthetic root-binding tests reject every changed claim bit,
missing/duplicated/reordered roots, and incorrect family geometry.

`census_exec_root_closed_observed` uses the same closed entry point with a
hard required-row cap, including the two public and two blinding rows. A cap
above the current `2^30` base-domain limit is refused. An observer failure is
sticky: later emission/allocation stops and neither builder finish method
can return a completed prefix. The result distinguishes `RejectedBudget`
prefix counts from `Complete` census data. Neither result is a satisfying-
assignment check, full proof, or RAM/disk/SRS admission.

```sh
ulimit -v 33554432
RAYON_NUM_THREADS=4 timeout 180 cargo test --release --locked \
  --manifest-path flock-stage4/Cargo.toml -p ixby-stage4-exec \
  native::tests::closure_tests::setup_owned_closure_matches_all_real_fold_roots \
  -- --ignored --test-threads=1 --nocapture
```

Before the structure-basis optimization, the separately ignored
`root_closed_supported_domain_admission_census` test
attempted whole-relation emission with that hard supported-domain cutoff. It
returned `RejectedBudget` after 1,245.361 seconds of emission: 643,831,813 R1CS
constraints and 1,073,741,821 PLONK constraint rows. With four reserved rows,
that prefix already exceeds the supported domain. The complete relation's
count is unknown; this is not a full census or a nearly fitting proof. The
[admission report](census/exec-root-closed-admission-v0.json) records source
hashes, exact counts, commands, and measurement scope. Cost reduction,
complete materialization/key preprocessing, and a closed-relation FFLONK proof
with isolated verification remain required.

## Assignment-free setup emission

`CompiledExecRootClosure::build_setup_r1cs` takes only allocation limits and
returns canonical matrices, never a witness. `emit_setup` streams the same
whole closed composition to a shape-only builder. Its inputs are the immutable
approved replay/table programs: no guest, commitment, expected Q, Flock proof,
or native replay witness is accepted. The two Q slots remain public variables;
their zero scratch assignments do not become circuit constants.

Setup mode suppresses only redundant native-value diagnostics. It still emits
all transcript/PoW, statement, algebra/inverse, PCS/Merkle, fold and exact-root
constraints, with structural validation intact. Private zero scratch remains
private, and this mode cannot export an assignment. Ordinary witness emission
still rejects inconsistent values and zero inverses.

Materialized setup has explicit variable/row/nonzero-term limits. Source-slot
payload is checked before allocation; the current scalar setup uses 514,449
bytes for 27,611 F128 words, 1,484 digests and 25,185 payload bytes. This excludes
container/allocator overhead, approved setup, gadget intermediates and matrices:
it is not a RAM admission. Matrix/observer refusals are sticky; all emitter
errors must be propagated, including source preflight errors.

Materialized component tests compare setup matrices with several real
assignments and reject mutations in challenge/inverse/statement/root/CAP wires.
The real-Exec regression compares the first 4,096 exact constraints and bounded
admission results for three executions with setup emission performed before
any guest/proof existed. That small prefix is not a full circuit identity.
`census_exec_root_closed_setup_observed` separately attempts the whole relation
without a Flock proof and retains the same supported-domain cutoff. Its initial
run, before the later structure-basis optimization,
returned `RejectedBudget` after 1,240.765 seconds of emission at exactly the
earlier witness-driven prefix counts: 643,831,813 R1CS constraints and
1,073,741,821 PLONK rows. The [separate proof-free report](census/exec-proof-free-root-closed-emission-v0.json)
records source hashes, bounds, component/native/debug tests and measurement
scope. This is count agreement up to a cutoff, not complete matrix/key equality
or a proof. A complete closed matrix/key and isolated terminal proof remain
outstanding and require cost reduction.

See [generic replay and remaining gates](../docs/IxbyStage4Replay.md).
`EXEC-REPLAY-PROVENANCE.json` records the donor hashes before this port,
excluded legacy interfaces, and semantic changes separately from M1.

## Explicit small-class diagnostic

The separate `capacity_tests` use a generic scalar class with 64 code bytes,
one function/block/operand/local/continuation/argument/input value, 32-byte
input/output buffers and four transitions. This is an explicit profile/setup
change, not a baseline replacement or a capacity suitable for Stage 2 guests.
The same pinned Fast128 configuration machinery admits `m=22`, its embedded
floor, with 14 live lanes instead of the baseline's 43 at `m=23`. All 371
queries and their grinding policy remain; no development query schedule is
installed. BLAKE3's full fixed matrices are unchanged.

Three real proofs (two local-return inputs and a different literal-return
image) reuse that one setup. All 48 native roots match its exact table programs,
and all three 4,096-row assigned prefixes match proof-free emission. Changed
commitments and proof bytes fail native replay. Each complete native Exec
bundle is 165,667 bytes; this is not a terminal FFLONK artifact.

`small_capacity_complete_root_closed_admission_census` separately measures
the whole closed relation, not a sum or subtraction of component counts.
It retains the hard `2^30` supported-domain cutoff and does not materialize
terminal matrices, check an entire assignment, create a key or prove anything.
The run returned `RejectedBudget` after 1,246.958 seconds of emission:
651,198,742 R1CS constraints and 1,073,741,821 PLONK constraint rows. Including
four public/blinding rows crosses the domain limit before the relation ends.
The full closed count is still unknown; reducing capacity alone did not make
this encoding feasible. This is a new refused prefix, not a full census.
The [small-class report](census/exec-small-class-root-closed-admission-v0.json)
records source hashes, setup identities, reproduction commands and result scope.

## Explicit packed-word compression backend

A Stage 3 compression implementation replaces the single flattened
BLAKE3 table with ten reusable word tables. Its twenty exact A/B diagrams
retain 1,582 nodes and 23,808 nonzero entries. Four native-field differentials
per matrix pass.

The complete independent matrix-component census is 8,786,640 R1CS
constraints / 14,121,316 PLONK rows, with setup-only and assigned projections
identical for every component. It includes twenty private point/value
bindings. The earlier two flattened-table components alone needed
430,918,142 PLONK rows (without separately allocated claimed values).
This is a component comparison, not a new full-Exec estimate: more outer rows,
dense words, matrix folds and wiring may increase other costs.

One actual lane-table component was materialized at 160,197 R1CS constraints.
Both assignments satisfy identical matrices, and all 128 claimed-output-bit
mutations reject. Two real native compression proofs also pass isolated
verification, with a locally valid but globally miswired row rejected.
Neither test is a terminal proof. The [historical packed-component report](census/packed-blake3-components-v0.json)
records those sources, exact counts and bounded commands.

`compile_exec_profile_with_backend(..., Blake3Backend::PackedWordsV0)` now
integrates the packed implementation into generic scalar Exec as an explicit
backend/key upgrade. The default legacy setup remains byte-identical. Backend
choice is verifier-owned, never taken from a guest or proof header. Stage 4
compiles exact diagrams for all 64 packed-registry A/B matrices, an exact
cofactor-basis structure program and a jagged diagram: all 66 roots are covered.
The old BLAKE3 formula API explicitly refuses packed setup; a formula/compiler
error never selects another backend or skips a root.

All 39 baseline scalar corpus proofs verify with the packed implementation,
each with a 339,563-byte native Exec bundle. Three small-class executions also
reuse one packed setup; their 236,307-byte native bundles match all 66 root
programs and the exact first 4,096 setup/assigned constraints. The baseline
and small classes retain respectively Fast128/m23 and m22 with all 371 queries
and the original grinding policy. Dense words/live lanes increase to
53,288/53 and 15,764/31, respectively; smaller hash-table components are not a
whole-verifier cost estimate. These are native proof/replay checks, not a
complete R1CS satisfaction check or terminal proof.

The separate `packed_small_exec_whole_root_closed_admission_census` measures
the entire proof-free closed emitter under the unchanged `2^30` domain cap.
The [integrated report](census/exec-packed-blake3-root-closed-v0.json) records
its outcome separately from the native tests, with source/setup identities
and explicit resource-measurement limits. It returned `RejectedBudget` after
1,349.908 seconds of emission: 643,838,506 R1CS constraints and 1,073,741,859
PLONK rows, still in `MatrixFold`. With the four reserved rows, that prefix
exceeds the supported domain before the relation ends. This is not a full
census or a claim that removing 39 rows would make the whole relation fit.
Packed compression alone has not solved complete-verifier feasibility.
Further cost reduction, materialization, terminal key/SRS admission and an
isolated full-relation FFLONK proof remain required.

## Direct closure of every original deferred claim

`compile_exec_original_claims_closure` is a separate, proof-free composition
that owns exact programs for all 64 original matrix, three structure and three
jagged claims of packed small-class Exec. It shares low matrix products and
high cofactors, structure suffixes, and balanced jagged equality products only
when the constrained point wires are identical. It checks every original claim;
there is no private unchecked root or native acceptance callback.

The complete original Flock-verifier body, statement binding, 371-query schedule
and grinding policy are unchanged. Only auxiliary folds generated by the
Stage 4 adapter are replaced by the direct equations. Setup accepts no proof,
guest, execution values or table hints. Its composition identity is distinct
from the retained fold-based diagnostic, and its only public fields are Q's
two limbs.

Three real 236,307-byte native Exec bundles match the same 4,096-constraint
setup prefix. Separate complete setup/assigned component censuses agree
exactly: 552,381,742 PLONK rows for all matrices, 37,492,660 for structure and
78,835,570 for jagged. These independently allocated components are not a
whole-relation count or a proof.

The first whole proof-free run on the CPU box returned `RejectedBudget` after
1,462.311 seconds at 667,661,260 R1CS constraints / 1,073,741,821 PLONK rows,
still in matrix closure. Adding two public and two blinding rows exceeds the
`2^30` domain limit. Substantial work remains beyond this prefix: removing one
row would not establish feasibility. Its 564,120 KiB test-process peak RSS is
only matrix-free census memory, not prover memory. The [report](census/exec-original-claims-closed-v0.json)
and [raw log](census/exec-original-claims-closed-v0.log) retain source identities,
bounds, negative tests and measurement scope. Further exact cost reduction,
whole-pipeline RAM/disk admission and an actual full closed proof remain required.

A subsequent test-only [coordinate-order exploration](census/exec-shared-matrix-order-v0.json)
checks all 64 native evaluations for sixteen fixed orders and one per-matrix
sifting candidate. The latter reduces high interpolation branches from 52,740
to 47,697; the low products/blocks are unchanged. It is not adopted or emitted
as a circuit, and the 9.56% branch saving is not a PLONK-row or whole-fit claim.

The separate [shared-matrix cofactor-span experiment](census/exec-shared-matrix-span-v0.json)
preserves every original matrix polynomial and passes all 64 native
differentials. It removes fewer than 2.2% of high product sites while adding
substantial XOR reconstruction. These are symbolic component counts, not
PLONK savings or whole-circuit admission. The candidate has no circuit gadget
or automatic selection and is not adopted by either closed composition.

## File-key storage without a duplicated C0

`preprocess_fflonk_to_file` stores eight fixed coefficient columns and three
sigma evaluation columns. Its C0 source now interleaves the authenticated
coefficients on demand, instead of writing another eight columns. This is a
storage change, not a different polynomial, commitment, preprocessing digest,
verification key or proof format. The file remains caller-owned scratch;
reopening its raw bytes cannot reconstruct a trusted key.

The payload is exactly `11*n*32` bytes, down from `19*n*32`. At `n=2^30`, this
is 352 GiB instead of 608 GiB, saving 256 GiB. Small real-file and proof
equivalence tests, chunk-boundary/range checks, and mutations in every stored
column pass. Every C0 read still authenticates its source chunks. The
[storage report](census/fflonk-derived-c0-storage-v1.json) records source hashes,
the exact capacity model, tests and development-setup scope.

The saving trades extra coefficient I/O for less storage; large-domain
throughput is not measured. The separate compressed SRS is still about
432 GiB at that domain, and the largest FFT array alone is 128 GiB. The
existing prover workspace already recycles released extents. Neither that
reuse nor a RAM disk establishes whole-pipeline RAM/disk admission. Historical
censuses retain the former file-key model under their pinned source revisions.

## Boundary that is not yet closed

`Stage4RelationPublicInputsV1` is the historical **root-conditional** relation.
Its matrix, structure, and jagged evaluations require external trusted-table
discharge. Its statement mapping is still the historical Stage 3 mapping.
The public-input-binding tests prove only their small binding circuits.
Neither is a complete generic IxBy execution proof.

The existing FFLONK body is exactly 992 bytes. The historical full terminal
statement also carries 600 scalar fields (19,200 bytes). A 992-byte body does
not establish the compact-proof goal: the generic execution adapter and all
terminal root checks must be constrained inside the final relation, followed
by an actual complete proof and isolated verification without root sidecars.
The old Stage 2 exporter entry point, CLI, fixture scheduler, and billion-row
census are deliberately not used as an IxBy backend or its cost estimate.
