# Packed-SHPLONK KZG for Aiur BN stages: soundness argument

Status: written argument for independent review (2026-11-13). Not adopted;
no release pin depends on it.

Code:
- native PCS: `crates/proof-compression/src/kzg/shplonk.rs` (opening),
  `src/kzg/packed_shplonk{.rs,/layout.rs,/config.rs}` (multi-stark `Pcs` and
  `ProofConfig`);
- source-wire projection: `src/aiur_backend/kzg_packed_advice.rs`;
- Aiur verifier: `MultiStark/MultiStark/BN/KzgPacked{Deserialize,Shape,Verifier}.lean`,
  `KzgPcsPacked.lean`;
- packed CompressBN stage: `MultiStark/MultiStark/BN/CompressBNPacked.lean`,
  `src/aiur_backend/compress_bn/packed.rs`.

## 1. Construction

A multi-stark proof commits three rounds of matrices (main traces, lookup
accumulators, quotient chunks) plus an optional fixed round in the key. Each
matrix is a set of columns over a power-of-two domain `H` of size `n`, stored
as monomial coefficients `f(X)` with `deg f < n`.

**Packs.** Each matrix shape in a commitment carries a prover-declared
next-row class bit. Per round, columns are grouped by equal height and equal
class (`layout::plan`): heights ascending, next-row matrices before
current-row-only ones, then matrix order, then column order; each class fills
`W = cap/n` columns per pack before starting the next pack, where `cap` is the
key's public trace cap (`max_log` in the key). The prover declares main
matrices from the circuits' next-row use, lookup accumulators as next-row and
quotient chunks as current-row-only. A pack of `W' ≤ W` columns
`f_0 … f_{W'-1}` commits

```text
P(X) = Σ_j X^j · f_j(X^{W'})        deg P < W'·n ≤ cap
C    = [P(τ)]₁                       (one MSM over the interleaved coefficients)
```

The plan is a deterministic function of the round's matrix shapes (with their
class bits) and `cap`.
The commitment carries the shapes and one point per pack; the verifier
recomputes the plan from the shapes and rejects a commitment whose pack count
differs (`PackedShplonkPcs::layout`; in Aiur, the pack list must be exhausted
exactly by the recomputed plan).

**Equal heights only.** No pack mixes heights, so no column is lifted
(`g(X) = f(X^{N/n})`) and no tiling/LogUp-restart argument is needed (§4 of
`aiur-narrow-recursion.md` describes the extra structure check lifting would
require).

**Openings.** Multi-stark requests every column at `ζ`, and the columns of a
circuit that reads next rows also at `ζω` (`omit_unused_next_row_openings`).
A pack is opened at the union `A` of its matrices' points, at every column.
Values a matrix did not request are *extra values*, carried in the proof.

For one pack and point set `A`:

```text
S    = { x : x^{W'} ∈ A }            Z_S(X) = Π_{a∈A} (X^{W'} − a)
P(X) mod (X^{W'} − a) = Σ_j f_j(a) X^j
r(X) = Σ_j X^j · R_j(X^{W'})          R_j interpolates f_j on A
r(z) = Σ_{a∈A} L_a(z^{W'}) · Σ_j f_j(a) · z^j
```

**Batch opening** (SHPLONK, Boneh–Drake–Fisch–Gabizon 2020 §4, with one
challenge `γ` across packs as in fflonk):

```text
γ;  [W₁] = [Σ_i γ^i (P_i − r_i)/Z_{S_i}];  z;
L(X) = Σ_i γ^i/Z_{S_i}(z) · (P_i(X) − r_i(z)) − W₁(X);   [W₂] = [L/(X − z)]
F    = Σ_i γ^i/Z_{S_i}(z) · (C_i − r_i(z)·[1]₁) − [W₁]
accept iff e(F + z·[W₂], [1]₂) · e(−[W₂], [τ]₂) = 1
```

This is the BDFG identity divided by `Z_T(z) = Π_i Z_{S_i}(z)`; the verifier
rejects if any `Z_{S_i}(z) = 0`. Only `[1]₂` and `[τ]₂` are used, so the
Aztec Ignition ceremony suffices. The Aiur verifier returns `(A, B) =
(F + z·[W₂], −[W₂])` as a deferred pairing pair; the CompressBN fold
accumulates it and the terminal discharges it against the policy's anchors.

## 2. Transcript order

The packed configuration's seed is the column configuration's seed (setup
anchors and public-setup identity, trace cap, quotient budget, and the BLAKE3
digest of the unbound source-wire key) followed by
`ix/multi-stark/packed-shplonk/v1\0`, so the two protocols never share
challenges. Multi-stark then absorbs, in order: circuit count and shapes,
activation flags, fixed commitment, main commitment, trace heights, claims;
samples `β`, `γ_lookup`; absorbs the lookup commitment and accumulators;
samples `α`; absorbs the quotient commitment; samples `ζ ≠ 0`.

Inside `Pcs::open`/`verify`:

1. domain tag `ix/kzg/packed-shplonk-pcs/open/v1\0`, round count;
2. per round: the commitment's native bytes (shapes and pack points), the
   matrix count, and every matrix's point list;
3. per round, per pack, per point of the pack's union: the full evaluation
   row (requested and extra values alike);
4. SHPLONK domain tag `ix/kzg/packed-shplonk/v1\0`; sample `γ`; absorb `[W₁]`;
   sample `z`; absorb `[W₂]`.

**Every claimed value is absorbed before `γ`.** This is load-bearing. The
checks after `γ` (the SHPLONK `[1]₁` coefficient `Σ γ^i/Z_{S_i}(z)·r_i(z)`) are
linear in the values; if values were bound only through a commitment `[E]`
opened at a public challenge, a prover could choose them after the challenges
and adjust several consistently. The test
`committed_evaluations_without_hashing_are_forgeable` performs that forgery;
the shipped mode hashes the values. The Aiur verifier replays this order
exactly (`KzgPcsPacked::reduce`), absorbing the packed commitments as their
native `IXPSHC02` bytes.

## 3. Soundness sketch

Assume the algebraic group model and q-SDH for BN254, and the random-oracle
model for the BLAKE3 transcript.

1. **Binding of packs to columns.** For any `P` the decomposition
   `P = Σ_j X^j f_j(X^{W'})`, `f_j(Y) = Σ_k p_{j+W'k} Y^k`, is unique for any
   degree. So a pack commitment binds the tuple `(f_j)` exactly as `W'`
   column commitments would.
2. **Openings.** For distinct `a ≠ b`, `X^{W'} − a` and `X^{W'} − b` are
   coprime, so `Z_S | P − r` iff `P ≡ r mod (X^{W'} − a)` for every `a ∈ A`,
   iff `f_j(a) = (claimed value)` for every `j, a`. BDFG's batch argument
   reduces `Z_{S_i} | P_i − r_i` for all `i` to one pairing check, with
   soundness error about `(#packs + max deg)/|F|` from `γ` and `z`
   (Schwartz–Zippel). Using any common multiple `Z_T` of the `Z_{S_i}` (here
   their product, even when point sets coincide) preserves the equivalence.
3. **Point sets without roots.** Neither `Z_S(z)` nor `r(z)` enumerates the
   roots of `X^{W'} − a`; the statement in (2) is a divisibility in `F[X]` and
   holds whether or not `a` is a `W'`-th power in `F` or `W'` divides
   `|F^×|`. `W'` is therefore not limited by the two-adicity of `F`. The
   closed forms are tested against polynomial division and, where roots
   exist, against root interpolation (`closed_forms_match_*`).
4. **Distinct points.** `ζ ≠ ζω` because multi-stark rejects `ζ = 0` and
   `ω ≠ 1` for `n ≥ 2`; height-one matrices (`ω = 1`) are deduplicated with an
   equality check on repeated rows, natively and in Aiur.
5. **Degree bounds.** Neither per-column nor packed KZG enforces
   `deg f < n` on the prover; an algebraic adversary's commitments have
   degree below the number of public G1 powers `D` (the Ignition ceremony's
   100.8M, not the loaded prefix). Multi-stark's checks are polynomial
   identities at random `ζ` (constraints modulo `Z_H`, quotient
   recombination, LogUp), so larger degrees only raise the Schwartz–Zippel
   terms to about `D·deg(C)/|F|`, still negligible. The column values on `H`
   that the identities constrain are determined by `f_j` whatever its degree.
   Packing tightens the effective per-column bound from `D` to
   `⌈D/W'⌉`; it never loosens it.
6. **Declared classes.** The class bit only decides which columns share a
   pack. It is part of the absorbed commitment, so the plan is fixed before
   any opening challenge, and a pack is still opened at the union of its
   members' requested points. A wrong declaration therefore costs extra
   values (or yields a pack the verifier plans differently, which fails),
   never soundness; no consistency check between bit and points is needed.
7. **Cross-circuit equal-height packs.** Columns of different circuits (and
   of the same circuit's matrices) share a pack only at equal height. Each
   circuit's constraints are evaluated from its own requested values; a pack
   adds no relation between its members beyond the shared opening. Because
   every member is opened at the union of points, each column is bound at
   every point anyone requested; extra values are hashed like requested
   ones, so they cannot be chosen after `γ`.
8. **Fiat–Shamir.** Every prover message and every claimed value is
   absorbed before the challenge that depends on it (§2), the plan is a
   function of absorbed shapes and the seeded cap, and point lists are
   absorbed explicitly, so the interactive argument's soundness carries over.
9. **Key binding.** The transcript seed contains the digest of the unbound
   source-wire key, and the CompressBN policy pins the BLAKE3 digest of the
   full (bound) key bytes that the Aiur verifier hashes and parses. Circuit
   constraint graphs are not absorbed individually; they are fixed by the
   pinned key digest.

## 4. Recursion

Two programs share CompressBN's public call (policy digest, positive stage,
statement, accumulator) and fold. The packed policy (`IXAUKP01`) pins the
anchors and three keys with their entries: the per-column CompressGL key,
the packed key of `CompressBNPacked::first_v1` and the packed key of
`CompressBNPacked::compress_v1`.

- `first_v1` accepts only stage one: the predecessor key must hash to the
  policy's GL key, is parsed as a per-column key, and the per-column KZG
  verifier checks the CompressGL proof;
- `compress_v1` accepts only stages `s > 1`: at `s = 2` the predecessor key
  must hash to the policy's first key and the claim must name the first
  entry; at `s > 2` both must be the policy's BN key and entry, which is this
  program's own packed key. The packed verifier checks the stage `s − 1`
  proof, whose claim must carry the same policy, stage `s − 1` and statement;
- in both, the key's anchors must equal the policy's anchors, the previous
  accumulator comes from the verified claim (the identity at stage one), and
  the stage folds `acc_s = current + w·acc_{s−1}`. `compress_v1`,
  `chain_v1` and the terminal `CompressFinalPacked::verify_accumulator_v1`
  squeeze `w` from the packed verifier's final transcript (§4a). `first_v1`,
  whose predecessor is a per-column proof, keeps the per-column fold:
  `w = BLAKE3-XOF(ix/aiur/kzg/fold/v1\0 ‖ policy ‖ statement ‖ stage ‖ key
  digest ‖ BLAKE3(proof bytes) ‖ four points)`.

Each program contains only the verifier it runs. One key serves every stage
after the second. The terminal must pin the policy digest and the
`compress_v1` key.

**Circuit copies (sharding).** A packed key (`IXAUSK02`) lists each distinct
circuit once with a copy count; the native system and the Aiur verifier both
expand it into that many consecutive identical circuits, so the transcript
and the shape walk see the expanded list. Only function circuits may have
several copies. Their constraints and lookups are row-local, so the prover
splits the executed rows across the copies (largest power of two first, each
copy zero-padded; unused copies inactive). Any accepting sharded witness
concatenates into an accepting witness of the single circuit: zero rows are
valid padding rows, the multiset of lookup messages is unchanged, and rows
duplicated across copies unbalance LogUp as within one circuit
(`tests/aiur_kzg_sharding.rs`). The copy counts are part of the key bytes the
policy pins.

## 4a. Transcript-derived fold weight

Code: `CompressBNPacked::fold_weight`/`fold`
(`MultiStark/MultiStark/BN/CompressBNPacked.lean`), used by `step`,
`chain_step` and `CompressFinalPacked::verify_accumulator_v1`; the packed
verifiers return their final transcript (`KzgPcsPacked::reduce`,
`KzgPackedVerifier::verify`, `KzgPackedTerminal::verify_key`). Native
reference: `kzg_advice::transcript_fold_challenge`, `compress_bn::fold_packed`
and `packed_shplonk::capture_verification`.

**Definition.** A stage `s` verifies the predecessor proof `π` under key `K`
(BLAKE3 digest `d_K` of its complete source-wire bytes) and claims `c`. Let
`T` be the packed verifier's transcript after it absorbs `[W₂]`, the last
proof element; the opening's last challenge `z` was sampled just before. The
verifier yields the deferred pair `(A, B)` of `π`; `(A', B')` is the previous
accumulator carried by `c` (the identity at stage one). Then

```text
w      = sample(T ‖ "ix/aiur/kzg/fold-transcript/v1\0" ‖ policy ‖ statement
                  ‖ u32le(s) ‖ d_K ‖ enc(A') ‖ enc(B') ‖ enc(A) ‖ enc(B))
acc_s  = (A + w·A', B + w·B'),     rejected if w = 0
```

`sample` is the native BLAKE3 challenger: BLAKE3 of the 32-byte chain state
`S_z` (produced by sampling `z`) followed by the buffered bytes `[W₂] ‖ …`,
the first 64 XOF bytes reduced little-endian modulo `r`. `enc` is the
canonical 32-byte compressed point, the digests are their 32 bytes. The new
state it produces is discarded. The predecessor proof bytes are no longer
hashed separately.

**What the fold needs.** Let `X = e(A,[1]₂)·e(B,[τ]₂)` and
`Y = e(A',[1]₂)·e(B',[τ]₂)` in the order-`r` group `G_T`. The folded pair
passes iff `X·Y^w = 1`. If `Y ≠ 1` exactly one `w ∈ F_r` passes; if `Y = 1`
and `X ≠ 1` none does. A false pair therefore survives only if `w` hits a
value fixed by the four points. The four points are in the sampled input, so
in the random-oracle model each query succeeds with probability at most
`1/r` and a prover making `q` oracle queries succeeds with probability at most
`q/r` (about `q·2^−254`), whatever else the input contains. This is the same
argument as for the digest-based fold; neither the proof digest nor the
transcript is needed for it.

**What `T` has bound.** Checked against `KzgPackedVerifier::verify`,
`KzgPcsPacked::reduce` (the terminal's `verify_key` replays the same order),
native `System::verify_multiple_claims` (multi-stark `bcf3fc8`),
`PackedShplonkPcs::verify` and `shplonk::challenges`: the seed (setup
anchors, public-setup identity, trace cap, quotient budget, digest of the
unbound key, packed tag); circuit count and shapes; activation flags; fixed
commitment; main commitment; trace heights; the claims, length-prefixed;
`β`, `γ_lookup`; lookup commitment and accumulators; `α`; quotient
commitment; `ζ`; the PCS open tag, round count, each round's commitment
bytes, matrix count and point lists; every pack's evaluation row (requested
and extra values); the SHPLONK tag; `γ`; `[W₁]`; `z`; `[W₂]`. Multi-stark
samples nothing after the PCS opening, so natively the transcript the PCS
leaves is the verifier's final one; `capture_verification` returns exactly
that state.

Every component of the parsed proof (`KzgPackedDeserialize::proof`) is in
`T`:

- activation flags, trace heights and lookup accumulators as fields;
- the three commitments as their exact `IXPSHC02` bytes, from which shapes,
  class bits and pack points are parsed;
- opened values: `KzgPackedShape::frames` consumes every opening matrix
  exactly, fixes each matrix's row count and width from the key, and requires
  `log ≤ max_log`, so `KzgPcsPacked::walk` visits every matrix and each value
  enters an absorbed pack row. The one value not absorbed verbatim, the
  repeated row of a height-one next-row matrix, is asserted equal to the
  absorbed row;
- extra values, absorbed in pack rows and required to be exhausted;
- `[W₁]` and `[W₂]` as their raw 32-byte encodings.

The proof and claims grammars are canonical (magic, counts and tags are
checked, scalars and points must be canonical, `KzgIO::finish` rejects
trailing bytes), so a byte string is determined by its parse, and the parse
is determined by `T` together with key-determined structure. No component or
encoding needed an explicit extra binding. The key is the exception: the
seed binds the digest of the unbound key, the fixed commitment and the shapes,
but not the circuit graphs, so `d_K`, the digest the policy authorizes, is
absorbed explicitly. Policy, statement and stage are absorbed explicitly for
the same reason (the stage-one claim carries no policy).

**Why dropping the proof digest loses nothing.** (1) The fold's soundness
uses only the four points, which stay in the input. (2) The verifier's
acceptance and its pair `(A, B)` are functions of `K`, `c` and what `T`
absorbed; by the canonical grammar distinct accepted proofs give distinct
`T`, so the weight remains a function of the exact proof, now through the
transcript's hash chain instead of a second hash of the same bytes. A
collision of two transcripts is a BLAKE3 collision. (3) The previous
accumulator is bound twice: through the claims, absorbed before `β`, so every
challenge of the predecessor proof depends on it, and explicitly in the fold
input.

**Domain separation.** Each sample hashes `state ‖ buffer`. The fold is the
only sample taken from `S_z`, the state after the opening's final challenge,
and its buffer continues past `[W₂]` with the 31-byte fold tag; no other
challenge of this verifier is sampled from `S_z`, and the multi-stark and
SHPLONK protocols never absorb anything after `[W₂]`. Different public calls
over the same proof (another stage, policy, statement or key) give different
inputs and therefore independent weights. The tag also differs from the
per-column fold's `ix/aiur/kzg/fold/v1`, whose input is a plain message rather
than a chained state.

**Tests** (`tests/aiur_kzg_packed_shplonk_source.rs`, entry
`KzgPackedTest::fold` in `kzg-packed-shplonk.ixa`):
`fold_weight_is_squeezed_from_the_final_verifier_transcript` checks the Aiur
weight and folded pair against the native reference, that changing policy,
statement, stage, key digest or the previous pair changes the weight, and
that a false previous pair is not cancelled;
`altering_any_proof_component_rejects_or_changes_the_fold_weight` alters
each commitment, a lookup accumulator, a main, lookup and quotient evaluation,
an extra value, `[W₁]`, `[W₂]` and the claims: each is rejected by the Aiur
verifier or, for the components that only enter the deferred pair (extra
values and opening witnesses), executes with a different weight.

## 5. What was tested

Native PCS (`cargo test -p ix-proof-compression --lib kzg::`, CPU 69/69 and
CUDA 80/80 with 18 ignored):
- closed forms against polynomial division and root interpolation;
- forgeries rejected: altered evaluations, extra values, commitments and
  witnesses; moved or dropped points; swapped or dropped packs; committed `E`
  without hashing is forgeable;
- next-row classes: separate packs, zero extra values, flipped class
  rejected, any declaration complete
  (`next_row_classes_separate_packs_and_remove_extra_values`);
- streaming and portable provers produce identical proofs; CPU and CUDA
  produce the same proof hash.

Aiur packed verifier (`tests/aiur_kzg_packed_shplonk_source.rs`, 8/8 against
the regenerated `kzg-packed-shplonk.ixa`): honest proofs with and without
extra values and with declared classes give the native deferred pair
(`B = −[W₂]`, pairing holds); altered extra values, evaluations, commitments
and witnesses, appended or dropped extras and dropped packs are rejected.

Packed CompressBN input (`tests/aiur_compress_bn.rs`): stage one reads
per-column key/proof formats, later stages only packed formats.

End to end on actual Init under the Ignition prefix, five consecutive stages
(`docs/measurements/aiur-packed-bn-stages.json`): every proof verifies
natively, a changed output is rejected, each deferred accumulator satisfies
the pairing equation under the Ignition anchors, and stage one's accumulator
equals the per-column baseline. Stages 2–5 run the Aiur packed verifier on
the previous stage's proof inside the proven execution.

Circuit copies: a key listing a circuit once with copy count two verifies
the sharded proof in Aiur with the native pair, and a key whose copies cover
the wrong circuits is rejected (`honest_packed_proof_with_circuit_copies_is_accepted`).
Packed policy: stage two accepts only the first program's key and entry,
later stages only the steady-state key and entry
(`packed_policy_authorizes_first_program_at_stage_two_only`).

Not tested: an adversarial prover against the full CompressBNPacked program
(only native-level and verifier-level forgeries), mixed heights, and a second
workload.

## 6. Open points for review

- The plan is height-then-source ordered. Planning by next-row use changes
  only which columns share a pack, not the argument.
- Inactive circuits contribute no matrices; the Aiur verifier inherits the
  column verifier's requirement that every fixed-table circuit is active.
- Mixed-height (lifted) packs are not implemented and would need the
  structure check of `aiur-narrow-recursion.md` §4.
