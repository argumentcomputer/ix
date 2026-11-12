# Constrained BN254 pairings

The tower is `Fq2 = Fq[u]/(u²+1)`, `Fq6 = Fq2[v]/(v³-(9+u))`, and
`Fq12 = Fq6[w]/(w²-v)`. Components use the Fq library's canonical four
radix-2^80 limbs. Arithmetic, inverse checks and range checks run as Aiur
programs. There is no native pairing hint or unchecked tower inverse.

`FqProducts` reduces `ab ± cd + p² = q*p + r` in one constrained step.
The remainder is canonical, quotient limbs have 80-bit bounds, and seven
signed carries use a `32*2^80` bias with 86-bit ranges and fixed endpoints.
Range decompositions use five 16-bit chunks plus the remaining high bits,
checked against complete fixed tables.
The `128*radix² + 128*radix < Fr` lemma bounds the difference between each
integer coefficient equation's two sides, excluding scalar-field wraparound.
Adding p² makes subtraction nonnegative; the honest quotient is below 3p.
Each coefficient has at most sixteen products of 80-bit limbs plus one
remainder limb. If a previous signed carry has absolute value at most
`20*(radix-1)`, the next exact carry has the same bound: the numerator is at
most `16*(radix-1)^2 + 21*(radix-1)`, below `20*radix*(radix-1)`.
The zero initial carry starts this induction, so the 32-radix bias and 86-bit
range include every honest carry with margin.
Fq2 products and squares use two of these reductions, avoiding repeated
canonicalization of intermediate base-field products and sums. Their hints
supply only candidate limbs, quotients and carries. Register `pairing::register`
in addition to `fq::register` for those arithmetic channels.

`BN254Pairing::check(a,b)` checks a product of two pairings against fixed,
authenticated G2 operands. The operands in G1 are checked points, including
the unique `(0,0,1)` infinity representation. The prepared G2 lines are
immutable compiler tables, not witness input. `pairing::fixed_lines` validates
both G2 points and their subgroup membership before preparing the table. The
87-row table contains the exact signed ATE schedule and both line triples;
its full contents are bound by the compiler artifact and backend key.

This interface intentionally accepts fixed G2 anchors. A variable-G2 interface
would additionally need constrained curve/subgroup checks and line preparation.
The existing final KZG relation has fixed G2 and tau-G2 anchors, so its G1
operands can remain data without that additional interface.

`BN254Pairing::check_chunks` shares `BN254G1Encoding` with the recursive
accumulator. Its four fields are little-endian 16-byte chunks of the two
compressed G1 points. Byte membership and recomposition constrain each chunk
below 2^128 before strict point decoding, including canonical infinity and sign
flags. The product convention is `e(L,G2) * e(R,tauG2) = 1`; R is already signed.

The implementation follows the pinned `ark-bn254 0.5.0` tower constants and
`ark-ec 0.5.0` BN implementation. Miller evaluation uses sparse `mul_034`
multiplication. Final exponentiation uses the easy Frobenius/inverse part and
Fuentes-Castaneda hard chain: three exponentiations by the 63-bit BN parameter,
cyclotomic squaring and Frobenius maps 1, 2 and 3. Cyclotomic operations require
cyclotomic-subgroup operands; `final_exponentiation` establishes this by first
running its easy part. The library is tested against arkworks, but those tests
are not a source-level correctness proof of the new arithmetic or pairing code.

`Examples/BN254Pairing.lean` exports two fixtures: duplicate G2 generator anchors,
and the released Ignition G2/tau-G2 anchors. The Rust regression reconstructs
their expected lines from independent anchors and compares every compiler-table
entry. It checks tower multiplication/squaring/inversion, Frobenius maps,
cyclotomic operations, final exponentiation, the native Miller result, pairing
cancellation, malformed operands and infinity. The Ignition fixture checks
`e([tau]G,G2) * e(-G,[tau]G2) = 1` and rejects an altered valid point.

Regenerate a prepared-line directory with `aiur_pairing_lines NEW_DIRECTORY`
(add `--ignition` for released anchors), then supply its `lines.txt` and an output
artifact path to `lean --run Aiur/Examples/BN254Pairing.lean`. The directory's
provenance records the anchor and line digests; Ignition mode also records the
released verifier-parameter digest. The release pins are not changed.

`Pairing.Preparation` independently reconstructs the line table in Lean from
canonical anchor coordinates, checks their compressed encoding and subgroup
membership, and rejects any differing coefficient. The terminal exporter runs
this check before compiling its fixed table. `BN254Preparation` compares the
generator and Ignition fixtures and exercises changed anchors and lines.

`aiur_pairing_profile ARTIFACT NEW_OUTPUT --ignition` executes the released-anchor
relation and exports exact padded circuit sizes. Add `--chunks` for the shared
four-field compressed encoding. `--prove-kzg` additionally
proves it using the admitted `IX_KZG_SRS`, verifies the proof through the portable
key/proof codec, and rejects a changed operand. `--compile-plonk` (with the plonk
feature) exports the fixed-capacity generic PLONK schema and checks its actual
compiled domain. Capacity failures are errors, not permission to exceed the
retained Ignition prefix.

The baseline released-anchor profile has 20,835,671 padded main-trace cells,
including 1,048,576 rows in `range80`. Applying 64-bit receiver-count checks to
that layout exceeds a `2^25` PLONK domain before the arithmetic constraints are
included. Capacity must be measured on the fully compiled final program.

`--estimate-plonk` compiles small per-circuit capacity changes with authenticated
fixed tables unchanged, then extrapolates the full row cost. Boundary-selector
circuits also receive a second increment check. Its report is explicitly an
estimate and is not a full-capacity compile or proof; it avoids materializing a
circuit already predicted to exceed the available domain.
