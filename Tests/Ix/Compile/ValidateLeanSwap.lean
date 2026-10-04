/-! BELOW-ORDER reproducer (A6f, 2026-10-04): user mutual pairs whose members
differ first in a mutual cross reference and only then in a strong position
(`Nat` against `Bool`, `True` against `False`). Pass 1 orders such a pair by the
strong difference (in the first refinement round both members are one class,
so the cross references compare equal); under the final classes the cross
references compare first, *weakly* and the other way round, in either stored
order. The kernels' single-pass canonicity gate (`validateCanonicalBlockSinglePass`
in `Ix.Tc`, `validate_canonical_block_single_pass` in `crates/kernel`) rejects a
weak `Greater` instead of falling back to the full refinement it runs on a weak
`Less`, so both kernels reject the block in meta mode (anonymous mode passes),
with the switch off and on, from both compilers. `ix validate-lean --local` on
this file: phase 4 fails (recorded as BELOW-ORDER). `PropCollapse`'s Lean
`IndPredBelow` block (`P.below`/`Q.below`, compiled under the switch) is the
same shape: its members differ first in the cross reference `Q.below`/`P.below`
and then in `motive_2`/`motive_1`. -/
namespace SwapPair
mutual
inductive SA : Type
  | mk : SB → Nat → SA
inductive SB : Type
  | mk : SA → Bool → SB
end
mutual
inductive PA : Prop
  | mk : PB → True → PA
inductive PB : Prop
  | mk : PA → False → PB
end
end SwapPair
