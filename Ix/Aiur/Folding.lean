/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Interpolation

/-! Global coefficient folding and restriction to a folding coset.
Coefficients use the ascending-power convention, with trailing zeros allowed.
-/

namespace Aiur.NativeAIR.Folding

open _root_.Aiur.NativeAIR.Quotient (horner)

def foldCoefficients [OfNat R 0] [Add R] [Mul R] (arity : Domain.Subgroup) (challenge : R)
    (coefficients : List R) : List R :=
  if _empty : coefficients = [] then []
  else horner challenge (coefficients.take (Domain.size arity)) ::
    foldCoefficients arity challenge (coefficients.drop (Domain.size arity))
termination_by coefficients.length
decreasing_by
  have positive := (show 0 < Domain.size arity from Nat.two_pow_pos arity.val)
  have nonempty := List.length_pos_iff.mpr _empty
  simp only [List.length_drop]
  omega

def rowCoefficients [OfNat R 0] [Add R] [Mul R] (arity : Domain.Subgroup) (point : R)
    (coefficients : List R) : List R :=
  if _empty : coefficients = [] then []
  else Polynomial.add (coefficients.take (Domain.size arity))
    (Polynomial.scale point (rowCoefficients arity point (coefficients.drop (Domain.size arity))))
termination_by coefficients.length
decreasing_by
  have positive := (show 0 < Domain.size arity from Nat.two_pow_pos arity.val)
  have nonempty := List.length_pos_iff.mpr _empty
  simp only [List.length_drop]
  omega

end Aiur.NativeAIR.Folding
