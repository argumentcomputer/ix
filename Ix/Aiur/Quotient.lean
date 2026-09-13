/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Domain

/-! The native composition fold and quotient coefficient recombination.
Each quotient slice combines two challenge-field values with the native
extension basis. An odd number of coordinates or a selector pole is rejected.
-/

namespace Aiur.NativeAIR.Quotient

open ProofCodec (Extension)

def horner [OfNat W 0] [Add W] [Mul W] (point : W) (coefficients : List W) : W :=
  coefficients.foldr (fun coefficient rest => coefficient + point * rest) 0

def composition [OfNat W 0] [Add W] [Mul W] (alpha : W) (constraints : List W) : W :=
  constraints.foldl (fun accumulated value => accumulated * alpha + value) 0

def coefficients : List Extension → Option (List Extension)
  | [] => some []
  | [_] => none
  | first :: second :: rest => return (first + second * Extension.basis) :: (← coefficients rest)

def evaluate (domain : Domain.Subgroup) (point : Extension) (row : List Extension) : Option Extension := do
  return horner (point.power (Domain.size domain)) (← coefficients row)

def check (domain : Domain.Subgroup) (point alpha : Extension)
    (constraints row : List Extension) : Option Bool := do
  let selected ← Domain.selectors domain point
  let quotient ← evaluate domain point row
  return composition alpha constraints * selected.invVanishing == quotient

end Aiur.NativeAIR.Quotient
