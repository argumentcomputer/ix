module

import IxC.Kernel.Verify.InferLemmas
public import IxC.Kernel.Verify.Denote.Pinned

public section

/-!
# The pinned-shape identifications (lane-shared)

The reserved-recursor refutation both verified lanes use to identify
the checker's shape tests with the pinned basis families: only `PUnit`
passes `isUnitLikeTy`.  (Its sibling — only `PSigma'` passed the
pair-eta test — retired with the pinned pair and `pairEtaCert`, task
#175 W6.)
Relocated from `IxC/Kernel/TTVerify/{ProofIrrelStep,PairEtaStep}.lean`
(task #148 T4, the T1-style move), generalized from `EnvTT` to the one
field they consume (`BasisPinnedTT` — itself relocated here-adjacent,
`IxC/Kernel/Verify/Denote/Pinned.lean`), so `IxC/Kernel/SetR/*` can consume
them without importing the TT lane.
-/

namespace Ix.Kernel.Verify

open Ix.Kernel.Term

/-- Which reserved names carry recursor-shaped pinned declarations.
The `pinnedInfoT` counterpart of `IxC/Kernel/Verify/EnvPreds.lean`'s
`pinnedInfo_ctorInfo_cases`, and proved the same way. -/
theorem pinnedInfoT_recInfo_cases {n : Key} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule}
    (h : pinnedInfo n = .recInfo cv mI rP rules) :
    n = eqRecName ∨ n = natRecName ∨
    n = punitRecName ∨
    n = emptyRecName ∨ n = falseRecName ∨
    n = quotLiftName ∨ n = quotIndName := by
  unfold pinnedInfo at h
  by_cases h1 : n = eqName
  · rw [if_pos h1] at h; exact nomatch h
  rw [if_neg h1] at h
  by_cases h2 : n = eqReflName
  · rw [if_pos h2] at h; exact nomatch h
  rw [if_neg h2] at h
  by_cases h3 : n = eqRecName
  · exact Or.inl h3
  rw [if_neg h3] at h
  by_cases h4 : n = natName
  · rw [if_pos h4] at h; exact nomatch h
  rw [if_neg h4] at h
  by_cases h5 : n = natZeroName
  · rw [if_pos h5] at h; exact nomatch h
  rw [if_neg h5] at h
  by_cases h6 : n = natSuccName
  · rw [if_pos h6] at h; exact nomatch h
  rw [if_neg h6] at h
  by_cases h7 : n = natRecName
  · exact Or.inr (Or.inl h7)
  rw [if_neg h7] at h
  by_cases h11 : n = punitName
  · rw [if_pos h11] at h; exact nomatch h
  rw [if_neg h11] at h
  by_cases h12 : n = punitUnitName
  · rw [if_pos h12] at h; exact nomatch h
  rw [if_neg h12] at h
  by_cases h13 : n = punitRecName
  · exact Or.inr (Or.inr (Or.inl h13))
  rw [if_neg h13] at h
  by_cases h14 : n = emptyName
  · rw [if_pos h14] at h; exact nomatch h
  rw [if_neg h14] at h
  by_cases h15 : n = emptyRecName
  · exact Or.inr (Or.inr (Or.inr (Or.inl h15)))
  rw [if_neg h15] at h
  by_cases h15a : n = falseName
  · rw [if_pos h15a] at h; exact nomatch h
  rw [if_neg h15a] at h
  by_cases h15b : n = falseRecName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h15b))))
  rw [if_neg h15b] at h
  by_cases h16 : n = quotName
  · rw [if_pos h16] at h; exact nomatch h
  rw [if_neg h16] at h
  by_cases h17 : n = quotMkName
  · rw [if_pos h17] at h; exact nomatch h
  rw [if_neg h17] at h
  by_cases h18 : n = quotLiftName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h18)))))
  rw [if_neg h18] at h
  by_cases h19 : n = quotIndName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h19)))))
  rw [if_neg h19] at h
  by_cases h20 : n = quotSoundName
  · rw [if_pos h20] at h; exact nomatch h
  rw [if_neg h20] at h
  exact nomatch h

/-- **Only `PUnit` passes the unit-like test**: the test compares the head
with `punitName`, and the pin identifies the stored former. -/
theorem unitLike_eq_punit {env : Env} {cval : TConstVal}
    (hbp : BasisPinnedTT env cval) {e : Expr}
    (h : isUnitLikeTy env e = true) :
    ∃ us, e = .const punitName us ∧
      env.find? punitName = some punitA := by
  obtain ⟨us, cvi, capsi, -, -, -, -, rfl, hfc, -, -, -⟩ := isUnitLikeTy_inv h
  have hp : ConstantInfo.indInfo cvi capsi = pinnedInfo punitName :=
    (hbp _ _ hfc (by decide)).1
  rw [show pinnedInfo punitName = punitA from rfl] at hp
  exact ⟨us, rfl, hp ▸ hfc⟩

end Ix.Kernel.Verify
