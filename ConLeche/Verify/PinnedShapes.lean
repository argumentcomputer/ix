module

import ConLeche.Verify.InferLemmas
public import ConLeche.Verify.Denote.Pinned

public section

/-!
# The pinned-shape identifications (lane-shared)

The reserved-recursor refutation both verified lanes use to identify
the checker's shape tests with the pinned basis families: only `PUnit`
passes `isUnitLikeTy`.  (Its sibling — only `PSigma'` passed the
pair-eta test — retired with the pinned pair and `pairEtaCert`, task
#175 W6.)
Relocated from `ConLeche/TTVerify/{ProofIrrelStep,PairEtaStep}.lean`
(task #148 T4, the T1-style move), generalized from `EnvTT` to the one
field they consume (`BasisPinnedTT` — itself relocated here-adjacent,
`ConLeche/Verify/Denote/Pinned.lean`), so `ConLeche/SetR/*` can consume
them without importing the TT lane.
-/

namespace ConLeche.Verify

open ConLeche.Term

/-- Which reserved names carry recursor-shaped pinned declarations.
The `pinnedInfoT` counterpart of `ConLeche/Verify/EnvPreds.lean`'s
`pinnedInfo_ctorInfo_cases`, and proved the same way. -/
theorem pinnedInfoT_recInfo_cases {n : Name} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule}
    (h : pinnedInfo n = .recInfo cv mI rP rules) :
    n = eqName.str "rec" ∨ n = natName.str "rec" ∨
    n = punitName.str "rec" ∨
    n = emptyName.str "rec" ∨ n = falseName.str "rec" ∨
    n = quotLiftName ∨ n = quotIndName := by
  unfold pinnedInfo at h
  by_cases h1 : n = eqName
  · rw [if_pos h1] at h; exact nomatch h
  rw [if_neg h1] at h
  by_cases h2 : n = eqReflName
  · rw [if_pos h2] at h; exact nomatch h
  rw [if_neg h2] at h
  by_cases h3 : n = eqName.str "rec"
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
  by_cases h7 : n = natName.str "rec"
  · exact Or.inr (Or.inl h7)
  rw [if_neg h7] at h
  by_cases h11 : n = punitName
  · rw [if_pos h11] at h; exact nomatch h
  rw [if_neg h11] at h
  by_cases h12 : n = punitUnitName
  · rw [if_pos h12] at h; exact nomatch h
  rw [if_neg h12] at h
  by_cases h13 : n = punitName.str "rec"
  · exact Or.inr (Or.inr (Or.inl h13))
  rw [if_neg h13] at h
  by_cases h14 : n = emptyName
  · rw [if_pos h14] at h; exact nomatch h
  rw [if_neg h14] at h
  by_cases h15 : n = emptyName.str "rec"
  · exact Or.inr (Or.inr (Or.inr (Or.inl h15)))
  rw [if_neg h15] at h
  by_cases h15a : n = falseName
  · rw [if_pos h15a] at h; exact nomatch h
  rw [if_neg h15a] at h
  by_cases h15b : n = falseName.str "rec"
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

/-- **Only `PUnit` passes the unit-like test.**  Every other reserved
recursor's pinned shape fails one of its three conditions. -/
theorem unitLike_eq_punit {env : Env} {cval : TConstVal}
    (hbp : BasisPinnedTT env cval) {e : Expr}
    (h : isUnitLikeTy env e = true) :
    ∃ us, e = .const punitName us ∧
      env.find? punitName = some punitA := by
  obtain ⟨c, us, cvi, capsi, cvr, mI, rP, r, rfl, hfc, hfr, hmI, hnf,
    hres⟩ := isUnitLikeTy_inv h
  -- the recursor's stored declaration is the pinned one
  have hpin : pinnedInfo (c.str "rec") = .recInfo cvr mI rP [r] :=
    (hbp _ _ hfr hres).1.symm
  -- and every pin but `PUnit.rec`'s is refuted by the test's own
  -- three conditions, or by its name
  have hc : c = punitName := by
    rcases pinnedInfoT_recInfo_cases hpin with
      he | he | he | he | he | he | he
    · -- `Eq.rec` has an index: `mI = 5`, `rP = 4`
      rw [he] at hpin
      rw [show pinnedInfo (eqName.str "rec") = eqRecA from rfl] at hpin
      simp only [eqRecA, ConstantInfo.recInfo.injEq] at hpin
      omega
    · -- `Nat.rec` has two rules
      rw [he] at hpin
      rw [show pinnedInfo (natName.str "rec") = natRecA from rfl] at hpin
      simp [natRecA] at hpin
    · exact (Name.str.injEq .. ▸ he).1
    · -- `Empty.rec` has no rules
      rw [he] at hpin
      rw [show pinnedInfo (emptyName.str "rec") = emptyRecA from rfl]
        at hpin
      simp [emptyRecA] at hpin
    · -- `False.rec` has no rules (task #181)
      rw [he] at hpin
      rw [show pinnedInfo (falseName.str "rec") = falseRecA from rfl]
        at hpin
      simp [falseRecA] at hpin
    · exact absurd (Name.str.injEq .. ▸ he).2 (by decide)
    · exact absurd (Name.str.injEq .. ▸ he).2 (by decide)
  subst hc
  have hp : ConstantInfo.indInfo cvi capsi = pinnedInfo punitName :=
    (hbp _ _ hfc (by decide)).1
  rw [show pinnedInfo punitName = punitA from rfl] at hp
  exact ⟨us, rfl, hp ▸ hfc⟩

end ConLeche.Verify
