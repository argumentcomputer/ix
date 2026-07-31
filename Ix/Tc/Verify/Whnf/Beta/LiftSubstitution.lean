import Ix.Tc.Verify.Whnf.Beta.SingletonSubstitution

/-!
# Lift/substitution cancellation for multi-beta

Peeling one more lambda turns the previous simultaneous substitutions into
terms lifted across the new innermost binder.  Applying that binder must
remove precisely the added lift.  This file proves that pure syntactic law
with the same no-wrap discipline as the production walkers.
-/

namespace Ix.Tc
namespace KExpr

private theorem toNat_max_bv (a b : UInt64) :
    (max a b).toNat = max a.toNat b.toNat := by
  show (if a ≤ b then b else a).toNat = max a.toNat b.toNat
  rw [Nat.max_def]
  by_cases h : a ≤ b
  · rw [if_pos h, if_pos (UInt64.le_iff_toNat_le.mp h)]
  · have hn : ¬a.toNat ≤ b.toNat := fun h' =>
      h (UInt64.le_iff_toNat_le.mpr h')
    rw [if_neg h, if_neg hn]

/-- Saturating predecessor changes the represented natural by at most one. -/
private theorem toNat_le_sat1_add_one_bv (x : UInt64) :
    x.toNat ≤ x.sat1.toNat + 1 := by
  unfold UInt64.sat1
  split
  · next h => rw [eq_of_beq h]; exact Nat.le_succ _
  · next h =>
      have hx0 : x ≠ 0 := fun he => h (beq_iff_eq.mpr he)
      have hn0 : x.toNat ≠ 0 := fun h0 =>
        hx0 (UInt64.toNat_inj.mp (by simpa using h0))
      have hsub : (x - 1).toNat = x.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le x 1 (UInt64.le_iff_toNat_le.mpr (by
          rw [show (1 : UInt64).toNat = 1 from rfl]
          omega))]
        rfl
      rw [hsub]
      omega

/-- Substituting at `shift + cutoff` cancels the extra unit in a lift by
`shift + 1` above `cutoff`.  The deliberately strong bound is stable under
syntax descent and is implied by the simultaneous-substitution request bound
at every use in multi-beta. -/
private theorem substSpec_liftSpec_succ_aux
    {e arg : KExpr .anon} (he : Constructed e)
    {shift cutoff : UInt64}
    (hbig : shift.toNat + cutoff.toNat + e.lbr.toNat + e.size + 1 <
      UInt64.size) :
    substSpec (liftSpec e (shift + 1) cutoff) arg (shift + cutoff) =
      liftSpec e shift cutoff := by
  induction he generalizing shift cutoff with
  | @var idx name md hidx =>
      rw [mkVar_lbr, mkVar_shape, size] at hbig
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl,
        Nat.mod_eq_of_lt hidx] at hbig
      have hshiftLt : shift.toNat + 1 < UInt64.size := by omega
      have hsumLt : shift.toNat + cutoff.toNat < UInt64.size := by omega
      have hshift1 : (shift + 1).toNat = shift.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt hshiftLt
      have hshiftCutoff : (shift + cutoff).toNat =
          shift.toNat + cutoff.toNat := by
        rw [UInt64.toNat_add]
        exact Nat.mod_eq_of_lt hsumLt
      by_cases hidxCutoff : idx ≥ cutoff
      · have hidxShiftLt : idx.toNat + shift.toNat + 1 <
            UInt64.size := by omega
        have hidxShift0Lt : idx.toNat + shift.toNat < UInt64.size := by
          omega
        have hidxShift : (idx + (shift + 1)).toNat =
            idx.toNat + shift.toNat + 1 := by
          rw [UInt64.toNat_add, hshift1]
          exact Nat.mod_eq_of_lt hidxShiftLt
        have hidxShift0 : (idx + shift).toNat =
            idx.toNat + shift.toNat := by
          rw [UInt64.toNat_add]
          exact Nat.mod_eq_of_lt hidxShift0Lt
        have hgt : idx + (shift + 1) > shift + cutoff :=
          UInt64.lt_iff_toNat_lt.mpr (by
            rw [hidxShift, hshiftCutoff]
            have := UInt64.le_iff_toNat_le.mp hidxCutoff
            omega)
        have hone : (1 : UInt64) ≤ idx + (shift + 1) :=
          UInt64.le_iff_toNat_le.mpr (by
            rw [show (1 : UInt64).toNat = 1 from rfl, hidxShift]
            omega)
        have hsub : idx + (shift + 1) - 1 = idx + shift := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le _ _ hone,
            show (1 : UInt64).toNat = 1 from rfl, hidxShift, hidxShift0]
          omega
        have hne : ¬((idx + (shift + 1) == shift + cutoff) = true) := by
          intro heq
          have heq' := congrArg UInt64.toNat (eq_of_beq heq)
          rw [hidxShift, hshiftCutoff] at heq'
          have hge' := UInt64.le_iff_toNat_le.mp hidxCutoff
          omega
        rw [mkVar_shape, liftSpec, if_pos hidxCutoff, mkVar_shape,
          substSpec, if_neg hne, if_pos hgt, hsub,
          liftSpec, if_pos hidxCutoff]
      · have hidxLtNat : idx.toNat < cutoff.toNat := by
          have hnle : ¬cutoff.toNat ≤ idx.toNat := fun h =>
            hidxCutoff (UInt64.le_iff_toNat_le.mpr h)
          omega
        have hidxLt : idx < cutoff :=
          UInt64.lt_iff_toNat_lt.mpr hidxLtNat
        have hlt : idx < shift + cutoff := by
          apply UInt64.lt_iff_toNat_lt.mpr
          rw [hshiftCutoff]
          omega
        have hne : ¬((idx == shift + cutoff) = true) := by
          intro heq
          have heq' := congrArg UInt64.toNat (eq_of_beq heq)
          have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
          omega
        have hngt : ¬idx > shift + cutoff := fun hgt => by
          have hgt' := UInt64.lt_iff_toNat_lt.mp hgt
          have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
          omega
        rw [mkVar_shape, liftSpec, if_neg hidxCutoff, substSpec,
          if_neg hne, if_neg hngt, liftSpec, if_neg hidxCutoff]
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | @app f a md hf ha ihf iha =>
      rw [mkApp_lbr, mkApp_shape, size] at hbig
      have hmax := toNat_max_bv f.lbr a.lbr
      rw [mkApp_shape, liftSpec, mkApp_shape, substSpec,
        ihf (shift := shift) (cutoff := cutoff) (by
          rw [hmax] at hbig
          omega),
        iha (shift := shift) (cutoff := cutoff) (by
          rw [hmax] at hbig
          omega),
        liftSpec]
  | @lam name bi ty body md hty hbody ihty ihbody =>
      rw [mkLam_lbr, mkLam_shape, size] at hbig
      have hmax := toNat_max_bv ty.lbr body.lbr.sat1
      rw [hmax] at hbig
      have hsat := toNat_le_sat1_add_one_bv body.lbr
      have hszty := size_pos ty
      have hszbody := size_pos body
      have hcut1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt
          (Nat.lt_of_le_of_lt (by omega) hbig)
      have hsum1 : (shift + cutoff + 1) = shift + (cutoff + 1) := by
        exact UInt64.add_assoc shift cutoff 1
      rw [mkLam_shape, liftSpec, mkLam_shape, substSpec,
        ihty (shift := shift) (cutoff := cutoff) (by
          exact Nat.lt_of_le_of_lt (by omega) hbig),
        hsum1,
        ihbody (shift := shift) (cutoff := cutoff + 1) (by
          rw [hcut1]
          exact Nat.lt_of_le_of_lt (by omega) hbig),
        liftSpec]
  | @all name bi ty body md hty hbody ihty ihbody =>
      rw [mkAll_lbr, mkAll_shape, size] at hbig
      have hmax := toNat_max_bv ty.lbr body.lbr.sat1
      rw [hmax] at hbig
      have hsat := toNat_le_sat1_add_one_bv body.lbr
      have hszty := size_pos ty
      have hszbody := size_pos body
      have hcut1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt
          (Nat.lt_of_le_of_lt (by omega) hbig)
      have hsum1 : (shift + cutoff + 1) = shift + (cutoff + 1) := by
        exact UInt64.add_assoc shift cutoff 1
      rw [mkAll_shape, liftSpec, mkAll_shape, substSpec,
        ihty (shift := shift) (cutoff := cutoff) (by
          exact Nat.lt_of_le_of_lt (by omega) hbig),
        hsum1,
        ihbody (shift := shift) (cutoff := cutoff + 1) (by
          rw [hcut1]
          exact Nat.lt_of_le_of_lt (by omega) hbig),
        liftSpec]
  | @letE name ty val body nondep md hty hval hbody ihty ihval ihbody =>
      rw [mkLet_lbr, mkLet_shape, size] at hbig
      have hmax1 := toNat_max_bv ty.lbr val.lbr
      have hmax2 := toNat_max_bv (max ty.lbr val.lbr) body.lbr.sat1
      rw [hmax2, hmax1] at hbig
      have hsat := toNat_le_sat1_add_one_bv body.lbr
      have hszty := size_pos ty
      have hszval := size_pos val
      have hszbody := size_pos body
      have hcut1 : (cutoff + 1).toNat = cutoff.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt
          (Nat.lt_of_le_of_lt (by omega) hbig)
      have hsum1 : (shift + cutoff + 1) = shift + (cutoff + 1) := by
        exact UInt64.add_assoc shift cutoff 1
      rw [mkLet_shape, liftSpec, mkLet_shape, substSpec,
        ihty (shift := shift) (cutoff := cutoff) (by
          exact Nat.lt_of_le_of_lt (by omega) hbig),
        ihval (shift := shift) (cutoff := cutoff) (by
          exact Nat.lt_of_le_of_lt (by omega) hbig),
        hsum1,
        ihbody (shift := shift) (cutoff := cutoff + 1) (by
          rw [hcut1]
          exact Nat.lt_of_le_of_lt (by omega) hbig),
        liftSpec]
  | @prj id field val md hval ihval =>
      rw [mkPrj_lbr, mkPrj_shape, size] at hbig
      rw [mkPrj_shape, liftSpec, mkPrj_shape, substSpec,
        ihval (shift := shift) (cutoff := cutoff) (by omega),
        liftSpec]
  | nat => rfl
  | str => rfl

/-- Depth-indexed public cancellation form used by the variable-hit case of
the simultaneous-substitution cons law. -/
theorem substSpec_liftSpec_succ
    {e arg : KExpr .anon} (he : Constructed e) {depth : UInt64}
    (hbig : e.lbr.toNat + e.size + depth.toNat + 1 < UInt64.size) :
    substSpec (liftSpec e (depth + 1) 0) arg depth =
      liftSpec e depth 0 := by
  have h := substSpec_liftSpec_succ_aux (arg := arg) he
    (shift := depth) (cutoff := 0) (by
      simp only [show (0 : UInt64).toNat = 0 from rfl]
      omega)
  simpa only [UInt64.add_zero] using h

end KExpr
end Ix.Tc
