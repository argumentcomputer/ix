import Ix.Tc.Verify.Whnf.Beta.PeelTrace

/-!
# Singleton simultaneous substitution

Production uses the simultaneous-substitution walker even when exactly one
lambda is consumed.  The existing semantic bridge accepted equality with
single substitution as a premise.  This slice proves that equality uniformly
from the same no-wrap bound required by the walker.
-/

namespace Ix.Tc
namespace KExpr

/-- A one-element simultaneous substitution is exactly the ordinary single
substitution at the same depth. -/
theorem simulSubstSpec_singleton
    {body arg : KExpr .anon} {depth : UInt64}
    (hbody : Constructed body)
    (hbig : depth.toNat + body.size + 1 < UInt64.size) :
    simulSubstSpec body #[arg] depth = substSpec body arg depth := by
  induction hbody generalizing depth with
  | @var idx name info hidx =>
      have hdepth : depth.toNat + 1 < UInt64.size := by
        rw [mkVar_shape, size] at hbig
        omega
      have hsucc : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt hdepth
      have hdepthLt : depth < depth + 1 :=
        UInt64.lt_iff_toNat_lt.mpr (by rw [hsucc]; omega)
      rw [mkVar_shape, simulSubstSpec, substSpec]
      have hsize : (#[arg].size.toUInt64 : UInt64) = 1 := rfl
      rw [hsize]
      change (if idx >= depth && idx < depth + 1 then
          liftSpec #[arg][(idx - depth).toNat]! depth 0
        else if idx >= depth + 1 then
          mkVar (idx - 1) (anonName (m := .anon))
        else .var idx name (mkVar idx name info).info) =
        if idx == depth then liftSpec arg depth 0
        else if idx > depth then mkVar (idx - 1) name
        else .var idx name (mkVar idx name info).info
      by_cases heq : (idx == depth) = true
      · have hidx : idx = depth := eq_of_beq heq
        subst idx
        have hwindow : ((depth >= depth && depth < depth + 1) = true) := by
          simp [hdepthLt]
        rw [if_pos hwindow, if_pos heq]
        simp
      · by_cases hgt : idx > depth
        · have hgeSucc : depth + 1 <= idx := by
            apply UInt64.le_iff_toNat_le.mpr
            rw [hsucc]
            have hgt' := UInt64.lt_iff_toNat_lt.mp hgt
            omega
          have hnltSucc : ¬(idx < depth + 1) := fun hlt => by
            have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
            have hge' := UInt64.le_iff_toNat_le.mp hgeSucc
            omega
          have hwindow :
              ¬((idx >= depth && idx < depth + 1) = true) := by
            simp [hnltSucc]
          rw [if_neg hwindow, if_pos hgeSucc, if_neg heq, if_pos hgt]
        · have hne : idx.toNat ≠ depth.toNat := fun h =>
            heq (beq_iff_eq.mpr (UInt64.toNat_inj.mp h))
          have hngt : ¬(depth.toNat < idx.toNat) := fun h =>
            hgt (UInt64.lt_iff_toNat_lt.mpr h)
          have hlt : idx.toNat < depth.toNat := by omega
          have hnge : ¬(idx >= depth) := fun h => by
            have h' := UInt64.le_iff_toNat_le.mp h
            omega
          have hgeSucc : ¬(idx >= depth + 1) := fun h => by
            have h' := UInt64.le_iff_toNat_le.mp h
            rw [hsucc] at h'
            omega
          have hwindow :
              ¬((idx >= depth && idx < depth + 1) = true) := by
            simp [hnge]
          rw [if_neg hwindow, if_neg hgeSucc, if_neg heq, if_neg hgt]
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | @app f arg info hf harg ihf iharg =>
      rw [mkApp_shape, size] at hbig
      rw [mkApp_shape, simulSubstSpec, substSpec,
        ihf (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig),
        iharg (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)]
  | @lam name bi ty body info hty hbody ihty ihbody =>
      rw [mkLam_shape, size] at hbig
      have hsucc : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      rw [mkLam_shape, simulSubstSpec, substSpec,
        ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig),
        ihbody (depth := depth + 1) (by rw [hsucc]; omega)]
  | @all name bi ty body info hty hbody ihty ihbody =>
      rw [mkAll_shape, size] at hbig
      have hsucc : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      rw [mkAll_shape, simulSubstSpec, substSpec,
        ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig),
        ihbody (depth := depth + 1) (by rw [hsucc]; omega)]
  | @letE name ty val body nondep info hty hval hbody ihty ihval ihbody =>
      rw [mkLet_shape, size] at hbig
      have hsucc : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      rw [mkLet_shape, simulSubstSpec, substSpec,
        ihty (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig),
        ihval (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig),
        ihbody (depth := depth + 1) (by rw [hsucc]; omega)]
  | @prj id field value info hvalue ihvalue =>
      rw [mkPrj_shape, size] at hbig
      rw [mkPrj_shape, simulSubstSpec, substSpec,
        ihvalue (depth := depth) (Nat.lt_of_le_of_lt (by omega) hbig)]
  | nat => rfl
  | str => rfl

end KExpr
end Ix.Tc
