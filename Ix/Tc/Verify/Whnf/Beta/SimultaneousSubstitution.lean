import Ix.Tc.Verify.Whnf.Beta.LiftSubstitution

/-!
# Simultaneous-substitution decomposition

When one more lambda is peeled, production prepends its argument to the
reverse-order simultaneous-substitution array.  This slice proves that the
result is exactly the older simultaneous substitution one binder deeper,
followed by ordinary beta substitution for the newly peeled argument.
-/

namespace Ix.Tc
namespace KExpr

private theorem toNat_toUInt64_bw (k : Nat) :
    k.toUInt64.toNat = k % UInt64.size := by
  unfold Nat.toUInt64
  rfl

private theorem getElemBang_singleton_append_zero_bw
    (a : α) (xs : Array α) [Inhabited α] :
    (#[a] ++ xs)[0]! = a := by
  rw [getElem!_pos (#[a] ++ xs) 0 (by simp; omega)]
  exact Array.getElem_append_left (by simp)

private theorem getElemBang_singleton_append_succ_bw
    (a : α) (xs : Array α) [Inhabited α]
    (j : Nat) (hj : j < xs.size) :
    (#[a] ++ xs)[j + 1]! = xs[j]! := by
  rw [getElem!_pos (#[a] ++ xs) (j + 1) (by simp; omega),
    getElem!_pos xs j hj]
  simpa using
    (Array.getElem_append_right (xs := #[a]) (ys := xs) (i := j + 1)
      (by simp))

private theorem simulSubstSpec_mkApp_bw (f a : KExpr .anon) (md)
    (xs : Array (KExpr .anon)) (d : UInt64) :
    simulSubstSpec (mkApp f a md) xs d =
      mkApp (simulSubstSpec f xs d) (simulSubstSpec a xs d) := by
  rw [mkApp_shape, simulSubstSpec]

private theorem substSpec_mkApp_bw (f a arg : KExpr .anon) (md)
    (d : UInt64) :
    substSpec (mkApp f a md) arg d =
      mkApp (substSpec f arg d) (substSpec a arg d) := by
  rw [mkApp_shape, substSpec]

private theorem simulSubstSpec_mkLam_bw (name bi) (ty inner : KExpr .anon)
    (md) (xs : Array (KExpr .anon)) (d : UInt64) :
    simulSubstSpec (mkLam name bi ty inner md) xs d =
      mkLam name bi (simulSubstSpec ty xs d)
        (simulSubstSpec inner xs (d + 1)) := by
  rw [mkLam_shape, simulSubstSpec]

private theorem substSpec_mkLam_bw (name bi) (ty inner arg : KExpr .anon)
    (md) (d : UInt64) :
    substSpec (mkLam name bi ty inner md) arg d =
      mkLam name bi (substSpec ty arg d)
        (substSpec inner arg (d + 1)) := by
  rw [mkLam_shape, substSpec]

private theorem simulSubstSpec_mkAll_bw (name bi) (ty inner : KExpr .anon)
    (md) (xs : Array (KExpr .anon)) (d : UInt64) :
    simulSubstSpec (mkAll name bi ty inner md) xs d =
      mkAll name bi (simulSubstSpec ty xs d)
        (simulSubstSpec inner xs (d + 1)) := by
  rw [mkAll_shape, simulSubstSpec]

private theorem substSpec_mkAll_bw (name bi) (ty inner arg : KExpr .anon)
    (md) (d : UInt64) :
    substSpec (mkAll name bi ty inner md) arg d =
      mkAll name bi (substSpec ty arg d)
        (substSpec inner arg (d + 1)) := by
  rw [mkAll_shape, substSpec]

private theorem simulSubstSpec_mkLet_bw (name) (ty val inner : KExpr .anon)
    (nondep) (md) (xs : Array (KExpr .anon)) (d : UInt64) :
    simulSubstSpec (mkLet name ty val inner nondep md) xs d =
      mkLet name (simulSubstSpec ty xs d) (simulSubstSpec val xs d)
        (simulSubstSpec inner xs (d + 1)) nondep := by
  rw [mkLet_shape, simulSubstSpec]

private theorem substSpec_mkLet_bw (name) (ty val inner arg : KExpr .anon)
    (nondep) (md) (d : UInt64) :
    substSpec (mkLet name ty val inner nondep md) arg d =
      mkLet name (substSpec ty arg d) (substSpec val arg d)
        (substSpec inner arg (d + 1)) nondep := by
  rw [mkLet_shape, substSpec]

private theorem simulSubstSpec_mkPrj_bw (id field) (val : KExpr .anon)
    (md) (xs : Array (KExpr .anon)) (d : UInt64) :
    simulSubstSpec (mkPrj id field val md) xs d =
      mkPrj id field (simulSubstSpec val xs d) := by
  rw [mkPrj_shape, simulSubstSpec]

private theorem substSpec_mkPrj_bw (id field) (val arg : KExpr .anon)
    (md) (d : UInt64) :
    substSpec (mkPrj id field val md) arg d =
      mkPrj id field (substSpec val arg d) := by
  rw [mkPrj_shape, substSpec]

/-- Simultaneous substitution by an empty array is the identity at every
depth.  Unlike the loose-binder fast-path lemma, this needs no `lbr` premise. -/
theorem simulSubstSpec_empty {body : KExpr .anon}
    {substs : Array (KExpr .anon)} {depth : UInt64}
    (hbody : Constructed body) (hempty : substs.size = 0) :
    simulSubstSpec body substs depth = body := by
  induction hbody generalizing depth with
  | @var idx name info hidx =>
    have hsize : substs.size.toUInt64 = 0 := by rw [hempty]; rfl
    rw [mkVar_shape, simulSubstSpec, hsize, UInt64.add_zero]
    have hwindow : ¬((idx ≥ depth && idx < depth) = true) := fun h => by
      obtain ⟨hge, hlt⟩ := Bool.and_eq_true_iff.mp h
      have hge' := UInt64.le_iff_toNat_le.mp (of_decide_eq_true hge)
      have hlt' := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true hlt)
      omega
    rw [if_neg hwindow]
    by_cases hge : idx ≥ depth
    · rw [if_pos hge, UInt64.sub_zero]
      exact (mkVar_shape idx name info).symm ▸ rfl
    · rw [if_neg hge]
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | @app f arg info hf harg ihf iharg =>
    rw [mkApp_shape, simulSubstSpec, ihf (depth := depth),
      iharg (depth := depth)]
    exact mkApp_shape f arg info
  | @lam name bi ty body info hty hbody ihty ihbody =>
    rw [mkLam_shape, simulSubstSpec, ihty (depth := depth),
      ihbody (depth := depth + 1)]
    exact mkLam_shape name bi ty body info
  | @all name bi ty body info hty hbody ihty ihbody =>
    rw [mkAll_shape, simulSubstSpec, ihty (depth := depth),
      ihbody (depth := depth + 1)]
    exact mkAll_shape name bi ty body info
  | @letE name ty val body nd info hty hval hbody ihty ihval ihbody =>
    rw [mkLet_shape, simulSubstSpec, ihty (depth := depth),
      ihval (depth := depth), ihbody (depth := depth + 1)]
    exact mkLet_shape name ty val body nd info
  | @prj id field val info hval ihval =>
    rw [mkPrj_shape, simulSubstSpec, ihval (depth := depth)]
    exact mkPrj_shape id field val info
  | nat => rfl
  | str => rfl

/-- Prepending one substitution is equivalent to applying the older array one
binder deeper and then substituting the new head argument. -/
theorem simulSubstSpec_cons
    {body arg : KExpr .anon} {rest : Array (KExpr .anon)}
    {depth : UInt64}
    (hbounds : WalkerRequest.Bounds
      (.simulSubst body (#[arg] ++ rest) depth)) :
    simulSubstSpec body (#[arg] ++ rest) depth =
      substSpec (simulSubstSpec body rest (depth + 1)) arg depth := by
  obtain ⟨hbody, hconstructed, hsizes, hbig, helem⟩ := hbounds
  induction hbody generalizing depth with
  | @var idx name info hidx =>
      rw [mkVar_shape, size] at hbig
      have htotalSize : (#[arg] ++ rest).size = rest.size + 1 := by
        simp [Array.size_append, Nat.add_comm]
      have hrestSizeNat : rest.size.toUInt64.toNat = rest.size := by
        rw [toNat_toUInt64_bw]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      have htotalSizeNat : (#[arg] ++ rest).size.toUInt64.toNat =
          (#[arg] ++ rest).size := by
        rw [toNat_toUInt64_bw]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      have hdirectBoundary :
          (depth + (#[arg] ++ rest).size.toUInt64).toNat =
            depth.toNat + (#[arg] ++ rest).size := by
        rw [UInt64.toNat_add, htotalSizeNat]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      have hrestBoundary :
          (depth + 1 + rest.size.toUInt64).toNat =
            depth.toNat + 1 + rest.size := by
        rw [UInt64.toNat_add, hd1, hrestSizeNat]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by
          rw [htotalSize] at hbig
          omega) hbig)
      have hboundary : depth + (#[arg] ++ rest).size.toUInt64 =
          depth + 1 + rest.size.toUInt64 := by
        apply UInt64.toNat_inj.mp
        rw [hdirectBoundary, hrestBoundary, htotalSize]
        omega
      by_cases hlt : idx < depth
      · have hnge : ¬idx ≥ depth := fun h => by
          have := UInt64.le_iff_toNat_le.mp h
          have := UInt64.lt_iff_toNat_lt.mp hlt
          omega
        have hnge1 : ¬idx ≥ depth + 1 := fun h => by
          have h' := UInt64.le_iff_toNat_le.mp h
          have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
          rw [hd1] at h'
          omega
        have hngeBoundary :
            ¬idx ≥ depth + (#[arg] ++ rest).size.toUInt64 := fun h => by
          have h' := UInt64.le_iff_toNat_le.mp h
          have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
          rw [hdirectBoundary] at h'
          omega
        have hngeRestBoundary : ¬idx ≥ depth + 1 + rest.size.toUInt64 := by
          rw [← hboundary]
          exact hngeBoundary
        have hdirectWindow : ¬((idx ≥ depth &&
            idx < depth + (#[arg] ++ rest).size.toUInt64) = true) := by
          simp [hnge]
        have hrestWindow : ¬((idx ≥ depth + 1 &&
            idx < depth + 1 + rest.size.toUInt64) = true) := by
          simp [hnge1]
        have hne : ¬(idx == depth) = true := by
          intro heq
          have heq' := eq_of_beq heq
          subst idx
          have := UInt64.lt_irrefl depth hlt
          contradiction
        have hngt : ¬idx > depth := fun h => by
          have h' := UInt64.lt_iff_toNat_lt.mp h
          have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
          omega
        have hdirectEval : simulSubstSpec (mkVar idx name info)
            (#[arg] ++ rest) depth = mkVar idx name info := by
          rw [mkVar_shape, simulSubstSpec, if_neg hdirectWindow,
            if_neg hngeBoundary]
        have hrestEval : simulSubstSpec (mkVar idx name info) rest
            (depth + 1) = mkVar idx name info := by
          rw [mkVar_shape, simulSubstSpec, if_neg hrestWindow,
            if_neg hngeRestBoundary]
        have hsubstEval : substSpec (mkVar idx name info) arg depth =
            mkVar idx name info := by
          rw [mkVar_shape, substSpec, if_neg hne, if_neg hngt]
        calc
          simulSubstSpec (mkVar idx name info) (#[arg] ++ rest) depth =
              mkVar idx name info := hdirectEval
          _ = substSpec (mkVar idx name info) arg depth := hsubstEval.symm
          _ = substSpec
              (simulSubstSpec (mkVar idx name info) rest (depth + 1)) arg
                depth := congrArg (fun e => substSpec e arg depth)
                  hrestEval.symm
      · by_cases heq : idx = depth
        · subst idx
          have hdepthLtBoundary :
              depth < depth + (#[arg] ++ rest).size.toUInt64 := by
            apply UInt64.lt_iff_toNat_lt.mpr
            rw [hdirectBoundary, htotalSize]
            omega
          have hdepthLtRestBoundary :
              depth < depth + 1 + rest.size.toUInt64 := by
            rw [← hboundary]
            exact hdepthLtBoundary
          have hdepthLtNormalized :
              depth < depth + (1 + rest.size.toUInt64) := by
            rw [← UInt64.add_assoc]
            exact hdepthLtRestBoundary
          have hdirectWindow : ((depth ≥ depth &&
              depth < depth + (#[arg] ++ rest).size.toUInt64) = true) := by
            simp [hdepthLtNormalized]
          have hnge1 : ¬depth ≥ depth + 1 := fun h => by
            have h' := UInt64.le_iff_toNat_le.mp h
            rw [hd1] at h'
            omega
          have hrestWindow : ¬((depth ≥ depth + 1 &&
              depth < depth + 1 + rest.size.toUInt64) = true) := by
            simp [hnge1]
          have hngeRestBoundary : ¬depth ≥
              depth + 1 + rest.size.toUInt64 := fun h => by
            have h' := UInt64.le_iff_toNat_le.mp h
            rw [hrestBoundary] at h'
            omega
          have heqBool : (depth == depth) = true := beq_iff_eq.mpr rfl
          have hsubZero : (depth - depth).toNat = 0 := by simp
          have hdirectEval : simulSubstSpec (mkVar depth name info)
              (#[arg] ++ rest) depth = liftSpec arg depth 0 := by
            rw [mkVar_shape, simulSubstSpec, if_pos hdirectWindow, hsubZero,
              getElemBang_singleton_append_zero_bw]
          have hrestEval : simulSubstSpec (mkVar depth name info) rest
              (depth + 1) = mkVar depth name info := by
            rw [mkVar_shape, simulSubstSpec, if_neg hrestWindow,
              if_neg hngeRestBoundary]
          have hsubstEval : substSpec (mkVar depth name info) arg depth =
              liftSpec arg depth 0 := by
            rw [mkVar_shape, substSpec, if_pos heqBool]
          calc
            simulSubstSpec (mkVar depth name info) (#[arg] ++ rest) depth =
                liftSpec arg depth 0 := hdirectEval
            _ = substSpec (mkVar depth name info) arg depth := hsubstEval.symm
            _ = substSpec
                (simulSubstSpec (mkVar depth name info) rest (depth + 1)) arg
                  depth := congrArg (fun e => substSpec e arg depth)
                    hrestEval.symm
        · by_cases hwindow : idx <
              depth + (#[arg] ++ rest).size.toUInt64
          · have hgeNat : depth.toNat ≤ idx.toNat := by
              have hnlt := fun h : idx.toNat < depth.toNat =>
                hlt (UInt64.lt_iff_toNat_lt.mpr h)
              exact Nat.le_of_not_gt hnlt
            have hneNat : idx.toNat ≠ depth.toNat := fun h =>
              heq (UInt64.toNat_inj.mp h)
            have hgtNat : depth.toNat < idx.toNat := by omega
            have hge : idx ≥ depth := UInt64.le_iff_toNat_le.mpr hgeNat
            have hge1 : idx ≥ depth + 1 :=
              UInt64.le_iff_toNat_le.mpr (by rw [hd1]; omega)
            have hwindowRest : idx < depth + 1 + rest.size.toUInt64 := by
              rw [← hboundary]
              exact hwindow
            have hwindowNormalized :
                idx < depth + (1 + rest.size.toUInt64) := by
              rw [← UInt64.add_assoc]
              exact hwindowRest
            have hdirectGuard : ((idx ≥ depth &&
                idx < depth + (#[arg] ++ rest).size.toUInt64) = true) := by
              simp [hge, hwindowNormalized]
            have hrestGuard : ((idx ≥ depth + 1 &&
                idx < depth + 1 + rest.size.toUInt64) = true) := by
              simp [hge1, hwindowRest]
            have hsubDepth : (idx - depth).toNat =
                idx.toNat - depth.toNat :=
              UInt64.toNat_sub_of_le idx depth hge
            have hsubDepth1 : (idx - (depth + 1)).toNat =
                idx.toNat - (depth.toNat + 1) := by
              rw [UInt64.toNat_sub_of_le idx (depth + 1) hge1, hd1]
            have hindexSucc : (idx - depth).toNat =
                (idx - (depth + 1)).toNat + 1 := by
              rw [hsubDepth, hsubDepth1]
              omega
            have hwindowNat := UInt64.lt_iff_toNat_lt.mp hwindowRest
            rw [hrestBoundary] at hwindowNat
            have hindexRest : (idx - (depth + 1)).toNat < rest.size := by
              rw [hsubDepth1]
              omega
            have hindexTotal : (idx - depth).toNat <
                (#[arg] ++ rest).size := by
              rw [hindexSucc, htotalSize]
              omega
            have hselected :
                (#[arg] ++ rest)[(idx - depth).toNat]! =
                  rest[(idx - (depth + 1)).toNat]! := by
              rw [hindexSucc]
              exact getElemBang_singleton_append_succ_bw arg rest _
                hindexRest
            have hselectedCon :
                Constructed rest[(idx - (depth + 1)).toNat]! := by
              rw [← hselected]
              exact hconstructed _ hindexTotal
            have hcancelBig :
                rest[(idx - (depth + 1)).toNat]!.lbr.toNat +
                    rest[(idx - (depth + 1)).toNat]!.size + depth.toNat + 1 <
                  UInt64.size := by
              have h := helem _ hindexTotal
              rw [hselected, mkVar_shape, size] at h
              omega
            have hdirectEval : simulSubstSpec (mkVar idx name info)
                (#[arg] ++ rest) depth =
                  liftSpec rest[(idx - (depth + 1)).toNat]! depth 0 := by
              rw [mkVar_shape, simulSubstSpec, if_pos hdirectGuard,
                hselected]
            have hrestEval : simulSubstSpec (mkVar idx name info) rest
                (depth + 1) =
                  liftSpec rest[(idx - (depth + 1)).toNat]! (depth + 1) 0 := by
              rw [mkVar_shape, simulSubstSpec, if_pos hrestGuard]
            have hcancel := substSpec_liftSpec_succ (arg := arg)
              hselectedCon hcancelBig
            calc
              simulSubstSpec (mkVar idx name info) (#[arg] ++ rest) depth =
                  liftSpec rest[(idx - (depth + 1)).toNat]! depth 0 :=
                hdirectEval
              _ = substSpec
                  (liftSpec rest[(idx - (depth + 1)).toNat]! (depth + 1) 0)
                    arg depth := hcancel.symm
              _ = substSpec
                  (simulSubstSpec (mkVar idx name info) rest (depth + 1)) arg
                    depth := congrArg (fun e => substSpec e arg depth)
                      hrestEval.symm
          · have hnotRestBoundary :
                ¬idx < depth + 1 + rest.size.toUInt64 := by
              intro h
              apply hwindow
              rw [hboundary]
              exact h
            have hnotNormalized :
                ¬idx < depth + (1 + rest.size.toUInt64) := by
              rw [← UInt64.add_assoc]
              exact hnotRestBoundary
            have hgeBoundary :
                idx ≥ depth + (#[arg] ++ rest).size.toUInt64 := by
              apply UInt64.le_iff_toNat_le.mpr
              exact Nat.le_of_not_gt (fun h =>
                hwindow (UInt64.lt_iff_toNat_lt.mpr h))
            have hgeRestBoundary :
                idx ≥ depth + 1 + rest.size.toUInt64 := by
              rw [← hboundary]
              exact hgeBoundary
            have hgeRestNat := UInt64.le_iff_toNat_le.mp hgeRestBoundary
            rw [hrestBoundary] at hgeRestNat
            have hrestLeNat : rest.size ≤ idx.toNat := by omega
            have htotalLeNat : (#[arg] ++ rest).size ≤ idx.toNat := by
              rw [htotalSize]
              omega
            have hrestLe : rest.size.toUInt64 ≤ idx :=
              UInt64.le_iff_toNat_le.mpr (by rw [hrestSizeNat]; omega)
            have htotalLe : (#[arg] ++ rest).size.toUInt64 ≤ idx :=
              UInt64.le_iff_toNat_le.mpr (by rw [htotalSizeNat]; omega)
            have hsubRest : (idx - rest.size.toUInt64).toNat =
                idx.toNat - rest.size := by
              rw [UInt64.toNat_sub_of_le idx rest.size.toUInt64 hrestLe,
                hrestSizeNat]
            have hsubTotal :
                (idx - (#[arg] ++ rest).size.toUInt64).toNat =
                  idx.toNat - (#[arg] ++ rest).size := by
              rw [UInt64.toNat_sub_of_le idx
                (#[arg] ++ rest).size.toUInt64 htotalLe,
                htotalSizeNat]
            have hqgtNat : depth.toNat <
                (idx - rest.size.toUInt64).toNat := by
              rw [hsubRest]
              omega
            have hqgt : idx - rest.size.toUInt64 > depth :=
              UInt64.lt_iff_toNat_lt.mpr hqgtNat
            have hqne : ¬((idx - rest.size.toUInt64 == depth) = true) := by
              intro h
              have h' := congrArg UInt64.toNat (eq_of_beq h)
              omega
            have hqOne : (1 : UInt64) ≤ idx - rest.size.toUInt64 :=
              UInt64.le_iff_toNat_le.mpr (by
                rw [show (1 : UInt64).toNat = 1 from rfl]
                omega)
            have hsubOne : (idx - rest.size.toUInt64 - 1).toNat =
                (idx.toNat - rest.size) - 1 := by
              rw [UInt64.toNat_sub_of_le (idx - rest.size.toUInt64) 1 hqOne,
                show (1 : UInt64).toNat = 1 from rfl, hsubRest]
            have hindexEq : idx - (#[arg] ++ rest).size.toUInt64 =
                idx - rest.size.toUInt64 - 1 := by
              apply UInt64.toNat_inj.mp
              rw [hsubTotal, hsubOne, htotalSize]
              omega
            have hdirectGuard : ¬((idx ≥ depth &&
                idx < depth + (#[arg] ++ rest).size.toUInt64) = true) := by
              simp [hnotNormalized]
            have hrestGuard : ¬((idx ≥ depth + 1 &&
                idx < depth + 1 + rest.size.toUInt64) = true) := by
              simp [hnotRestBoundary]
            have hdirectEval : simulSubstSpec (mkVar idx name info)
                (#[arg] ++ rest) depth =
                  mkVar (idx - (#[arg] ++ rest).size.toUInt64)
                    (anonName (m := .anon)) := by
              rw [mkVar_shape, simulSubstSpec, if_neg hdirectGuard,
                if_pos hgeBoundary]
            have hrestEval : simulSubstSpec (mkVar idx name info) rest
                (depth + 1) =
                  mkVar (idx - rest.size.toUInt64)
                    (anonName (m := .anon)) := by
              rw [mkVar_shape, simulSubstSpec, if_neg hrestGuard,
                if_pos hgeRestBoundary]
            have hsubstEval :
                substSpec
                    (mkVar (idx - rest.size.toUInt64)
                      (anonName (m := .anon))) arg depth =
                  mkVar (idx - rest.size.toUInt64 - 1)
                    (anonName (m := .anon)) := by
              rw [mkVar_shape, substSpec, if_neg hqne, if_pos hqgt]
            calc
              simulSubstSpec (mkVar idx name info) (#[arg] ++ rest) depth =
                  mkVar (idx - (#[arg] ++ rest).size.toUInt64)
                    (anonName (m := .anon)) := hdirectEval
              _ = mkVar (idx - rest.size.toUInt64 - 1)
                    (anonName (m := .anon)) := by rw [hindexEq]
              _ = substSpec
                    (mkVar (idx - rest.size.toUInt64)
                      (anonName (m := .anon))) arg depth := hsubstEval.symm
              _ = substSpec
                  (simulSubstSpec (mkVar idx name info) rest (depth + 1)) arg
                    depth := congrArg (fun e => substSpec e arg depth)
                      hrestEval.symm
  | fvar => rfl
  | sort => rfl
  | const => rfl
  | @app f a info hf ha ihf iha =>
      rw [mkApp_shape, size] at hbig
      have hfElem : ∀ k, k < (#[arg] ++ rest).size →
          (#[arg] ++ rest)[k]!.lbr.toNat +
              (#[arg] ++ rest)[k]!.size + depth.toNat + f.size <
            UInt64.size := by
        intro k hk
        have h := helem k hk
        rw [mkApp_shape, size] at h
        omega
      have haElem : ∀ k, k < (#[arg] ++ rest).size →
          (#[arg] ++ rest)[k]!.lbr.toNat +
              (#[arg] ++ rest)[k]!.size + depth.toNat + a.size <
            UInt64.size := by
        intro k hk
        have h := helem k hk
        rw [mkApp_shape, size] at h
        omega
      calc
        simulSubstSpec (mkApp f a info) (#[arg] ++ rest) depth =
            mkApp (simulSubstSpec f (#[arg] ++ rest) depth)
              (simulSubstSpec a (#[arg] ++ rest) depth) :=
          simulSubstSpec_mkApp_bw f a info _ _
        _ = mkApp
              (substSpec (simulSubstSpec f rest (depth + 1)) arg depth)
              (substSpec (simulSubstSpec a rest (depth + 1)) arg depth) := by
          rw [ihf (depth := depth) (by omega) hfElem,
            iha (depth := depth) (by omega) haElem]
        _ = substSpec
              (mkApp (simulSubstSpec f rest (depth + 1))
                (simulSubstSpec a rest (depth + 1))) arg depth :=
          (substSpec_mkApp_bw _ _ arg _ depth).symm
        _ = substSpec
              (simulSubstSpec (mkApp f a info) rest (depth + 1)) arg depth :=
          congrArg (fun e => substSpec e arg depth)
            (simulSubstSpec_mkApp_bw f a info rest (depth + 1)).symm
  | @lam name bi ty inner info hty hinner ihty ihinner =>
      rw [mkLam_shape, size] at hbig
      have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      have htyElem : ∀ k, k < (#[arg] ++ rest).size →
          (#[arg] ++ rest)[k]!.lbr.toNat +
              (#[arg] ++ rest)[k]!.size + depth.toNat + ty.size <
            UInt64.size := by
        intro k hk
        have h := helem k hk
        rw [mkLam_shape, size] at h
        omega
      have hinnerElem : ∀ k, k < (#[arg] ++ rest).size →
          (#[arg] ++ rest)[k]!.lbr.toNat +
              (#[arg] ++ rest)[k]!.size + (depth + 1).toNat + inner.size <
            UInt64.size := by
        intro k hk
        have h := helem k hk
        rw [mkLam_shape, size] at h
        rw [hd1]
        omega
      calc
        simulSubstSpec (mkLam name bi ty inner info)
            (#[arg] ++ rest) depth =
          mkLam name bi
            (simulSubstSpec ty (#[arg] ++ rest) depth)
            (simulSubstSpec inner (#[arg] ++ rest) (depth + 1)) :=
          simulSubstSpec_mkLam_bw name bi ty inner info _ _
        _ = mkLam name bi
            (substSpec (simulSubstSpec ty rest (depth + 1)) arg depth)
            (substSpec (simulSubstSpec inner rest (depth + 1 + 1)) arg
              (depth + 1)) := by
          rw [ihty (depth := depth) (by omega) htyElem,
            ihinner (depth := depth + 1) (by rw [hd1]; omega) hinnerElem]
        _ = substSpec
            (mkLam name bi (simulSubstSpec ty rest (depth + 1))
              (simulSubstSpec inner rest (depth + 1 + 1))) arg depth :=
          (substSpec_mkLam_bw name bi _ _ arg _ depth).symm
        _ = substSpec
            (simulSubstSpec (mkLam name bi ty inner info) rest (depth + 1))
              arg depth :=
          congrArg (fun e => substSpec e arg depth)
            (simulSubstSpec_mkLam_bw name bi ty inner info rest
              (depth + 1)).symm
  | @all name bi ty inner info hty hinner ihty ihinner =>
      rw [mkAll_shape, size] at hbig
      have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      have htyElem : ∀ k, k < (#[arg] ++ rest).size →
          (#[arg] ++ rest)[k]!.lbr.toNat +
              (#[arg] ++ rest)[k]!.size + depth.toNat + ty.size <
            UInt64.size := by
        intro k hk
        have h := helem k hk
        rw [mkAll_shape, size] at h
        omega
      have hinnerElem : ∀ k, k < (#[arg] ++ rest).size →
          (#[arg] ++ rest)[k]!.lbr.toNat +
              (#[arg] ++ rest)[k]!.size + (depth + 1).toNat + inner.size <
            UInt64.size := by
        intro k hk
        have h := helem k hk
        rw [mkAll_shape, size] at h
        rw [hd1]
        omega
      calc
        simulSubstSpec (mkAll name bi ty inner info)
            (#[arg] ++ rest) depth =
          mkAll name bi
            (simulSubstSpec ty (#[arg] ++ rest) depth)
            (simulSubstSpec inner (#[arg] ++ rest) (depth + 1)) :=
          simulSubstSpec_mkAll_bw name bi ty inner info _ _
        _ = mkAll name bi
            (substSpec (simulSubstSpec ty rest (depth + 1)) arg depth)
            (substSpec (simulSubstSpec inner rest (depth + 1 + 1)) arg
              (depth + 1)) := by
          rw [ihty (depth := depth) (by omega) htyElem,
            ihinner (depth := depth + 1) (by rw [hd1]; omega) hinnerElem]
        _ = substSpec
            (mkAll name bi (simulSubstSpec ty rest (depth + 1))
              (simulSubstSpec inner rest (depth + 1 + 1))) arg depth :=
          (substSpec_mkAll_bw name bi _ _ arg _ depth).symm
        _ = substSpec
            (simulSubstSpec (mkAll name bi ty inner info) rest (depth + 1))
              arg depth :=
          congrArg (fun e => substSpec e arg depth)
            (simulSubstSpec_mkAll_bw name bi ty inner info rest
              (depth + 1)).symm
  | @letE name ty val inner nondep info hty hval hinner ihty ihval ihinner =>
      rw [mkLet_shape, size] at hbig
      have hd1 : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hbig)
      have htyElem : ∀ k, k < (#[arg] ++ rest).size →
          (#[arg] ++ rest)[k]!.lbr.toNat +
              (#[arg] ++ rest)[k]!.size + depth.toNat + ty.size <
            UInt64.size := by
        intro k hk
        have h := helem k hk
        rw [mkLet_shape, size] at h
        omega
      have hvalElem : ∀ k, k < (#[arg] ++ rest).size →
          (#[arg] ++ rest)[k]!.lbr.toNat +
              (#[arg] ++ rest)[k]!.size + depth.toNat + val.size <
            UInt64.size := by
        intro k hk
        have h := helem k hk
        rw [mkLet_shape, size] at h
        omega
      have hinnerElem : ∀ k, k < (#[arg] ++ rest).size →
          (#[arg] ++ rest)[k]!.lbr.toNat +
              (#[arg] ++ rest)[k]!.size + (depth + 1).toNat + inner.size <
            UInt64.size := by
        intro k hk
        have h := helem k hk
        rw [mkLet_shape, size] at h
        rw [hd1]
        omega
      calc
        simulSubstSpec (mkLet name ty val inner nondep info)
            (#[arg] ++ rest) depth =
          mkLet name
            (simulSubstSpec ty (#[arg] ++ rest) depth)
            (simulSubstSpec val (#[arg] ++ rest) depth)
            (simulSubstSpec inner (#[arg] ++ rest) (depth + 1)) nondep :=
          simulSubstSpec_mkLet_bw name ty val inner nondep info _ _
        _ = mkLet name
            (substSpec (simulSubstSpec ty rest (depth + 1)) arg depth)
            (substSpec (simulSubstSpec val rest (depth + 1)) arg depth)
            (substSpec (simulSubstSpec inner rest (depth + 1 + 1)) arg
              (depth + 1)) nondep := by
          rw [ihty (depth := depth) (by omega) htyElem,
            ihval (depth := depth) (by omega) hvalElem,
            ihinner (depth := depth + 1) (by rw [hd1]; omega) hinnerElem]
        _ = substSpec
            (mkLet name (simulSubstSpec ty rest (depth + 1))
              (simulSubstSpec val rest (depth + 1))
              (simulSubstSpec inner rest (depth + 1 + 1)) nondep) arg
              depth :=
          (substSpec_mkLet_bw name _ _ _ arg nondep _ depth).symm
        _ = substSpec
            (simulSubstSpec (mkLet name ty val inner nondep info) rest
              (depth + 1)) arg depth :=
          congrArg (fun e => substSpec e arg depth)
            (simulSubstSpec_mkLet_bw name ty val inner nondep info rest
              (depth + 1)).symm
  | @prj id field val info hval ihval =>
      rw [mkPrj_shape, size] at hbig
      have hvalElem : ∀ k, k < (#[arg] ++ rest).size →
          (#[arg] ++ rest)[k]!.lbr.toNat +
              (#[arg] ++ rest)[k]!.size + depth.toNat + val.size <
            UInt64.size := by
        intro k hk
        have h := helem k hk
        rw [mkPrj_shape, size] at h
        omega
      calc
        simulSubstSpec (mkPrj id field val info) (#[arg] ++ rest) depth =
            mkPrj id field (simulSubstSpec val (#[arg] ++ rest) depth) :=
          simulSubstSpec_mkPrj_bw id field val info _ _
        _ = mkPrj id field
            (substSpec (simulSubstSpec val rest (depth + 1)) arg depth) := by
          rw [ihval (depth := depth) (by omega) hvalElem]
        _ = substSpec (mkPrj id field
            (simulSubstSpec val rest (depth + 1))) arg depth :=
          (substSpec_mkPrj_bw id field _ arg _ depth).symm
        _ = substSpec
            (simulSubstSpec (mkPrj id field val info) rest (depth + 1)) arg
              depth :=
          congrArg (fun e => substSpec e arg depth)
            (simulSubstSpec_mkPrj_bw id field val info rest
              (depth + 1)).symm
  | nat => rfl
  | str => rfl

end KExpr
end Ix.Tc
