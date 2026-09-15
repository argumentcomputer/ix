import Ix.Kernel.Verify.Support
import Ix.Kernel.Verify.Whnf.Beta.LambdaPeeling

/-! Pure planning and arithmetic for cheap beta, shared by both
semantic developments without importing either model. -/

namespace Ix.Kernel

namespace RecM.BetaPeel

/-- Prefix one already-proved peel by the outermost lambda and its first
argument. -/
theorem prepend
    {inner body : KExpr .anon} {consumed : List (KExpr .anon)}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty arg : KExpr .anon} {info : ExprInfo .anon}
    (h : BetaPeel inner consumed body) :
    BetaPeel (.lam name bi ty inner info) (arg :: consumed) body := by
  induction h with
  | nil =>
      simpa using
        (BetaPeel.snoc (arg := arg)
          (BetaPeel.nil (.lam name bi ty inner info)))
  | snoc hprefix ih =>
      simpa [List.cons_append] using BetaPeel.snoc ih

/-- `peelLamsN` consumes exactly the corresponding list prefix. -/
theorem of_peelLamsN (head : KExpr .anon) (args : List (KExpr .anon)) :
    let (body, consumed) := peelLamsN args.length head
    BetaPeel head (args.take consumed) body ∧ consumed ≤ args.length := by
  induction args generalizing head with
  | nil =>
      simp only [List.length_nil, peelLamsN, List.take_zero]
      exact ⟨BetaPeel.nil head, Nat.le_refl 0⟩
  | cons arg args ih =>
      cases head with
      | lam name bi ty inner info =>
          simp only [List.length_cons]
          generalize hpeel : peelLamsN args.length inner = peeled
          rcases peeled with ⟨body, consumed⟩
          have hrun :
              peelLamsN (args.length + 1) (.lam name bi ty inner info) =
                (body, consumed + 1) := by
            rw [peelLamsN, hpeel]
          rw [hrun]
          have htail := ih inner
          rw [hpeel] at htail
          dsimp only at htail
          refine ⟨?_, by omega⟩
          simpa only [List.take_succ_cons] using
            (htail.1.prepend (name := name) (bi := bi) (ty := ty)
              (arg := arg) (info := info))
      | var | fvar | sort | const | app | all | letE | prj | nat | str =>
          simp only [List.length_cons, peelLamsN, List.take_zero]
          exact ⟨BetaPeel.nil _, Nat.zero_le _⟩

end RecM.BetaPeel

namespace WalkerRequest.Bounds

/-- Recover the simultaneous-substitution budget for the exact prefix
selected by a cheap-beta plan. -/
theorem cheapBeta_simul
    {source head body : KExpr .anon} {args : Array (KExpr .anon)}
    {consumed : Nat}
    (h : WalkerRequest.Bounds (.cheapBeta source))
    (hspine : source.collectSpine = (head, args))
    (hpeel : peelLamsN args.size head = (body, consumed)) :
    WalkerRequest.Bounds
      (.simulSubst body (args.extract 0 consumed).reverse 0) :=
  h.2 hspine hpeel

end WalkerRequest.Bounds

private theorem toNat_toUInt64_cheapBeta (n : Nat) :
    n.toUInt64.toNat = n % UInt64.size := by
  unfold Nat.toUInt64
  rfl

/-- Selection witnesses a syntactic lambda head. Reading a let by
substitution may expose a model lambda without selecting a kernel plan. -/
theorem cheapBetaPlan?_head_lambda {source : KExpr .anon} {plan : CheapBetaPlan .anon}
    (selected : cheapBetaPlan? source = some plan) :
    ∃ name bi domain body info,
      source.collectSpine.1 = .lam name bi domain body info := by
  cases source with
  | app fn arg info =>
      simp only [cheapBetaPlan?] at selected
      generalize spine : (KExpr.app fn arg info).collectSpine = collected at selected ⊢
      obtain ⟨head, arguments⟩ := collected
      cases head with
      | lam name bi domain body info => exact ⟨name, bi, domain, body, info, rfl⟩
      | _ => contradiction
  | _ => contradiction

/-- A successful cheap-beta plan is exactly the simultaneous substitution
of the consumed lambda prefix followed by the untouched application suffix.
This is the arithmetic seam behind the selected-variable fast path: the
production index `consumed - k - 1` is index `k` in the reversed prefix. -/
theorem cheapBetaPlan?_simul
    {source : KExpr .anon} {plan : CheapBetaPlan .anon}
    (hplan : cheapBetaPlan? source = some plan)
    (hbounds : WalkerRequest.Bounds (.cheapBeta source)) :
    ∃ (head body : KExpr .anon) (args : Array (KExpr .anon))
        (consumed : Nat),
      source.collectSpine = (head, args) ∧
      peelLamsN args.size head = (body, consumed) ∧
      consumed ≤ args.size ∧
      plan.base = KExpr.simulSubstSpec body
        (args.extract 0 consumed).reverse 0 ∧
      plan.trailing = (args.extract consumed args.size).toList := by
  cases source with
  | app f arg info =>
      simp only [cheapBetaPlan?] at hplan
      generalize hspine : (KExpr.app f arg info).collectSpine = spine at hplan
      rcases spine with ⟨head, args⟩
      cases head with
      | lam name bi ty inner lamInfo =>
          generalize hpeel :
            peelLamsN args.size (.lam name bi ty inner lamInfo) = peeled
            at hplan
          rcases peeled with ⟨body, consumed⟩
          have hcount :=
            RecM.BetaPeel.of_peelLamsN
              (.lam name bi ty inner lamInfo) args.toList
          rw [show args.toList.length = args.size by simp, hpeel] at hcount
          dsimp only at hcount
          have hsim := hbounds.2 hspine hpeel
          have hprefixSize : (args.extract 0 consumed).size = consumed := by
            simp only [Array.size_extract]
            omega
          by_cases hclosed : body.lbr == 0
          · simp only [hclosed, if_true, Option.some.injEq] at hplan
            subst plan
            have hlbr : body.lbr ≤ 0 := by
              rw [beq_iff_eq.mp hclosed]
              exact UInt64.le_iff_toNat_le.mpr (Nat.le_refl 0)
            have hsimEq := KExpr.simulSubstSpec_id hsim.1
              (by simpa only [UInt64.toNat_zero, Nat.zero_add, hprefixSize]
                using hsim.2.2.2.1)
              hlbr
            exact ⟨_, _, _, _, rfl, hpeel, hcount.2,
              hsimEq.symm, rfl⟩
          · cases body with
            | var k varName varInfo =>
                by_cases hk : k < consumed.toUInt64
                · simp only [hclosed, Bool.false_eq_true, if_false, hk,
                    if_true, Option.some.injEq] at hplan
                  subst plan
                  have hconsumedLt : consumed < UInt64.size := by
                    have hbodySize := KExpr.size_pos
                      (.var k varName varInfo : KExpr .anon)
                    have hbig := hsim.2.2.2.1
                    simp only [Array.size_reverse, hprefixSize] at hbig
                    omega
                  have hconsumedNat : consumed.toUInt64.toNat = consumed := by
                    rw [toNat_toUInt64_cheapBeta]
                    exact Nat.mod_eq_of_lt hconsumedLt
                  have hkNat : k.toNat < consumed := by
                    have := UInt64.lt_iff_toNat_lt.mp hk
                    rwa [hconsumedNat] at this
                  have hkPrefix :
                      k.toNat < (args.extract 0 consumed).reverse.size := by
                    simpa only [Array.size_reverse, hprefixSize] using hkNat
                  have hselected :
                      (args.extract 0 consumed).reverse[k.toNat]! =
                        args[consumed - k.toNat - 1]! := by
                    rw [getElem!_pos
                        (args.extract 0 consumed).reverse k.toNat hkPrefix,
                      Array.getElem_reverse]
                    have hsourceIndex : consumed - k.toNat - 1 < args.size :=
                      by omega
                    rw [getElem!_pos args (consumed - k.toNat - 1)
                        hsourceIndex,
                      Array.getElem_extract]
                    congr 1
                    omega
                  have hprefixSize64 :
                      (args.extract 0 consumed).reverse.size.toUInt64.toNat =
                        consumed := by
                    rw [toNat_toUInt64_cheapBeta]
                    simp only [Array.size_reverse, hprefixSize]
                    exact Nat.mod_eq_of_lt hconsumedLt
                  have hkWindow :
                      (k ≥ (0 : UInt64) &&
                        k < 0 +
                          (args.extract 0 consumed).reverse.size.toUInt64) =
                        true := by
                    apply Bool.and_eq_true_iff.mpr
                    constructor
                    · exact decide_eq_true (UInt64.le_iff_toNat_le.mpr
                        (Nat.zero_le _))
                    · exact decide_eq_true (UInt64.lt_iff_toNat_lt.mpr
                        (by
                          rw [UInt64.toNat_add, UInt64.toNat_zero,
                            hprefixSize64, Nat.zero_add,
                            Nat.mod_eq_of_lt hconsumedLt]
                          exact hkNat))
                  have hselectedConstructed := hsim.2.1 k.toNat (by
                    simpa only [Array.size_reverse, hprefixSize] using hkNat)
                  have hsimEq :
                      KExpr.simulSubstSpec (.var k varName varInfo)
                          (args.extract 0 consumed).reverse 0 =
                        args[consumed - k.toNat - 1]! := by
                    rw [KExpr.simulSubstSpec, if_pos hkWindow,
                      UInt64.sub_zero,
                      KExpr.liftSpec_zero hselectedConstructed, hselected]
                  exact ⟨_, _, _, _, rfl, hpeel, hcount.2,
                    hsimEq.symm, rfl⟩
                · simp [hclosed, hk] at hplan
            | fvar | sort | const | app | lam | all | letE | prj | nat |
                str =>
                simp [hclosed] at hplan
      | var | fvar | sort | const | app | all | letE | prj | nat | str =>
          cases hplan
  | var | fvar | sort | const | lam | all | letE | prj | nat | str =>
      cases hplan

end Ix.Kernel
