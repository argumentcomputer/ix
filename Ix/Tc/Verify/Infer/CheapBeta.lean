import Ix.Tc.Verify.Infer.BinderScopes
import Ix.Tc.Verify.Whnf.Beta.Meaning
import Ix.Tc.Verify.Whnf.Structural.ApplicationCongruence

/-!
# Audited cheap beta reduction

Lambda and let inference run `cheapBetaReduce` inside the intern table.  This
module connects its pure plan to the finite `WalkerRequest.cheapBeta`
footprint and proves exact execution while preserving the complete checker
invariant.  The Theory-level beta meaning is intentionally a separate layer;
the operational theorem here cannot silently assume it.
-/

namespace Ix.Tc

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

/-- Cheap beta reduction preserves the Theory meaning of a structurally
translated source.  A successful plan is discharged by K1's constructive
multi-beta theorem; an absent plan is reflexive. -/
theorem KExpr.cheapBetaReduceResult_meaning
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars) {Delta : KVLCtx}
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hbounds : WalkerRequest.Bounds (.cheapBeta source)) :
    WhnfMeaning trProj world uvars Delta source
      (KExpr.cheapBetaReduceResult source) := by
  cases hplan : cheapBetaPlan? source with
  | none =>
      rw [KExpr.cheapBetaReduceResult, hplan]
      exact WhnfMeaning.refl hsource
        (hsource.wf world.venvWF.ordered theory.literalWF
          theory.projections.wf hDelta)
  | some plan =>
      rw [KExpr.cheapBetaReduceResult, hplan]
      obtain ⟨head, body, args, consumed, hspine, hpeel, hcount,
        hbase, htrailing⟩ := cheapBetaPlan?_simul hplan hbounds
      have htyped := RecM.trAppSpine_of_collectSpine hsource hspine
      obtain ⟨headV, hheadTr, hsuffix⟩ := htyped.toSuffix
      have hprefixList :
          (args.extract 0 consumed).toList =
            args.toList.take consumed := by
        simp only [Array.toList_extract, List.extract_eq_take_drop,
          List.drop_zero, Nat.sub_zero]
      have htrailingList :
          (args.extract consumed args.size).toList =
            args.toList.drop consumed := by
        rw [Array.toList_extract]
        simp only [List.extract_eq_take_drop]
        have hargsLength : args.toList.length = args.size := by simp
        have hdropLength :
            (args.toList.drop consumed).length =
              args.size - consumed := by
          rw [List.length_drop, hargsLength]
        rw [← hdropLength]
        exact List.take_length
      obtain ⟨middleV, hprefix, htrailingSuffix⟩ :=
        hsuffix.splitAt consumed (by simpa using hcount)
      rw [← hprefixList] at hprefix
      rw [← htrailingList] at htrailingSuffix
      have hpeelCert := RecM.BetaPeel.of_peelLamsN head args.toList
      rw [show args.toList.length = args.size by simp, hpeel] at hpeelCert
      dsimp only at hpeelCert
      rw [← hprefixList] at hpeelCert
      have hsimBounds := hbounds.cheapBeta_simul hspine hpeel
      obtain ⟨reducedV, hreducedTr, hmiddleReduced⟩ :=
        RecM.betaPrefixMeaning trProj world theory hDelta hheadTr
          hpeelCert.1 hprefix hsimBounds
      rw [← htrailing] at htrailingSuffix
      obtain ⟨finalV, hfinalTr, hsourceFinal⟩ :=
        htrailingSuffix.rebase world.venvWF hDelta hreducedTr
          hmiddleReduced
      refine ⟨sourceV, finalV, hsource, ?_, hsourceFinal⟩
      change TrKExprS world.venv uvars world.nameOf trProj Delta
        (plan.trailing.foldl KExpr.mkApp plan.base) finalV
      rw [hbase]
      exact hfinalTr

namespace KExpr.CheapBetaReach

@[simp] theorem source (e : KExpr .anon) : CheapBetaReach e e := by
  simp [CheapBetaReach]

theorem of_plan {source : KExpr .anon} {plan : CheapBetaPlan .anon}
    (hplan : cheapBetaPlan? source = some plan) {x : KExpr .anon}
    (hx : x ∈ cheapBetaChainList plan.base plan.trailing) :
    CheapBetaReach source x := by
  simp [CheapBetaReach, hplan, hx]

end KExpr.CheapBetaReach

/-- The pure result of an application-chain plan occurs in its exact finite
candidate list. -/
theorem cheapBetaChainList_result_mem (base : KExpr .anon) :
    ∀ trailing : List (KExpr .anon),
      trailing.foldl KExpr.mkApp base ∈ cheapBetaChainList base trailing
  | [] => by simp [cheapBetaChainList]
  | arg :: trailing => by
      simp only [List.foldl_cons, cheapBetaChainList, List.mem_cons]
      exact Or.inr (cheapBetaChainList_result_mem
        (KExpr.mkApp base arg) trailing)

theorem cheapBetaChainList_base_mem (base : KExpr .anon)
    (trailing : List (KExpr .anon)) :
    base ∈ cheapBetaChainList base trailing := by
  cases trailing <;> simp [cheapBetaChainList]

namespace KExpr.CheapBetaReach

theorem result (source : KExpr .anon) :
    CheapBetaReach source (KExpr.cheapBetaReduceResult source) := by
  cases hplan : cheapBetaPlan? source with
  | none =>
      simp [KExpr.cheapBetaReduceResult, hplan, KExpr.CheapBetaReach]
  | some plan =>
      rw [KExpr.cheapBetaReduceResult, hplan]
      exact of_plan hplan
        (cheapBetaChainList_result_mem plan.base plan.trailing)

end KExpr.CheapBetaReach

/-- Execute one selected application chain exactly.  Every candidate offered
to the intern table is drawn from `cheapBetaChainList`; collision freedom
therefore returns the anonymous expression itself rather than a colliding
resident. -/
theorem internAppChain_spec
    {support : RunSupport} (hcollision : support.CollisionFree)
    {base : KExpr .anon} {trailing : List (KExpr .anon)}
    (hreach : ∀ x, x ∈ cheapBetaChainList base trailing → support x)
    (it : InternTable .anon) (hwf : it.WF)
    (hcover : support.CoversIntern it) :
    (internAppChain base trailing it).1 =
        trailing.foldl KExpr.mkApp base ∧
      (internAppChain base trailing it).2.WF ∧
      support.CoversIntern (internAppChain base trailing it).2 := by
  induction trailing generalizing base it with
  | nil =>
      exact ⟨rfl, hwf, hcover⟩
  | cons arg trailing ih =>
      let candidate := KExpr.mkApp base arg
      have hcandidate : support candidate :=
        hreach candidate (by
          simp only [cheapBetaChainList, List.mem_cons]
          exact Or.inr (cheapBetaChainList_base_mem candidate trailing))
      have hintern := TcM.internExpr_support_spec hcollision hcandidate
        it hwf hcover
      rcases hintern with ⟨hcanon, hwf', hcover'⟩
      have htail : ∀ x,
          x ∈ cheapBetaChainList candidate trailing → support x := by
        intro x hx
        exact hreach x (by
          simp only [cheapBetaChainList, List.mem_cons]
          exact Or.inr hx)
      have hrest := ih htail (it.internExpr candidate).2 hwf' hcover'
      change
        (internAppChain (it.internExpr candidate).1 trailing
          (it.internExpr candidate).2).1 =
            (arg :: trailing).foldl KExpr.mkApp base ∧
        (internAppChain (it.internExpr candidate).1 trailing
          (it.internExpr candidate).2).2.WF ∧
        support.CoversIntern
          (internAppChain (it.internExpr candidate).1 trailing
            (it.internExpr candidate).2).2
      rw [hcanon]
      simpa only [List.foldl_cons] using hrest

/-- InternM-level exactness and support preservation for the whole
peephole reducer. -/
theorem cheapBetaReduce_spec
    {support : RunSupport} (hcollision : support.CollisionFree)
    {source : KExpr .anon}
    (hreach : ∀ x, KExpr.CheapBetaReach source x → support x)
    (it : InternTable .anon) (hwf : it.WF)
    (hcover : support.CoversIntern it) :
    (cheapBetaReduce source it).1 = KExpr.cheapBetaReduceResult source ∧
      (cheapBetaReduce source it).2.WF ∧
      support.CoversIntern (cheapBetaReduce source it).2 := by
  cases hplan : cheapBetaPlan? source with
  | none =>
      rw [cheapBetaReduce, hplan]
      change source = KExpr.cheapBetaReduceResult source ∧
        it.WF ∧ support.CoversIntern it
      simpa [KExpr.cheapBetaReduceResult, hplan] using
        (show source = source ∧ it.WF ∧ support.CoversIntern it from
          ⟨rfl, hwf, hcover⟩)
  | some plan =>
      have hchain : ∀ x,
          x ∈ cheapBetaChainList plan.base plan.trailing → support x :=
        fun x hx => hreach x (KExpr.CheapBetaReach.of_plan hplan hx)
      simpa [cheapBetaReduce, KExpr.cheapBetaReduceResult, hplan,
        CheapBetaPlan.result] using
        internAppChain_spec hcollision hchain it hwf hcover

/-- Finite callback resources for cheap beta at any supported recursive
inference result.  The source quantifier ranges over a finite `RunSupport`,
so this remains a finite closure obligation. -/
structure CheapBetaResources (support : RunSupport) : Prop where
  reach : ∀ {source : KExpr .anon}, support source → ∀ x,
    KExpr.CheapBetaReach source x → support x
  bounds : ∀ {source : KExpr .anon}, support source →
    WalkerRequest.Bounds (.cheapBeta source)

namespace CheapBetaResources

/-- Request-independent execution rule used when `source` is returned by a
recursive callback and therefore is not statically named in the enclosing
execution certificate. -/
theorem whnf_wf
    {support : RunSupport} (hresources : CheapBetaResources support)
    (hcollision : support.CollisionFree)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {source : KExpr .anon}
    (hsource : support source) {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.runIntern (cheapBetaReduce source))
      (fun result after =>
        result = KExpr.cheapBetaReduceResult source ∧
          support result ∧ InternUpdateFrame s after) := by
  have hreach := hresources.reach hsource
  apply TcM.WF.mono
    (TcM.runIntern_whnf_wf (fun it hwf hcover =>
      cheapBetaReduce_spec hcollision hreach it hwf hcover))
  · intro result after hpost
    rcases hpost with ⟨rfl, hframe⟩
    exact ⟨rfl, hreach _ (KExpr.CheapBetaReach.result source), hframe⟩
  · intro _ _ herror
    exact herror

end CheapBetaResources

namespace RunAssumptions

/-- The audited request-list form used by inference branches. -/
theorem cheapBeta_whnf_wf
    {alpha : Type} {initial : TcState .anon}
    {program : TcM .anon alpha} {requests : List WalkerRequest}
    {support : RunSupport}
    (h : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {source : KExpr .anon}
    (hmem : WalkerRequest.cheapBeta source ∈ requests)
    {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.runIntern (cheapBetaReduce source))
      (fun result after =>
        result = KExpr.cheapBetaReduceResult source ∧
          support result ∧ InternUpdateFrame s after) := by
  have hreach : ∀ x, KExpr.CheapBetaReach source x → support x :=
    (h.coverage.requests _ hmem).expr
  apply TcM.WF.mono
    (TcM.runIntern_whnf_wf (fun it hwf hcover =>
      cheapBetaReduce_spec h.collisionFree hreach it hwf hcover))
  · intro result after hpost
    rcases hpost with ⟨rfl, hframe⟩
    refine ⟨rfl, ?_, hframe⟩
    exact hreach _ (KExpr.CheapBetaReach.result source)
  · intro _ _ herror
    exact herror

end RunAssumptions

end Ix.Tc
