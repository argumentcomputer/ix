import IxVMRefinement.TwinFamily.ProducerRow
import IxVMRefinement.TwinFamily.ClosureTwin
import IxVMRefinement.Binding.FamilyReconCheck
import IxVMRefinement.Binding.FamilyReconLevels
import IxVMRefinement.FamilyGraph.CheckedKinds

/-! # Connecting `Binding.FamilyRecon` to the twin recursor producers

Wires `Binding.FamilyRecon.familyFlat_of_call`, `Binding.FamilyRecon.familyForm_of_call`, and
`Binding.FamilyRecon.familyForm_of_call_group` directly into both twin-step endpoints
(`ClosureTwinSteps` and `FamilyTwinRowFamClosed`), eliminating `TwinCallFlat` and `TwinCallRecon`:

* `StoreLevelsParams t R`: blob-independent level-parameter well-scopedness and inductive
  parameter coherence on a binding witness store `R`;
* `recordWrapConsObs_of_recon`: converts `Binding.FamilyRecon.RecordWrapConsObs` (plus the
  `ctorsBefore` minor-count equality from `familyFlat_of_call`) to `TwinFamily.RecordWrapConsObs`;
* `closureStore_levels_and_params`, `closureTwinSteps_of_storeLevels`: discharges
  `Binding.ClosureTwinSteps` across every group `6 ≤ g < 77` of every binding run from
  `StoredRecLvlsOk` and `StoreLevelsParams` on the pre-group store `R`;
* `TypingUseSet`, `typingUseStore_usedClosed`, `typingUseStore_levels_and_params`,
  `FamilyTwinRowFamClosed`, `familyTwinWF_of_storeLevels`: builds the `UsedClosed` store
  `recordsAt E (TypingUseSet ...)` on the typing side, establishes `StoreLevelsOk` and
  `StoreIndParamsOk` over it from `StoreLevelsParams t R`, committed basis rows, `TopWalkCore`,
  `InnerChecked`, and `FamilyChecksAt`, and discharges `FamilyTwinRowFamClosed` from
  `StoredRecLvlsOk` alone (given `StoreLevelsParams t R` at the witness store). -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (KExpr KLevel KKey ExprLvEq)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open IxVM.Refinement.Binding (BRun BindingRun AtGroups ClosureCtx ClosureTwinSteps StoredFamiliesRForm
  IsTwinShape UnitCheckedAt)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry RecordFlat BlockDerivedFlat Held)
open IxVM.Refinement.Binding.FamilyRecon (ReconView RFormS MemberRecon StoreLevelsOk
  StoreIndParamsOk UnitLevelsAndParamsOk ctorsBefore wrapAt)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Store-level invariant interface -/

/-- **Blob-independent level-parameter well-scopedness and inductive-parameter coherence on `R`**:
for any store `E` extending `R` on records, both `StoreLevelsOk t E (Held R)` and
`StoreIndParamsOk E (Held R)` hold. -/
def StoreLevelsParams (t : Ix.Kernel.RoleTable) (R : Ixon.Env) : Prop :=
  ∀ E : Ixon.Env, (∀ y c, recordOf R y = some c → recordOf E y = some c) →
    StoreLevelsOk t E (Held R) ∧ StoreIndParamsOk E (Held R)

/-! ## Conversion from `Binding.FamilyRecon` wrapper observations to `TwinFamily` -/

private theorem wrapperObserved_of_recon {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {w : KKey} {n : Nat} (h : Binding.FamilyRecon.WrapperObserved calls t w n) :
    WrapperObserved calls t w n := h

private theorem consumesObs_of_recon {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {W : KKey → Option (Option Nat)} {e₁ e₂ : KExpr}
    (h : Binding.FamilyRecon.ConsumesObs W (Binding.FamilyRecon.WrapperObserved calls t) e₁ e₂) :
    ConsumesObs W (WrapperObserved calls t) e₁ e₂ := by
  induction h with
  | refl e => exact .refl e
  | step hc hd hw ho _ ih => exact .step hc hd hw (wrapperObserved_of_recon ho) ih

private theorem wrapConsObs_of_recon {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {W : KKey → Option (Option Nat)} {e₁ e₂ : KExpr}
    (h : Binding.FamilyRecon.WrapConsObs W (Binding.FamilyRecon.WrapperObserved calls t) e₁ e₂) :
    WrapConsObs W (WrapperObserved calls t) e₁ e₂ := by
  induction h with
  | bvar i => exact .bvar i
  | fvar he => exact .fvar he
  | sort hl => exact .sort hl
  | const hl => exact .const hl
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hc _ _ iht ihb => exact .lam hpw (consumesObs_of_recon hc) iht ihb
  | forallE hpw hc _ _ iht ihb => exact .forallE hpw (consumesObs_of_recon hc) iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ihe => exact .proj ihe

private theorem recordWrapConsObs_of_recon {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E : Ixon.Env} {B rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {es : List FlatEntry} {off : Nat}
    (hrec : recordOf E rb = some crb) (hmuts : crb.info = .muts rs)
    (hBD : BlockDerivedFlat t E B off es)
    (hct : ∀ k rc, rs[k]? = some (.recr rc) →
      ctorsBefore (ReconView.ofStore t E) es es.length = some rc.minors.toNat)
    (h : Binding.FamilyRecon.RecordWrapConsObs calls t E B rb) :
    RecordWrapConsObs calls t E B rb := by
  obtain ⟨crb', rs', es', off', fuel, hrec', hmuts', hRF', hBD', hM'⟩ := h
  have ecr : crb' = crb := Option.some.inj (hrec'.symm.trans hrec)
  subst crb'
  have ers : rs' = rs := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hmuts)
  subst rs'
  obtain ⟨hoff, hes⟩ := Binding.FamilyFlat.blockDerivedFlat_off_unique
    (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2))
    (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hBD' hBD
  subst off' es'
  refine ⟨crb, rs, es, off, fuel, hrec, hmuts, hRF', hBD, fun k rc hk => ?_⟩
  obtain ⟨ty, R, bodies, cbk, hty, hR, hrel, hbod, hcbk, hrules⟩ := hM' k rc hk
  exact ⟨hct k rc hk, ty, R, bodies, cbk, hty, hR, wrapConsObs_of_recon hrel, hbod, hcbk, hrules⟩

/-! ## Decidable `UnitLevelsAndParamsOk` over committed basis rows -/

private def univVarsLtB (n : Nat) : Ixon.Univ → Bool
  | .zero => true
  | .succ u => univVarsLtB n u
  | .max a b => univVarsLtB n a && univVarsLtB n b
  | .imax a b => univVarsLtB n a && univVarsLtB n b
  | .var i => decide (i.toNat < n)

private theorem convUniv_allParamsDefined_b {n : Nat} :
    ∀ u : Ixon.Univ, univVarsLtB n u = true →
      (Ix.Kernel.Reader.convUniv id u).allParamsDefined (List.range n) = true
  | .zero, _ => rfl
  | .succ u, h => convUniv_allParamsDefined_b u h
  | .max a b, h => by
    simp only [univVarsLtB, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Reader.convUniv, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨convUniv_allParamsDefined_b a h.1, convUniv_allParamsDefined_b b h.2⟩
  | .imax a b, h => by
    simp only [univVarsLtB, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Reader.convUniv, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨convUniv_allParamsDefined_b a h.1, convUniv_allParamsDefined_b b h.2⟩
  | .var i, h => by
    simp only [univVarsLtB, decide_eq_true_eq] at h
    simp only [Ix.Kernel.Reader.convUniv, id, Ix.Kernel.Level.allParamsDefined,
      List.contains_eq_mem, decide_eq_true_eq, List.mem_range]
    exact h

private def univIdxOkB (univs : Array Ixon.Univ) (n : Nat) (i : UInt64) : Bool :=
  match univs[i.toNat]? with
  | some u => univVarsLtB n u
  | none => true

private def exprUnivsLtGoB (univs : Array Ixon.Univ) (n : Nat) (tbl : Array Bool) :
    Ixon.Expr → Bool
  | .var _ | .str _ | .nat _ => true
  | .sort i => univIdxOkB univs n i
  | .ref _ us | .recur _ us => us.toList.all (univIdxOkB univs n)
  | .prj _ _ v => exprUnivsLtGoB univs n tbl v
  | .app f a => exprUnivsLtGoB univs n tbl f && exprUnivsLtGoB univs n tbl a
  | .lam t b | .all t b => exprUnivsLtGoB univs n tbl t && exprUnivsLtGoB univs n tbl b
  | .letE _ _ t v b =>
    exprUnivsLtGoB univs n tbl t && exprUnivsLtGoB univs n tbl v && exprUnivsLtGoB univs n tbl b
  | .share i => tbl.getD i.toNat true

private def buildUnivsOkTblGoB (univs : Array Ixon.Univ) (n : Nat) :
    Array Bool → List Ixon.Expr → Array Bool
  | acc, [] => acc
  | acc, e :: es => buildUnivsOkTblGoB univs n (acc.push (exprUnivsLtGoB univs n acc e)) es

private def exprUnivsOkB (src : Ixon.Constant) (n : Nat) (e : Ixon.Expr) : Bool :=
  exprUnivsLtGoB src.univs n (buildUnivsOkTblGoB src.univs n #[] src.sharing.toList) e

private theorem ecx_level_allParamsDefined_b {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat} {i : UInt64} {l : KLevel}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id))
    (hok : univIdxOkB univs n i = true) (hl : ecx.level i = .ok l) :
    l.allParamsDefined (List.range n) = true := by
  unfold Ix.Kernel.Reader.ECx.level at hl
  rw [hunivs, Array.getElem?_map] at hl
  unfold univIdxOkB at hok
  cases hget : univs[i.toNat]? with
  | none => rw [hget] at hl; simp [Ix.Kernel.Reader.malformed] at hl
  | some u =>
    rw [hget] at hl hok
    simp only [Option.map_some] at hl
    rw [← Except.ok.inj hl]
    exact convUniv_allParamsDefined_b u hok

private theorem ecx_levels_allParamsDefined_b {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id)) :
    ∀ (us : List UInt64) (ls : List KLevel),
      us.all (univIdxOkB univs n) = true →
      us.mapM ecx.level = .ok ls →
      ls.all (Ix.Kernel.Level.allParamsDefined (List.range n)) = true
  | [], ls, _, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | u :: us, ls, hok, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hl : ecx.level u with
    | error _ => rw [hl] at h; cases h
    | ok l =>
      rw [hl] at h
      cases hls : us.mapM ecx.level with
      | error _ => rw [hls] at h; cases h
      | ok ls' =>
        rw [hls] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [List.all_cons, Bool.and_eq_true]
        exact ⟨ecx_level_allParamsDefined_b hunivs hok.1 hl,
          ecx_levels_allParamsDefined_b hunivs us ls' hok.2 hls⟩

private theorem convExpr_allLevelParamsDefined_b {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat}
    {shareTbl : Array (Ix.Kernel.Reader.ReadM KExpr)} {okTbl : Array Bool}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id))
    (htbl : ∀ i E_rd, shareTbl[i]? = some (.ok E_rd) → okTbl.getD i true = true →
      E_rd.allLevelParamsDefined (List.range n) = true) :
    ∀ (e : Ixon.Expr) (E_rd : KExpr),
      exprUnivsLtGoB univs n okTbl e = true →
      Ix.Kernel.Reader.convExpr ecx shareTbl e = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range n) = true
  | .var i, E_rd, _, h => by
    simp only [Ix.Kernel.Reader.convExpr, pure, Except.pure, Except.ok.injEq] at h
    subst h; rw [Ix.Kernel.Expr.mkBvar_eq]; rfl
  | .sort i, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hl : ecx.level i with
    | error _ => rw [hl] at h; cases h
    | ok l =>
      rw [hl] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      exact ecx_level_allParamsDefined_b hunivs hok hl
  | .ref i us, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hk : ecx.keyAt i with
    | error _ => rw [hk] at h; cases h
    | ok k =>
      rw [hk] at h
      cases hls : ecx.levels us with
      | error _ => rw [hls] at h; cases h
      | ok ls =>
        rw [hls] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        exact ecx_levels_allParamsDefined_b hunivs us.toList ls hok hls
  | .recur i us, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr] at h
    cases hs : ecx.self i.toNat with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs] at h; simp only [bind, Except.bind] at h
      cases hm : m with
      | error _ => rw [hm] at h; cases h
      | ok k =>
        rw [hm] at h
        cases hls : ecx.levels us with
        | error _ => rw [hls] at h; cases h
        | ok ls =>
          rw [hls] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          exact ecx_levels_allParamsDefined_b hunivs us.toList ls hok hls
  | .prj i f v, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hk : ecx.keyAt i with
    | error _ => rw [hk] at h; cases h
    | ok k =>
      rw [hk] at h
      cases hv : Ix.Kernel.Reader.convExpr ecx shareTbl v with
      | error _ => rw [hv] at h; cases h
      | ok ev =>
        rw [hv] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        exact convExpr_allLevelParamsDefined_b hunivs htbl v ev hok hv
  | .str i, E_rd, _, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hb : ecx.blobAt i with
    | error _ => rw [hb] at h; cases h
    | ok bs =>
      rw [hb] at h; dsimp only at h
      cases hs : String.fromUTF8? bs with
      | none => rw [hs] at h; cases h
      | some s =>
        rw [hs] at h; dsimp only at h
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | .nat i, E_rd, _, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hn : ecx.natAt i with
    | error _ => rw [hn] at h; cases h
    | ok m =>
      rw [hn] at h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  | .app f a, E_rd, hok, h => by
    simp only [exprUnivsLtGoB, Bool.and_eq_true] at hok
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hf : Ix.Kernel.Reader.convExpr ecx shareTbl f with
    | error _ => rw [hf] at h; cases h
    | ok ef =>
      rw [hf] at h
      cases ha : Ix.Kernel.Reader.convExpr ecx shareTbl a with
      | error _ => rw [ha] at h; cases h
      | ok ea =>
        rw [ha] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true]
        exact ⟨convExpr_allLevelParamsDefined_b hunivs htbl f ef hok.1 hf,
          convExpr_allLevelParamsDefined_b hunivs htbl a ea hok.2 ha⟩
  | .lam t b, E_rd, hok, h => by
    simp only [exprUnivsLtGoB, Bool.and_eq_true] at hok
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases ht : Ix.Kernel.Reader.convExpr ecx shareTbl t with
    | error _ => rw [ht] at h; cases h
    | ok et =>
      rw [ht] at h
      cases hb : Ix.Kernel.Reader.convExpr ecx shareTbl b with
      | error _ => rw [hb] at h; cases h
      | ok eb =>
        rw [hb] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true,
          Ix.Kernel.BinderMeta.leanNever, Ix.Kernel.PropWhen.paramsDefined]
        exact ⟨⟨convExpr_allLevelParamsDefined_b hunivs htbl t et hok.1 ht,
          convExpr_allLevelParamsDefined_b hunivs htbl b eb hok.2 hb⟩, rfl⟩
  | .all t b, E_rd, hok, h => by
    simp only [exprUnivsLtGoB, Bool.and_eq_true] at hok
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases ht : Ix.Kernel.Reader.convExpr ecx shareTbl t with
    | error _ => rw [ht] at h; cases h
    | ok et =>
      rw [ht] at h
      cases hb : Ix.Kernel.Reader.convExpr ecx shareTbl b with
      | error _ => rw [hb] at h; cases h
      | ok eb =>
        rw [hb] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true,
          Ix.Kernel.BinderMeta.leanNever, Ix.Kernel.PropWhen.paramsDefined]
        exact ⟨⟨convExpr_allLevelParamsDefined_b hunivs htbl t et hok.1 ht,
          convExpr_allLevelParamsDefined_b hunivs htbl b eb hok.2 hb⟩, rfl⟩
  | .letE _ _ t v b, E_rd, hok, h => by
    simp only [exprUnivsLtGoB, Bool.and_eq_true] at hok
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases ht : Ix.Kernel.Reader.convExpr ecx shareTbl t with
    | error _ => rw [ht] at h; cases h
    | ok et =>
      rw [ht] at h
      cases hv : Ix.Kernel.Reader.convExpr ecx shareTbl v with
      | error _ => rw [hv] at h; cases h
      | ok ev =>
        rw [hv] at h
        cases hb : Ix.Kernel.Reader.convExpr ecx shareTbl b with
        | error _ => rw [hb] at h; cases h
        | ok eb =>
          rw [hb] at h; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
          simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true]
          exact ⟨⟨convExpr_allLevelParamsDefined_b hunivs htbl t et hok.1.1 ht,
            convExpr_allLevelParamsDefined_b hunivs htbl v ev hok.1.2 hv⟩,
            convExpr_allLevelParamsDefined_b hunivs htbl b eb hok.2 hb⟩
  | .share i, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr] at h
    cases hg : shareTbl[i.toNat]? with
    | none => rw [hg] at h; cases h
    | some r =>
      rw [hg] at h; dsimp only at h
      exact htbl i.toNat E_rd (by rw [hg, h]) hok

private theorem buildUnivsOkTblGoB_sound {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id)) :
    ∀ (es : List Ixon.Expr) (shareAcc : Array (Ix.Kernel.Reader.ReadM KExpr))
      (okAcc : Array Bool),
      shareAcc.size = okAcc.size →
      (∀ i E_rd, shareAcc[i]? = some (.ok E_rd) → okAcc.getD i true = true →
        E_rd.allLevelParamsDefined (List.range n) = true) →
      ∀ i E_rd, (L1.buildShareTblGo ecx shareAcc es)[i]? = some (.ok E_rd) →
        (buildUnivsOkTblGoB univs n okAcc es).getD i true = true →
        E_rd.allLevelParamsDefined (List.range n) = true
  | [], _, _, _, hinv, i, E_rd, hs, hok => hinv i E_rd hs hok
  | e :: es, shareAcc, okAcc, hsz, hinv, i, E_rd, hs, hok => by
    refine buildUnivsOkTblGoB_sound hunivs es
      (shareAcc.push (Ix.Kernel.Reader.convExpr ecx shareAcc e))
      (okAcc.push (exprUnivsLtGoB univs n okAcc e)) (by simp [hsz]) ?_ i E_rd hs hok
    intro j E' hj hokj
    by_cases hlt : j < shareAcc.size
    · rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt] at hj
      have hlt' : j < okAcc.size := by omega
      have hgetd : (okAcc.push (exprUnivsLtGoB univs n okAcc e)).getD j true = okAcc.getD j true := by
        simp [Array.getD, hlt', Array.size_push, Nat.lt_succ_of_lt hlt', Array.getElem_push_lt hlt']
      rw [hgetd] at hokj
      exact hinv j E' hj hokj
    · have hj_eq : j = shareAcc.size := by
        have hlt_p := (Array.getElem?_eq_some_iff.mp hj).1
        simp only [Array.size_push] at hlt_p; omega
      subst hj_eq
      rw [Array.getElem?_push_size] at hj
      have hconv := Option.some.inj hj
      have hgetd : (okAcc.push (exprUnivsLtGoB univs n okAcc e)).getD shareAcc.size true =
          exprUnivsLtGoB univs n okAcc e := by
        simp [Array.getD, hsz]
      rw [hgetd] at hokj
      exact convExpr_allLevelParamsDefined_b hunivs hinv e E' hokj hconv

private theorem exprUnivsOkB_sound {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {n : Nat} {e : Ixon.Expr} {E_rd : KExpr}
    (hok : exprUnivsOkB src n e = true)
    (hread : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read e = .ok E_rd) :
    E_rd.allLevelParamsDefined (List.range n) = true := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq cx src id self
  unfold Ix.Kernel.Reader.MemberReader.read at hread
  rw [hecx, htbl] at hread
  have hinv := buildUnivsOkTblGoB_sound
    (ecx := ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv id), self⟩)
    (univs := src.univs) (n := n) rfl src.sharing.toList #[] #[] rfl
    (fun i _ h => by simp at h)
  exact convExpr_allLevelParamsDefined_b rfl hinv e E_rd hok hread

private def constLevelsOkB (c : Ixon.Constant) : Bool :=
  match c.info with
  | .defn d =>
    if d.kind == .defn then decide (d.lvls.toNat < 4294967296) && exprUnivsOkB c d.lvls.toNat d.value
    else true
  | .muts ms =>
    ms.toList.all fun m =>
      match m with
      | .defn d =>
        if d.kind == .defn then decide (d.lvls.toNat < 4294967296) && exprUnivsOkB c d.lvls.toNat d.value
        else true
      | .indc ind =>
        decide (ind.lvls.toNat < 4294967296) && exprUnivsOkB c ind.lvls.toNat ind.typ &&
          ind.ctors.toList.all fun ct =>
            decide (ct.lvls.toNat < 4294967296) && exprUnivsOkB c ct.lvls.toNat ct.typ
      | .recr r =>
        decide (r.lvls.toNat < 4294967296) && exprUnivsOkB c r.lvls.toNat r.typ &&
          r.rules.toList.all fun ru => exprUnivsOkB c r.lvls.toNat ru.rhs
  | _ => true

private def constIndParamsOkB (c : Ixon.Constant) : Bool :=
  match c.info with
  | .muts ms =>
    ms.toList.all fun m =>
      match m with
      | .indc ind =>
        ind.ctors.toList.all (fun ct => ct.params == ind.params) &&
          ms.toList.all fun m2 =>
            match m2 with
            | .indc ind2 => ind2.params == ind.params
            | _ => true
      | _ => true
  | _ => true

set_option maxRecDepth 200000 in
private theorem basisRows_levelsOkB :
    StoreInhabit.basisRows.all (fun e => constLevelsOkB e.2) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
private theorem basisRows_indParamsOkB :
    StoreInhabit.basisRows.all (fun e => constIndParamsOkB e.2) = true := by
  decide +kernel

private theorem unitLevelsAndParamsOk_of_basis {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {a : _root_.Address} {c : Ixon.Constant}
    (hb : recordOf StoreInhabit.basisStore a = some c) :
    UnitLevelsAndParamsOk t E₀ a c := by
  have hlv : constLevelsOkB c = true :=
    List.all_eq_true.mp basisRows_levelsOkB (a, c) (StoreInhabit.store_record_inv hb)
  have hpr : constIndParamsOkB c = true :=
    List.all_eq_true.mp basisRows_indParamsOkB (a, c) (StoreInhabit.store_record_inv hb)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hci hdk
    simp only [constLevelsOkB, hci, hdk] at hlv
    change (decide (d.lvls.toNat < 4294967296) && exprUnivsOkB c d.lvls.toNat d.value) = true at hlv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlv
    exact ⟨hlv.1, fun E_rd hr => exprUnivsOkB_sound hlv.2 hr⟩
  · intro ms i d hci hi hdk
    simp only [constLevelsOkB, hci, List.all_eq_true] at hlv
    have hm := hlv (.defn d) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    simp only [hdk] at hm
    change (decide (d.lvls.toNat < 4294967296) && exprUnivsOkB c d.lvls.toNat d.value) = true at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    exact ⟨hm.1, fun E_rd hr => exprUnivsOkB_sound hm.2 hr⟩
  · intro ms i ind hci hi
    simp only [constLevelsOkB, hci, List.all_eq_true] at hlv
    simp only [constIndParamsOkB, hci, List.all_eq_true] at hpr
    have hml := hlv (.indc ind) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    have hmp := hpr (.indc ind) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hml hmp
    refine ⟨⟨hml.1.1, fun E_rd hr => exprUnivsOkB_sound hml.1.2 hr⟩, ?_, ?_⟩
    · intro j ct hj
      have hct := hml.2 ct (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj))
      have hctp := hmp.1 ct (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj))
      exact ⟨hct.1, fun E_rd hr => exprUnivsOkB_sound hct.2 hr, beq_iff_eq.mp hctp⟩
    · intro i₂ ind₂ hi₂
      have hp2 := hmp.2 (.indc ind₂) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi₂))
      exact (beq_iff_eq.mp hp2).symm
  · intro ms k r hci hk
    simp only [constLevelsOkB, hci, List.all_eq_true] at hlv
    have hm := hlv (.recr r) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hm
    refine ⟨hm.1.1, fun E_rd hr => exprUnivsOkB_sound hm.1.2 hr, ?_⟩
    intro j ru E_rd hj hr
    have hru := hm.2 ru (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj))
    exact exprUnivsOkB_sound hru hr

/-! ## General `UnitLevelsAndParamsOk` constructors -/

private theorem unitLevelsAndParamsOk_of_nonUnit {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {a : _root_.Address} {c : Ixon.Constant}
    (hnd : ∀ d, c.info ≠ .defn d) (hnm : ∀ ms, c.info ≠ .muts ms) :
    UnitLevelsAndParamsOk t E₀ a c :=
  ⟨fun d h _ => (hnd d h).elim,
   fun ms _ _ h _ _ => (hnm ms h).elim,
   fun ms _ _ h _ => (hnm ms h).elim,
   fun ms _ _ h _ => (hnm ms h).elim⟩

private theorem unitLevelsAndParamsOk_of_familyCall {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B r : _root_.Address} {cr : Ixon.Constant}
    {rs : Array Ixon.MutConst} {lim : Option Nat} {cs : List (Call F)}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hRec : FamRecRecord E₀ r cr rs)
    (hfc : FamilyCallAtLim calls bAddr t B r lim cs) :
    UnitLevelsAndParamsOk t E₀ r cr := by
  obtain ⟨h_cf, h'_cf, xrc_cf, xb_cf, xrb_cf, r_cf, -, -, ⟨rb_b, hrb_b, hrb_eq⟩,
    ev_cf, -, hsub_cf⟩ := hfc
  subst hrb_eq
  have hrecs := Binding.FamilyRecon.check_family_recr_levelsOk (t := t) hS hbd
    hRec.record hRec.muts hrb_b ev_cf hsub_cf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd; rw [hRec.muts] at hd; cases hd
  · intro ms i d hms hi _
    have heq : ms = rs := Ixon.ConstantInfo.muts.inj (hms.symm.trans hRec.muts)
    subst heq
    obtain ⟨r', hr'⟩ := hRec.recrs (.defn d) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    cases hr'
  · intro ms i ind hms hi
    have heq : ms = rs := Ixon.ConstantInfo.muts.inj (hms.symm.trans hRec.muts)
    subst heq
    obtain ⟨r', hr'⟩ := hRec.recrs (.indc ind) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    cases hr'
  · intro ms k rc hms hk
    have heq : ms = rs := Ixon.ConstantInfo.muts.inj (hms.symm.trans hRec.muts)
    subst heq
    exact hrecs k rc hk

/-- Bound on member array size of a block stored in a bounded run store. -/
private theorem muts_size_lt_u64 {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    {a : _root_.Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hc : recordOf E₀ a = some c) (hms : c.info = .muts ms) :
    ms.size < UInt64.size := by
  cases hget : E₀.consts.get? a with
  | none => unfold recordOf at hc; rw [hget] at hc; cases hc
  | some lc =>
    obtain ⟨c', -, hde⟩ := hS.decoded a lc hget
    have hceq : c' = c := by
      unfold recordOf at hc; rw [hget, Option.bind_some, hde] at hc
      exact Option.some.inj hc
    subst hceq
    obtain ⟨⟨cl, hcl, _, _, hargs, hrep⟩, -⟩ := hS.loaded.1 a lc hget
    have hlen : lc.rawBytes.data.toList.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbd hcl (by rw [hargs]; exact List.mem_cons_self ..) hrep
    have hres : c'.resourceSize ≤ 2 * lc.rawBytes.size :=
      Ixon.Verify.ConstantBounds.deConstantExact_resource_bound lc.rawBytes c' hde
    have hsz : lc.rawBytes.size = lc.rawBytes.data.toList.length := by
      rw [Array.length_toList]; rfl
    have hms_le : ms.size ≤ c'.resourceSize := Claim.muts_size_le hms
    change ms.size < 2 ^ 64
    omega

/-- Converts `StoreLevelsParams t R` over a `UsedClosed` store `R` merged into `E` with `E₀`
into `UnitLevelsAndParamsOk t E₀ a c` at any address `a` held by `R` and `E₀`. -/
private theorem unitLevelsAndParamsOk_of_held_R {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {R E₀ E : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hclR : UsedClosed R)
    (hR_E : ∀ a c, recordOf R a = some c → recordOf E a = some c)
    (hE₀_E : ∀ a c, recordOf E₀ a = some c → recordOf E a = some c)
    (hE₀_blob : ∀ x b, E₀.blobs.get? x = some b → E.blobs.get? x = some b)
    (hLP : StoreLevelsParams t R)
    {a : _root_.Address} {c : Ixon.Constant}
    (hRa : Held R a) (hc₀ : recordOf E₀ a = some c) :
    UnitLevelsAndParamsOk t E₀ a c := by
  obtain ⟨hlv_E, hpar_E⟩ := hLP E hR_E
  have hcE : recordOf E a = some c := hE₀_E a c hc₀
  have hcR : recordOf R a = some c := by
    obtain ⟨cR, hcR⟩ := Option.isSome_iff_exists.mp hRa
    have heq : cR = c := Option.some.inj ((hR_E a cR hcR).symm.trans hcE)
    exact heq ▸ hcR
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hci hdk
    obtain ⟨hnl, hdef⟩ := hlv_E.defnVal a c d hRa hcE hci hdk
    exact ⟨hnl, fun E_rd hr => hdef E_rd (ReaderReads.exprReader_mono hE₀_blob hr)⟩
  · intro ms i d hms hi hdk
    have hi_lt : i < ms.size := (Array.getElem?_eq_some_iff.mp hi).1
    have hsz64 : ms.size < UInt64.size := muts_size_lt_u64 hS hbd hc₀ hms
    have hi64 : i.toUInt64.toNat = i := by
      change (UInt64.ofNat i).toNat = i
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    have hmemR := (hclR.2 a c ms hcR hms i (.defn d) hi).1
    have hmemE := hR_E _ _ hmemR
    have hmemHeld : Held R (memberAddr a i (.defn d)) :=
      Option.isSome_iff_exists.mpr ⟨_, hmemR⟩
    obtain ⟨hnl, hdef⟩ := hlv_E.dPrjVal (memberAddr a i (.defn d))
      (memberProjection a i (.defn d)) ⟨i.toUInt64, a⟩ c ms d hmemHeld hmemE rfl hcE hms
      (by rwa [hi64]) hdk
    exact ⟨hnl, fun E_rd hr => hdef E_rd (ReaderReads.exprReader_mono hE₀_blob hr)⟩
  · intro ms i ind hms hi
    have hi_lt : i < ms.size := (Array.getElem?_eq_some_iff.mp hi).1
    have hsz64 : ms.size < UInt64.size := muts_size_lt_u64 hS hbd hc₀ hms
    have hi64 : i.toUInt64.toNat = i := by
      change (UInt64.ofNat i).toNat = i
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    have hmemR := (hclR.2 a c ms hcR hms i (.indc ind) hi).1
    have hmemE := hR_E _ _ hmemR
    have hmemHeld : Held R (memberAddr a i (.indc ind)) :=
      Option.isSome_iff_exists.mpr ⟨_, hmemR⟩
    obtain ⟨hnl_i, hdef_i⟩ := hlv_E.indTy (memberAddr a i (.indc ind))
      (memberProjection a i (.indc ind)) ⟨i.toUInt64, a⟩ c ms ind hmemHeld hmemE rfl hcE hms
      (by rwa [hi64])
    refine ⟨⟨hnl_i, fun E_rd hr => hdef_i E_rd (ReaderReads.exprReader_mono hE₀_blob hr)⟩, ?_, ?_⟩
    · intro j ct hj
      obtain ⟨hnl_c, hdef_c⟩ := hlv_E.ctorTy a c ms i ind j ct hRa hcE hms hi hj
      exact ⟨hnl_c, fun E_rd hr => hdef_c E_rd (ReaderReads.exprReader_mono hE₀_blob hr),
        hpar_E.ctorParams a c ms i ind j ct hRa hcE hms hi hj⟩
    · intro i₂ ind₂ hi₂
      exact hpar_E.blockParams a c ms i i₂ ind ind₂ hRa hcE hms hi hi₂
  · intro ms k rc hms hk
    obtain ⟨hnl, hdefT, hdefR⟩ := hlv_E.recr a c ms k rc hRa hcE hms hk
    exact ⟨hnl,
      fun E_rd hr => hdefT E_rd (ReaderReads.exprReader_mono hE₀_blob hr),
      fun j ru E_rd hj hr => hdefR j ru E_rd hj (ReaderReads.exprReader_mono hE₀_blob hr)⟩

/-- `StoreLevelsOk` and `StoreIndParamsOk` over any `UsedClosed` store `R_use` agreeing with `E₀`
whose overlapping records satisfy `UnitLevelsAndParamsOk t E₀`. -/
private theorem storeLevelsOk_and_indParamsOk_of_units_agree {t : Ix.Kernel.RoleTable}
    {E₀ R_use : Ixon.Env}
    (hagree : ∀ y c c', recordOf R_use y = some c → recordOf E₀ y = some c' → c = c')
    (hcl : UsedClosed R_use)
    (hunits : ∀ a c, Held R_use a → recordOf E₀ a = some c → UnitLevelsAndParamsOk t E₀ a c) :
    StoreLevelsOk t E₀ (Held R_use) ∧ StoreIndParamsOk E₀ (Held R_use) := by
  have held_rec : ∀ a c, Held R_use a → recordOf E₀ a = some c → recordOf R_use a = some c := by
    intro a c ha hcE
    obtain ⟨cR, hcR⟩ := Option.isSome_iff_exists.mp ha
    have heq := hagree a cR c hcR hcE
    exact heq ▸ hcR
  have owner_held : ∀ a c, Held R_use a → recordOf E₀ a = some c →
      Held R_use (Ix.Cert.ownerOf a c) :=
    fun a c ha hcE => (hcl.1 a c (held_rec a c ha hcE)).1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a c d ha hcE hci hdk
    exact (hunits a c ha hcE).defnVal d hci hdk
  · intro a c p cb ms d ha hcE hci hcbE hms hi hdk
    have hpb : Held R_use p.block := by
      simpa [Ix.Cert.ownerOf, hci] using owner_held a c ha hcE
    exact (hunits p.block cb hpb hcbE).mutDefn ms p.idx.toNat d hms hi hdk
  · intro a c p cb ms ind ha hcE hci hcbE hms hi
    have hpb : Held R_use p.block := by
      simpa [Ix.Cert.ownerOf, hci] using owner_held a c ha hcE
    exact ((hunits p.block cb hpb hcbE).mutInd ms p.idx.toNat ind hms hi).1
  · intro b cb ms i ind j ct hb hcbE hms hi hj
    have hct := ((hunits b cb hb hcbE).mutInd ms i ind hms hi).2.1 j ct hj
    exact ⟨hct.1, hct.2.1⟩
  · intro rb crb rs k r hrb hcrbE hrs hk
    exact (hunits rb crb hrb hcrbE).mutRecr rs k r hrs hk
  · intro b cb ms i ind j ct hb hcbE hms hi hj
    exact (((hunits b cb hb hcbE).mutInd ms i ind hms hi).2.1 j ct hj).2.2
  · intro b cb ms i₁ i₂ ind₁ ind₂ hb hcbE hms hi₁ hi₂
    exact ((hunits b cb hb hcbE).mutInd ms i₁ ind₁ hms hi₁).2.2 i₂ ind₂ hi₂

/-! ## Binding-closure twin producer (`ClosureTwinSteps`) -/

/-- Discharges `StoreLevelsOk` and `StoreIndParamsOk` over the closure store `R₁` from
`StoreLevelsParams t R` on the pre-group store `R` and the group's `ClosureCtx`. -/
private theorem closureStore_levels_and_params
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun} {Rs : Nat → Ixon.Env}
    (hrun : BindingRun calls t ρ Rs) {g : Nat} (hg : g < 77)
    {R R' R₁ : Ixon.Env} {env₀ : Ix.Kernel.Env .anon}
    {famOf₀ famOf : _root_.Address → Option _root_.Address}
    {adv cont : _root_.Address → _root_.Address → Prop} {bAddr : _root_.Address}
    (hC : ClosureCtx.{u} FormerOpenTraceAt calls ρ t g R R' R₁ env₀ famOf₀ famOf adv cont bAddr)
    (hLP : StoreLevelsParams t R) :
    StoreLevelsOk t ρ.E₀ (Held R₁) ∧ StoreIndParamsOk ρ.E₀ (Held R₁) := by
  have hloaded : ∀ a lr, R₁.consts.get? a = some lr → ρ.E₀.consts.get? a = some lr :=
    fun a lr h => hC.admits.loaded a lr (hC.store.le₂.1 a lr h)
  have hR₁_sub : ∀ y c, recordOf R₁ y = some c → recordOf ρ.E₀ y = some c :=
    fun _ _ h => Binding.recordOf_of_loaded hloaded h
  have hR_sub : ∀ y c, recordOf R y = some c → recordOf ρ.E₀ y = some c :=
    fun _ _ h => hR₁_sub _ _ (Binding.recordOf_of_loaded hC.store.le₁.1 h)
  have hR_blob : ∀ x b, ρ.E₀.blobs.get? x = some b → ρ.E₀.blobs.get? x = some b :=
    fun _ _ h => h
  obtain ⟨bAddrChk, hchk_iff⟩ := hrun.checked_iff
  refine Binding.FamilyRecon.storeLevelsOk_and_indParamsOk_of_units hR₁_sub hC.closed ?_
  intro a c hc₁
  have hc₀ : recordOf ρ.E₀ a = some c := hR₁_sub a c hc₁
  cases hRa : recordOf R a with
  | some cR =>
    exact unitLevelsAndParamsOk_of_held_R hrun.runStore hrun.bounded hC.bnd.shape.usedClosed
      hR_sub (fun _ _ h => h) hR_blob hLP (Option.isSome_iff_exists.mpr ⟨cR, hRa⟩) hc₀
  | none =>
    have hc' : recordOf R' a = some c := Binding.recordOf_of_loaded hC.store.le₂.1 hc₁
    have hnew' : Binding.New R R' a := ⟨by rw [hc']; rfl, hRa⟩
    have hlog : InLogic c := hC.admits.logic a c hnew' hc'
    by_cases hdm : (∃ d, c.info = .defn d) ∨ (∃ ms, c.info = .muts ms)
    · have hUK : UnitKind c := by
        rcases hdm with ⟨d, hd⟩ | ⟨ms, hms⟩
        · exact Or.inl ⟨d, hd⟩
        · exact Or.inr (Or.inr ⟨ms, hms⟩)
      by_cases htw : IsTwinShape c
      · obtain ⟨rs, hmuts, hpos, hrecrs⟩ := htw
        have hRec : FamRecRecord ρ.E₀ a c rs :=
          ⟨hc₀, hmuts, hrecrs, hlog, fun i m hm =>
            hR₁_sub _ _ (hC.closed.2 a c rs hc₁ hmuts i m hm).1⟩
        rcases hC.checks.claimed a c rs hnew' hc₀ hmuts hpos hrecrs with ⟨B', hfamB'⟩ | ⟨B', cs', hfc⟩
        · obtain ⟨-, -, cs', advAs', hown', -⟩ := hC.checks.famCall B' a hfamB'
          exact unitLevelsAndParamsOk_of_familyCall hrun.runStore hrun.bounded hRec hown'.toCall
        · exact unitLevelsAndParamsOk_of_familyCall hrun.runStore hrun.bounded hRec hfc
      · rcases hC.famAdmits.checked a c hnew' hc' hUK htw with hchk | ⟨B', hfamB', -⟩
        · have hU : UnitCheckedAt calls bAddrChk t ρ.E₀ a (some (Binding.valLimit g)) :=
            (hchk_iff a (Binding.valLimit g)).mp hchk
          exact Binding.FamilyRecon.unitCheckedAt_unitLevelsAndParamsOk
            hrun.runStore hrun.bounded hc₀ hlog hU
        · obtain ⟨-, -, cs', advAs', hown', -⟩ := hC.checks.famCall B' a hfamB'
          obtain ⟨_, _, crb', rs', _, hFOB⟩ := hC.checks.family B' a hfamB'
          have heq : crb' = c := Option.some.inj (hFOB.record.record.symm.trans hc₀)
          rw [heq] at hFOB
          exact unitLevelsAndParamsOk_of_familyCall hrun.runStore hrun.bounded
            hFOB.record hown'.toCall
    · push_neg at hdm
      exact unitLevelsAndParamsOk_of_nonUnit hdm.1 hdm.2

/-- **Binding-closure twin step (`Binding.ClosureTwinSteps`) from `StoredRecLvlsOk` and
`StoreLevelsParams` on the pre-group store**: completely discharges `TwinCallFlat` and
`TwinCallRecon` via `Binding.FamilyRecon.{familyFlat_of_call, familyForm_of_call_group}`. -/
theorem closureTwinSteps_of_storeLevels
    (hStoredLvls : StoredRecLvlsOk)
    (hStoreLP : ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (ρ : BRun)
        (Rs : Nat → Ixon.Env) (g : Nat) (R R' R₁ : Ixon.Env) (env₀ : Ix.Kernel.Env .anon)
        (famOf₀ famOf : _root_.Address → Option _root_.Address)
        (adv cont : _root_.Address → _root_.Address → Prop) (bAddr : _root_.Address),
      BindingRun calls t ρ Rs → AllBound t → t.check = .ok () → 6 ≤ g → g < 77 →
      ClosureCtx.{u} FormerOpenTraceAt calls ρ t g R R' R₁ env₀ famOf₀ famOf adv cont bAddr →
      StoreLevelsParams t R) :
    ∀ calls, AtGroups (BindingRun calls) (ClosureTwinSteps.{u} FormerOpenTraceAt calls) := by
  intro calls t ρ Rs hrun hall ht g hg6 hg R R' R₁ env₀ famOf₀ famOf adv cont bAddr A c
    hC hnA hc₁ htw hfamA huncA
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hloaded : ∀ a lr, R₁.consts.get? a = some lr → ρ.E₀.consts.get? a = some lr :=
    fun a lr h => hC.admits.loaded a lr (hC.store.le₂.1 a lr h)
  have hR₁_sub : ∀ y d, recordOf R₁ y = some d → recordOf ρ.E₀ y = some d :=
    fun _ _ h => Binding.recordOf_of_loaded hloaded h
  have hR₁_agree : ∀ y c₁ c₂, recordOf R₁ y = some c₁ → recordOf ρ.E₀ y = some c₂ → c₁ = c₂ :=
    fun y c₁ c₂ h1 h2 => Option.some.inj ((hR₁_sub y c₁ h1).symm.trans h2)
  have hzc : R₁.consts.get? Ix.HostAdmission.Merkle.padding = none := by
    cases h : R₁.consts.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some lc =>
      have h' := hC.store.le₂.1 _ lc h
      rw [hC.admits.zeroFree.1] at h'; cases h'
  have hzb : R₁.blobs.get? Ix.HostAdmission.Merkle.padding = none := by
    cases h : R₁.blobs.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some b =>
      have h' := hC.store.le₂.2 _ b h
      rw [hC.admits.zeroFree.2] at h'; cases h'
  obtain ⟨Ec, -, hst⟩ := hrun.stepStores R₁ hloaded
    (fun a b h => hC.admits.loadedBlobs a b (hC.store.le₂.2 a b h))
    (fun p hp lc h => hC.admits.committed p hp lc (hC.store.le₂.1 _ lc h)) ⟨hzc, hzb⟩
  have hM : Binding.FamilyRecon.ModeledAnswers calls (Held R₁) (ReconView.ofStore t ρ.E₀) :=
    Binding.FamilyRecon.modeledAnswers_mono_S (fun _ _ => trivial)
      (Binding.FamilyRecon.modeledAnswers_of_stepStore hrun.runStore hrun.hashedStored hst)
  obtain ⟨hlv₁, hpar₁⟩ := closureStore_levels_and_params hrun hg hC
    (hStoreLP calls t ρ Rs g R R' R₁ env₀ famOf₀ famOf adv cont bAddr hrun hall ht hg6 hg hC)
  have hrecRefs : ∀ {r cr} {rs : Array Ixon.MutConst}, Held R₁ r → recordOf ρ.E₀ r = some cr →
      ∀ i ∈ usedRefIdxs cr, ∀ a, cr.refs[i]? = some a →
        Held R₁ a ∨ a = r ∨ ∃ k m, rs[k]? = some m ∧ a = memberAddr r k m := by
    intro r cr rs hRr hcr i hi a ha
    obtain ⟨cr', hcr'⟩ := Option.isSome_iff_exists.mp hRr
    have heq := hR₁_agree r cr' cr hcr' hcr
    subst heq
    exact Or.inl ((hC.closed.1 r cr' hcr').2 i hi a ha)
  have hvl : Binding.valLimit g < 77 := Nat.lt_of_le_of_lt (Binding.valLimit_le g) hg
  refine closureTwinSteps_at hStoredLvls hrun hall ht hg6 hg hC hnA hc₁ htw hfamA huncA ?_ ?_
  · intro B r cr rs cs hRB hRr hRec hsz hlogB hfc
    obtain ⟨cb, ms, es, off, hFOB, hRF, hBD, hlvls, -⟩ :=
      Binding.FamilyRecon.familyFlat_of_call ht htwf hrun.runStore hrun.hashedStored hrun.bounded
        hR₁_agree hC.closed hRB (hrecRefs hRr hRec.record) hlv₁ hpar₁ hM hRec hsz hlogB hfc
    exact ⟨cb, ms, es, off, hFOB, hRF, hBD, hlvls⟩
  · intro B r cb cr ms rs cs hRB hRr hB hRec hsz hfc
    have hlogB : ∀ cb', recordOf ρ.E₀ B = some cb' → InLogic cb' := by
      intro cb' hcb'
      rw [Option.some.inj (hcb'.symm.trans hB.record)]
      exact hB.logic
    exact Or.inl (Binding.FamilyRecon.familyForm_of_call_group ht htwf hrun.runStore
      hrun.hashedStored hrun.bounded hR₁_agree hC.closed hRB (hrecRefs hRr hRec.record)
      hlv₁ hpar₁ hM hRec hsz hlogB hvl hfc)

/-! ## Typing-side used-closed store and `FamilyTwinRowFamClosed` -/

/-- **Address set for the typing-side `UsedClosed` store `recordsAt E (TypingUseSet ...)`**:
records held in the binding witness store `R`, committed basis records, safe top-walked records,
in-logic non-projection inner records, claimed family records, and member/constructor projections
of blocks in the three run-checked classes. -/
def TypingUseSet (R E₀ : Ixon.Env) (Top Inner : _root_.Address → Prop)
    (fam : _root_.Address → Option _root_.Address) (a : _root_.Address) : Prop :=
  Held R a ∨
  Held StoreInhabit.basisStore a ∨
  (Top a ∧ Claim.SourceSafe E₀ a) ∨
  (Inner a ∧ ∃ c, recordOf E₀ a = some c ∧ InLogic c ∧ ¬ IsProj c) ∨
  (∃ B', fam B' = some a) ∨
  (∃ D cD ms, ((Top D ∧ Claim.SourceSafe E₀ D) ∨ (Inner D ∧ InLogic cD) ∨ (∃ B', fam B' = some D)) ∧
    recordOf E₀ D = some cD ∧ cD.info = .muts ms ∧
    ∃ i m, ms[i]? = some m ∧
      (a = memberAddr D i m ∨ ∃ ind j, m = .indc ind ∧ j < ind.ctors.size ∧ a = ctorAddr D i j))

private theorem recordOf_recordsAt {E : Ixon.Env} {S : _root_.Address → Prop} {a : _root_.Address}
    {c : Ixon.Constant} :
    recordOf (Binding.recordsAt E S) a = some c ↔ S a ∧ recordOf E a = some c :=
  Binding.recordOf_restrict (fun _ => Binding.recordsAt_consts) c

private theorem ownerOf_eq_self_of_not_proj {a : _root_.Address} {c : Ixon.Constant}
    (hnp : ¬ IsProj c) : Ix.Cert.ownerOf a c = a := by
  cases h : c.info with
  | dPrj p => exact (hnp (Or.inl ⟨p, h⟩)).elim
  | iPrj p => exact (hnp (Or.inr (Or.inl ⟨p, h⟩))).elim
  | cPrj p => exact (hnp (Or.inr (Or.inr (Or.inl ⟨p, h⟩)))).elim
  | rPrj p => exact (hnp (Or.inr (Or.inr (Or.inr ⟨p, h⟩)))).elim
  | defn _ | recr _ | axio _ | quot _ | muts _ => simp [Ix.Cert.ownerOf, h]

private theorem held_R_or_basis_of_storedAt {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t (fun _ => True) R envT)
    (ht : t.check = .ok ()) (htwf : t.wf = true) {x : _root_.Address}
    (hst : StoredAt t envT x) :
    Held R x ∨ Held StoreInhabit.basisStore x := by
  obtain ⟨ci, -, hbas | hkept⟩ := storedAt_provenance hshape ht htwf hst
  · exact Or.inr hbas
  · obtain ⟨-, ci₀, ⟨cR, hcR, -⟩, -⟩ := hkept
    exact Or.inl (Option.isSome_iff_exists.mpr ⟨cR, hcR⟩)

private theorem held_R_or_basis_of_covered {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} (hshape : TableShape.{u} t (fun _ => True) R envT)
    (ht : t.check = .ok ()) (htwf : t.wf = true) {x : _root_.Address}
    (hcov : Covered t x) :
    Held R x ∨ Held StoreInhabit.basisStore x :=
  held_R_or_basis_of_storedAt hshape ht htwf (covered_stored hshape htwf hcov)

private theorem typingUseStore_usedClosed {calls : List (Call F)} {bAddrW bAddrIC : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    {R : Ixon.Env} {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hWc : Claim.TopWalkCore calls bAddrW t seeds E₀ lim Top rank)
    (hG : TopGraph t E₀ seeds Top rank)
    (hFR : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hIC : InnerChecked calls bAddrIC t envT E₀ lim Top rank fam twin Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E) :
    UsedClosed (Binding.recordsAt E (TypingUseSet R E₀ Top Inner fam)) := by
  have ht : t.check = .ok () := hWc.check_ok
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  let S := TypingUseSet R E₀ Top Inner fam
  let R_use := Binding.recordsAt E S
  have hR_E : ∀ a c, recordOf R a = some c → recordOf E a = some c :=
    fun a c h => (recordOf_eq_recordAt_of_decoded hctx.recordsFor.1 a).trans (hctx.recordsFor.2.1 a c h)
  have hE₀_E : ∀ a c, recordOf E₀ a = some c → recordOf E a = some c :=
    fun a c h => (recordOf_eq_recordAt_of_decoded hctx.recordsFor.1 a).trans (hctx.runRecord a c h)
  have hBas_E : ∀ a c, recordOf StoreInhabit.basisStore a = some c → recordOf E a = some c :=
    fun a c h => (recordOf_eq_recordAt_of_decoded hctx.recordsFor.1 a).trans
      (recordAt_E_of_basisStore hctx.recordsFor h)
  have held_of_R : ∀ y, Held R y → Held R_use y := by
    intro y hy
    obtain ⟨cy, hcy⟩ := Option.isSome_iff_exists.mp hy
    exact Option.isSome_iff_exists.mpr ⟨cy, recordOf_recordsAt.mpr ⟨Or.inl hy, hR_E y cy hcy⟩⟩
  have held_of_bas : ∀ y, Held StoreInhabit.basisStore y → Held R_use y := by
    intro y hy
    obtain ⟨cy, hcy⟩ := Option.isSome_iff_exists.mp hy
    exact Option.isSome_iff_exists.mpr ⟨cy, recordOf_recordsAt.mpr ⟨Or.inr (Or.inl hy), hBas_E y cy hcy⟩⟩
  have held_of_stored : ∀ y, StoredAt t envT y → Held R_use y := by
    intro y hy
    rcases held_R_or_basis_of_storedAt hctx.shape ht htwf hy with h1 | h2
    · exact held_of_R y h1
    · exact held_of_bas y h2
  have held_of_cov : ∀ y, Covered t y → Held R_use y :=
    fun y hy => held_of_stored y (covered_stored hctx.shape htwf hy)
  have held_of_owned : ∀ {k x}, NeedOk E₀ x → OwnedBelow E₀ Top Inner rank fam k x → Held R_use x := by
    intro k x hneed hob
    obtain ⟨cx, hcx, -, hlogx, hown_logx⟩ := hneed
    obtain ⟨D, hWD, -, -, cD, hcD, hown⟩ := hob
    have hxE : recordOf E x = some cx := hE₀_E x cx hcx
    suffices hSx : S x from Option.isSome_iff_exists.mpr ⟨cx, recordOf_recordsAt.mpr ⟨hSx, hxE⟩⟩
    rcases hown with hxD | ⟨rb, crb, hfamD, hcrb, hxrb⟩
    · rcases hxD with ⟨rfl, hstD⟩ | ⟨ms, i, m, hms, hm, hproj⟩
      · have hnp : ¬ IsProj cD := fun hp => standalone_not_proj hstD hp
        have hc_eq : cD = cx := Option.some.inj (hcD.symm.trans hcx)
        subst hc_eq
        rcases hWD with hTD | hID
        · refine Or.inr (Or.inr (Or.inl ⟨hTD, fun c' hc' => ?_⟩))
          have e := Option.some.inj (hc'.symm.trans hcD); subst e
          exact ⟨hlogx, fun cb hcb => hown_logx cb hcb⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hID, cD, hcD, hlogx, hnp⟩)))
      · have hlogD : InLogic cD := by
          have hpx : Ix.Cert.ownerOf x cx = D := by
            rcases hWD with hTD | hID
            · rcases hproj with rfl | ⟨ind, j, rfl, hj, rfl⟩
              · have h1 := (hG.members D cD ms hTD hcD hms i m hm).1
                have e := Option.some.inj (hcx.symm.trans h1); rw [e]; exact ownerOf_memberProjection _ D i m
              · have h1 := (hG.members D cD ms hTD hcD hms i (.indc ind) hm).2 ind j rfl hj
                have e := Option.some.inj (hcx.symm.trans h1); rw [e]; exact ownerOf_constructorProjection _ D i j
            · rcases hproj with rfl | ⟨ind, j, rfl, hj, rfl⟩
              · have h1 := (hFR.graph.innerMembers D cD ms hID hcD hms i m hm).1
                have e := Option.some.inj (hcx.symm.trans h1); rw [e]; exact ownerOf_memberProjection _ D i m
              · have h1 := (hFR.graph.innerMembers D cD ms hID hcD hms i (.indc ind) hm).2 ind j rfl hj
                have e := Option.some.inj (hcx.symm.trans h1); rw [e]; exact ownerOf_constructorProjection _ D i j
          exact hown_logx cD (by rwa [hpx])
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨D, cD, ms, ?_, hcD, hms, i, m, hm, hproj⟩))))
        rcases hWD with hTD | hID
        · refine Or.inl ⟨hTD, fun c' hc' => ?_⟩
          have e := Option.some.inj (hc'.symm.trans hcD); subst e
          refine ⟨hlogD, fun cb hcb => ?_⟩
          have ho : Ix.Cert.ownerOf D cD = D := by simp [Ix.Cert.ownerOf, hms]
          rw [ho] at hcb
          rw [Option.some.inj (hcb.symm.trans hcD)]; exact hlogD
        · exact Or.inr (Or.inl ⟨hID, hlogD⟩)
    · obtain ⟨crb', rs, hF⟩ := hFR.graph.famRecord D rb hfamD
      have e : crb' = crb := Option.some.inj (hF.record.symm.trans hcrb)
      subst e
      rcases hxrb with ⟨-, hst⟩ | ⟨ms, i, m, hms, hm, hproj⟩
      · exact (standalone_not_block hst ⟨rs, hF.muts⟩).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨rb, crb', ms, Or.inr (Or.inr ⟨D, hfamD⟩), hcrb, hms, i, m, hm, hproj⟩))))
  -- Helper: member & constructor projection records of a block in `E₀`
  have mem_and_ctor_of : ∀ (D : _root_.Address) (cD : Ixon.Constant) (ms : Array Ixon.MutConst),
      ((Top D ∧ Claim.SourceSafe E₀ D) ∨ (Inner D ∧ InLogic cD) ∨ (∃ B', fam B' = some D)) →
      recordOf E₀ D = some cD → cD.info = .muts ms →
      (∀ i m, ms[i]? = some m →
        recordOf E₀ (memberAddr D i m) = some (memberProjection D i m) ∧
        ∀ ind j, m = .indc ind → j < ind.ctors.size →
          recordOf E₀ (ctorAddr D i j) = some (constructorProjection D i j)) →
      ∀ i m, ms[i]? = some m →
        recordOf R_use (memberAddr D i m) = some (memberProjection D i m) ∧
        ∀ ind j, m = .indc ind → j < ind.ctors.size →
          recordOf R_use (ctorAddr D i j) = some (constructorProjection D i j) := by
    intro D cD ms hcls hcD hms hmem i m hm
    refine ⟨recordOf_recordsAt.mpr ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨D, cD, ms, hcls, hcD, hms, i, m, hm, Or.inl rfl⟩)))), hE₀_E _ _ (hmem i m hm).1⟩, ?_⟩
    intro ind j hmind hj
    exact recordOf_recordsAt.mpr ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨D, cD, ms, hcls, hcD, hms, i, m, hm, Or.inr ⟨ind, j, hmind, hj, rfl⟩⟩)))),
      hE₀_E _ _ ((hmem i m hm).2 ind j hmind hj)⟩
  constructor
  · -- Part 1: owner and used references
    intro a c ha
    obtain ⟨hSa, hcE⟩ := recordOf_recordsAt.mp ha
    rcases hSa with hRa | hBa | ⟨hTa, hSafe⟩ | ⟨hIa, c₀, hc₀, hlog₀, hnp₀⟩ | ⟨B', hfam'⟩ |
        ⟨D, cD, ms, hcls, hcD, hms, i, m, hm, hproj⟩
    · -- (1) `Held R a`
      obtain ⟨cR, hcR⟩ := Option.isSome_iff_exists.mp hRa
      have e : cR = c := Option.some.inj ((hR_E a cR hcR).symm.trans hcE)
      subst e
      obtain ⟨hown, hrefs⟩ := hctx.shape.usedClosed.1 a cR hcR
      exact ⟨held_of_R _ hown, fun j hj x hx => held_of_R _ (hrefs j hj x hx)⟩
    · -- (2) `Held StoreInhabit.basisStore a`
      obtain ⟨cB, hcB⟩ := Option.isSome_iff_exists.mp hBa
      have e : cB = c := Option.some.inj ((hBas_E a cB hcB).symm.trans hcE)
      subst e
      obtain ⟨hown, hrefs⟩ := StoreInhabit.store_usedClosed.1 a cB hcB
      exact ⟨held_of_bas _ hown, fun j hj x hx => held_of_bas _ (hrefs j hj x hx)⟩
    · -- (3) `Top a ∧ Claim.SourceSafe E₀ a`
      obtain ⟨c₀, hc₀⟩ := hG.record a hTa
      have e : c₀ = c := Option.some.inj ((hE₀_E a c₀ hc₀).symm.trans hcE)
      subst e
      refine ⟨?_, ?_⟩
      · by_cases hp : IsProj c₀
        · have hTown := (hG.owner a c₀ hTa hc₀ hp).1
          obtain ⟨cb, hcb, hca⟩ := hG.projMember a c₀ hTa hc₀ hp
          have hlog_cb : InLogic cb := (hSafe c₀ hc₀).2 cb hcb
          have hcb_muts : ∃ ms, cb.info = .muts ms := by
            rcases hca with ⟨heqa, hst⟩ | ⟨ms, -, -, hms, -⟩
            · rw [← heqa] at hcb
              have e' := Option.some.inj (hcb.symm.trans hc₀)
              rw [e'] at hst
              exact (standalone_not_proj hst hp).elim
            · exact ⟨ms, hms⟩
          obtain ⟨ms, hms⟩ := hcb_muts
          have hSafe_own : Claim.SourceSafe E₀ (Ix.Cert.ownerOf a c₀) := by
            intro cb' hcb'
            have e' := Option.some.inj (hcb'.symm.trans hcb); subst e'
            refine ⟨hlog_cb, fun cb₂ hcb₂ => ?_⟩
            have ho : Ix.Cert.ownerOf (Ix.Cert.ownerOf a c₀) cb = Ix.Cert.ownerOf a c₀ := by
              simp [Ix.Cert.ownerOf, hms]
            rw [ho] at hcb₂
            rw [Option.some.inj (hcb₂.symm.trans hcb)]; exact hlog_cb
          exact Option.isSome_iff_exists.mpr ⟨cb,
            recordOf_recordsAt.mpr ⟨Or.inr (Or.inr (Or.inl ⟨hTown, hSafe_own⟩)), hE₀_E _ _ hcb⟩⟩
        · rw [ownerOf_eq_self_of_not_proj hp]
          exact Option.isSome_iff_exists.mpr ⟨c₀, ha⟩
      · intro j hj x hx
        have hu : UsedRef E₀ a x := ⟨c₀, j, hc₀, hj, hx⟩
        rcases hG.closed a x hTa hu with ⟨hTx, -⟩ | hcov
        · by_cases hcov' : Covered t x
          · exact held_of_cov x hcov'
          · obtain ⟨cx, hcx⟩ := hG.record x hTx
            exact Option.isSome_iff_exists.mpr ⟨cx,
              recordOf_recordsAt.mpr ⟨Or.inr (Or.inr (Or.inl ⟨hTx, hWc.safeRefs a x hTa hSafe hu hcov'⟩)),
                hE₀_E x cx hcx⟩⟩
        · exact held_of_cov x hcov
    · -- (4) `Inner a ∧ InLogic c₀ ∧ ¬ IsProj c₀`
      have e : c₀ = c := Option.some.inj ((hE₀_E a c₀ hc₀).symm.trans hcE)
      subst e
      refine ⟨by rw [ownerOf_eq_self_of_not_proj hnp₀]; exact Option.isSome_iff_exists.mpr ⟨c₀, ha⟩, ?_⟩
      intro j hj x hx
      have hu : UsedRef E₀ a x := ⟨c₀, j, hc₀, hj, hx⟩
      cases htw : twin a with
      | none =>
        rcases hIC.refsBelow a x hIa htw hu with hst | hcov | ⟨hneed, hob⟩
        · exact held_of_stored x hst
        · exact held_of_cov x hcov
        · exact held_of_owned hneed hob
      | some B' =>
        obtain ⟨bAddrFR, hCFR⟩ := hFR.checks
        obtain ⟨cs', hcall'⟩ := hCFR.twinCall a B' htw
        rcases recRefs_of_familyCall hWc.runStore hWc.hashedStored hc₀ hcall' x hu with hcovAt | hneed
        · obtain ⟨r, hr, hw, -⟩ := hcovAt
          exact held_of_cov x ⟨r, hr, hw⟩
        · rcases hFR.graph.innerClosed a x hIa hu hneed with hst | hcov | ⟨c', hc', hca⟩ | hob
          · exact held_of_stored x hst
          · exact held_of_cov x hcov
          · have e' := Option.some.inj (hc'.symm.trans hc₀); subst e'
            obtain ⟨cT, rsT, hFT, -⟩ := hFR.graph.twinRecord a B' htw
            have eT := Option.some.inj (hFT.record.symm.trans hc₀); subst eT
            rcases hca with ⟨-, hst⟩ | ⟨ms, k, m, hms, hm, hproj⟩
            · exact (standalone_not_block hst ⟨rsT, hFT.muts⟩).elim
            · have hm_mem := hFR.graph.innerMembers a cT ms hIa hc₀ hms k m hm
              rcases hproj with rfl | ⟨ind, q, rfl, hq, rfl⟩
              · exact Option.isSome_iff_exists.mpr ⟨_, recordOf_recordsAt.mpr
                  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, cT, ms, Or.inr (Or.inl ⟨hIa, hlog₀⟩),
                    hc₀, hms, k, m, hm, Or.inl rfl⟩)))), hE₀_E _ _ hm_mem.1⟩⟩
              · exact Option.isSome_iff_exists.mpr ⟨_, recordOf_recordsAt.mpr
                  ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, cT, ms, Or.inr (Or.inl ⟨hIa, hlog₀⟩),
                    hc₀, hms, k, .indc ind, hm, Or.inr ⟨ind, q, rfl, hq, rfl⟩⟩)))),
                    hE₀_E _ _ (hm_mem.2 ind q rfl hq)⟩⟩
          · exact held_of_owned hneed hob
    · -- (5) `fam B' = some a`
      obtain ⟨crb, rs, hF⟩ := hFR.graph.famRecord B' a hfam'
      have e : crb = c := Option.some.inj ((hE₀_E a crb hF.record).symm.trans hcE)
      subst e
      have hnp : ¬ IsProj crb := fun hp => proj_not_block hp ⟨rs, hF.muts⟩
      refine ⟨by rw [ownerOf_eq_self_of_not_proj hnp]; exact Option.isSome_iff_exists.mpr ⟨crb, ha⟩, ?_⟩
      intro j hj x hx
      have hu : UsedRef E₀ a x := ⟨crb, j, hF.record, hj, hx⟩
      obtain ⟨bAddrFR, -, hrecAt⟩ := hFR.famRecAt
      obtain ⟨rs', cs', -, hcall'⟩ := hrecAt B' a crb hfam' hF.record
      rcases recRefs_of_familyCall hWc.runStore hWc.hashedStored hF.record hcall' x hu with hcovAt | hneed
      · obtain ⟨r, hr, hw, -⟩ := hcovAt
        exact held_of_cov x ⟨r, hr, hw⟩
      · rcases hFR.graph.famClosed B' a x hfam' hu hneed with
            hst | hcov | ⟨cb', hcb', hcaB⟩ | ⟨crb', hcrb', hcar⟩ | hob
        · exact held_of_stored x hst
        · exact held_of_cov x hcov
        · obtain ⟨cb₀, msB, hcb₀, hmsB, -⟩ := hFR.famInd B' a hfam'
          have ecb := Option.some.inj (hcb'.symm.trans hcb₀); subst ecb
          have hTB := hFR.graph.famBlock B' a hfam'
          obtain ⟨-, cb₁, hcb₁, hlogB₁, -⟩ := hFR.graph.famUnit B' a hfam'
          have ecb₁ := Option.some.inj (hcb₁.symm.trans hcb₀); subst ecb₁
          have hSafeB : Claim.SourceSafe E₀ B' := by
            intro cb₂ hcb₂
            have e₂ := Option.some.inj (hcb₂.symm.trans hcb₀); subst e₂
            refine ⟨hlogB₁, fun cb₃ hcb₃ => ?_⟩
            have ho : Ix.Cert.ownerOf B' cb₁ = B' := by simp [Ix.Cert.ownerOf, hmsB]
            rw [ho] at hcb₃
            rw [Option.some.inj (hcb₃.symm.trans hcb₀)]; exact hlogB₁
          rcases hcaB with ⟨-, hst⟩ | ⟨ms', k, m, hms', hm, hproj⟩
          · exact (standalone_not_block hst ⟨msB, hmsB⟩).elim
          · have hm_mem := hG.members B' cb₁ ms' hTB hcb₀ hms' k m hm
            rcases hproj with rfl | ⟨ind, q, rfl, hq, rfl⟩
            · exact Option.isSome_iff_exists.mpr ⟨_, recordOf_recordsAt.mpr
                ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨B', cb₁, ms', Or.inl ⟨hTB, hSafeB⟩,
                  hcb₀, hms', k, m, hm, Or.inl rfl⟩)))), hE₀_E _ _ hm_mem.1⟩⟩
            · exact Option.isSome_iff_exists.mpr ⟨_, recordOf_recordsAt.mpr
                ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨B', cb₁, ms', Or.inl ⟨hTB, hSafeB⟩,
                  hcb₀, hms', k, .indc ind, hm, Or.inr ⟨ind, q, rfl, hq, rfl⟩⟩)))),
                  hE₀_E _ _ (hm_mem.2 ind q rfl hq)⟩⟩
        · have ecr := Option.some.inj (hcrb'.symm.trans hF.record); subst ecr
          rcases hcar with ⟨-, hst⟩ | ⟨ms', k, m, hms', hm, hproj⟩
          · exact (standalone_not_block hst ⟨rs, hF.muts⟩).elim
          · have hrs' : rs = ms' := Ixon.ConstantInfo.muts.inj (hF.muts.symm.trans hms')
            subst hrs'
            rcases hproj with rfl | ⟨ind, q, hmind, -, -⟩
            · exact Option.isSome_iff_exists.mpr ⟨_, recordOf_recordsAt.mpr
                ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, crb, rs, Or.inr (Or.inr ⟨B', hfam'⟩),
                  hF.record, hF.muts, k, m, hm, Or.inl rfl⟩)))), hE₀_E _ _ (hF.members k m hm)⟩⟩
            · obtain ⟨rc', hrc'⟩ := hF.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm))
              rw [hmind] at hrc'; cases hrc'
        · exact held_of_owned hneed hob
    · -- (6) member or constructor projection of a block `D`
      have hrec_a : (a = memberAddr D i m ∧ c = memberProjection D i m) ∨
          (∃ ind j, m = .indc ind ∧ j < ind.ctors.size ∧
            a = ctorAddr D i j ∧ c = constructorProjection D i j) := by
        rcases hcls with ⟨hTD, -⟩ | ⟨hID, -⟩ | ⟨B', hfamD⟩
        · have hmem := hG.members D cD ms hTD hcD hms i m hm
          rcases hproj with rfl | ⟨ind, j, hmind, hj, rfl⟩
          · exact Or.inl ⟨rfl, Option.some.inj (hcE.symm.trans (hE₀_E _ _ hmem.1))⟩
          · exact Or.inr ⟨ind, j, hmind, hj, rfl,
              Option.some.inj (hcE.symm.trans (hE₀_E _ _ (hmem.2 ind j hmind hj)))⟩
        · have hmem := hFR.graph.innerMembers D cD ms hID hcD hms i m hm
          rcases hproj with rfl | ⟨ind, j, hmind, hj, rfl⟩
          · exact Or.inl ⟨rfl, Option.some.inj (hcE.symm.trans (hE₀_E _ _ hmem.1))⟩
          · exact Or.inr ⟨ind, j, hmind, hj, rfl,
              Option.some.inj (hcE.symm.trans (hE₀_E _ _ (hmem.2 ind j hmind hj)))⟩
        · obtain ⟨crb, rs, hF⟩ := hFR.graph.famRecord B' D hfamD
          have e := Option.some.inj (hF.record.symm.trans hcD); subst e
          have ers := Ixon.ConstantInfo.muts.inj (hF.muts.symm.trans hms); subst ers
          rcases hproj with rfl | ⟨ind, j, hmind, -, -⟩
          · exact Or.inl ⟨rfl, Option.some.inj (hcE.symm.trans (hE₀_E _ _ (hF.members i m hm)))⟩
          · obtain ⟨rc', hrc'⟩ := hF.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm))
            rw [hmind] at hrc'; cases hrc'
      have hSD : S D := by
        rcases hcls with ⟨hTD, hSafeD⟩ | ⟨hID, hlogD⟩ | ⟨B', hfamD⟩
        · exact Or.inr (Or.inr (Or.inl ⟨hTD, hSafeD⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hID, cD, hcD, hlogD,
            fun hp => proj_not_block hp ⟨ms, hms⟩⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨B', hfamD⟩))))
      rcases hrec_a with ⟨rfl, rfl⟩ | ⟨ind, j, -, -, rfl, rfl⟩
      · refine ⟨?_, fun k hk _ _ => by cases m <;> simp [usedRefIdxs, memberProjection] at hk⟩
        rw [ownerOf_memberProjection]
        exact Option.isSome_iff_exists.mpr ⟨cD, recordOf_recordsAt.mpr ⟨hSD, hE₀_E D cD hcD⟩⟩
      · refine ⟨?_, fun k hk _ _ => by simp [usedRefIdxs, constructorProjection] at hk⟩
        rw [ownerOf_constructorProjection]
        exact Option.isSome_iff_exists.mpr ⟨cD, recordOf_recordsAt.mpr ⟨hSD, hE₀_E D cD hcD⟩⟩
  · -- Part 2: block member & constructor projections
    intro B c ms hB hms i m hm
    obtain ⟨hSB, hcE⟩ := recordOf_recordsAt.mp hB
    rcases hSB with hRB | hBasB | ⟨hTB, hSafeB⟩ | ⟨hIB, c₀, hc₀, hlog₀, -⟩ | ⟨B', hfam'⟩ |
        ⟨D, cD, msD, hcls, hcD, hmsD, iD, mD, hmD, hproj⟩
    · obtain ⟨cR, hcR⟩ := Option.isSome_iff_exists.mp hRB
      have e : cR = c := Option.some.inj ((hR_E B cR hcR).symm.trans hcE)
      subst e
      have h2 := hctx.shape.usedClosed.2 B cR ms hcR hms i m hm
      refine ⟨recordOf_recordsAt.mpr ⟨Or.inl (Option.isSome_iff_exists.mpr ⟨_, h2.1⟩),
        hR_E _ _ h2.1⟩, fun ind j hmind hj =>
        recordOf_recordsAt.mpr ⟨Or.inl (Option.isSome_iff_exists.mpr ⟨_, h2.2 ind hmind j hj⟩),
          hR_E _ _ (h2.2 ind hmind j hj)⟩⟩
    · obtain ⟨cBas, hcBas⟩ := Option.isSome_iff_exists.mp hBasB
      have e : cBas = c := Option.some.inj ((hBas_E B cBas hcBas).symm.trans hcE)
      subst e
      have h2 := StoreInhabit.store_usedClosed.2 B cBas ms hcBas hms i m hm
      refine ⟨recordOf_recordsAt.mpr ⟨Or.inr (Or.inl (Option.isSome_iff_exists.mpr ⟨_, h2.1⟩)),
        hBas_E _ _ h2.1⟩, fun ind j hmind hj =>
        recordOf_recordsAt.mpr ⟨Or.inr (Or.inl (Option.isSome_iff_exists.mpr ⟨_, h2.2 ind hmind j hj⟩)),
          hBas_E _ _ (h2.2 ind hmind j hj)⟩⟩
    · obtain ⟨c₀, hc₀⟩ := hG.record B hTB
      have e : c₀ = c := Option.some.inj ((hE₀_E B c₀ hc₀).symm.trans hcE)
      subst e
      exact mem_and_ctor_of B c₀ ms (Or.inl ⟨hTB, hSafeB⟩) hc₀ hms
        (hG.members B c₀ ms hTB hc₀ hms) i m hm
    · have e : c₀ = c := Option.some.inj ((hE₀_E B c₀ hc₀).symm.trans hcE)
      subst e
      exact mem_and_ctor_of B c₀ ms (Or.inr (Or.inl ⟨hIB, hlog₀⟩)) hc₀ hms
        (hFR.graph.innerMembers B c₀ ms hIB hc₀ hms) i m hm
    · obtain ⟨crb, rs, hF⟩ := hFR.graph.famRecord B' B hfam'
      have e : crb = c := Option.some.inj ((hE₀_E B crb hF.record).symm.trans hcE)
      subst e
      have ers : rs = ms := Ixon.ConstantInfo.muts.inj (hF.muts.symm.trans hms)
      subst ers
      refine mem_and_ctor_of B crb rs (Or.inr (Or.inr ⟨B', hfam'⟩)) hF.record hF.muts
        (fun k mk hmk => ⟨hF.members k mk hmk, fun ind _ hmind _ => ?_⟩) i m hm
      obtain ⟨rc', hrc'⟩ := hF.recrs mk (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hmk))
      rw [hmind] at hrc'; cases hrc'
    · exfalso
      have hproj_E : IsProj c := by
        rcases hcls with ⟨hTD, -⟩ | ⟨hID, -⟩ | ⟨B', hfamD⟩
        · have hmem := hG.members D cD msD hTD hcD hmsD iD mD hmD
          rcases hproj with rfl | ⟨ind, j, hmind, hj, rfl⟩
          · rw [Option.some.inj (hcE.symm.trans (hE₀_E _ _ hmem.1))]; exact memberProjection_isProj D iD mD
          · rw [Option.some.inj (hcE.symm.trans (hE₀_E _ _ (hmem.2 ind j hmind hj)))]
            exact constructorProjection_isProj D iD j
        · have hmem := hFR.graph.innerMembers D cD msD hID hcD hmsD iD mD hmD
          rcases hproj with rfl | ⟨ind, j, hmind, hj, rfl⟩
          · rw [Option.some.inj (hcE.symm.trans (hE₀_E _ _ hmem.1))]; exact memberProjection_isProj D iD mD
          · rw [Option.some.inj (hcE.symm.trans (hE₀_E _ _ (hmem.2 ind j hmind hj)))]
            exact constructorProjection_isProj D iD j
        · obtain ⟨crb, rs, hF⟩ := hFR.graph.famRecord B' D hfamD
          have e := Option.some.inj (hF.record.symm.trans hcD); subst e
          have ers := Ixon.ConstantInfo.muts.inj (hF.muts.symm.trans hmsD); subst ers
          rcases hproj with rfl | ⟨ind, j, hmind, -, -⟩
          · rw [Option.some.inj (hcE.symm.trans (hE₀_E _ _ (hF.members iD mD hmD)))]
            exact memberProjection_isProj D iD mD
          · obtain ⟨rc', hrc'⟩ := hF.recrs mD (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hmD))
            rw [hmind] at hrc'; cases hrc'
      exact proj_not_block hproj_E ⟨ms, hms⟩

private theorem typingUseStore_levels_and_params
    {calls : List (Call F)} {bAddrW bAddrIC : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    {R : Ixon.Env} {envT : Ix.Kernel.Env .anon} {E : Ixon.Env}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hWc : Claim.TopWalkCore calls bAddrW t seeds E₀ lim Top rank)
    (hG : TopGraph t E₀ seeds Top rank)
    (hFR : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hIC : InnerChecked calls bAddrIC t envT E₀ lim Top rank fam twin Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E)
    (hLP : StoreLevelsParams t R) :
    StoreLevelsOk t E₀ (Held (Binding.recordsAt E (TypingUseSet R E₀ Top Inner fam))) ∧
    StoreIndParamsOk E₀ (Held (Binding.recordsAt E (TypingUseSet R E₀ Top Inner fam))) := by
  let S := TypingUseSet R E₀ Top Inner fam
  let R_use := Binding.recordsAt E S
  have hb : Bounded calls := (hctx.good envT lim).2
  have hR_E : ∀ a c, recordOf R a = some c → recordOf E a = some c :=
    fun a c h => (recordOf_eq_recordAt_of_decoded hctx.recordsFor.1 a).trans (hctx.recordsFor.2.1 a c h)
  have hE₀_E : ∀ a c, recordOf E₀ a = some c → recordOf E a = some c :=
    fun a c h => (recordOf_eq_recordAt_of_decoded hctx.recordsFor.1 a).trans (hctx.runRecord a c h)
  have hBas_E : ∀ a c, recordOf StoreInhabit.basisStore a = some c → recordOf E a = some c :=
    fun a c h => (recordOf_eq_recordAt_of_decoded hctx.recordsFor.1 a).trans
      (recordAt_E_of_basisStore hctx.recordsFor h)
  have hagree : ∀ y c₁ c₂, recordOf R_use y = some c₁ → recordOf E₀ y = some c₂ → c₁ = c₂ :=
    fun y c₁ c₂ h1 h2 => Option.some.inj ((recordOf_recordsAt.mp h1).2.symm.trans (hE₀_E y c₂ h2))
  have hcl : UsedClosed R_use := typingUseStore_usedClosed hWc hG hFR hIC hctx
  refine storeLevelsOk_and_indParamsOk_of_units_agree hagree hcl ?_
  intro a c ha hc₀
  obtain ⟨cR, hcR⟩ := Option.isSome_iff_exists.mp ha
  have e : cR = c := hagree a cR c hcR hc₀
  subst e
  have hSa : S a := (recordOf_recordsAt.mp hcR).1
  rcases hSa with hRa | hBas | ⟨hTa, hSafe⟩ | ⟨hIa, c₀, hc', hlog₀, -⟩ | ⟨B', hfam'⟩ |
      ⟨D, cD, ms, hcls, hcD, hms, i, m, hm, hproj⟩
  · exact unitLevelsAndParamsOk_of_held_R hWc.runStore hb hctx.shape.usedClosed
      hR_E hE₀_E hctx.runBlob hLP hRa hc₀
  · obtain ⟨cBas, hcBas⟩ := Option.isSome_iff_exists.mp hBas
    have e' : cBas = cR := Option.some.inj ((hBas_E a cBas hcBas).symm.trans (hE₀_E a cR hc₀))
    subst e'
    exact unitLevelsAndParamsOk_of_basis hcBas
  · obtain ⟨c', hc', hchk⟩ := hWc.checked a hTa
    have e' : c' = cR := Option.some.inj (hc'.symm.trans hc₀)
    subst e'
    have hU : UnitCheckedAt calls bAddrW t E₀ a lim := by
      rcases hchk with ⟨ms, hms, hmem⟩ | h1
      · exact Or.inr ⟨c', ms, hc₀, hms, hmem⟩
      · exact Or.inl h1
    exact Binding.FamilyRecon.unitCheckedAt_unitLevelsAndParamsOk
      hWc.runStore hb hc₀ (hSafe c' hc₀).1 hU
  · have e' : c₀ = cR := Option.some.inj (hc'.symm.trans hc₀)
    subst e'
    cases htw : twin a with
    | none =>
      have hU : UnitCheckedAt calls bAddrIC t E₀ a lim := by
        rcases hIC.checked a c₀ hIa htw hc₀ with ⟨ms, hms, hmem⟩ | h1
        · exact Or.inr ⟨c₀, ms, hc₀, hms, hmem⟩
        · exact Or.inl h1
      exact Binding.FamilyRecon.unitCheckedAt_unitLevelsAndParamsOk
        hWc.runStore hb hc₀ hlog₀ hU
    | some B' =>
      obtain ⟨cT, rsT, hFT, -⟩ := hFR.graph.twinRecord a B' htw
      have eT : cT = c₀ := Option.some.inj (hFT.record.symm.trans hc₀)
      subst eT
      obtain ⟨bAddrFR, hCFR⟩ := hFR.checks
      obtain ⟨cs', hcall'⟩ := hCFR.twinCall a B' htw
      exact unitLevelsAndParamsOk_of_familyCall hWc.runStore hb hFT hcall'
  · obtain ⟨bAddrFR, -, hrecAt⟩ := hFR.famRecAt
    obtain ⟨rs', cs', hF, hcall'⟩ := hrecAt B' a cR hfam' hc₀
    exact unitLevelsAndParamsOk_of_familyCall hWc.runStore hb hF hcall'
  · have hproj_c : IsProj cR := by
      rcases hcls with ⟨hTD, -⟩ | ⟨hID, -⟩ | ⟨B', hfamD⟩
      · have hmem := hG.members D cD ms hTD hcD hms i m hm
        rcases hproj with rfl | ⟨ind, j, hmind, hj, rfl⟩
        · rw [Option.some.inj (hc₀.symm.trans hmem.1)]; exact memberProjection_isProj D i m
        · rw [Option.some.inj (hc₀.symm.trans (hmem.2 ind j hmind hj))]
          exact constructorProjection_isProj D i j
      · have hmem := hFR.graph.innerMembers D cD ms hID hcD hms i m hm
        rcases hproj with rfl | ⟨ind, j, hmind, hj, rfl⟩
        · rw [Option.some.inj (hc₀.symm.trans hmem.1)]; exact memberProjection_isProj D i m
        · rw [Option.some.inj (hc₀.symm.trans (hmem.2 ind j hmind hj))]
          exact constructorProjection_isProj D i j
      · obtain ⟨crb, rs, hF⟩ := hFR.graph.famRecord B' D hfamD
        have e := Option.some.inj (hF.record.symm.trans hcD); subst e
        have ers := Ixon.ConstantInfo.muts.inj (hF.muts.symm.trans hms); subst ers
        rcases hproj with rfl | ⟨ind, j, hmind, -, -⟩
        · rw [Option.some.inj (hc₀.symm.trans (hF.members i m hm))]; exact memberProjection_isProj D i m
        · obtain ⟨rc', hrc'⟩ := hF.recrs m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm))
          rw [hmind] at hrc'; cases hrc'
    exact unitLevelsAndParamsOk_of_nonUnit
      (fun d hd => by rcases hproj_c with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> (rw [hd] at h; cases h))
      (fun ms' hms' => proj_not_block hproj_c ⟨ms', hms'⟩)

/-- **`FamilyTwinRowFamWF` extended with `InnerChecked` and `StoreLevelsParams t R`**, matching the
context available in `FamilyStepsFamFull` (`ProducersClosed.lean`). -/
def FamilyTwinRowFamClosed (RFormS : Binding.StoredFormPred)
    (L : Ix.Kernel.Env .anon → Ix.Kernel.Semantics.NativeFam .anon → Prop) : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop)
      (bAddrIC : _root_.Address),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      InnerChecked calls bAddrIC t envT E₀ lim Top rank fam twin Inner →
      StepCtx.{u} calls t R envT E₀ E →
      Ix.Kernel.EnvWF envT →
      (∀ E', RecordsFor R E' →
        ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
          (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E' a = some c →
          Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E' B = some cb → cb.info = .muts ms →
          BlockStored t envT B ms) →
      StoreLevelsParams t R →
      ∀ famOf : _root_.Address → Option _root_.Address, StoredFamiliesRForm RFormS t R famOf →
      ∀ (A : _root_.Address) (c : Ixon.Constant) (B rb : _root_.Address) (crb : Ixon.Constant),
        Walked Top Inner A → recordOf E₀ A = some c → InLogic c → twin A = some B →
        ((fam B = some rb ∧ recordOf E₀ rb = some crb ∧
            RecBlock E₀ rb ∧ (RFormS t E₀ B A → RFormS t E₀ B rb)) ∨
          (fam B = none ∧ StoredTwinCanon t R envT famOf B rb crb)) →
        UnitStepTwin.{u} (fun env => FoldExtra.{u} L t E env ∧ FamilyRecsModeled t E₀ fam env)
          t envT E₀ E lim A c rb crb

/-- **Typing-half twin row `FamilyTwinRowFamClosed` from `StoredRecLvlsOk` alone**: completely
discharges `TwinCallFlat`, `TwinCallRecon`, and `GraphStoreClosed` via
`Binding.FamilyRecon.{familyFlat_of_call, familyForm_of_call}` and `graphStoreClosed_of_envWF`. -/
theorem familyTwinWF_of_storeLevels (hStoredLvls : StoredRecLvlsOk) :
    FamilyTwinRowFamClosed.{u} RFormS FormerOpenTraceAt := by
  intro calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner bAddrIC
    hFR hIC hctx hEnvWF hWhole hLP famOf hRF A c B rb crb hW hc hlog htw hcase
  obtain ⟨bAddrW, hWc, hG⟩ := hWalk
  have ht : t.check = .ok () := hWc.check_ok
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hb : Bounded calls := (hctx.good envT lim).2
  let S := TypingUseSet R E₀ Top Inner fam
  let R_use := Binding.recordsAt E S
  have hR_E : ∀ a d, recordOf R a = some d → recordOf E a = some d :=
    fun a d h => (recordOf_eq_recordAt_of_decoded hctx.recordsFor.1 a).trans (hctx.recordsFor.2.1 a d h)
  have hE₀_E : ∀ a d, recordOf E₀ a = some d → recordOf E a = some d :=
    fun a d h => (recordOf_eq_recordAt_of_decoded hctx.recordsFor.1 a).trans (hctx.runRecord a d h)
  have hagree : ∀ y c₁ c₂, recordOf R_use y = some c₁ → recordOf E₀ y = some c₂ → c₁ = c₂ :=
    fun y c₁ c₂ h1 h2 => Option.some.inj ((recordOf_recordsAt.mp h1).2.symm.trans (hE₀_E y c₂ h2))
  have hcl : UsedClosed R_use := typingUseStore_usedClosed hWc hG hFR hIC hctx
  obtain ⟨hlv, hpar⟩ := typingUseStore_levels_and_params hWc hG hFR hIC hctx hLP
  have hM : Binding.FamilyRecon.ModeledAnswers calls (Held R_use) (ReconView.ofStore t E₀) :=
    Binding.FamilyRecon.modeledAnswers_mono_S (fun _ _ => trivial)
      (Binding.FamilyRecon.modeledAnswers_of_stepStore hWc.runStore hWc.hashedStored hctx.toStepStore)
  have hRB : Held R_use B := by
    rcases hcase with ⟨hfam, -, -, -⟩ | ⟨-, hcanon⟩
    · have hTB : Top B := hFR.graph.famBlock B rb hfam
      obtain ⟨-, cb₀, hcb₀, hlogB, -⟩ := hFR.graph.famUnit B rb hfam
      obtain ⟨cb₁, ms₁, hcb₁, hms₁, -⟩ := hFR.famInd B rb hfam
      have e := Option.some.inj (hcb₁.symm.trans hcb₀); subst e
      have hSafeB : Claim.SourceSafe E₀ B := by
        intro cb' hcb'
        have e' := Option.some.inj (hcb'.symm.trans hcb₀); subst e'
        refine ⟨hlogB, fun cb₂ hcb₂ => ?_⟩
        have ho : Ix.Cert.ownerOf B cb₁ = B := by simp [Ix.Cert.ownerOf, hms₁]
        rw [ho] at hcb₂
        rw [Option.some.inj (hcb₂.symm.trans hcb₀)]; exact hlogB
      exact Option.isSome_iff_exists.mpr ⟨cb₁,
        recordOf_recordsAt.mpr ⟨Or.inr (Or.inr (Or.inl ⟨hTB, hSafeB⟩)), hE₀_E B cb₁ hcb₀⟩⟩
    · obtain ⟨cb, _, _, _, _, hFOB_R, -, -⟩ := hcanon.family
      exact Option.isSome_iff_exists.mpr ⟨cb,
        recordOf_recordsAt.mpr ⟨Or.inl (Option.isSome_iff_exists.mpr ⟨cb, hFOB_R.block.record⟩),
          hR_E B cb hFOB_R.block.record⟩⟩
  have hRr_of : ∀ {r cr} {rs : Array Ixon.MutConst}, (r = A ∨ fam B = some r) →
      FamRecRecord E₀ r cr rs → Held R_use r := by
    intro r cr rs hrel hRec
    have hnp : ¬ IsProj cr := fun hp => proj_not_block hp ⟨rs, hRec.muts⟩
    rcases hrel with rfl | hfamr
    · rcases hW with hTA | hIA
      · have hSafeA : Claim.SourceSafe E₀ A := by
          intro c' hc'
          have e' := Option.some.inj (hc'.symm.trans hRec.record); subst e'
          refine ⟨hRec.logic, fun cb₂ hcb₂ => ?_⟩
          have ho : Ix.Cert.ownerOf A cr = A := by simp [Ix.Cert.ownerOf, hRec.muts]
          rw [ho] at hcb₂
          rw [Option.some.inj (hcb₂.symm.trans hRec.record)]; exact hRec.logic
        exact Option.isSome_iff_exists.mpr ⟨cr,
          recordOf_recordsAt.mpr ⟨Or.inr (Or.inr (Or.inl ⟨hTA, hSafeA⟩)), hE₀_E A cr hRec.record⟩⟩
      · exact Option.isSome_iff_exists.mpr ⟨cr,
          recordOf_recordsAt.mpr ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨hIA, cr, hRec.record, hRec.logic, hnp⟩))),
            hE₀_E A cr hRec.record⟩⟩
    · exact Option.isSome_iff_exists.mpr ⟨cr,
        recordOf_recordsAt.mpr ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨B, hfamr⟩)))),
          hE₀_E r cr hRec.record⟩⟩
  have hrecRefs : ∀ {r cr} {rs : Array Ixon.MutConst}, (r = A ∨ fam B = some r) →
      FamRecRecord E₀ r cr rs →
      ∀ i ∈ usedRefIdxs cr, ∀ a, cr.refs[i]? = some a →
        Held R_use a ∨ a = r ∨ ∃ k m, rs[k]? = some m ∧ a = memberAddr r k m := by
    intro r cr rs hrel hRec i hi a ha
    obtain ⟨cr', hcr'⟩ := Option.isSome_iff_exists.mp (hRr_of hrel hRec)
    have e := hagree r cr' cr hcr' hRec.record
    subst e
    exact Or.inl ((hcl.1 r cr' hcr').2 i hi a ha)
  refine familyTwin_step_core hStoredLvls hWalk hFR hctx hRF hW hc hlog htw hcase ?_ ?_
    (fun _ hfam hrb => graphStoreClosed_of_envWF hWalk hFR hctx hEnvWF hWhole hfam hrb)
  · intro bAddr r cr rs cs hrel hRec hsz hlogB hfc
    obtain ⟨cb, ms, es, off, hFOB, hRF', hBD, hlvls, -⟩ :=
      Binding.FamilyRecon.familyFlat_of_call ht htwf hWc.runStore hWc.hashedStored hb
        hagree hcl hRB (hrecRefs hrel hRec) hlv hpar hM hRec hsz hlogB hfc
    exact ⟨cb, ms, es, off, hFOB, hRF', hBD, hlvls⟩
  · intro bAddr r cb cr ms rs cs hrel hB hRec hsz hfc
    have hlogB : ∀ cb', recordOf E₀ B = some cb' → InLogic cb' := by
      intro cb' hcb'
      rw [Option.some.inj (hcb'.symm.trans hB.record)]
      exact hB.logic
    obtain ⟨_, _, es, off, -, -, hBD, -, hct⟩ :=
      Binding.FamilyRecon.familyFlat_of_call ht htwf hWc.runStore hWc.hashedStored hb
        hagree hcl hRB (hrecRefs hrel hRec) hlv hpar hM hRec hsz hlogB hfc
    rcases Binding.FamilyRecon.familyForm_of_call ht htwf hWc.runStore hWc.hashedStored hb
        hagree hcl hRB (hrecRefs hrel hRec) hlv hpar hM hRec hsz hlogB hfc with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (recordWrapConsObs_of_recon hRec.record hRec.muts hBD hct h2)

end IxVM.Refinement.Typing.TwinFamily
