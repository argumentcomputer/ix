import IxVMRefinement.Decl.NativeRec
import IxVMRefinement.Obs.KernelCheck2
import IxVMRefinement.Obs.KernelCheck5
import IxVMRefinement.Obs.KernelCheck6

/-!
# Native One-Type Inductive Blocks with Recursor (`L5` Native Recursor Checker — Part 1)

Pure kernel/circuit-frame recursor correspondence lemmas and circuit refinement specifications
for `nat_none_mention`, `nat_rec_idx`, `nat_ctor`, `nat_minors`, `nat_former_tele`, and
`nat_ih_apps`.
-/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo RecRule Declaration)
open Ix.Kernel.Rules (Red DefEq Infer Annot)
open Ix.Kernel.Semantics (Judgements ConstantValCheckJ StructDomsJ FieldSortsJ
  SumIndRunJ SumCtorRunJ SumCtorsRunJ FormerReadJ
  NativeRecRunJ RecStoredJ NativeRecJ DeclNativeRunJ DeclNativeNoRecRunJ
  IndRoutesJ DeclRunJ letFree)
open Ix.Kernel.Model (rulesJ)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Section 1: Pure Kernel, Positivity-Index, and Circuit-Frame Recursor Helpers -/

theorem hasLooseBVarB_false_of_hasLooseBVar_false :
    ∀ (e : KExpr) (i : Nat), e.hasLooseBVar i = false → e.hasLooseBVarB i = false
  | .bvar j, i, h => by
    unfold Expr.hasLooseBVarB
    split
    · rfl
    · simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne] at h ⊢
      omega
  | .fvar _ _, i, _ | .sort _, i, _ | .const _ _, i, _ | .lit _, i, _ => by
    unfold Expr.hasLooseBVarB
    split <;> rfl
  | .app a b, i, h => by
    unfold Expr.hasLooseBVarB
    split
    · rfl
    · simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at h
      simp [hasLooseBVarB_false_of_hasLooseBVar_false a i h.1,
        hasLooseBVarB_false_of_hasLooseBVar_false b i h.2]
  | .lam ty bo _, i, h => by
    unfold Expr.hasLooseBVarB
    split
    · rfl
    · simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at h
      simp [hasLooseBVarB_false_of_hasLooseBVar_false ty i h.1,
        hasLooseBVarB_false_of_hasLooseBVar_false bo (i + 1) h.2]
  | .forallE ty bo _, i, h => by
    unfold Expr.hasLooseBVarB
    split
    · rfl
    · simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at h
      simp [hasLooseBVarB_false_of_hasLooseBVar_false ty i h.1,
        hasLooseBVarB_false_of_hasLooseBVar_false bo (i + 1) h.2]
  | .letE t v bo _, i, h => by
    unfold Expr.hasLooseBVarB
    split
    · rfl
    · simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at h
      simp [hasLooseBVarB_false_of_hasLooseBVar_false t i h.1.1,
        hasLooseBVarB_false_of_hasLooseBVar_false v i h.1.2,
        hasLooseBVarB_false_of_hasLooseBVar_false bo (i + 1) h.2]
  | .proj _ _ e, i, h => by
    unfold Expr.hasLooseBVarB
    split
    · rfl
    · simp only [Expr.hasLooseBVar] at h
      exact hasLooseBVarB_false_of_hasLooseBVar_false e i h

theorem ilp_hasLooseBVar (ks : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (i : Nat),
      (e.instantiateLevelParams ks us).hasLooseBVar i = e.hasLooseBVar i
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar _ _, _ => rfl
  | .app a b, i => by
    simp [Expr.instantiateLevelParams, Expr.hasLooseBVar,
      ilp_hasLooseBVar ks us a i, ilp_hasLooseBVar ks us b i]
  | .lam ty bo _, i => by
    simp [Expr.instantiateLevelParams, Expr.hasLooseBVar,
      ilp_hasLooseBVar ks us ty i, ilp_hasLooseBVar ks us bo (i + 1)]
  | .forallE ty bo _, i => by
    simp [Expr.instantiateLevelParams, Expr.hasLooseBVar,
      ilp_hasLooseBVar ks us ty i, ilp_hasLooseBVar ks us bo (i + 1)]
  | .letE t v bo _, i => by
    simp [Expr.instantiateLevelParams, Expr.hasLooseBVar,
      ilp_hasLooseBVar ks us t i, ilp_hasLooseBVar ks us v i,
      ilp_hasLooseBVar ks us bo (i + 1)]
  | .proj _ _ e, i => by
    simp [Expr.instantiateLevelParams, Expr.hasLooseBVar, ilp_hasLooseBVar ks us e i]

theorem ilp_mentionsConst (ks : List LevelParam) (us : List KLevel) (T : KKey) :
    ∀ (e : KExpr), (e.instantiateLevelParams ks us).mentionsConst T = e.mentionsConst T
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ ty => ilp_mentionsConst ks us T ty
  | .app a b => by
    simp [Expr.instantiateLevelParams, Expr.mentionsConst,
      ilp_mentionsConst ks us T a, ilp_mentionsConst ks us T b]
  | .lam ty bo _ => by
    simp [Expr.instantiateLevelParams, Expr.mentionsConst,
      ilp_mentionsConst ks us T ty, ilp_mentionsConst ks us T bo]
  | .forallE ty bo _ => by
    simp [Expr.instantiateLevelParams, Expr.mentionsConst,
      ilp_mentionsConst ks us T ty, ilp_mentionsConst ks us T bo]
  | .letE t v bo _ => by
    simp [Expr.instantiateLevelParams, Expr.mentionsConst,
      ilp_mentionsConst ks us T t, ilp_mentionsConst ks us T v,
      ilp_mentionsConst ks us T bo]
  | .proj _ _ e => by
    simp [Expr.instantiateLevelParams, Expr.mentionsConst, ilp_mentionsConst ks us T e]

theorem noProjAt_ilp (ks : List LevelParam) (us : List KLevel) (T : KKey) :
    ∀ (e : KExpr), noProjAt T (e.instantiateLevelParams ks us) = noProjAt T e
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ ty => noProjAt_ilp ks us T ty
  | .app a b => by
    simp [Expr.instantiateLevelParams, noProjAt, noProjAt_ilp ks us T a, noProjAt_ilp ks us T b]
  | .lam ty bo _ => by
    simp [Expr.instantiateLevelParams, noProjAt, noProjAt_ilp ks us T ty, noProjAt_ilp ks us T bo]
  | .forallE ty bo _ => by
    simp [Expr.instantiateLevelParams, noProjAt, noProjAt_ilp ks us T ty, noProjAt_ilp ks us T bo]
  | .letE t v bo _ => by
    simp [Expr.instantiateLevelParams, noProjAt, noProjAt_ilp ks us T t,
      noProjAt_ilp ks us T v, noProjAt_ilp ks us T bo]
  | .proj _ _ e => by
    simp [Expr.instantiateLevelParams, noProjAt, noProjAt_ilp ks us T e]

theorem noProjAt_stripPis_binder {T : KKey} :
    ∀ (n : Nat) {e body : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      noProjAt T e = true →
      e.stripPis n = some (bs, body) →
      (∀ i < n, noProjAt T (bs.getD i default).1 = true) ∧ noProjAt T body = true
  | 0, e, body, bs, hnp, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨_, rfl⟩ := hs
    exact ⟨(fun _ hi => nomatch hi), hnp⟩
  | m + 1, .forallE ty bo bi, body, bs, hnp, hs => by
    simp only [noProjAt, Bool.and_eq_true] at hnp
    rw [Expr.stripPis, Option.map_eq_some_iff] at hs
    obtain ⟨⟨bs', body'⟩, hs', hpair⟩ := hs
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    obtain ⟨hdoms, hbo⟩ := noProjAt_stripPis_binder m hnp.2 hs'
    refine ⟨fun i hi => ?_, hbo⟩
    cases i with
    | zero => exact hnp.1
    | succ i' => simpa [List.getD_cons_succ] using hdoms i' (by omega)
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs
  | _ + 1, .sort _, _, _, _, hs | _ + 1, .const _ _, _, _, _, hs
  | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs
  | _ + 1, .proj _ _ _, _, _, _, hs => nomatch hs

theorem structUsedLater_false_of_posOf_stripPis {rlps : List LevelParam} {cty₀ emid : KExpr}
    {ebs : List (KExpr × Ix.Kernel.BinderMeta)} {nP i : Nat} {cbs₀ : List (KExpr × Ix.Kernel.BinderMeta)}
    {cbody₀ : KExpr} (hs₀ : cty₀.stripPis (nP + i + 1) = some (cbs₀, cbody₀))
    (hsE : (posOf rlps cty₀).stripPis (nP + i + 1) = some (ebs, emid))
    (hno : emid.hasLooseBVar 0 = false) :
    Ix.Kernel.structUsedLater cty₀ nP i = false := by
  have hs_pos := ilp_stripPis rlps (posLevels rlps) (nP + i + 1) hs₀
  change (posOf rlps cty₀).stripPis (nP + i + 1) = _ at hs_pos
  rw [hsE] at hs_pos
  injection hs_pos with hp
  have hemid : emid = posOf rlps cbody₀ := (Prod.mk.inj hp).2
  rw [hemid] at hno
  unfold posOf at hno
  rw [ilp_hasLooseBVar] at hno
  simp [Ix.Kernel.structUsedLater, hs₀, hasLooseBVarB_false_of_hasLooseBVar_false cbody₀ 0 hno]

theorem recPositivity_ne_ordinary_of_mentions {T : KKey} {lps : List LevelParam}
    {nP nIdx o : Nat} :
    ∀ (dom : KExpr) (k : Nat),
      dom.mentionsConst T = true →
      Ix.Kernel.recPositivity T lps nP nIdx o dom k ≠ .ordinary
  | .forallE ty bo _, k, hmen => by
    simp only [Expr.mentionsConst, Bool.or_eq_true] at hmen
    unfold Ix.Kernel.recPositivity
    by_cases hty : ty.mentionsConst T = true
    · simp [hty]
    · have htyF : ty.mentionsConst T = false := Bool.eq_false_iff.mpr hty
      have hbo : bo.mentionsConst T = true := by
        rcases hmen with h1 | h2
        · exact absurd h1 hty
        · exact h2
      simpa [htyF] using recPositivity_ne_ordinary_of_mentions bo (k + 1) hbo
  | .bvar _, _, hmen | .sort _, _, hmen | .lit _, _, hmen =>
    nomatch hmen
  | .fvar idx ty, k, hmen => by
    unfold Ix.Kernel.recPositivity
    simp only [hmen, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> decide
  | .const nm us, k, hmen => by
    unfold Ix.Kernel.recPositivity
    simp only [hmen, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> decide
  | .app a b, k, hmen => by
    unfold Ix.Kernel.recPositivity
    simp only [hmen, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> decide
  | .lam _ _ _, k, hmen | .letE _ _ _ _, k, hmen | .proj _ _ _, k, hmen => by
    unfold Ix.Kernel.recPositivity
    simp only [hmen, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    (try split) <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem recFieldKind_rec_or_refl_iff_mentions {T : KKey} {lps : List LevelParam}
    {nP nIdx i : Nat} {dom : KExpr}
    (hpos : Ix.Kernel.recFieldKind T lps nP nIdx i dom ≠ .negative ∧
      Ix.Kernel.recFieldKind T lps nP nIdx i dom ≠ .unsupported) :
    (Ix.Kernel.recFieldKind T lps nP nIdx i dom == .recursive ||
      Ix.Kernel.recFieldKind T lps nP nIdx i dom == .reflexive) = dom.mentionsConst T := by
  cases hm : dom.mentionsConst T with
  | false =>
    simp [Ix.Kernel.recFieldKind, hm]
  | true =>
    have hne_ord : Ix.Kernel.recFieldKind T lps nP nIdx i dom ≠ .ordinary := by
      simp only [Ix.Kernel.recFieldKind, hm, ↓reduceIte]
      exact recPositivity_ne_ordinary_of_mentions dom 0 hm
    rcases hpos with ⟨hne_neg, hne_uns⟩
    cases hk : Ix.Kernel.recFieldKind T lps nP nIdx i dom with
    | ordinary => exact absurd hk hne_ord
    | recursive => rfl
    | reflexive => rfl
    | negative => exact absurd hk hne_neg
    | unsupported => exact absurd hk hne_uns

/-- Recursive field-index collector from field `i` upward, matching `KernelCheck::nat_rec_idx`. -/
def recIdxFrom (ecbs : List (KExpr × Ix.Kernel.BinderMeta)) (T : KKey) (nP nF i : Nat) :
    List Nat :=
  if _ : i < nF then
    let rest := recIdxFrom ecbs T nP nF (i + 1)
    if (ecbs.getD (nP + i) default).1.mentionsConst T then i :: rest else rest
  else []
termination_by nF - i

theorem recIdxFrom_ge {ecbs : List (KExpr × Ix.Kernel.BinderMeta)} {T : KKey} {nP nF i : Nat}
    (hge : nF ≤ i) : recIdxFrom ecbs T nP nF i = [] := by
  unfold recIdxFrom
  have hnot : ¬ i < nF := by omega
  simp [hnot]

theorem recIdxFrom_lt {ecbs : List (KExpr × Ix.Kernel.BinderMeta)} {T : KKey} {nP nF i : Nat}
    (hlt : i < nF) :
    recIdxFrom ecbs T nP nF i =
      if (ecbs.getD (nP + i) default).1.mentionsConst T then
        i :: recIdxFrom ecbs T nP nF (i + 1)
      else
        recIdxFrom ecbs T nP nF (i + 1) := by
  conv => lhs; unfold recIdxFrom
  simp [hlt]

theorem recIdxFrom_eq_filter_drop {ecbs : List (KExpr × Ix.Kernel.BinderMeta)} {T : KKey}
    {nP nF : Nat} :
    ∀ (rem i : Nat), i + rem = nF →
      recIdxFrom ecbs T nP nF i =
        ((List.range nF).drop i).filter (fun idx => (ecbs.getD (nP + idx) default).1.mentionsConst T)
  | 0, i, h => by
    subst h
    rw [recIdxFrom_ge (by omega)]
    simp [List.drop_eq_nil_of_le]
  | rem + 1, i, h => by
    have hlt : i < nF := by omega
    have hdrop : (List.range nF).drop i = i :: (List.range nF).drop (i + 1) := by
      have hi_len : i < (List.range nF).length := by simp [hlt]
      rw [← List.cons_getElem_drop_succ (h := hi_len)]
      simp
    rw [recIdxFrom_lt hlt, recIdxFrom_eq_filter_drop rem (i + 1) (by omega), hdrop, List.filter_cons]

theorem recIdxOf_eq_recIdxFrom {rlps : List LevelParam} {T : KKey} {lps : List LevelParam}
    {nP nIdx : Nat} {cA : KConstantVal × Nat} {ks : List Ix.Kernel.RecFieldKind}
    {cbs : List (KExpr × Ix.Kernel.BinderMeta)} {cbody : KExpr}
    {ecbs : List (KExpr × Ix.Kernel.BinderMeta)} {ebody : KExpr}
    (hck : Ix.Kernel.recCtorKinds T lps nP nIdx cA = some ks)
    (hok : ∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported)
    (hs₀ : cA.1.type.stripPis (nP + cA.2) = some (cbs, cbody))
    (hsE : (posOf rlps cA.1.type).stripPis (nP + cA.2) = some (ecbs, ebody)) :
    Ix.Kernel.recIdxOf ks = recIdxFrom ecbs T nP cA.2 0 := by
  rw [recIdxFrom_eq_filter_drop cA.2 0 (by omega), List.drop_zero]
  unfold Ix.Kernel.recCtorKinds at hck
  rw [hs₀] at hck
  dsimp only at hck
  have hs_pos := ilp_stripPis rlps (posLevels rlps) (nP + cA.2) hs₀
  change (posOf rlps cA.1.type).stripPis (nP + cA.2) = _ at hs_pos
  rw [hsE] at hs_pos
  injection hs_pos with hp
  have hecbs : ecbs = cbs.map (fun b => (posOf rlps b.1,
      { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw })) := (Prod.mk.inj hp).1
  have hlen_cbs : cbs.length = nP + cA.2 := stripPis_length (nP + cA.2) hs₀
  by_cases hret : (cbody.getAppArgs.drop nP).all (fun a => !a.mentionsConst T) = true
  · rw [ite_eq_left hret] at hck
    injection hck with hks
    have hks_eq : ks = (List.range cA.2).map (fun i =>
        match Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 with
        | .recursive => if Ix.Kernel.structUsedLater cA.1.type nP i then .unsupported else .recursive
        | .reflexive => if Ix.Kernel.structUsedLater cA.1.type nP i then .unsupported else .reflexive
        | k => k) := hks.symm
    have hks_len : ks.length = cA.2 := by
      rw [hks_eq, List.length_map, List.length_range]
    rw [Ix.Kernel.recIdxOf, hks_len]
    apply List.filter_congr
    intro idx hidx
    have hidx_lt : idx < cA.2 := List.mem_range.mp hidx
    let fk := Ix.Kernel.recFieldKind T lps nP nIdx idx (cbs.getD (nP + idx) default).1
    let k_at : Ix.Kernel.RecFieldKind :=
      match fk with
      | .recursive => if Ix.Kernel.structUsedLater cA.1.type nP idx then .unsupported else .recursive
      | .reflexive => if Ix.Kernel.structUsedLater cA.1.type nP idx then .unsupported else .reflexive
      | k => k
    have hget : ks.getD idx .ordinary = k_at := by
      rw [hks_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hidx_lt]
      rfl
    have hmem_k : k_at ∈ ks := by
      rw [hks_eq]
      exact List.mem_map.mpr ⟨idx, List.mem_range.mpr hidx_lt, rfl⟩
    obtain ⟨hne_neg, hne_uns⟩ := hok k_at hmem_k
    have hfk_ok : fk ≠ .negative ∧ fk ≠ .unsupported := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · apply hne_neg; dsimp only [k_at]; rw [h]
      · apply hne_uns; dsimp only [k_at]; rw [h]
    have hkat_eq : (k_at == .recursive || k_at == .reflexive) =
        (fk == .recursive || fk == .reflexive) := by
      dsimp only [k_at]
      cases hfk : fk with
      | ordinary => rfl
      | negative => exact absurd hfk hfk_ok.1
      | unsupported => exact absurd hfk hfk_ok.2
      | recursive =>
        cases hu : Ix.Kernel.structUsedLater cA.1.type nP idx
        · rfl
        · exfalso; apply hne_uns; dsimp only [k_at]; rw [hfk, hu]; rfl
      | reflexive =>
        cases hu : Ix.Kernel.structUsedLater cA.1.type nP idx
        · rfl
        · exfalso; apply hne_uns; dsimp only [k_at]; rw [hfk, hu]; rfl
    have hdom_ecbs : (ecbs.getD (nP + idx) default).1 = posOf rlps (cbs.getD (nP + idx) default).1 := by
      have hlt_all : nP + idx < cbs.length := by omega
      rw [hecbs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hlt_all]
      rfl
    rw [hget, hkat_eq, hdom_ecbs]
    unfold posOf
    rw [ilp_mentionsConst]
    exact recFieldKind_rec_or_refl_iff_mentions hfk_ok
  · rw [ite_eq_right hret] at hck
    injection hck with hks
    have hks_len : ks.length = cA.2 := by
      rw [← hks, List.length_map, List.length_map, List.length_range]
    cases h_c2 : cA.2 with
    | zero =>
      have hnil : ks = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      simp [Ix.Kernel.recIdxOf]
    | succ m =>
      exfalso
      have h0 : ks[0]? = some .negative := by
        rw [← hks, List.getElem?_map, List.getElem?_map, h_c2, List.getElem?_range (by omega)]
        rfl
      exact (hok .negative (List.mem_of_getElem? h0)).1 rfl

/-! ### `WrapRelSem` environment congruence across `CapsUpgradeAt` and `EnvExt` -/

theorem consumeWrapper_congr_defn {find₁ find₂ : KKey → Option (ConstantInfo .anon)}
    (hEq : ∀ w, Ix.Kernel.Semantics.wrapperArity find₁ w = Ix.Kernel.Semantics.wrapperArity find₂ w)
    (t : KExpr) :
    Ix.Kernel.Semantics.consumeWrapper find₁ t = Ix.Kernel.Semantics.consumeWrapper find₂ t := by
  unfold Ix.Kernel.Semantics.consumeWrapper
  cases t.getAppFn with
  | const w us =>
    cases t.getAppArgs with
    | nil => rfl
    | cons a rest => simp [hEq w]
  | _ => rfl

theorem WrapRelSem.congr_wrapperArity {find₁ find₂ : KKey → Option (ConstantInfo .anon)}
    (hEq : ∀ w, Ix.Kernel.Semantics.wrapperArity find₁ w = Ix.Kernel.Semantics.wrapperArity find₂ w)
    {g d : KExpr} (h : WrapRelSem find₁ g d) : WrapRelSem find₂ g d :=
  WrapRelSem.rec
    (motive_1 := fun g d _ => WrapRelSem find₂ g d)
    (motive_2 := fun t t' _ => WrapDomSem find₂ t t')
    (bvar := fun i => .bvar i)
    (fvar := fun _ ih => .fvar ih)
    (sort := fun hu => .sort hu)
    (const := fun hus => .const hus)
    (lit := fun l => .lit l)
    (app := fun _ _ ihf iha => .app ihf iha)
    (lam := fun hpw _ _ ihd ihb => .lam hpw ihd ihb)
    (forallE := fun hpw _ _ ihd ihb => .forallE hpw ihd ihb)
    (letE := fun _ _ _ iht ihv ihb => .letE iht ihv ihb)
    (proj := fun _ ihe => .proj ihe)
    (zeta := fun _ ihz => .zeta ihz)
    (keep := fun _ ihr => .keep ihr)
    (consume := fun hc _ ihd => .consume (by rwa [← consumeWrapper_congr_defn hEq]) ihd)
    h

theorem wrapperArity_eq_of_nonDefn_change {find₁ find₂ : KKey → Option (ConstantInfo .anon)}
    (h12 : ∀ w cv v hn, find₁ w = some (.defnInfo cv v hn) → find₂ w = some (.defnInfo cv v hn))
    (h21 : ∀ w cv v hn, find₂ w = some (.defnInfo cv v hn) → find₁ w = some (.defnInfo cv v hn))
    (w : KKey) :
    Ix.Kernel.Semantics.wrapperArity find₁ w = Ix.Kernel.Semantics.wrapperArity find₂ w := by
  unfold Ix.Kernel.Semantics.wrapperArity
  cases h₁ : find₁ w with
  | none =>
    cases h₂ : find₂ w with
    | none => rfl
    | some ci₂ =>
      cases ci₂ with
      | defnInfo cv v hn =>
        have := h21 w cv v hn h₂
        rw [h₁] at this
        exact nomatch this
      | axiomInfo _ | thmInfo _ _
      | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _ | projInfo _ => rfl
  | some ci₁ =>
    cases ci₁ with
    | defnInfo cv v hn =>
      rw [h12 w cv v hn h₁]
    | axiomInfo _ | thmInfo _ _
    | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _ | projInfo _ =>
      cases h₂ : find₂ w with
      | none => rfl
      | some ci₂ =>
        cases ci₂ with
        | defnInfo cv v hn =>
          have := h21 w cv v hn h₂
          rw [h₁] at this
          exact nomatch this
        | axiomInfo _ | thmInfo _ _
        | indInfo _ _ | ctorInfo _ _ _ | recInfo _ _ _ _ | projInfo _ => rfl

/-! ### Circuit-Frame Native Recursor Type & Rule RHS Generators (`cMinorsPis`, `cMinorsLams`, `cRecTy`, `cRuleRhs`) -/

def cMinorsPis (clvls : List KLevel) (nP : Nat) (pw : Ix.Kernel.PropWhen) :
    List (KKey × Nat × KExpr × List Nat) → Nat → KExpr → Option KExpr
  | [], _, body => some body
  | (C, nF, cty, recIdx) :: cs, o, body =>
    (cMinorTy C clvls nP nF o pw cty recIdx).bind fun mty =>
    (cMinorsPis clvls nP pw cs (o + 1) body).map fun rest =>
      .forallE mty rest { pw }

def cMinorsLams (clvls : List KLevel) (nP : Nat) (pw : Ix.Kernel.PropWhen) :
    List (KKey × Nat × KExpr × List Nat) → Nat → KExpr → Option KExpr
  | [], _, body => some body
  | (C, nF, cty, recIdx) :: cs, o, body =>
    (cMinorTy C clvls nP nF o pw cty recIdx).bind fun mty =>
    (cMinorsLams clvls nP pw cs (o + 1) body).map fun rest =>
      .lam mty rest { pw }

def cFamI (T : KKey) (clvls : List KLevel) (nP nIdx e o : Nat) : KExpr :=
  Expr.mkAppN (.const T clvls)
    (Ix.Kernel.structPsAt (o + e + nIdx) nP ++ Ix.Kernel.structPsAt o nIdx)

def cMotiveTyI (T : KKey) (clvls : List KLevel) (ℓ : KLevel) (nP nIdx : Nat)
    (itele : KExpr) : Option KExpr :=
  Expr.replacePisPw .never nIdx itele
    (.forallE (cFamI T clvls nP nIdx 0 0) (.sort ℓ) { pw := .never })

def cRecTy (T : KKey) (clvls : List KLevel) (ℓ : KLevel) (nP nIdx : Nat) (tty : KExpr)
    (ctors : List (KKey × Nat × KExpr × List Nat)) : Option KExpr :=
  let pw := Level.zeronessOf ℓ
  let n := ctors.length
  (tty.stripPis nP).bind fun q =>
  (cMotiveTyI T clvls ℓ nP nIdx q.2).bind fun motiveTy =>
  (Expr.replacePisPw pw nIdx (q.2.liftLooseBVars (n + 1) 0)
    (.forallE (cFamI T clvls nP nIdx (n + 1) 0)
      (Expr.mkAppN (.bvar (nIdx + n + 1))
        (Ix.Kernel.structPsAt 1 nIdx ++ [.bvar 0]))
      { pw })).bind fun major =>
  (cMinorsPis clvls nP pw ctors 1 major).bind fun minors =>
    Expr.replacePisPw pw nP tty (.forallE motiveTy minors { pw })

def cRuleRhs (T : KKey) (clvls : List KLevel) (ℓ : KLevel) (nP nIdx : Nat) (tty : KExpr)
    (ctors : List (KKey × Nat × KExpr × List Nat)) (recC : KKey) (rlvls : List KLevel)
    (j : Nat) : Option KExpr :=
  let pw := Level.zeronessOf ℓ
  let n := ctors.length
  ctors[j]?.bind fun (C, nF, cty, recIdx) =>
  (tty.stripPis nP).bind fun tq =>
  (cMotiveTyI T clvls ℓ nP nIdx tq.2).bind fun motiveTy =>
  (cty.stripPis nP).bind fun q =>
  (Expr.pisToLamsPw pw nF (q.2.liftLooseBVars (n + 1) 0)
    (Ix.Kernel.structRuleBodyR recC rlvls pw nP n nF j recIdx
      (Ix.Kernel.structFieldTeleOf cty nP nF)
      (Ix.Kernel.structFieldIdxOf cty nP nF))).bind fun inner =>
  (cMinorsLams clvls nP pw ctors 1 inner).bind fun minors =>
    Expr.pisToLamsPw pw nP tty (.lam motiveTy minors { pw })

theorem posOf_structMinorsPisR (rlps : List LevelParam) (lps : List LevelParam)
    (nP : Nat) (pw₀ : Ix.Kernel.PropWhen) :
    ∀ (ctors : List (KKey × Nat × KExpr × List Nat)) (o : Nat) (body₀ : KExpr),
      (∀ c ∈ ctors, (∃ cbs cbody, c.2.2.1.stripPis (nP + c.2.1) = some (cbs, cbody)) ∧
        ∀ i ∈ c.2.2.2, i < c.2.1) →
      (Ix.Kernel.structMinorsPisR lps nP pw₀ ctors o body₀).map (posOf rlps) =
        cMinorsPis ((lps.map .param).map (Level.subst rlps (posLevels rlps))) nP
          (Level.substPW rlps (posLevels rlps) pw₀)
          (ctors.map fun c => (c.1, c.2.1, posOf rlps c.2.2.1, c.2.2.2)) o (posOf rlps body₀)
  | [], _, body₀, _ => rfl
  | (C, nF, cty₀, recIdx) :: cs, o, body₀, hcs => by
    obtain ⟨hs_c, hrec_c⟩ := hcs (C, nF, cty₀, recIdx) List.mem_cons_self
    have hmty := posOf_structMinorTyR rlps C lps nP nF o pw₀ cty₀ recIdx hs_c hrec_c
    have hrest := posOf_structMinorsPisR rlps lps nP pw₀ cs (o + 1) body₀
      (fun c hc => hcs c (List.mem_cons_of_mem _ hc))
    simp only [Ix.Kernel.structMinorsPisR, cMinorsPis, List.map_cons]
    cases hm₀ : Ix.Kernel.structMinorTyR C lps nP nF o pw₀ cty₀ recIdx with
    | none =>
      rw [hm₀] at hmty
      simp only [Option.map_none] at hmty
      rw [← hmty]
      rfl
    | some mty₀ =>
      rw [hm₀, Option.map_some] at hmty
      rw [← hmty]
      simp only [Option.bind_some]
      cases hr₀ : Ix.Kernel.structMinorsPisR lps nP pw₀ cs (o + 1) body₀ with
      | none =>
        rw [hr₀, Option.map_none] at hrest
        rw [← hrest]
        rfl
      | some rest₀ =>
        rw [hr₀, Option.map_some] at hrest
        rw [← hrest]
        rfl

theorem posOf_structMinorsLamsR (rlps : List LevelParam) (lps : List LevelParam)
    (nP : Nat) (pw₀ : Ix.Kernel.PropWhen) :
    ∀ (ctors : List (KKey × Nat × KExpr × List Nat)) (o : Nat) (body₀ : KExpr),
      (∀ c ∈ ctors, (∃ cbs cbody, c.2.2.1.stripPis (nP + c.2.1) = some (cbs, cbody)) ∧
        ∀ i ∈ c.2.2.2, i < c.2.1) →
      (Ix.Kernel.structMinorsLamsR lps nP pw₀ ctors o body₀).map (posOf rlps) =
        cMinorsLams ((lps.map .param).map (Level.subst rlps (posLevels rlps))) nP
          (Level.substPW rlps (posLevels rlps) pw₀)
          (ctors.map fun c => (c.1, c.2.1, posOf rlps c.2.2.1, c.2.2.2)) o (posOf rlps body₀)
  | [], _, body₀, _ => rfl
  | (C, nF, cty₀, recIdx) :: cs, o, body₀, hcs => by
    obtain ⟨hs_c, hrec_c⟩ := hcs (C, nF, cty₀, recIdx) List.mem_cons_self
    have hmty := posOf_structMinorTyR rlps C lps nP nF o pw₀ cty₀ recIdx hs_c hrec_c
    have hrest := posOf_structMinorsLamsR rlps lps nP pw₀ cs (o + 1) body₀
      (fun c hc => hcs c (List.mem_cons_of_mem _ hc))
    simp only [Ix.Kernel.structMinorsLamsR, cMinorsLams, List.map_cons]
    cases hm₀ : Ix.Kernel.structMinorTyR C lps nP nF o pw₀ cty₀ recIdx with
    | none =>
      rw [hm₀] at hmty
      simp only [Option.map_none] at hmty
      rw [← hmty]
      rfl
    | some mty₀ =>
      rw [hm₀, Option.map_some] at hmty
      rw [← hmty]
      simp only [Option.bind_some]
      cases hr₀ : Ix.Kernel.structMinorsLamsR lps nP pw₀ cs (o + 1) body₀ with
      | none =>
        rw [hr₀, Option.map_none] at hrest
        rw [← hrest]
        rfl
      | some rest₀ =>
        rw [hr₀, Option.map_some] at hrest
        rw [← hrest]
        rfl

theorem posOf_structFamI (rlps lps : List LevelParam) (T : KKey) (nP nIdx e o : Nat) :
    posOf rlps (Ix.Kernel.structFamI T lps nP nIdx e o) =
      cFamI T ((lps.map .param).map (Level.subst rlps (posLevels rlps))) nP nIdx e o := by
  unfold posOf Ix.Kernel.structFamI cFamI
  rw [ilp_mkAppN, List.map_append, ilp_structPsAt, ilp_structPsAt]
  rfl

theorem substPW_elim_zeroness (k : Nat) (large : Bool) :
    let rlps := if large then k :: List.range k else List.range k
    let elim := if large then k else 0
    let ℓ_c := if large then Level.param 0 else Level.zero
    Level.subst rlps (posLevels rlps) (Ix.Kernel.structElimLevel elim large) = ℓ_c ∧
    Level.substPW rlps (posLevels rlps)
      (Level.zeronessOf (Ix.Kernel.structElimLevel elim large)) = Level.zeronessOf ℓ_c := by
  intro rlps elim ℓ_c
  suffices h1 : Level.subst rlps (posLevels rlps) (Ix.Kernel.structElimLevel elim large) = ℓ_c by
    exact ⟨h1, by rw [← Level.zeronessOf_subst, h1]⟩
  dsimp only [rlps, elim, ℓ_c]
  cases large with
  | false =>
    simp [Ix.Kernel.structElimLevel, Level.subst]
  | true =>
    have hpos : posLevels (k :: List.range k) =
        Level.param 0 :: (List.range k).map (fun i => Level.param (1 + i)) := by
      simp only [posLevels, List.length_cons, List.length_range, List.range_succ_eq_map,
        List.map_cons, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro x _
      simp [Nat.add_comm]
    simp [Ix.Kernel.structElimLevel, Level.subst, Level.subst.go, hpos]

theorem posOf_structMotiveTyI (rlps lps : List LevelParam) (T : KKey) (ℓ₀ ℓ_c : KLevel)
    (nP nIdx : Nat) (itele₀ : KExpr)
    (hℓ : Level.subst rlps (posLevels rlps) ℓ₀ = ℓ_c) :
    (Ix.Kernel.structMotiveTyI T lps nP nIdx ℓ₀ itele₀).map (posOf rlps) =
      cMotiveTyI T ((lps.map .param).map (Level.subst rlps (posLevels rlps))) ℓ_c nP nIdx
        (posOf rlps itele₀) := by
  unfold Ix.Kernel.structMotiveTyI cMotiveTyI posOf
  rw [option_map_ilp_replacePisPw]
  have hnever : Level.substPW rlps (posLevels rlps) .never = .never := rfl
  have hfam := posOf_structFamI rlps lps T nP nIdx 0 0
  unfold posOf at hfam
  rw [hnever]
  congr 1
  simp only [Expr.instantiateLevelParams, hfam, hℓ]
  rfl

theorem posOf_structRecTyR (k : Nat) (large : Bool) (T : KKey) (nP nIdx : Nat) (tty₀ : KExpr)
    (ctors₀ : List (KKey × Nat × KExpr × List Nat))
    (htty : ∃ tbs tsort, tty₀.stripPis (nP + nIdx) = some (tbs, tsort))
    (hcs : ∀ c ∈ ctors₀, (∃ cbs cbody, c.2.2.1.stripPis (nP + c.2.1) = some (cbs, cbody)) ∧
      ∀ i ∈ c.2.2.2, i < c.2.1) :
    let lps := List.range k
    let rlps := if large then k :: List.range k else List.range k
    let elim := if large then k else 0
    let ℓ_c := if large then Level.param 0 else Level.zero
    let clvls := ((lps.map .param).map (Level.subst rlps (posLevels rlps)))
    (Ix.Kernel.structRecTyR T lps elim large nP nIdx tty₀ ctors₀).map (posOf rlps) =
      cRecTy T clvls ℓ_c nP nIdx (posOf rlps tty₀)
        (ctors₀.map fun c => (c.1, c.2.1, posOf rlps c.2.2.1, c.2.2.2)) := by
  intro lps rlps elim ℓ_c clvls
  dsimp only [lps, rlps, elim, ℓ_c, clvls]
  obtain ⟨hℓ_eq, hpw_eq⟩ := substPW_elim_zeroness k large
  obtain ⟨tbs, tsort, hsT⟩ := htty
  obtain ⟨tbsP, itele₀, tbsI, hsTP, _, _, _⟩ := stripPis_split nP nIdx hsT
  have hmotive := posOf_structMotiveTyI (if large then k :: List.range k else List.range k)
    (List.range k) T (Ix.Kernel.structElimLevel (if large then k else 0) large)
    (if large then Level.param 0 else Level.zero) nP nIdx itele₀ hℓ_eq
  unfold Ix.Kernel.structRecTyR cRecTy
  dsimp only
  have hsTP_pos := ilp_stripPis (if large then k :: List.range k else List.range k)
    (posLevels (if large then k :: List.range k else List.range k)) nP hsTP
  change (posOf (if large then k :: List.range k else List.range k) tty₀).stripPis nP =
    some (_, posOf (if large then k :: List.range k else List.range k) itele₀) at hsTP_pos
  rw [hsTP, hsTP_pos]
  simp only [Option.bind_eq_bind, Option.bind, List.length_map]
  cases hmot₀ :
      Ix.Kernel.structMotiveTyI T (List.range k) nP nIdx
        (Ix.Kernel.structElimLevel (if large then k else 0) large) itele₀ with
  | none =>
    rw [hmot₀, Option.map_none] at hmotive
    rw [← hmotive]
    rfl
  | some motive₀ =>
    rw [hmot₀, Option.map_some] at hmotive
    rw [← hmotive]
    simp only [Option.bind_eq_bind, Option.bind]
    have hmaj_eq :
        (Expr.replacePisPw
          (Level.zeronessOf (Ix.Kernel.structElimLevel (if large then k else 0) large)) nIdx
          (itele₀.liftLooseBVars (ctors₀.length + 1) 0)
          (.forallE (Ix.Kernel.structFamI T (List.range k) nP nIdx (ctors₀.length + 1) 0)
            (Expr.mkAppN (.bvar (nIdx + ctors₀.length + 1))
              (Ix.Kernel.structPsAt 1 nIdx ++ [.bvar 0]))
            { pw := Level.zeronessOf
                (Ix.Kernel.structElimLevel (if large then k else 0) large) })).map
          (posOf (if large then k :: List.range k else List.range k)) =
        Expr.replacePisPw (Level.zeronessOf (if large then Level.param 0 else Level.zero)) nIdx
          ((posOf (if large then k :: List.range k else List.range k) itele₀).liftLooseBVars
            (ctors₀.length + 1) 0)
          (.forallE
            (cFamI T (((List.range k).map .param).map
              (Level.subst (if large then k :: List.range k else List.range k)
                (posLevels (if large then k :: List.range k else List.range k))))
              nP nIdx (ctors₀.length + 1) 0)
            (Expr.mkAppN (.bvar (nIdx + ctors₀.length + 1))
              (Ix.Kernel.structPsAt 1 nIdx ++ [.bvar 0]))
            { pw := Level.zeronessOf (if large then Level.param 0 else Level.zero) }) := by
      unfold posOf
      rw [option_map_ilp_replacePisPw, hpw_eq, ilp_liftLooseBVars]
      congr 1
      have hfam := posOf_structFamI (if large then k :: List.range k else List.range k)
        (List.range k) T nP nIdx (ctors₀.length + 1) 0
      unfold posOf at hfam
      simp only [Expr.instantiateLevelParams, hfam, hpw_eq, ilp_mkAppN, List.map_append,
        ilp_structPsAt, List.map_cons, List.map_nil]
    cases hmaj₀ :
        Expr.replacePisPw
          (Level.zeronessOf (Ix.Kernel.structElimLevel (if large then k else 0) large)) nIdx
          (itele₀.liftLooseBVars (ctors₀.length + 1) 0)
          (.forallE (Ix.Kernel.structFamI T (List.range k) nP nIdx (ctors₀.length + 1) 0)
            (Expr.mkAppN (.bvar (nIdx + ctors₀.length + 1))
              (Ix.Kernel.structPsAt 1 nIdx ++ [.bvar 0]))
            { pw := Level.zeronessOf
                (Ix.Kernel.structElimLevel (if large then k else 0) large) }) with
    | none =>
      rw [hmaj₀, Option.map_none] at hmaj_eq
      rw [← hmaj_eq]
      rfl
    | some major₀ =>
      rw [hmaj₀, Option.map_some] at hmaj_eq
      rw [← hmaj_eq]
      simp only [Option.bind_eq_bind, Option.bind]
      have hmin_eq := posOf_structMinorsPisR
        (if large then k :: List.range k else List.range k) (List.range k) nP
        (Level.zeronessOf (Ix.Kernel.structElimLevel (if large then k else 0) large))
        ctors₀ 1 major₀ hcs
      rw [hpw_eq] at hmin_eq
      cases hmin₀ :
          Ix.Kernel.structMinorsPisR (List.range k) nP
            (Level.zeronessOf (Ix.Kernel.structElimLevel (if large then k else 0) large))
            ctors₀ 1 major₀ with
      | none =>
        rw [hmin₀, Option.map_none] at hmin_eq
        rw [← hmin_eq]
        rfl
      | some minors₀ =>
        rw [hmin₀, Option.map_some] at hmin_eq
        rw [← hmin_eq]
        simp only [Option.bind_eq_bind, Option.bind]
        unfold posOf
        rw [option_map_ilp_replacePisPw, hpw_eq]
        simp only [Expr.instantiateLevelParams, hpw_eq]

theorem posOf_structRuleBodyR (rlps : List LevelParam) (recC : KKey) (rlvls₀ : List KLevel)
    (pw₀ : Ix.Kernel.PropWhen) (nP n nF j : Nat) (recIdx : List Nat) (cty₀ : KExpr)
    (hs : ∃ cbs cbody, cty₀.stripPis (nP + nF) = some (cbs, cbody))
    (hrec : ∀ i ∈ recIdx, i < nF) :
    posOf rlps
      (Ix.Kernel.structRuleBodyR recC rlvls₀ pw₀ nP n nF j recIdx
        (Ix.Kernel.structFieldTeleOf cty₀ nP nF)
        (Ix.Kernel.structFieldIdxOf cty₀ nP nF)) =
      Ix.Kernel.structRuleBodyR recC (rlvls₀.map (Level.subst rlps (posLevels rlps)))
        (Level.substPW rlps (posLevels rlps) pw₀) nP n nF j recIdx
        (Ix.Kernel.structFieldTeleOf (posOf rlps cty₀) nP nF)
        (Ix.Kernel.structFieldIdxOf (posOf rlps cty₀) nP nF) := by
  obtain ⟨cbs, cbody, hstrip_all⟩ := hs
  obtain ⟨bsP, _, bsF, hstripP, hstripF, rfl, _⟩ := stripPis_split nP nF hstrip_all
  have hlenP : bsP.length = nP := stripPis_length nP hstripP
  have hlenF : bsF.length = nF := stripPis_length nF hstripF
  unfold posOf Ix.Kernel.structRuleBodyR
  rw [ilp_mkAppN, List.map_append, List.map_map, List.map_map]
  simp only [Expr.instantiateLevelParams]
  refine congrArg (Expr.mkAppN _) (congrArg₂ (· ++ ·) rfl ?_)
  apply List.map_congr_left
  intro i hi
  have hlt_i : nP + i < (bsP ++ bsF).length := by
    rw [List.length_append, hlenP, hlenF]; have := hrec i hi; omega
  have hft := ilp_structFieldTeleOf rlps (posLevels rlps) cty₀ nP nF i ⟨_, _, hstrip_all, hlt_i⟩
  have hfi := ilp_structFieldIdxOf rlps (posLevels rlps) cty₀ nP nF i ⟨_, _, hstrip_all, hlt_i⟩
  simp only [Function.comp_def, Ix.Kernel.structIhApp]
  rw [ilp_mkLamsOf, ilp_mkAppN, List.map_append, List.map_append,
    List.map_cons, List.map_nil, ilp_mkAppN]
  have hpref :
      (Ix.Kernel.structRecPrefixAt (md := .anon) nP n nF
        (Ix.Kernel.structFieldTeleOf cty₀ nP nF i).length).map
        (Expr.instantiateLevelParams rlps (posLevels rlps)) =
      Ix.Kernel.structRecPrefixAt nP n nF
        (Ix.Kernel.structFieldTeleOf (posOf rlps cty₀) nP nF i).length := by
    unfold Ix.Kernel.structRecPrefixAt posOf
    rw [hft, List.length_map, List.map_append, List.map_append, ilp_structPsAt,
      List.map_cons, List.map_nil, List.map_map]
    rfl
  have hvars :
      (Ix.Kernel.structTeleVars (md := .anon)
        (Ix.Kernel.structFieldTeleOf cty₀ nP nF i).length).map
        (Expr.instantiateLevelParams rlps (posLevels rlps)) =
      Ix.Kernel.structTeleVars
        (Ix.Kernel.structFieldTeleOf (posOf rlps cty₀) nP nF i).length := by
    unfold Ix.Kernel.structTeleVars posOf
    rw [hft, List.length_map, List.map_map]
    rfl
  have hidx_map :
      ((Ix.Kernel.structFieldIdxOf cty₀ nP nF i).map
        (Ix.Kernel.structIdxAt nF (n + 1) i 0
          (Ix.Kernel.structFieldTeleOf cty₀ nP nF i).length)).map
        (Expr.instantiateLevelParams rlps (posLevels rlps)) =
      (Ix.Kernel.structFieldIdxOf (posOf rlps cty₀) nP nF i).map
        (Ix.Kernel.structIdxAt nF (n + 1) i 0
          (Ix.Kernel.structFieldTeleOf (posOf rlps cty₀) nP nF i).length) := by
    unfold posOf
    rw [hft, hfi, List.length_map, List.map_map, List.map_map]
    apply List.map_congr_left
    intro e _
    simp [Function.comp_def, ilp_structIdxAt]
  have htele_eq :
      (Ix.Kernel.structTeleAt nF (n + 1) i 0 pw₀
        (Ix.Kernel.structFieldTeleOf cty₀ nP nF i)).map
        (fun b => (b.1.instantiateLevelParams rlps (posLevels rlps),
          { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw })) =
      Ix.Kernel.structTeleAt nF (n + 1) i 0 (Level.substPW rlps (posLevels rlps) pw₀)
        (Ix.Kernel.structFieldTeleOf (posOf rlps cty₀) nP nF i) := by
    unfold posOf
    rw [ilp_structTeleAt, ← hft]
  rw [htele_eq, hpref, hidx_map, hvars]
  unfold posOf
  rw [hft, List.length_map]
  simp only [Expr.instantiateLevelParams]

theorem posOf_structRecRhsR (k : Nat) (large : Bool) (T : KKey) (nP nIdx : Nat) (tty₀ : KExpr)
    (ctors₀ : List (KKey × Nat × KExpr × List Nat)) (recC : KKey) (j : Nat)
    (hj : j < ctors₀.length)
    (htty : ∃ tbs tsort, tty₀.stripPis (nP + nIdx) = some (tbs, tsort))
    (hcs : ∀ c ∈ ctors₀, (∃ cbs cbody, c.2.2.1.stripPis (nP + c.2.1) = some (cbs, cbody)) ∧
      ∀ i ∈ c.2.2.2, i < c.2.1) :
    let lps := List.range k
    let rlps := if large then k :: List.range k else List.range k
    let elim := if large then k else 0
    let ℓ_c := if large then Level.param 0 else Level.zero
    let clvls := ((lps.map .param).map (Level.subst rlps (posLevels rlps)))
    let rlvls_c := ((rlps.map .param).map (Level.subst rlps (posLevels rlps)))
    (Ix.Kernel.structRecRhsR T lps elim large nP nIdx tty₀ ctors₀ recC (rlps.map .param) j).map
        (posOf rlps) =
      cRuleRhs T clvls ℓ_c nP nIdx (posOf rlps tty₀)
        (ctors₀.map fun c => (c.1, c.2.1, posOf rlps c.2.2.1, c.2.2.2))
        recC rlvls_c j := by
  intro lps rlps elim ℓ_c clvls rlvls_c
  dsimp only [lps, rlps, elim, ℓ_c, clvls, rlvls_c]
  obtain ⟨hℓ_eq, hpw_eq⟩ := substPW_elim_zeroness k large
  obtain ⟨tbs, tsort, hsT⟩ := htty
  obtain ⟨tbsP, itele₀, _, hsTP, _, _, _⟩ := stripPis_split nP nIdx hsT
  have hmotive := posOf_structMotiveTyI (if large then k :: List.range k else List.range k)
    (List.range k) T (Ix.Kernel.structElimLevel (if large then k else 0) large)
    (if large then Level.param 0 else Level.zero) nP nIdx itele₀ hℓ_eq
  rcases hget_j : ctors₀[j]'hj with ⟨C, nF, cty₀, recIdx⟩
  have hcj : ctors₀[j]? = some (C, nF, cty₀, recIdx) := by
    rw [List.getElem?_eq_getElem hj, hget_j]
  have hcj_map :
      (ctors₀.map fun c =>
        (c.1, c.2.1, posOf (if large then k :: List.range k else List.range k) c.2.2.1, c.2.2.2))[j]? =
        some (C, nF, posOf (if large then k :: List.range k else List.range k) cty₀, recIdx) := by
    simp [List.getElem?_map, hcj]
  obtain ⟨⟨cbs, cbody, hsC⟩, hrec_c⟩ := hcs (C, nF, cty₀, recIdx) (List.mem_of_getElem? hcj)
  obtain ⟨cbsP, crest₀, _, hsCP, _, _, _⟩ := stripPis_split nP nF hsC
  have hsTP_pos := ilp_stripPis (if large then k :: List.range k else List.range k)
    (posLevels (if large then k :: List.range k else List.range k)) nP hsTP
  have hsCP_pos := ilp_stripPis (if large then k :: List.range k else List.range k)
    (posLevels (if large then k :: List.range k else List.range k)) nP hsCP
  change (posOf (if large then k :: List.range k else List.range k) tty₀).stripPis nP =
    some (_, posOf (if large then k :: List.range k else List.range k) itele₀) at hsTP_pos
  change (posOf (if large then k :: List.range k else List.range k) cty₀).stripPis nP =
    some (_, posOf (if large then k :: List.range k else List.range k) crest₀) at hsCP_pos
  unfold Ix.Kernel.structRecRhsR cRuleRhs
  dsimp only
  rw [hcj, hcj_map]
  simp only [Option.bind_eq_bind, Option.bind, List.length_map]
  rw [hsTP, hsTP_pos]
  simp only [Option.bind_eq_bind, Option.bind]
  cases hmot₀ :
      Ix.Kernel.structMotiveTyI T (List.range k) nP nIdx
        (Ix.Kernel.structElimLevel (if large then k else 0) large) itele₀ with
  | none =>
    rw [hmot₀, Option.map_none] at hmotive
    rw [← hmotive]
    rfl
  | some motive₀ =>
    rw [hmot₀, Option.map_some] at hmotive
    rw [← hmotive]
    simp only [Option.bind_eq_bind, Option.bind]
    rw [hsCP, hsCP_pos]
    simp only [Option.bind_eq_bind, Option.bind]
    have hbody_pos := posOf_structRuleBodyR
      (if large then k :: List.range k else List.range k) recC
      ((if large then k :: List.range k else List.range k).map .param)
      (Level.zeronessOf (Ix.Kernel.structElimLevel (if large then k else 0) large))
      nP ctors₀.length nF j recIdx cty₀ ⟨cbs, cbody, hsC⟩ hrec_c
    rw [hpw_eq] at hbody_pos
    have hinner_eq :
        (Expr.pisToLamsPw
          (Level.zeronessOf (Ix.Kernel.structElimLevel (if large then k else 0) large)) nF
          (crest₀.liftLooseBVars (ctors₀.length + 1) 0)
          (Ix.Kernel.structRuleBodyR recC
            ((if large then k :: List.range k else List.range k).map .param)
            (Level.zeronessOf (Ix.Kernel.structElimLevel (if large then k else 0) large))
            nP ctors₀.length nF j recIdx
            (Ix.Kernel.structFieldTeleOf cty₀ nP nF)
            (Ix.Kernel.structFieldIdxOf cty₀ nP nF))).map
          (posOf (if large then k :: List.range k else List.range k)) =
        Expr.pisToLamsPw (Level.zeronessOf (if large then Level.param 0 else Level.zero)) nF
          ((posOf (if large then k :: List.range k else List.range k) crest₀).liftLooseBVars
            (ctors₀.length + 1) 0)
          (Ix.Kernel.structRuleBodyR recC
            (((if large then k :: List.range k else List.range k).map .param).map
              (Level.subst (if large then k :: List.range k else List.range k)
                (posLevels (if large then k :: List.range k else List.range k))))
            (Level.zeronessOf (if large then Level.param 0 else Level.zero))
            nP ctors₀.length nF j recIdx
            (Ix.Kernel.structFieldTeleOf
              (posOf (if large then k :: List.range k else List.range k) cty₀) nP nF)
            (Ix.Kernel.structFieldIdxOf
              (posOf (if large then k :: List.range k else List.range k) cty₀) nP nF)) := by
      rw [← hbody_pos]
      unfold posOf
      rw [option_map_ilp_pisToLamsPw, hpw_eq, ilp_liftLooseBVars]
    cases hin₀ :
        Expr.pisToLamsPw
          (Level.zeronessOf (Ix.Kernel.structElimLevel (if large then k else 0) large)) nF
          (crest₀.liftLooseBVars (ctors₀.length + 1) 0)
          (Ix.Kernel.structRuleBodyR recC
            ((if large then k :: List.range k else List.range k).map .param)
            (Level.zeronessOf (Ix.Kernel.structElimLevel (if large then k else 0) large))
            nP ctors₀.length nF j recIdx
            (Ix.Kernel.structFieldTeleOf cty₀ nP nF)
            (Ix.Kernel.structFieldIdxOf cty₀ nP nF)) with
    | none =>
      rw [hin₀, Option.map_none] at hinner_eq
      rw [← hinner_eq]
      rfl
    | some inner₀ =>
      rw [hin₀, Option.map_some] at hinner_eq
      rw [← hinner_eq]
      simp only [Option.bind_eq_bind, Option.bind]
      have hmin_eq := posOf_structMinorsLamsR
        (if large then k :: List.range k else List.range k) (List.range k) nP
        (Level.zeronessOf (Ix.Kernel.structElimLevel (if large then k else 0) large))
        ctors₀ 1 inner₀ hcs
      rw [hpw_eq] at hmin_eq
      cases hmin₀ :
          Ix.Kernel.structMinorsLamsR (List.range k) nP
            (Level.zeronessOf (Ix.Kernel.structElimLevel (if large then k else 0) large))
            ctors₀ 1 inner₀ with
      | none =>
        rw [hmin₀, Option.map_none] at hmin_eq
        rw [← hmin_eq]
        rfl
      | some minors₀ =>
        rw [hmin₀, Option.map_some] at hmin_eq
        rw [← hmin_eq]
        simp only [Option.bind_eq_bind, Option.bind]
        unfold posOf
        rw [option_map_ilp_pisToLamsPw, hpw_eq]
        simp only [Expr.instantiateLevelParams, hpw_eq]

theorem checkNativeRules_ok_go {envR : Ix.Kernel.Env .anon} {rlps lps : List LevelParam}
    {T recC : KKey} {elim : LevelParam} {large : Bool} {nP nIdx : Nat} {tty : KExpr}
    {ctors : List (KKey × Nat × KExpr × List Nat)}
    (hlps_sub : ∀ x ∈ lps, x ∈ rlps)
    (helim : large = true → elim ∈ rlps)
    (hT_res : (envR.find? T).isSome = true)
    (hT_not_defn : ∀ cv v hn, envR.find? T ≠ some (.defnInfo cv v hn))
    (hR_res : (envR.find? recC).isSome = true)
    (hR_not_defn : ∀ cv v hn, envR.find? recC ≠ some (.defnInfo cv v hn))
    (htty_sc : GenScoped envR rlps 0 tty)
    (htty_st : ∃ tbs tsort, tty.stripPis (nP + nIdx) = some (tbs, tsort))
    (hcs : ∀ c ∈ ctors, (envR.find? c.1).isSome = true ∧
      (∀ cv v hn, envR.find? c.1 ≠ some (.defnInfo cv v hn)) ∧
      GenScoped envR rlps 0 c.2.2.1 ∧
      (∀ i ∈ c.2.2.2, i < c.2.1) ∧
      ∃ cbs cbody, c.2.2.1.stripPis (nP + c.2.1) = some (cbs, cbody)) :
    ∀ (rem j : Nat),
      j + rem = ctors.length →
      ∃ rhsG,
        Ix.Kernel.checkNativeRules (m := Ix.Kernel.CheckM .anon)
          envR rlps T lps elim large nP nIdx tty ctors recC (rlps.map .param) rem j = .ok rhsG ∧
        rhsG.length = rem ∧
        ∀ t < rem, ∃ rhs,
          rhsG[t]? = some rhs ∧
          Ix.Kernel.structRecRhsR T lps elim large nP nIdx tty ctors recC
            (rlps.map .param) (j + t) = some rhs ∧
          GenScoped envR rlps 0 rhs
  | 0, _, _ =>
    ⟨[], rfl, rfl, fun _ ht => nomatch ht⟩
  | rem + 1, j, hjr => by
    have hj_lt : j < ctors.length := by omega
    obtain ⟨rhs, hrhs⟩ := structRecRhsR_exists T lps elim large nP nIdx tty ctors recC
      (rlps.map .param) j hj_lt htty_st (fun c hc => (hcs c hc).2.2.2.2)
    have hsc_rhs : GenScoped envR rlps 0 rhs :=
      GenScoped.structRecRhsR hlps_sub helim hT_res hT_not_defn hR_res hR_not_defn
        htty_sc hcs hj_lt hrhs
    obtain ⟨rest, hrest_ok, hrest_len, hrest_get⟩ :=
      checkNativeRules_ok_go hlps_sub helim hT_res hT_not_defn hR_res hR_not_defn
        htty_sc htty_st hcs rem (j + 1) (by omega)
    have hguard : (rhs.allLevelParamsDefined rlps && rhs.constsResolve envR &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar) = true := by
      simp [hsc_rhs.2.1, hsc_rhs.2.2.1, hsc_rhs.1, hsc_rhs.2.2.2.1]
    refine ⟨rhs :: rest, ?_, by simp [hrest_len], fun t ht => ?_⟩
    · unfold Ix.Kernel.checkNativeRules
      rw [hrhs]
      show (do
        unless (rhs.allLevelParamsDefined rlps && rhs.constsResolve envR &&
            rhs.looseBVarsBounded 0 && !rhs.hasFvar) = true do throw _
        let rest' ← Ix.Kernel.checkNativeRules (m := Ix.Kernel.CheckM .anon)
          envR rlps T lps elim large nP nIdx tty ctors recC (rlps.map .param) rem (j + 1)
        pure (rhs :: rest') : Ix.Kernel.CheckM .anon _) = .ok (rhs :: rest)
      dsimp only
      rw [ite_eq_left hguard, hrest_ok]
      rfl
    · cases t with
      | zero =>
        rw [Nat.add_zero]
        exact ⟨rhs, rfl, hrhs, hsc_rhs⟩
      | succ t' =>
        obtain ⟨rhs', hg', hr', hsc'⟩ := hrest_get t' (by omega)
        rw [show j + 1 + t' = j + (t' + 1) by omega] at hr'
        exact ⟨rhs', hg', hr', hsc'⟩

/-! ## Section 2: Native Recursor Circuit Specifications (`nat_none_mention`..`nat_ih_apps`) -/

theorem kexpr_list_concat_spec' {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {xs ys : List KExpr} {l₁ l₂ r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::concat<&KernelTypes::KExprNode>» [l₁, l₂] h r h' cs)
    (h₁ : RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h xs l₁)
    (h₂ : RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h ys l₂) :
    RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h' (xs ++ ys) r := by
  have ev' : ObsFn W (Instance.mk "Lists::concat" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      [l₁, l₂] h r h' cs := by
    rw [Obs.Names.«Lists::concat<&KernelTypes::KExprNode>».symbol]; exact ev
  have h₁' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      (fun h E p => Tm κ d Γ h k E p) h xs l₁ := by
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact h₁
  have h₂' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      (fun h E p => Tm κ d Γ h k E p) h ys l₂ := by
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact h₂
  have hres := Lib.Lists.concat_spec (R := fun h E p => Tm κ d Γ h k E p)
    (fun _ _ _ _ ext r => Tm.mono ext r) ev' h₁' h₂'
  rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hres

theorem kexpr_list_drop_spec' {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k n : Nat} {xs : List KExpr} {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hn : n < 4294967296)
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field (n : F)] h r h' cs)
    (hl : RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h xs l) :
    n ≤ xs.length ∧
      RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h (xs.drop n) r ∧ h' = h := by
  have hval : ZMod.val (n : F) = n :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hn (by decide))
  have hres := Lib.Lists.drop_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (R := fun h₀ X p₀ => Tm κ d Γ h₀ k X p₀) n hval
    (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol, hval] at hres
  exact hres

/-- `KernelCheck::nat_none_mention` returning `.field 1` leaves the heap unchanged. -/
theorem nat_none_mention_one_spec {κ : _root_.Address → KKey} {bT : Bytes.Address} :
    ∀ {d : Nat} {Γ : Nat → KExpr} {k : Nat} {es : List KExpr}
      {pes pt : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h es pes →
      Bytes.RepAddressRef addrTy h bT pt →
      ObsFn W "KernelCheck::nat_none_mention" [pes, pt] h (.field 1) h' cs →
      h' = h := by
  intro d Γ k es
  induction es with
  | nil =>
    intro pes pt h h' cs hes _ ev
    match Obs.«KernelCheck::nat_none_mention».obs ev with
    | .Nil (he21 := hh) .. => exact hh
    | .Cons_other (ld12 := ld) .. =>
      have ld' : loadValue h pes = .ok (.construct kexprListEnum "Cons" [_, _]) := ld
      cases hes with | nil cell => exact (load_cell_ne cell ld' (by decide)).elim
    | .Cons_n0 (ld12 := ld) .. =>
      have ld' : loadValue h pes = .ok (.construct kexprListEnum "Cons" [_, _]) := ld
      cases hes with | nil cell => exact (load_cell_ne cell ld' (by decide)).elim
  | cons E rest ih =>
    intro pes pt h h' cs hes hpt ev
    match Obs.«KernelCheck::nat_none_mention».obs ev with
    | .Nil (ld12 := ld) .. =>
      have ld' : loadValue h pes = .ok (.construct kexprListEnum "Nil" []) := ld
      cases hes with | cons cell _ _ => exact (load_cell_ne cell ld' (by decide)).elim
    | .Cons_other (he102 := hr) .. =>
      exact absurd (Value.field.inj hr) one_ne_zero
    | .Cons_n0 (cs52 := cs52) (ld12 := ld) (ev54 := ev_m) (ev80 := ev_rest) .. =>
      obtain ⟨E', rest', heq, hE, hrest⟩ := RepList.cons_of_load hes ld
      injection heq with h1 h2; subst h1 h2
      obtain ⟨_, hm41⟩ := nat_mentions_ret_bit cs52.length (Nat.le_refl _) hE hpt ev_m
      rw [hm41] at ev_rest
      exact ih hrest hpt ev_rest

/-- `KernelCheck::nat_rec_idx` builds `recIdxFrom ecbs T nP nF i` and certifies that no recursive
field index in that suffix is mentioned in the remainder of the constructor telescope. -/
theorem nat_rec_idx_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {T : KKey} {bT : Bytes.Address} {nP nIdx nF : Nat}
    {Rcty Ecty rbody ebody : KExpr} {rcbs ecbs : List (KExpr × Ix.Kernel.BinderMeta)}
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hnPF_lt : nP + nF < 2147483648)
    (hsR : Rcty.stripPis (nP + nF) = some (rcbs, rbody))
    (hsE : Ecty.stripPis (nP + nF) = some (ecbs, ebody))
    (hnp_dom : ∀ idx < nF, noProjAt T (ecbs.getD (nP + idx) default).1 = true) :
    ∀ (rem i : Nat) {pcty pt plps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      i + rem = nF →
      IxVM.Consistency.Bounded cs →
      RawTm κ 0 Γ₀ h 0 Rcty Ecty pcty →
      Bytes.RepAddressRef addrTy h bT pt →
      ObsFn W "KernelCheck::nat_rec_idx"
        [pcty, pt, plps, .field (nP : F), .field (nIdx : F), .field (nF : F), .field (i : F)]
        h r h' cs →
      RepList fieldListEnum (fun _ (idx : Nat) v => v = .field (idx : F)) h'
        (recIdxFrom ecbs T nP nF i) r ∧
      ∀ idx ∈ recIdxFrom ecbs T nP nF i,
        ∃ ebs₁ emid, Ecty.stripPis (nP + idx + 1) = some (ebs₁, emid) ∧
          emid.hasLooseBVar 0 = false
  | 0, i, pcty, pt, plps, r, h, h', cs, hir, _, _, _, ev => by
    subst hir
    match Obs.«KernelCheck::nat_rec_idx».obs ev with
    | .n0 (he28 := hr) (hm27 := hm) .. =>
      subst hr hm
      rw [recIdxFrom_ge (by omega)]
      exact ⟨.nil (by simp), (fun _ hmem => nomatch hmem)⟩
    | .other_n0 (op17 := op17) (hne33 := hne33) .. =>
      rw [evalBinOp_sub_nat (Nat.le_refl i) op17] at hne33
      simp only [Nat.sub_self, Nat.cast_zero] at hne33
      exact (hne33 rfl).elim
    | .other_other (op17 := op17) (hne33 := hne33) .. =>
      rw [evalBinOp_sub_nat (Nat.le_refl i) op17] at hne33
      simp only [Nat.sub_self, Nat.cast_zero] at hne33
      exact (hne33 rfl).elim
  | rem + 1, i, pcty, pt, plps, r, h, h', cs, hir, hbnd, hRaw, hpt, ev => by
    have hi_lt : i < nF := by omega
    match Obs.«KernelCheck::nat_rec_idx».obs ev with
    | .n0 (op17 := op17) .. =>
      have hsub := evalBinOp_sub_nat (by omega : i ≤ nF) op17
      have hval := congrArg ZMod.val (Value.field.inj hsub.symm)
      have h1 : ZMod.val ((nF - i : Nat) : F) = nF - i :=
        ZMod.val_natCast_of_lt (Nat.lt_trans (by omega : nF - i < 2147483648) (by decide))
      rw [h1, ZMod.val_zero] at hval
      omega
    | .other_n0 (m38 := m38) (m180 := m180) (v213 := v213) (v199 := v199) (m202 := m202)
        (v236 := v236) (m237 := m237) (cs247 := cs_rec) (v256 := v256)
        (ev50 := ev_dom) (sg187 := sg) (op227 := op227) (ev212 := ev_iz)
        (op312 := op312) (ev249 := ev_rec) (he329 := hr) (he330 := hh) (hc331 := hc) .. =>
      subst hc hr hh
      obtain ⟨hm38, hdom⟩ := nat_field_dom_rawTm_spec hi_lt (by omega) hRaw hsR hsE ev_dom
      rw [hm38] at sg
      have hsg : m180 = h ∧ (ecbs.getD (nP + i) default).1.mentionsConst T = false := by
        cases sg with
        | n0 _ cs87 ev89 _ hm76 _ =>
          subst hm76
          obtain ⟨hmen0, hm_eq⟩ := nat_mentions_zero_spec hκ_inj cs87.length (Nat.le_refl _)
            hdom.toTm hpt (hnp_dom i hi_lt) (fun _ hk => nomatch hk) ev89
          exact ⟨hm_eq, hmen0⟩
        | other v75 m76 cs87 cs120 ev89 _ ev122 _ =>
          obtain ⟨_, hm76_eq⟩ := nat_mentions_ret_bit cs87.length (Nat.le_refl _) hdom.toTm hpt ev89
          rw [hm76_eq] at ev122
          have h0_ne_3 : (.field 0 : SourceValue F) ≠ .field 3 := by
            intro h03
            have hv := congrArg ZMod.val (Value.field.inj h03)
            rw [ZMod.val_zero, show (3 : F) = ((3 : Nat) : F) from rfl,
              ZMod.val_natCast_of_lt (by decide)] at hv
            exact absurd hv (by decide)
          obtain ⟨h012, _⟩ := nat_positivity_ok_spec hT cs120.length (Nat.le_refl _)
            h0_ne_3 hdom hpt ev122
          rcases h012 with h1 | h2
          · exact absurd (Value.field.inj h1).symm one_ne_zero
          · have hv := congrArg ZMod.val (Value.field.inj h2)
            rw [ZMod.val_zero, show (2 : F) = ((2 : Nat) : F) from rfl,
              ZMod.val_natCast_of_lt (by decide)] at hv
            exact absurd hv (by decide)
      obtain ⟨hm180_eq, hmenF⟩ := hsg
      rw [hm180_eq] at ev_iz
      have hv213 : ∃ f213 : F, v213 = .field f213 := by
        cases op227; exact ⟨_, rfl⟩
      obtain ⟨f213, rfl⟩ := hv213
      obtain ⟨_, hm202_eq⟩ := Lib.is_zero_spec ev_iz
      rw [hm202_eq, evalBinOp_add_one i op312] at ev_rec
      have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      obtain ⟨hrep_tl, hunused_tl⟩ :=
        nat_rec_idx_spec hT hκ_inj hnPF_lt hsR hsE hnp_dom rem (i + 1) (by omega)
          hbnd_rec hRaw hpt ev_rec
      rw [recIdxFrom_lt hi_lt, hmenF]
      exact ⟨hrep_tl, hunused_tl⟩
    | .other_other (m38 := m38) (v179 := v179) (m180 := m180) (v199 := v199) (m202 := m202)
        (v213 := v213) (v236 := v236) (m237 := m237) (cs247 := cs_rec) (v256 := v256)
        (v347 := v347) (m350 := m350) (cs358 := cs_bvar) (v361 := v361) (m364 := m364)
        (v376 := v376) (x390 := x390)
        (ev50 := ev_dom) (sg187 := sg) (op227 := op227) (ev212 := ev_iz) (heq235 := heq235)
        (op312 := op312) (ev249 := ev_rec) (hne332 := hne332)
        (op405 := op405) (op397 := op397) (ev374 := ev_peel) (ev360 := ev_bvar)
        (heq420 := heq420) (he425 := hr) (hm424 := hm_end) (hc445 := hc) .. =>
      subst hc hr hm_end
      obtain ⟨hm38, hdom⟩ := nat_field_dom_rawTm_spec hi_lt (by omega) hRaw hsR hsE ev_dom
      rw [hm38] at sg
      have hv179_f : ∃ f179 : F, v179 = .field f179 ∧ v213 = .field (f179 - 3) := by
        cases v179 <;> simp [evalBinOp] at op227
        exact ⟨_, rfl, op227.symm⟩
      obtain ⟨f179, rfl, rfl⟩ := hv179_f
      obtain ⟨hv199, hm202_eq⟩ := Lib.is_zero_spec ev_iz
      have hne3 : (.field f179 : SourceValue F) ≠ .field 3 := by
        intro h3
        injection h3 with hf3
        subst hf3
        simp only [sub_self, ↓reduceIte] at hv199
        rw [heq235] at hv199
        exact absurd (Value.field.inj hv199.symm) one_ne_zero
      have hsg : Heap.Extends h m180 ∧ (ecbs.getD (nP + i) default).1.mentionsConst T = true := by
        cases sg with
        | n0 _ _ _ hv0 _ _ =>
          exact absurd hv0 hne332
        | other v75 m76 cs87 cs120 ev89 _ ev122 _ =>
          obtain ⟨_, hm76_eq⟩ := nat_mentions_ret_bit cs87.length (Nat.le_refl _) hdom.toTm hpt ev89
          rw [hm76_eq] at ev122
          obtain ⟨_, hmenT⟩ := nat_positivity_ok_spec hT cs120.length (Nat.le_refl _) hne3 hdom hpt ev122
          exact ⟨ev122.heap_extends, hmenT⟩
      rcases hsg with ⟨ext_180, hmenT⟩
      rw [hm202_eq, evalBinOp_add_one i op312] at ev_rec
      have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      obtain ⟨hrep_tl, hunused_tl⟩ :=
        nat_rec_idx_spec hT hκ_inj hnPF_lt hsR hsE hnp_dom rem (i + 1) (by omega) hbnd_rec
          (hRaw.mono ext_180) (Bytes.repAddressRef_heapMono₂ addrTy ext_180 hpt) ev_rec
      rw [evalBinOp_add_nat nP i op405] at op397
      rw [evalBinOp_add_one (nP + i) op397] at ev_peel
      have ext_237 := ext_180.trans ev_rec.heap_extends
      obtain ⟨hm364_eq, _, ebs₁, _, emid, _, hsE₁, hmid⟩ :=
        peel_n_foralls_rawTm_spec (nP + i + 1) (by omega) (hRaw.mono ext_237) ev_peel
      rw [hm364_eq, heq420] at ev_bvar
      have hbnd_bvar : IxVM.Consistency.Bounded cs_bvar :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hmid_tm : Tm κ 0 Γ₀ m237 (nP + i + 1) emid v361 := by
        simpa [Nat.zero_add] using hmid.toTm
      obtain ⟨hbvarF, hm350_eq⟩ :=
        expr_has_bvar_at_zero_spec (by omega : 0 < nP + i + 1) (by decide : 0 < 4294967296)
          hbnd_bvar hmid_tm ev_bvar
      rw [hm350_eq]
      have ext_end : Heap.Extends m237
          (m237 ++ [.construct fieldListEnum "Cons" [.field (i : F), v236]]) :=
        Heap.Extends.snoc _ _
      rw [recIdxFrom_lt hi_lt, hmenT]
      simp only [↓reduceIte]
      refine ⟨.cons (by simp) rfl (fieldRepList_mono ext_end hrep_tl), fun idx hidx => ?_⟩
      rcases List.mem_cons.mp hidx with rfl | hmem_tl
      · exact ⟨ebs₁, emid, hsE₁, hbvarF⟩
      · exact hunused_tl idx hmem_tl

/-- An observed recursive-index scan supplies the unused-later condition directly for every
field whose unopened domain mentions the former. This extraction precedes field classification. -/
theorem nat_rec_idx_unused_later {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {T : KKey} {bT : Bytes.Address} {nP nIdx nF : Nat}
    {Rcty Ecty rbody ebody : KExpr} {rcbs ecbs : List (KExpr × Ix.Kernel.BinderMeta)}
    {pcty pt plps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hnPF_lt : nP + nF < 2147483648)
    (hsR : Rcty.stripPis (nP + nF) = some (rcbs, rbody))
    (hsE : Ecty.stripPis (nP + nF) = some (ecbs, ebody))
    (hnp_dom : ∀ i < nF, noProjAt T (ecbs.getD (nP + i) default).1 = true)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hcty : RawTm κ 0 Γ₀ h 0 Rcty Ecty pcty)
    (ht : Bytes.RepAddressRef addrTy h bT pt)
    (ev : ObsFn W "KernelCheck::nat_rec_idx"
      [pcty, pt, plps, .field (nP : F), .field (nIdx : F), .field (nF : F), .field 0]
      h r h' cs) :
    ∀ i < nF, (ecbs.getD (nP + i) default).1.mentionsConst T = true →
      Ix.Kernel.structUsedLater Ecty nP i = false := by
  obtain ⟨_, hunused⟩ := nat_rec_idx_spec hT hκ_inj hnPF_lt hsR hsE hnp_dom
    nF 0 (Nat.zero_add nF) hbnd hcty ht ev
  intro i hi hmentions
  have hmem : i ∈ recIdxFrom ecbs T nP nF 0 := by
    rw [recIdxFrom_eq_filter_drop nF 0 (Nat.zero_add nF), List.drop_zero]
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hi, hmentions⟩
  obtain ⟨bs, rest, hstrip, hfree⟩ := hunused i hmem
  simp only [Ix.Kernel.structUsedLater, hstrip, Expr.hasLooseBVarB_eq, hfree]

/-- Per-constructor `get_ci_cprj` load witness for native recursor checking (`nat_ctor`, `nat_minors`,
`nat_rule_rhs`, `nat_check_rules`). Each entry `(C, nF, R₀, C₀, recIdx)` carries the constructor key,
field count, raw constructor type `R₀`, annotated constructor type `C₀`, and recursive field indices. -/
def NatCtorLoad (κ : _root_.Address → KKey) (b₀ : Bytes.Address) (k : Nat)
    (ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat))
    (x_block : SourceValue F) (calls_bound : List (Call F)) : Prop :=
  ∀ (j : Nat), j < ctors_info.length →
    ∀ (p9 : SourceValue F) (h m2 : Heap F) (cs15 : List (Call F))
      (w45 x_cty0 w46 w47 w48 w49 x_nf w50 : SourceValue F),
      (∀ x ∈ cs15, x ∈ calls_bound) →
      Bytes.RepAddressRef addrTy h b₀ x_block →
      ObsFn W "Ingress::get_ci_cprj" [x_block, .field 0, .field (j : F)] h p9 m2 cs15 →
      loadValue m2 p9 = .ok (.construct kciEnum "Ctor"
        [w45, x_cty0, w46, w47, w48, w49, x_nf, w50]) →
      ∀ info, ctors_info[j]? = some info →
        info.1 = κ (cprjAddr (ixAddr b₀) 0 j) ∧
        x_nf = .field (info.2.1 : F) ∧
        RawTm κ 0 (fun _ => default) m2 0
          (posOf (List.range k) info.2.2.1) (posOf (List.range k) info.2.2.2.1) x_cty0

theorem NatCtorLoad.mono_calls {κ : _root_.Address → KKey} {b₀ : Bytes.Address} {k : Nat}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)} {x_block : SourceValue F}
    {cs₁ cs₂ : List (Call F)} (hsub : ∀ x ∈ cs₁, x ∈ cs₂)
    (h : NatCtorLoad κ b₀ k ctors_info x_block cs₂) :
    NatCtorLoad κ b₀ k ctors_info x_block cs₁ :=
  fun j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 hs =>
    h j hj p9 hp m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50 (fun x hx => hsub x (hs x hx))

/-- Well-formedness of a `ctors_info` entry for native recursor checking at
`(T, k, large, nP, nIdx, num_ctors)`. -/
structure NatCtorInfoWf (T : KKey) (k : Nat) (large : Bool) (nP nIdx num_ctors : Nat)
    (info : KKey × Nat × KExpr × KExpr × List Nat) : Prop where
  nf_lt : nP + info.2.1 < 2147483648
  lps_R : info.2.2.1.allLevelParamsDefined (List.range k) = true
  lps_C : info.2.2.2.1.allLevelParamsDefined (List.range k) = true
  noProj_C : noProjAt T info.2.2.2.1 = true
  strip_R : ∃ rcbs rus rargs,
    info.2.2.1.stripPis (nP + info.2.1) = some (rcbs, Expr.mkAppN (.const T rus) rargs)
  strip_C : ∃ ecbs eus eargs,
    info.2.2.2.1.stripPis (nP + info.2.1) = some (ecbs, Expr.mkAppN (.const T eus) eargs)
  recIdx_eq : ∀ ecbs ebody,
    (posOf (if large then k :: List.range k else List.range k) info.2.2.2.1).stripPis
      (nP + info.2.1) = some (ecbs, ebody) →
    info.2.2.2.2 = recIdxFrom ecbs T nP info.2.1 0
  rec_spines : ∀ i ∈ info.2.2.2.2, i < info.2.1 ∧
    ∀ rcbs rbody ecbs ebody,
      info.2.2.1.stripPis (nP + info.2.1) = some (rcbs, rbody) →
      info.2.2.2.1.stripPis (nP + info.2.1) = some (ecbs, ebody) →
      RawRecSpine T (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1
  minor_base_lt : nP + 1 + num_ctors + info.2.1 + info.2.2.2.2.length < 4294967296
  tele_lt : ∀ i ∈ info.2.2.2.2,
    nP + 1 + num_ctors + info.2.1 + info.2.2.2.2.length +
      (Ix.Kernel.structFieldTeleOf info.2.2.2.1 nP info.2.1 i).length < 4294967296

theorem clvls_eq_subst_params (k : Nat) (large : Bool) :
    let lps := List.range k
    let rlps := if large then k :: List.range k else List.range k
    (List.range k).map (fun i => Level.param ((if large then 1 else 0) + i)) =
      ((lps.map .param).map (Level.subst rlps (posLevels rlps))) := by
  cases large with
  | false =>
    have h0 := map_subst_range_params k (posLevels (List.range k)) (by simp [posLevels])
    simpa [posLevels, Nat.zero_add] using h0.symm
  | true =>
    exact (map_subst_large_former_params k).symm

/-- `KernelCheck::nat_ctor` loads constructor `j`, instantiates its universe parameters to the
recursor's frame `rlps`, verifies its return spine mentions `T` nowhere in its indices, and
computes its recursive field indices `recIdx` along with `structUsedLater = false` on each. -/
theorem nat_ctor_spec {κ : _root_.Address → KKey}
    {T : KKey} {b₀ bT : Bytes.Address} {k nP nIdx num_ctors j : Nat} {large : Bool}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {info : KKey × Nat × KExpr × KExpr × List Nat}
    {x_block x_t x_lps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hT : κ (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → a = bT)
    (hj : j < ctors_info.length)
    (hinfo : ctors_info[j]? = some info)
    (hwf : NatCtorInfoWf T k large nP nIdx num_ctors info)
    (hload : NatCtorLoad κ b₀ k ctors_info x_block cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hb₀ : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hbT : Bytes.RepAddressRef addrTy h bT x_t)
    (hlps : RepKLevelList h
      ((List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx))) x_lps)
    (ev : ObsFn W "KernelCheck::nat_ctor"
      [x_block, .field 0, .field (j : F), x_t, x_lps, .field (nP : F), .field (nIdx : F),
        .field ((if large then 1 else 0 : Nat) : F)]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    ∃ x_cty x_rec_idx,
      r = .tuple [x_cty, .field (info.2.1 : F), x_rec_idx] ∧
      RawTm κ 0 (fun _ => default) h' 0 (posOf rlps info.2.2.1) (posOf rlps info.2.2.2.1) x_cty ∧
      RepList fieldListEnum (fun _ (idx : Nat) v => v = .field (idx : F)) h'
        info.2.2.2.2 x_rec_idx ∧
      (∀ idx ∈ info.2.2.2.2, Ix.Kernel.structUsedLater info.2.2.2.1 nP idx = false) := by
  intro rlps
  dsimp only [rlps]
  rcases Obs.«KernelCheck::nat_ctor».obs ev with
    ⟨m2, p9, cs15, w45, x_cty0, w46, w47, w48, w49, x_nf, w50,
      v136, m137, cs139, m146, cs156, v159, m161, cs169, v173, w200, x_rargs,
      v222, m225, cs233, v236, m239, cs247, v284, m301, cs309,
      ev17, ld11, sg144, op194, ev171, ev158, ev249, ev235, heq279, htup_out, ev311, hm_out, hc⟩
  subst hc htup_out hm_out
  obtain ⟨_, hnf_eq, hRaw0⟩ :=
    hload j hj p9 h m2 cs15 w45 x_cty0 w46 w47 w48 w49 x_nf w50
      (fun x hx => by simp [hx]) hb₀ ev17 ld11 info hinfo
  subst hnf_eq
  let nF := info.2.1
  let R₀ := info.2.2.1
  let C₀ := info.2.2.2.1
  let recIdx := info.2.2.2.2
  have hnPF_lt : nP + nF < 2147483648 := hwf.nf_lt
  -- Step 1: `Seg1` produces `RawTm` for `(posOf rlps R₀, posOf rlps C₀)` at `v136`
  have hRaw_rlps :
      RawTm κ 0 (fun _ => default) m137 0
        (posOf (if large then k :: List.range k else List.range k) R₀)
        (posOf (if large then k :: List.range k else List.range k) C₀) v136 ∧
      Heap.Extends m2 m137 := by
    cases sg144 with
    | n0 hv104 hv136 hm137 _ =>
      subst hv136 hm137
      cases large with
      | false => exact ⟨hRaw0, Heap.Extends.refl _⟩
      | true =>
        simp only [↓reduceIte] at hv104
        exact absurd (Value.field.inj hv104) one_ne_zero
    | other cs116 hne109 ev118 hc_sg =>
      subst hc_sg
      cases large with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hne109
        exact absurd rfl hne109
      | true =>
        simp only [↓reduceIte] at hlps ⊢
        have hbnd_inst : IxVM.Consistency.Bounded cs116 :=
          RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
        have hlps_m2 := RepKLevelList.mono hlps ev17.heap_extends
        have hlv_rep : LvListRep m2 ((List.range k).map (fun idx => Level.param (1 + idx))) x_lps :=
          ⟨_, hlps_m2, LvEqList.refl _⟩
        have hinst := expr_inst_levels_rawTm hbnd_inst hRaw0 hlv_rep ev118
        simp only [List.length_map, List.length_range] at hinst
        rw [posOf_range, posOf_range, ← posOf_large_eq_inst_shifted k hwf.lps_R,
          ← posOf_large_eq_inst_shifted k hwf.lps_C] at hinst
        exact ⟨hinst, ev118.heap_extends⟩
  rcases hRaw_rlps with ⟨hRaw137, ext_2_137⟩
  have ext_h_137 := ev17.heap_extends.trans ext_2_137
  -- Step 2: `peel_n_foralls`, `collect_spine`, `drop`, `nat_none_mention`
  rw [evalBinOp_add_nat nP nF op194] at ev171
  obtain ⟨hm161_eq, _, _, _, _, _, _, hmid⟩ :=
    peel_n_foralls_rawTm_spec (nP + nF) (by omega) hRaw137 ev171
  rw [hm161_eq] at ev158
  obtain ⟨hd_sp, sp_sp, _, _, _, Eas, htup_sp, _, hEas, _, _, _, _⟩ :=
    collect_spine_rawTm_spec hmid ev158
  -- Wait: let's check `v159 = .tuple [w200, x_rargs]` in `Obs.«KernelCheck::nat_ctor»`!
  -- Wait: `htup_sp : .tuple [w200, x_rargs] = .tuple [hd_sp, sp_sp]`
  injection htup_sp with hsp_list
  injection hsp_list with _ hsp_tl
  injection hsp_tl with hsp_eq _
  subst hsp_eq
  rw [Nat.zero_add] at hEas
  obtain ⟨_, hdrop, hm239_eq⟩ := kexpr_list_drop_spec' (by omega) ev249 hEas
  rw [hm239_eq, heq279] at ev235
  have ext_h_146 := ext_h_137.trans ev158.heap_extends
  have hbT_146 := Bytes.repAddressRef_heapMono₂ addrTy ext_h_146 hbT
  have hm225 := nat_none_mention_one_spec hdrop hbT_146 ev235
  rw [hm225] at ev311
  -- Step 3: `nat_rec_idx`
  let rlps' := if large then k :: List.range k else List.range k
  obtain ⟨rcbs₀, rus₀, rargs₀, hsR₀⟩ := hwf.strip_R
  obtain ⟨ecbs₀, eus₀, eargs₀, hsC₀⟩ := hwf.strip_C
  have hsR_pos := ilp_stripPis rlps' (posLevels rlps') (nP + nF) hsR₀
  change (posOf rlps' R₀).stripPis (nP + nF) = _ at hsR_pos
  have hsE_pos := ilp_stripPis rlps' (posLevels rlps') (nP + nF) hsC₀
  change (posOf rlps' C₀).stripPis (nP + nF) = _ at hsE_pos
  have hnp_pos : noProjAt T (posOf rlps' C₀) = true := by
    unfold posOf
    rw [noProjAt_ilp]
    exact hwf.noProj_C
  obtain ⟨hnp_doms, _⟩ := noProjAt_stripPis_binder (nP + nF) hnp_pos hsE_pos
  have hnp_dom_f : ∀ idx < nF,
      noProjAt T ((ecbs₀.map (fun b => (posOf rlps' b.1,
        { b.2 with pw := Level.substPW rlps' (posLevels rlps') b.2.pw }))).getD
        (nP + idx) default).1 = true :=
    fun idx hidx => hnp_doms (nP + idx) (by omega)
  have hbnd_rec : IxVM.Consistency.Bounded cs309 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have ev311' : ObsFn W "KernelCheck::nat_rec_idx"
      [v136, x_t, x_lps, .field (nP : F), .field (nIdx : F), .field (nF : F),
        .field ((0 : Nat) : F)]
      m146 v284 h' cs309 := by
    simpa using ev311
  obtain ⟨hrep_idx, hunused_idx⟩ :=
    nat_rec_idx_spec hT hκ_inj hnPF_lt hsR_pos hsE_pos hnp_dom_f nF 0 (by omega) hbnd_rec
      (hRaw137.mono ev158.heap_extends) hbT_146 ev311'
  have hrec_eq := hwf.recIdx_eq _ _ hsE_pos
  rw [← hrec_eq] at hrep_idx hunused_idx
  refine ⟨v136, v284, rfl, (hRaw137.mono ev158.heap_extends).mono ev311'.heap_extends,
    hrep_idx, fun idx hidx => ?_⟩
  obtain ⟨hi_lt, _⟩ := hwf.rec_spines idx hidx
  obtain ⟨ebs₁, emid, hsE₁, hbvarF⟩ := hunused_idx idx hidx
  have hsplit : nP + nF = (nP + idx + 1) + (nF - 1 - idx) := by omega
  have hsC₀' : C₀.stripPis ((nP + idx + 1) + (nF - 1 - idx)) =
      some (ecbs₀, Expr.mkAppN (.const T eus₀) eargs₀) := by
    rwa [← hsplit]
  obtain ⟨cbs₁, cbody₁, _, hsC₁, _, _, _⟩ := stripPis_split (nP + idx + 1) (nF - 1 - idx) hsC₀'
  exact structUsedLater_false_of_posOf_stripPis hsC₁ hsE₁ hbvarF

/-- `KernelCheck::nat_minors` builds `cMinorsPis` (when `isLam = false`) or `cMinorsLams`
(when `isLam = true`) from constructor index `j` (`o = j + 1`) upward. -/
theorem nat_minors_spec {c : Ctx}
    {T : KKey} {b₀ bT : Bytes.Address} {k nP nIdx : Nat} {large isLam : Bool} {ℓ : KLevel}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    (hT : keyOf c.t (ixAddr bT) = T)
    (hκ_inj : ∀ a : Bytes.Address, keyOf c.t (ixAddr a) = T → a = bT)
    (hnCtors_lt : ctors_info.length < 4294967296)
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWf T k large nP nIdx ctors_info.length info) :
    ∀ (rem j : Nat) {body : KExpr}
      {x_block x_t x_lps x_pw x_body r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      j + rem = ctors_info.length →
      NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs →
      Good c cs →
      IxVM.Consistency.Bounded cs →
      Bytes.RepAddressRef addrTy h b₀ x_block →
      Bytes.RepAddressRef addrTy h bT x_t →
      RepKLevelList h
        ((List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx))) x_lps →
      RepKLevel h ℓ x_pw →
      Tm (keyOf c.t) 0 (fun _ => default) h (nP + 1 + ctors_info.length) body x_body →
      ObsFn W "KernelCheck::nat_minors"
        [x_block, .field 0, x_t, x_lps, .field (nP : F), .field (nIdx : F), x_pw,
          .field (ctors_info.length : F),
          .field ((if large then 1 else 0 : Nat) : F),
          .field (j : F), x_body,
          .field ((if isLam then 1 else 0 : Nat) : F)]
        h r h' cs →
      let rlps := if large then k :: List.range k else List.range k
      let clvls := (List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx))
      let cs_tail := (ctors_info.drop j).map
        (fun info => (info.1, info.2.1, posOf rlps info.2.2.2.1, info.2.2.2.2))
      ∃ out,
        (if isLam then cMinorsLams clvls nP ℓ.zeronessOf cs_tail (j + 1) body
         else cMinorsPis clvls nP ℓ.zeronessOf cs_tail (j + 1) body) = some out ∧
        Tm (keyOf c.t) 0 (fun _ => default) h' (nP + j + 1) out r
  | 0, j, body, x_block, x_t, x_lps, x_pw, x_body, r, h, h', cs, hjr, _, _, _, _, _, _, _, hbody, ev => by
    have hj_eq : j = ctors_info.length := by omega
    subst hj_eq
    match Obs.«KernelCheck::nat_minors».obs ev with
    | .n0 (he25 := hr) (he26 := hh) .. =>
      subst hr hh
      refine ⟨body, ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using hbody⟩
      cases isLam <;> simp [List.drop_length, cMinorsPis, cMinorsLams]
    | .other_n0 (op17 := op17) (hne28 := hne28) .. =>
      rw [evalBinOp_sub_nat (Nat.le_refl ctors_info.length) op17] at hne28
      simp only [Nat.sub_self, Nat.cast_zero] at hne28
      exact (hne28 rfl).elim
    | .other_other (op17 := op17) (hne28 := hne28) .. =>
      rw [evalBinOp_sub_nat (Nat.le_refl ctors_info.length) op17] at hne28
      simp only [Nat.sub_self, Nat.cast_zero] at hne28
      exact (hne28 rfl).elim
  | rem + 1, j, body, x_block, x_t, x_lps, x_pw, x_body, r, h, h', cs,
      hjr, hload, hgood, hbnd, hb₀, hbT, hlps, hpw, hbody, ev => by
    let rlps := if large then k :: List.range k else List.range k
    let clvls := (List.range k).map (fun idx => Level.param ((if large then 1 else 0) + idx))
    have hj_lt : j < ctors_info.length := by omega
    let info := ctors_info[j]'hj_lt
    have hinfo_get : ctors_info[j]? = some info := List.getElem?_eq_getElem hj_lt
    have hwf_j : NatCtorInfoWf T k large nP nIdx ctors_info.length info :=
      hwf_all info (List.mem_of_getElem? hinfo_get)
    have hdrop_j : ctors_info.drop j = info :: ctors_info.drop (j + 1) := by
      rw [← List.cons_getElem_drop_succ (h := hj_lt)]
    obtain ⟨rcbs₀, rus₀, rargs₀, hsR₀⟩ := hwf_j.strip_R
    obtain ⟨ecbs₀, eus₀, eargs₀, hsC₀⟩ := hwf_j.strip_C
    have hsR_pos : (posOf rlps info.2.2.1).stripPis (nP + info.2.1) =
        some (rcbs₀.map (fun b => (posOf rlps b.1,
          { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw })),
          Expr.mkAppN (.const T (rus₀.map (Level.subst rlps (posLevels rlps))))
            (rargs₀.map (posOf rlps))) := by
      have hs := ilp_stripPis rlps (posLevels rlps) (nP + info.2.1) hsR₀
      unfold posOf at hs ⊢
      rwa [ilp_mkAppN, Expr.instantiateLevelParams] at hs
    have hsE_pos : (posOf rlps info.2.2.2.1).stripPis (nP + info.2.1) =
        some (ecbs₀.map (fun b => (posOf rlps b.1,
          { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw })),
          Expr.mkAppN (.const T (eus₀.map (Level.subst rlps (posLevels rlps))))
            (eargs₀.map (posOf rlps))) := by
      have hs := ilp_stripPis rlps (posLevels rlps) (nP + info.2.1) hsC₀
      unfold posOf at hs ⊢
      rwa [ilp_mkAppN, Expr.instantiateLevelParams] at hs
    have hall_minor : ∀ idx ∈ info.2.2.2.2, idx < info.2.1 ∧
        RawRecSpine T
          ((rcbs₀.map (fun b => (posOf rlps b.1,
            { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw }))).getD
            (nP + idx) default).1
          ((ecbs₀.map (fun b => (posOf rlps b.1,
            { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw }))).getD
            (nP + idx) default).1 ∧
        nP + (j + 1) + info.2.1 + info.2.2.2.2.length +
          (Ix.Kernel.structFieldTeleOf (posOf rlps info.2.2.2.1) nP info.2.1 idx).length <
            4294967296 := by
      intro idx hidx
      obtain ⟨hi_lt, hsp_fn⟩ := hwf_j.rec_spines idx hidx
      have hsp0 := hsp_fn rcbs₀ _ ecbs₀ _ hsR₀ hsC₀
      have hlenR : rcbs₀.length = nP + info.2.1 := stripPis_length (nP + info.2.1) hsR₀
      have hlenC : ecbs₀.length = nP + info.2.1 := stripPis_length (nP + info.2.1) hsC₀
      have hltR : nP + idx < rcbs₀.length := by omega
      have hltC : nP + idx < ecbs₀.length := by omega
      have hgetR : (rcbs₀.map (fun b => (posOf rlps b.1,
          { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw }))).getD (nP + idx) default =
          (posOf rlps (rcbs₀[nP + idx]'hltR).1,
            { (rcbs₀[nP + idx]'hltR).2 with
              pw := Level.substPW rlps (posLevels rlps) (rcbs₀[nP + idx]'hltR).2.pw }) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hltR]; rfl
      have hgetC : (ecbs₀.map (fun b => (posOf rlps b.1,
          { b.2 with pw := Level.substPW rlps (posLevels rlps) b.2.pw }))).getD (nP + idx) default =
          (posOf rlps (ecbs₀[nP + idx]'hltC).1,
            { (ecbs₀[nP + idx]'hltC).2 with
              pw := Level.substPW rlps (posLevels rlps) (ecbs₀[nP + idx]'hltC).2.pw }) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hltC]; rfl
      have hgetR0 : rcbs₀.getD (nP + idx) default = rcbs₀[nP + idx]'hltR := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltR]; rfl
      have hgetC0 : ecbs₀.getD (nP + idx) default = ecbs₀[nP + idx]'hltC := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltC]; rfl
      rw [hgetR0, hgetC0] at hsp0
      have hft_len : (Ix.Kernel.structFieldTeleOf (posOf rlps info.2.2.2.1) nP info.2.1 idx).length =
          (Ix.Kernel.structFieldTeleOf info.2.2.2.1 nP info.2.1 idx).length := by
        unfold posOf
        rw [ilp_structFieldTeleOf rlps (posLevels rlps) info.2.2.2.1 nP info.2.1 idx
          ⟨_, _, hsC₀, hltC⟩, List.length_map]
      have htl_lt := hwf_j.tele_lt idx hidx
      refine ⟨hi_lt, ?_, by rw [hft_len]; omega⟩
      rw [hgetR, hgetC]
      exact rawRecSpine_ilp rlps (posLevels rlps) hsp0
    have hbase_lt : nP + (j + 1) + info.2.1 + info.2.2.2.2.length < 4294967296 := by
      have := hwf_j.minor_base_lt
      omega
    match Obs.«KernelCheck::nat_minors».obs ev with
    | .n0 (op17 := op17) .. =>
      have hsub := evalBinOp_sub_nat (by omega : j ≤ ctors_info.length) op17
      have hval := congrArg ZMod.val (Value.field.inj hsub.symm)
      have h1 : ZMod.val ((ctors_info.length - j : Nat) : F) = ctors_info.length - j :=
        ZMod.val_natCast_of_lt (Nat.lt_trans (by omega : ctors_info.length - j < 4294967296) (by decide))
      rw [h1, ZMod.val_zero] at hval
      omega
    | .other_n0 (m33 := m33) (cs43 := cs_ctor) (x_cty := x_cty) (x_nf := x_nf)
        (x_rec_idx := x_rec_idx) (v128 := v128) (m129 := m129) (cs139 := cs_mty)
        (v142 := v142) (v146 := v146) (m151 := m151) (cs159 := cs_proj)
        (v243 := v243) (m244 := m244) (cs254 := cs_rec) (v266 := v266)
        (ev45 := ev_ctor) (ev161 := ev_proj) (op220 := op220) (ev141 := ev_mty)
        (op345 := op345) (ev256 := ev_rec) (hv374 := hv_lam) (he379 := hr)
        (hm378 := hm_end) (hc407 := hc) .. =>
      subst hc hr hm_end
      have hisLam : isLam = false := by
        cases isLam with
        | false => rfl
        | true =>
          simp only [↓reduceIte] at hv_lam
          exact absurd (Value.field.inj hv_lam) one_ne_zero
      subst hisLam
      have hbnd_ctor : IxVM.Consistency.Bounded cs_ctor :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hload_ctor : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs_ctor :=
        hload.mono_calls (fun x hx => by simp [hx])
      obtain ⟨x_cty', x_rec_idx', htup_c, hRaw_c, hrec_c, _⟩ :=
        nat_ctor_spec hT hκ_inj hj_lt hinfo_get hwf_j hload_ctor hbnd_ctor hb₀ hbT hlps ev_ctor
      injection htup_c with hl_c
      injection hl_c with h1 hl_c; injection hl_c with h2 hl_c; injection hl_c with h3
      subst h1 h2 h3
      have hC_key : info.1 = keyOf c.t (cprjAddr (ixAddr b₀) 0 j) := by
        rcases Obs.«KernelCheck::nat_ctor».obs ev_ctor with ⟨m2_c, p9_c, cs15_c,
          w45_c, x_cty0_c, w46_c, w47_c, w48_c, w49_c, x_nf_c, w50_c, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, ev17_c, ld11_c, _, _, _, _, _, _, _, _, _, _, hc_c⟩
        subst hc_c
        exact (hload_ctor j hj_lt p9_c h m2_c cs15_c w45_c x_cty0_c w46_c w47_c w48_c w49_c
          x_nf_c w50_c (fun x hx => by simp [hx]) hb₀ ev17_c ld11_c info hinfo_get).1
      have hb₀_33 := Bytes.repAddressRef_heapMono₂ addrTy ev_ctor.heap_extends hb₀
      have hgood_proj : Good c cs_proj :=
        hgood.sub (fun x hx => by simp [hx])
      have ev_proj' : ObsFn W "KernelCheck::projection_addr_ctor"
          [.field ((0 : Nat) : F), .field (j : F), x_block] m33 v142 m151 cs_proj := by
        simpa using ev_proj
      obtain ⟨bC, hbC, hbC_addr⟩ := projection_addr_ctor_spec (by decide : 0 < 4294967296)
        (by omega : j < 4294967296) hb₀_33 hgood_proj ev_proj'
      rw [evalBinOp_add_one j op220] at ev_mty
      have ext_h_151 := ev_ctor.heap_extends.trans ev_proj.heap_extends
      have hbnd_mty : IxVM.Consistency.Bounded cs_mty :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      obtain ⟨mty, hmty_eq, hmty_tm⟩ :=
        nat_minor_ty_spec (κ := keyOf c.t) (Γ₀ := fun _ => default)
          (by rw [hbC_addr, ← hC_key])
          (by omega : 1 ≤ j + 1) hsR_pos hsE_pos hall_minor hbase_lt hbnd_mty hbC
          (RepKLevelList.mono hlps ext_h_151)
          (repKLevel_heapMono₂ ext_h_151 hpw)
          (hRaw_c.mono ev_proj.heap_extends)
          (fieldRepList_mono ev_proj.heap_extends hrec_c) ev_mty
      rw [evalBinOp_add_one j op345] at ev_rec
      have ext_h_129 := ext_h_151.trans ev_mty.heap_extends
      have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hgood_rec : Good c cs_rec :=
        hgood.sub (fun x hx => by simp [hx])
      have hload_rec : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs_rec :=
        hload.mono_calls (fun x hx => by simp [hx])
      obtain ⟨rest_out, hrest_eq, hrest_tm⟩ :=
        nat_minors_spec hT hκ_inj hnCtors_lt hwf_all rem (j + 1) (by omega)
          hload_rec hgood_rec hbnd_rec
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hb₀)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hbT)
          (RepKLevelList.mono hlps ext_h_129)
          (repKLevel_heapMono₂ ext_h_129 hpw)
          (hbody.mono ext_h_129) ev_rec
      simp only [Bool.false_eq_true, ↓reduceIte] at hrest_eq ⊢
      have ext_end : Heap.Extends m244
          (m244 ++ [.construct kexprEnum "Forall" [v128, v243, x_pw]]) :=
        Heap.Extends.snoc _ _
      refine ⟨.forallE mty rest_out { pw := ℓ.zeronessOf }, ?_, ?_⟩
      · rw [hdrop_j, List.map_cons, cMinorsPis, hmty_eq]
        dsimp only [Option.bind]
        rw [hrest_eq, Option.map_some]
      · have hmty_end : Tm (keyOf c.t) 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Forall" [v128, v243, x_pw]])
            (nP + j + 1) mty v128 := by
          rw [show nP + j + 1 = nP + (j + 1) by omega]
          exact (hmty_tm.mono ev_rec.heap_extends).mono ext_end
        have hrest_end : Tm (keyOf c.t) 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Forall" [v128, v243, x_pw]])
            ((nP + j + 1) + 1) rest_out v243 := by
          rw [show (nP + j + 1) + 1 = nP + (j + 1) + 1 by omega]
          exact hrest_tm.mono ext_end
        exact .forallE (by simp) hmty_end hrest_end
          (repKLevel_heapMono₂ (ext_h_129.trans (ev_rec.heap_extends.trans ext_end)) hpw)
    | .other_other (m33 := m33) (cs43 := cs_ctor) (x_cty := x_cty) (x_nf := x_nf)
        (x_rec_idx := x_rec_idx) (v128 := v128) (m129 := m129) (cs139 := cs_mty)
        (v142 := v142) (v146 := v146) (m151 := m151) (cs159 := cs_proj)
        (v243 := v243) (m244 := m244) (cs254 := cs_rec) (v266 := v266)
        (ev45 := ev_ctor) (ev161 := ev_proj) (op220 := op220) (ev141 := ev_mty)
        (op345 := op345) (ev256 := ev_rec) (hne408 := hne_lam) (he416 := hr)
        (hm415 := hm_end) (hc444 := hc) .. =>
      subst hc hr hm_end
      have hisLam : isLam = true := by
        cases isLam with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hne_lam
          exact absurd rfl hne_lam
        | true => rfl
      subst hisLam
      have hbnd_ctor : IxVM.Consistency.Bounded cs_ctor :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hload_ctor : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs_ctor :=
        hload.mono_calls (fun x hx => by simp [hx])
      obtain ⟨x_cty', x_rec_idx', htup_c, hRaw_c, hrec_c, _⟩ :=
        nat_ctor_spec hT hκ_inj hj_lt hinfo_get hwf_j hload_ctor hbnd_ctor hb₀ hbT hlps ev_ctor
      injection htup_c with hl_c
      injection hl_c with h1 hl_c; injection hl_c with h2 hl_c; injection hl_c with h3
      subst h1 h2 h3
      have hC_key : info.1 = keyOf c.t (cprjAddr (ixAddr b₀) 0 j) := by
        rcases Obs.«KernelCheck::nat_ctor».obs ev_ctor with ⟨m2_c, p9_c, cs15_c,
          w45_c, x_cty0_c, w46_c, w47_c, w48_c, w49_c, x_nf_c, w50_c, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, ev17_c, ld11_c, _, _, _, _, _, _, _, _, _, _, hc_c⟩
        subst hc_c
        exact (hload_ctor j hj_lt p9_c h m2_c cs15_c w45_c x_cty0_c w46_c w47_c w48_c w49_c
          x_nf_c w50_c (fun x hx => by simp [hx]) hb₀ ev17_c ld11_c info hinfo_get).1
      have hb₀_33 := Bytes.repAddressRef_heapMono₂ addrTy ev_ctor.heap_extends hb₀
      have hgood_proj : Good c cs_proj :=
        hgood.sub (fun x hx => by simp [hx])
      have ev_proj' : ObsFn W "KernelCheck::projection_addr_ctor"
          [.field ((0 : Nat) : F), .field (j : F), x_block] m33 v142 m151 cs_proj := by
        simpa using ev_proj
      obtain ⟨bC, hbC, hbC_addr⟩ := projection_addr_ctor_spec (by decide : 0 < 4294967296)
        (by omega : j < 4294967296) hb₀_33 hgood_proj ev_proj'
      rw [evalBinOp_add_one j op220] at ev_mty
      have ext_h_151 := ev_ctor.heap_extends.trans ev_proj.heap_extends
      have hbnd_mty : IxVM.Consistency.Bounded cs_mty :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      obtain ⟨mty, hmty_eq, hmty_tm⟩ :=
        nat_minor_ty_spec (κ := keyOf c.t) (Γ₀ := fun _ => default)
          (by rw [hbC_addr, ← hC_key])
          (by omega : 1 ≤ j + 1) hsR_pos hsE_pos hall_minor hbase_lt hbnd_mty hbC
          (RepKLevelList.mono hlps ext_h_151)
          (repKLevel_heapMono₂ ext_h_151 hpw)
          (hRaw_c.mono ev_proj.heap_extends)
          (fieldRepList_mono ev_proj.heap_extends hrec_c) ev_mty
      rw [evalBinOp_add_one j op345] at ev_rec
      have ext_h_129 := ext_h_151.trans ev_mty.heap_extends
      have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hgood_rec : Good c cs_rec :=
        hgood.sub (fun x hx => by simp [hx])
      have hload_rec : NatCtorLoad (keyOf c.t) b₀ k ctors_info x_block cs_rec :=
        hload.mono_calls (fun x hx => by simp [hx])
      obtain ⟨rest_out, hrest_eq, hrest_tm⟩ :=
        nat_minors_spec hT hκ_inj hnCtors_lt hwf_all rem (j + 1) (by omega)
          hload_rec hgood_rec hbnd_rec
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hb₀)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_129 hbT)
          (RepKLevelList.mono hlps ext_h_129)
          (repKLevel_heapMono₂ ext_h_129 hpw)
          (hbody.mono ext_h_129) ev_rec
      simp only [↓reduceIte] at hrest_eq ⊢
      have ext_end : Heap.Extends m244
          (m244 ++ [.construct kexprEnum "Lam" [v128, v243, x_pw]]) :=
        Heap.Extends.snoc _ _
      refine ⟨.lam mty rest_out { pw := ℓ.zeronessOf }, ?_, ?_⟩
      · rw [hdrop_j, List.map_cons, cMinorsLams, hmty_eq]
        dsimp only [Option.bind]
        rw [hrest_eq, Option.map_some]
      · have hmty_end : Tm (keyOf c.t) 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Lam" [v128, v243, x_pw]])
            (nP + j + 1) mty v128 := by
          rw [show nP + j + 1 = nP + (j + 1) by omega]
          exact (hmty_tm.mono ev_rec.heap_extends).mono ext_end
        have hrest_end : Tm (keyOf c.t) 0 (fun _ => default)
            (m244 ++ [.construct kexprEnum "Lam" [v128, v243, x_pw]])
            ((nP + j + 1) + 1) rest_out v243 := by
          rw [show (nP + j + 1) + 1 = nP + (j + 1) + 1 by omega]
          exact hrest_tm.mono ext_end
        exact .lam (by simp) hmty_end hrest_end
          (repKLevel_heapMono₂ (ext_h_129.trans (ev_rec.heap_extends.trans ext_end)) hpw)

/-- When raw former term `R` is already a syntactic `rem`-binder `∀`-telescope
(`R.stripPis rem = some _`), `KernelCheck::nat_former_tele` takes only the `Forall` spine without
invoking `whnf` and returns a pointer representing the exact same `RawTm` pair `(R, E)`. -/
theorem nat_former_tele_syntactic_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr} :
    ∀ (rem : Nat) {k : Nat} {R E rbody : KExpr} {rbs : List (KExpr × Ix.Kernel.BinderMeta)}
      {x_rc x_ty x_types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      rem < 4294967296 →
      R.stripPis rem = some (rbs, rbody) →
      RawTm κ 0 Γ₀ h k R E x_ty →
      ObsFn W "KernelCheck::nat_former_tele" [x_rc, x_ty, .field (rem : F), x_types] h r h' cs →
      RawTm κ 0 Γ₀ h' k R E r
  | 0, k, R, E, _, _, _, x_ty, _, r, h, h', _, _, _, hRaw, ev => by
    match Obs.«KernelCheck::nat_former_tele».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact hRaw
    | .other_Forall (hne19 := hne) .. =>
      exact absurd rfl hne
    | .other_other (hne19 := hne) .. =>
      exact absurd rfl hne
  | m + 1, k, R, E, rbody, rbs, x_rc, x_ty, x_types, r, h, h', cs, hlt, hs, hRaw, ev => by
    have hR_forall : ∃ rdom rbo rbi rbs', R = .forallE rdom rbo rbi ∧
        rbo.stripPis m = some (rbs', rbody) := by
      cases R with
      | forallE rdom rbo rbi =>
        rw [Expr.stripPis, Option.map_eq_some_iff] at hs
        obtain ⟨⟨rbs', rbody'⟩, hs', hp⟩ := hs
        injection hp with _ hb_eq
        subst hb_eq
        exact ⟨rdom, rbo, rbi, rbs', rfl, hs'⟩
      | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
      | lit _ | proj _ _ _ => nomatch hs
    obtain ⟨rdom, rbo, rbi, rbs', rfl, hs'⟩ := hR_forall
    match Obs.«KernelCheck::nat_former_tele».obs ev with
    | .n0 (hv14 := hv14) .. =>
      have hval := congrArg ZMod.val (Value.field.inj hv14)
      have h1 : ZMod.val ((m + 1 : Nat) : F) = m + 1 :=
        ZMod.val_natCast_of_lt (Nat.lt_trans hlt (by decide))
      rw [h1, ZMod.val_zero] at hval
      omega
    | .other_other (ld34 := ld34) (hne157 := hne157) .. =>
      cases hRaw with
      | forallE cell _ _ _ =>
        rw [loadValue_enum_cell cell] at ld34
        injection ld34 with hv
        exact (hne157 [_, _, _] rfl hv.symm).elim
    | .other_Forall (x_d := x_d) (x_b := x_b) (x_m := x_m) (v66 := v66) (m76 := m76)
        (v89 := v89) (m121 := m121)
        (ld34 := ld34) (he61 := hr) (hm60 := hm_end) (op118 := op118) (hm129 := hm121)
        (ev86 := ev_rec) .. =>
      subst hr hm_end
      cases hRaw with
      | forallE cell hdom hbo hlpw =>
        obtain ⟨-, hxs⟩ := load_cell cell ld34
        injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3
        symm at h1 h2 h3
        subst h1 h2 h3
        rw [evalBinOp_sub_succ m op118] at ev_rec
        have ext_121 : Heap.Extends h m121 := by rw [hm121]; exact Heap.Extends.snoc _ _
        have hbo_rec := nat_former_tele_syntactic_spec m (by omega) hs' (hbo.mono ext_121) ev_rec
        have ext_end : Heap.Extends m76
            (m76 ++ [.construct kexprEnum "Forall" [x_d, v66, x_m]]) := Heap.Extends.snoc _ _
        exact .forallE (by simp)
          (((hdom.mono ext_121).mono ev_rec.heap_extends).mono ext_end)
          (hbo_rec.mono ext_end)
          (repKLevel_heapMono₂ (ext_121.trans (ev_rec.heap_extends.trans ext_end)) hlpw)

/-- `KernelCheck::nat_ih_apps` builds `(is.map fun i => Ix.Kernel.structIhApp ...)` at binder depth
`nP + 1 + n + nF`. -/
theorem nat_ih_apps_spec {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {T recC : KKey} {bRec : Bytes.Address} {rlvls_c : List KLevel}
    {nP n nF : Nat} {ℓ : KLevel} {Rcty Ecty rbody ebody : KExpr}
    {rcbs ecbs : List (KExpr × Ix.Kernel.BinderMeta)}
    (hRec : κ (ixAddr bRec) = recC)
    (hnPF_lt : nP + nF < 2147483648)
    (hsR : Rcty.stripPis (nP + nF) = some (rcbs, rbody))
    (hsE : Ecty.stripPis (nP + nF) = some (ecbs, ebody)) :
    ∀ {is : List Nat}
      {x_rec x_rlvls x_pw x_rec_idx x_cty r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ i ∈ is, i < nF ∧
        RawRecSpine T (rcbs.getD (nP + i) default).1 (ecbs.getD (nP + i) default).1 ∧
        nP + 1 + n + nF + (Ix.Kernel.structFieldTeleOf Ecty nP nF i).length < 4294967296) →
      nP + 1 + n + nF < 4294967296 →
      IxVM.Consistency.Bounded cs →
      Bytes.RepAddressRef addrTy h bRec x_rec →
      RepKLevelList h rlvls_c x_rlvls →
      RepKLevel h ℓ x_pw →
      RepList fieldListEnum (fun _ (idx : Nat) v => v = .field (idx : F)) h is x_rec_idx →
      RawTm κ 0 Γ₀ h 0 Rcty Ecty x_cty →
      ObsFn W "KernelCheck::nat_ih_apps"
        [x_rec, x_rlvls, x_pw, .field (nP : F), .field (n : F), .field (nF : F),
          x_rec_idx, x_cty] h r h' cs →
      RepList kexprListEnum (fun h E p => Tm κ 0 Γ₀ h (nP + 1 + n + nF) E p) h'
        (is.map (fun i => Ix.Kernel.structIhApp recC rlvls_c ℓ.zeronessOf nP n nF i
          (Ix.Kernel.structFieldTeleOf Ecty nP nF i)
          (Ix.Kernel.structFieldIdxOf Ecty nP nF i))) r := by
  intro is
  induction is with
  | nil =>
    intro x_rec x_rlvls x_pw x_rec_idx x_cty r h h' cs _ _ _ _ _ _ his _ ev
    match Obs.«KernelCheck::nat_ih_apps».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      subst hr hm
      exact .nil (by simp)
    | .Cons (ld12 := ld) .. =>
      have ld' : loadValue h x_rec_idx = .ok (.construct fieldListEnum "Cons" [_, _]) := ld
      cases his with | nil cell => exact (load_cell_ne cell ld' (by decide)).elim
  | cons i rest ih =>
    intro x_rec x_rlvls x_pw x_rec_idx x_cty r h h' cs hall hlt_base hbnd hbR hrlvls hpw his hRaw ev
    match Obs.«KernelCheck::nat_ih_apps».obs ev with
    | .Nil (ld12 := ld) .. =>
      have ld' : loadValue h x_rec_idx = .ok (.construct fieldListEnum "Nil" []) := ld
      cases his with | cons cell _ _ => exact (load_cell_ne cell ld' (by decide)).elim
    | .Cons (m47 := m47) (x_tele := x_tele) (x_idx := x_idx) (v97 := v97) (m98 := m98)
        (v119 := v119) (m120 := m120) (v133 := v133) (v134 := v134) (m136 := m136)
        (v147 := v147) (m150 := m150) (v161 := v161) (x169 := x169) (x177 := x177)
        (m204 := m204) (v216 := v216) (x223 := x223) (m243 := m243) (v254 := v254)
        (v279 := v279) (m280 := m280) (v294 := v294) (m296 := m296) (v308 := v308)
        (x315 := x315) (x323 := x323) (m343 := m343) (v369 := v369) (m370 := m370)
        (v383 := v383) (m386 := m386) (v398 := v398) (m407 := m407) (cs415 := cs_map)
        (v419 := v419) (v480 := v480) (m481 := m481) (v494 := v494) (v495 := v495)
        (m498 := m498) (cs506 := cs_ta) (v510 := v510) (m572 := m572) (m586 := m586)
        (v636 := v636) (m645 := m645) (cs653 := cs_rec)
        (ld12 := ld) (ev59 := ev_ft) (ev110 := ev_len)
        (op192 := op192) (op184 := op184) (op176 := op176) (ev160 := ev_psP)
        (hm212 := hm204) (op238 := op238) (op230 := op230) (ev146 := ev_snoc1)
        (op269 := op269) (ev253 := ev_psN) (ev132 := ev_cat1)
        (hm304 := hm296) (op338 := op338) (op330 := op330) (op322 := op322)
        (ev353 := ev_psM) (ev292 := ev_app_fi)
        (op444 := op444) (ev417 := ev_map) (ev396 := ev_cat2) (ev382 := ev_snoc2)
        (op536 := op536) (ev508 := ev_ta) (hm594 := hm586) (ev582 := ev_app_rec)
        (ev493 := ev_mk) (he631 := hr) (hm630 := hm_end) (ev655 := ev_rec) (hc720 := hc) .. =>
      subst hc hr hm_end
      obtain ⟨i', rest', heq, hi_eq, hrest_rep⟩ := RepList.cons_of_load his ld
      injection heq with h1 h2; subst h1 h2; subst hi_eq
      obtain ⟨hi_lt, hspine_i, hlt_m⟩ := hall i List.mem_cons_self
      let tele_i := Ix.Kernel.structFieldTeleOf Ecty nP nF i
      let idx_i := Ix.Kernel.structFieldIdxOf Ecty nP nF i
      let m := tele_i.length
      have hlt_m' : nP + 1 + n + nF + m < 4294967296 := hlt_m
      obtain ⟨ptele, pidx, htup_ft, htele_m47, hidx_m47⟩ :=
        nat_field_tele_spec hi_lt (by omega) hRaw hsR hsE hspine_i ev_ft
      injection htup_ft with hl_ft; injection hl_ft with h1 hl_ft; injection hl_ft with h2
      subst h1 h2
      obtain ⟨hv97, hm98⟩ := tele_length_spec ev_len htele_m47
      rw [hm98] at ev_psP
      have hv97' : v97 = .field (m : F) := hv97
      rw [hv97'] at op192 op238 op269 op322 ev_psM ev_map
      -- `structRecPrefixAt nP n nF m`
      rw [evalBinOp_add_nat m nF op192] at op184
      rw [evalBinOp_add_nat (m + nF) n op184] at op176
      rw [evalBinOp_add_one (m + nF + n) op176] at ev_psP
      have hpsP := nat_ps_at_spec (κ := κ) (d := 0) (Γ := Γ₀)
        nP (m + nF + n + 1) (nP + 1 + n + nF + m) (by omega) hlt_m' ev_psP
      rw [evalBinOp_add_nat m nF op238] at op230
      rw [evalBinOp_add_nat (m + nF) n op230] at hm204
      have ext_m204 : Heap.Extends m150 m204 := by rw [hm204]; exact Heap.Extends.snoc _ _
      have hbvar_mot : Tm κ 0 Γ₀ m204 (nP + 1 + n + nF + m)
          (.bvar (m + nF + n)) (.ptr (.enum kexprEnum) m150.length) := by
        rw [hm204]; exact tm_bvarLocal_nat (by simp) (by omega) (by omega)
      have hsnoc1 := SubstAux.ksnoc (R := fun h E p => Tm κ 0 Γ₀ h (nP + 1 + n + nF + m) E p)
        (fun _ _ _ _ ext r => Tm.mono ext r) ev_snoc1 (tmRepList_mono ext_m204 hpsP) hbvar_mot
      rw [evalBinOp_add_nat m nF op269] at ev_psN
      have hpsN := nat_ps_at_spec (κ := κ) (d := 0) (Γ := Γ₀)
        n (m + nF) (nP + 1 + n + nF + m) (by omega) hlt_m' ev_psN
      have hpref := kexpr_list_concat_spec' ev_cat1
        (tmRepList_mono ev_psN.heap_extends hsnoc1) hpsN
      have hpref_eq :
          Ix.Kernel.structPsAt (m + nF + n + 1) nP ++ [.bvar (m + nF + n)] ++
            Ix.Kernel.structPsAt (m + nF) n =
          Ix.Kernel.structRecPrefixAt (md := .anon) nP n nF m := by
        rfl
      rw [hpref_eq] at hpref
      -- `f_i a⃗`
      rw [evalBinOp_sub_nat (by omega : 1 ≤ nF) op338] at op330
      rw [evalBinOp_sub_nat (by omega : i ≤ nF - 1) op330] at op322
      rw [evalBinOp_add_nat (nF - 1 - i) m op322] at hm296
      have ext_m296 : Heap.Extends m120 m296 := by rw [hm296]; exact Heap.Extends.snoc _ _
      have hbvar_fi : Tm κ 0 Γ₀ m296 (nP + 1 + n + nF + m)
          (.bvar (nF - 1 - i + m)) (.ptr (.enum kexprEnum) m120.length) := by
        rw [hm296]; exact tm_bvarLocal_nat (by simp) (by omega) (by omega)
      have hpsM := nat_ps_at_spec (κ := κ) (d := 0) (Γ := Γ₀)
        m 0 (nP + 1 + n + nF + m) (by omega) hlt_m' ev_psM
      rw [structPsAt_zero_eq_structTeleVars] at hpsM
      have hfi_app := nat_app_n_spec (hbvar_fi.mono ev_psM.heap_extends) hpsM ev_app_fi
      -- `idx_i.map (structIdxAt nF (n + 1) i 0 m)` and full spine
      rw [evalBinOp_add_one n op444] at ev_map
      have ext_47_280 := ev_psP.heap_extends.trans (ext_m204.trans (ev_snoc1.heap_extends.trans
        (ev_psN.heap_extends.trans (ev_cat1.heap_extends.trans (ext_m296.trans
          (ev_psM.heap_extends.trans ev_app_fi.heap_extends))))))
      have hidx_280 : RepList kexprListEnum (fun h E p => Tm κ 0 Γ₀ h (nP + i + m) E p)
          m280 idx_i x_idx := by
        simpa [Nat.zero_add] using tmRepList_mono ext_47_280 hidx_m47
      have hbnd_map : IxVM.Consistency.Bounded cs_map :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hmap_idx := nat_map_idx_at_spec (k_base := nP) (o := n + 1) (l := 0) (m := m)
        (by omega : i ≤ nF) (by omega) hbnd_map hidx_280 ev_map
      have hmap_idx' : RepList kexprListEnum
          (fun h E p => Tm κ 0 Γ₀ h (nP + 1 + n + nF + m) E p)
          m407 (idx_i.map (Ix.Kernel.structIdxAt nF (n + 1) i 0 m)) v398 := by
        rw [show nP + (n + 1) + nF + 0 + m = nP + 1 + n + nF + m by omega] at hmap_idx
        exact hmap_idx
      have ext_120_407 := ext_m296.trans (ev_psM.heap_extends.trans
        (ev_app_fi.heap_extends.trans ev_map.heap_extends))
      have hcat2 := kexpr_list_concat_spec' ev_cat2 (tmRepList_mono ext_120_407 hpref) hmap_idx'
      have hsnoc2 := SubstAux.ksnoc (R := fun h E p => Tm κ 0 Γ₀ h (nP + 1 + n + nF + m) E p)
        (fun _ _ _ _ ext r => Tm.mono ext r) ev_snoc2 hcat2
        ((hfi_app.mono ev_map.heap_extends).mono ev_cat2.heap_extends)
      -- `nat_tele_at`, `Const`, `nat_app_n`, `nat_mk_binders`
      rw [evalBinOp_add_one n op536] at ev_ta
      have ext_47_370 := ext_47_280.trans
        (ev_map.heap_extends.trans (ev_cat2.heap_extends.trans ev_snoc2.heap_extends))
      have ext_h_370 := ev_ft.heap_extends.trans ext_47_370
      have hbnd_ta : IxVM.Consistency.Bounded cs_ta :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have htele_370 := htele_m47.mono ext_47_370
      rw [Nat.zero_add] at htele_370
      have hta := nat_tele_at_spec (k_base := nP) (o := n + 1) (l := 0)
        (by omega : i ≤ nF) (by omega) hbnd_ta
        (repKLevel_heapMono₂ ext_h_370 hpw) htele_370 ev_ta
      have hta' : TeleRep κ 0 Γ₀ m498 (nP + 1 + n + nF)
          (Ix.Kernel.structTeleAt nF (n + 1) i 0 ℓ.zeronessOf tele_i) v494 := by
        rw [show nP + (n + 1) + nF + 0 = nP + 1 + n + nF by omega] at hta
        exact hta
      have ext_m586 : Heap.Extends m498 m586 := by rw [hm586]; exact Heap.Extends.snoc _ _
      have ext_h_498 := ext_h_370.trans ev_ta.heap_extends
      have ext_h_586 := ext_h_498.trans ext_m586
      have hconst_rec : Tm κ 0 Γ₀ m586 (nP + 1 + n + nF + m)
          (.const recC rlvls_c) (.ptr (.enum kexprEnum) m498.length) := by
        rw [← hRec]
        exact .const (by rw [hm586]; simp)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_586 hbR)
          (RepKLevelList.mono hrlvls ext_h_586)
          (LvEqList.refl _)
      have happ_rec := nat_app_n_spec hconst_rec
        (tmRepList_mono (ev_ta.heap_extends.trans ext_m586) hsnoc2) ev_app_rec
      have hta_len : (Ix.Kernel.structTeleAt nF (n + 1) i 0 ℓ.zeronessOf tele_i).length = m := by
        simp [Ix.Kernel.structTeleAt, m]
      have happ_rec' : Tm κ 0 Γ₀ m572
          ((nP + 1 + n + nF) + (Ix.Kernel.structTeleAt nF (n + 1) i 0 ℓ.zeronessOf tele_i).length)
          (Expr.mkAppN (.const recC rlvls_c)
            (Ix.Kernel.structRecPrefixAt nP n nF m ++
              idx_i.map (Ix.Kernel.structIdxAt nF (n + 1) i 0 m) ++
              [Expr.mkAppN (.bvar (nF - 1 - i + m)) (Ix.Kernel.structTeleVars m)])) v495 := by
        rw [hta_len]
        simpa [List.append_assoc] using happ_rec
      have hih_app := nat_mk_binders_spec
        (hta'.mono (ext_m586.trans ev_app_rec.heap_extends)) happ_rec' ev_mk
      have h1_ne_0 : (.field 1 : SourceValue F) ≠ .field 0 := by
        intro h01; exact absurd (Value.field.inj h01) one_ne_zero
      rw [ite_eq_right h1_ne_0] at hih_app
      -- Recursive call on `rest`
      have ext_h_481 := ext_h_586.trans (ev_app_rec.heap_extends.trans ev_mk.heap_extends)
      have hbnd_rec : IxVM.Consistency.Bounded cs_rec :=
        RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
      have hall_rest : ∀ k ∈ rest, k < nF ∧
          RawRecSpine T (rcbs.getD (nP + k) default).1 (ecbs.getD (nP + k) default).1 ∧
          nP + 1 + n + nF + (Ix.Kernel.structFieldTeleOf Ecty nP nF k).length < 4294967296 :=
        fun k hk => hall k (List.mem_cons_of_mem _ hk)
      have hrest_ih := ih hall_rest hlt_base hbnd_rec
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_481 hbR)
        (RepKLevelList.mono hrlvls ext_h_481)
        (repKLevel_heapMono₂ ext_h_481 hpw)
        (fieldRepList_mono ext_h_481 hrest_rep)
        (hRaw.mono ext_h_481) ev_rec
      have ext_end : Heap.Extends m645
          (m645 ++ [.construct kexprListEnum "Cons" [v480, v636]]) := Heap.Extends.snoc _ _
      exact .cons (by simp)
        ((hih_app.mono ev_rec.heap_extends).mono ext_end)
        (tmRepList_mono ext_end hrest_ih)

end IxVM.Refinement.Decl
