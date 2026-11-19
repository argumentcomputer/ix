import IxVMRefinement.Binding.FamilyReconCanon
import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.Binding.PayloadClosed
import IxVMRefinement.Binding.StoreLogic
import IxVMRefinement.FamilyAlias.CallLists
import IxVMRefinement.Obs.KernelCheck1
import IxVMRefinement.Obs.KernelCheck2
import IxVMRefinement.Obs.KernelCheck12
import IxVMRefinement.Obs.KernelCheck13
import IxVMRefinement.Obs.KernelModeled2
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.KernelModeled4
import IxVMRefinement.Obs.KernelModeled5

/-! # Level-parameter well-scopedness and inductive parameter coherence over run stores

This module discharges `StoreLevelsOk t E₀ (Held R)` (`IxVMRefinement.Binding.FamilyRecon`) and
`StoreIndParamsOk E₀ (Held R)` (constructors match their inductive's parameter count, and mutual
inductive peers share their parameter count) for every store `groupStore t E₀ (runPayload ...) g`
(`6 ≤ g ≤ 77`) of a collision-free bounded binding run, as well as for any `UsedClosed` store
whose units are basis rows, checked by `UnitCheckedAt`, or checked by `FamilyCallAtLim`.

* Part 1: decidable level-parameter and inductive-parameter checks over `StoreInhabit.basisRows`
  (`basisRow_constLevelsOk`, `basisRow_constIndParamsOk`), proved sound directly against
  `Ix.Kernel.Reader.MemberReader`.
* Part 2: `Assembly.validate_expr_well_scoped_spec` applied to `CheckedLimAt`,
  `MemberCheckedLimAt`, and `KernelModeled::check_family` (`check_recs` / `check_rules` /
  `check_iota_rule`), together with inductive parameter coherence from
  `check_inductive_shape_ctors`, `check_modeled_ctors`, `check_block_peer_param_agreement`, and
  `block_nparams`.
* Part 3: strong induction over `6 ≤ g ≤ 77` for `groupStore t E₀ (runPayload calls bAddr t) g`
  via `payReach_payClass_of_run` and `groupStore_usedClosed_all`. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Core (W KExpr KLevel KKey kciEnum krrEnum krrListEnum addrTy addrListEnum
  ixAddr)
open IxVM.Refinement.Binding
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open IxVM (F)

set_option maxHeartbeats 2400000
set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem mem_of_eq {α : Type*} {x : α} {l₁ l₂ : List α} (heq : l₁ = l₂) (h : x ∈ l₂) :
    x ∈ l₁ :=
  heq ▸ h

local syntax "call_mem" : tactic
local macro_rules
  | `(tactic| call_mem) =>
    `(tactic| repeat first
      | assumption
      | exact List.mem_cons_self
      | exact List.mem_append_left _ (by assumption)
      | exact List.mem_append_left _ List.mem_cons_self
      | apply List.mem_cons_of_mem
      | apply List.mem_append_right)

/-! ## Inductive parameter coherence predicate -/

/-- **Inductive parameter coherence over a store subset `S`**: every constructor of an inductive
block in `S` has the same parameter count as its parent inductive, and any two inductive members
of the same block in `S` share their parameter count. -/
structure StoreIndParamsOk (E : Ixon.Env) (S : _root_.Address → Prop) : Prop where
  ctorParams : ∀ (b : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor),
    S b → recordOf E b = some cb → cb.info = .muts ms →
    ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct → ct.params = ind.params
  blockParams : ∀ (b : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (i₁ i₂ : Nat) (ind₁ ind₂ : Ixon.Inductive),
    S b → recordOf E b = some cb → cb.info = .muts ms →
    ms[i₁]? = some (.indc ind₁) → ms[i₂]? = some (.indc ind₂) → ind₁.params = ind₂.params

/-! ## Part 1: Pure level-parameter check and basis rows -/

private def univVarsLt (n : Nat) : Ixon.Univ → Bool
  | .zero => true
  | .succ u => univVarsLt n u
  | .max a b => univVarsLt n a && univVarsLt n b
  | .imax a b => univVarsLt n a && univVarsLt n b
  | .var i => decide (i.toNat < n)

private theorem convUniv_allParamsDefined {n : Nat} :
    ∀ u : Ixon.Univ, univVarsLt n u = true →
      (Ix.Kernel.Reader.convUniv id u).allParamsDefined (List.range n) = true
  | .zero, _ => rfl
  | .succ u, h => convUniv_allParamsDefined u h
  | .max a b, h => by
    simp only [univVarsLt, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Reader.convUniv, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨convUniv_allParamsDefined a h.1, convUniv_allParamsDefined b h.2⟩
  | .imax a b, h => by
    simp only [univVarsLt, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Reader.convUniv, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨convUniv_allParamsDefined a h.1, convUniv_allParamsDefined b h.2⟩
  | .var i, h => by
    simp only [univVarsLt, decide_eq_true_eq] at h
    simp only [Ix.Kernel.Reader.convUniv, id, Ix.Kernel.Level.allParamsDefined, List.contains_eq_mem,
      decide_eq_true_eq, List.mem_range]
    exact h

private def univIdxOk (univs : Array Ixon.Univ) (n : Nat) (i : UInt64) : Bool :=
  match univs[i.toNat]? with
  | some u => univVarsLt n u
  | none => true

private def exprUnivsLtGo (univs : Array Ixon.Univ) (n : Nat) (tbl : Array Bool) :
    Ixon.Expr → Bool
  | .var _ | .str _ | .nat _ => true
  | .sort i => univIdxOk univs n i
  | .ref _ us | .recur _ us => us.toList.all (univIdxOk univs n)
  | .prj _ _ v => exprUnivsLtGo univs n tbl v
  | .app f a => exprUnivsLtGo univs n tbl f && exprUnivsLtGo univs n tbl a
  | .lam t b | .all t b => exprUnivsLtGo univs n tbl t && exprUnivsLtGo univs n tbl b
  | .letE _ _ t v b =>
    exprUnivsLtGo univs n tbl t && exprUnivsLtGo univs n tbl v && exprUnivsLtGo univs n tbl b
  | .share i => tbl.getD i.toNat true

private def buildUnivsOkTblGo (univs : Array Ixon.Univ) (n : Nat) :
    Array Bool → List Ixon.Expr → Array Bool
  | acc, [] => acc
  | acc, e :: es => buildUnivsOkTblGo univs n (acc.push (exprUnivsLtGo univs n acc e)) es

private def exprUnivsOk (src : Ixon.Constant) (n : Nat) (e : Ixon.Expr) : Bool :=
  exprUnivsLtGo src.univs n (buildUnivsOkTblGo src.univs n #[] src.sharing.toList) e

private theorem ecx_level_allParamsDefined {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat} {i : UInt64} {l : KLevel}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id))
    (hok : univIdxOk univs n i = true)
    (hl : ecx.level i = .ok l) :
    l.allParamsDefined (List.range n) = true := by
  unfold Ix.Kernel.Reader.ECx.level at hl
  rw [hunivs, Array.getElem?_map] at hl
  unfold univIdxOk at hok
  cases hget : univs[i.toNat]? with
  | none => rw [hget] at hl; simp [Ix.Kernel.Reader.malformed] at hl
  | some u =>
    rw [hget] at hl hok
    simp only [Option.map_some] at hl
    have heq : Ix.Kernel.Reader.convUniv id u = l := Except.ok.inj hl
    rw [← heq]
    exact convUniv_allParamsDefined u hok

private theorem ecx_levels_allParamsDefined {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id)) :
    ∀ (us : List UInt64) (ls : List KLevel),
      us.all (univIdxOk univs n) = true →
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
        exact ⟨ecx_level_allParamsDefined hunivs hok.1 hl,
          ecx_levels_allParamsDefined hunivs us ls' hok.2 hls⟩

private theorem convExpr_allLevelParamsDefined {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat}
    {shareTbl : Array (Ix.Kernel.Reader.ReadM KExpr)} {okTbl : Array Bool}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id))
    (htbl : ∀ i E_rd, shareTbl[i]? = some (.ok E_rd) → okTbl.getD i true = true →
      E_rd.allLevelParamsDefined (List.range n) = true) :
    ∀ (e : Ixon.Expr) (E_rd : KExpr),
      exprUnivsLtGo univs n okTbl e = true →
      Ix.Kernel.Reader.convExpr ecx shareTbl e = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range n) = true
  | .var i, E_rd, _, h => by
    simp only [Ix.Kernel.Reader.convExpr, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [Ix.Kernel.Expr.mkBvar_eq]; rfl
  | .sort i, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hl : ecx.level i with
    | error _ => rw [hl] at h; cases h
    | ok l =>
      rw [hl] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ecx_level_allParamsDefined hunivs hok hl
  | .ref i us, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hk : ecx.keyAt i with
    | error _ => rw [hk] at h; cases h
    | ok k =>
      rw [hk] at h
      cases hls : ecx.levels us with
      | error _ => rw [hls] at h; cases h
      | ok ls =>
        rw [hls] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ecx_levels_allParamsDefined hunivs us.toList ls hok hls
  | .recur i us, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr] at h
    cases hs : ecx.self i.toNat with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs] at h
      simp only [bind, Except.bind] at h
      cases hm : m with
      | error _ => rw [hm] at h; cases h
      | ok k =>
        rw [hm] at h
        cases hls : ecx.levels us with
        | error _ => rw [hls] at h; cases h
        | ok ls =>
          rw [hls] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ecx_levels_allParamsDefined hunivs us.toList ls hok hls
  | .prj i f v, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hk : ecx.keyAt i with
    | error _ => rw [hk] at h; cases h
    | ok k =>
      rw [hk] at h
      cases hv : Ix.Kernel.Reader.convExpr ecx shareTbl v with
      | error _ => rw [hv] at h; cases h
      | ok ev =>
        rw [hv] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact convExpr_allLevelParamsDefined hunivs htbl v ev hok hv
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
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; rfl
  | .nat i, E_rd, _, h => by
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hn : ecx.natAt i with
    | error _ => rw [hn] at h; cases h
    | ok m =>
      rw [hn] at h; dsimp only at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; rfl
  | .app f a, E_rd, hok, h => by
    simp only [exprUnivsLtGo, Bool.and_eq_true] at hok
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases hf : Ix.Kernel.Reader.convExpr ecx shareTbl f with
    | error _ => rw [hf] at h; cases h
    | ok ef =>
      rw [hf] at h
      cases ha : Ix.Kernel.Reader.convExpr ecx shareTbl a with
      | error _ => rw [ha] at h; cases h
      | ok ea =>
        rw [ha] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true]
        exact ⟨convExpr_allLevelParamsDefined hunivs htbl f ef hok.1 hf,
          convExpr_allLevelParamsDefined hunivs htbl a ea hok.2 ha⟩
  | .lam t b, E_rd, hok, h => by
    simp only [exprUnivsLtGo, Bool.and_eq_true] at hok
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases ht : Ix.Kernel.Reader.convExpr ecx shareTbl t with
    | error _ => rw [ht] at h; cases h
    | ok et =>
      rw [ht] at h
      cases hb : Ix.Kernel.Reader.convExpr ecx shareTbl b with
      | error _ => rw [hb] at h; cases h
      | ok eb =>
        rw [hb] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true,
          Ix.Kernel.BinderMeta.leanNever, Ix.Kernel.PropWhen.paramsDefined]
        exact ⟨⟨convExpr_allLevelParamsDefined hunivs htbl t et hok.1 ht,
          convExpr_allLevelParamsDefined hunivs htbl b eb hok.2 hb⟩, rfl⟩
  | .all t b, E_rd, hok, h => by
    simp only [exprUnivsLtGo, Bool.and_eq_true] at hok
    simp only [Ix.Kernel.Reader.convExpr, bind, Except.bind] at h
    cases ht : Ix.Kernel.Reader.convExpr ecx shareTbl t with
    | error _ => rw [ht] at h; cases h
    | ok et =>
      rw [ht] at h
      cases hb : Ix.Kernel.Reader.convExpr ecx shareTbl b with
      | error _ => rw [hb] at h; cases h
      | ok eb =>
        rw [hb] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true,
          Ix.Kernel.BinderMeta.leanNever, Ix.Kernel.PropWhen.paramsDefined]
        exact ⟨⟨convExpr_allLevelParamsDefined hunivs htbl t et hok.1 ht,
          convExpr_allLevelParamsDefined hunivs htbl b eb hok.2 hb⟩, rfl⟩
  | .letE _ _ t v b, E_rd, hok, h => by
    simp only [exprUnivsLtGo, Bool.and_eq_true] at hok
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
          rw [hb] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true]
          exact ⟨⟨convExpr_allLevelParamsDefined hunivs htbl t et hok.1.1 ht,
            convExpr_allLevelParamsDefined hunivs htbl v ev hok.1.2 hv⟩,
            convExpr_allLevelParamsDefined hunivs htbl b eb hok.2 hb⟩
  | .share i, E_rd, hok, h => by
    simp only [Ix.Kernel.Reader.convExpr] at h
    cases hg : shareTbl[i.toNat]? with
    | none => rw [hg] at h; cases h
    | some r =>
      rw [hg] at h; dsimp only at h
      exact htbl i.toNat E_rd (by rw [hg, h]) hok

private theorem buildUnivsOkTblGo_sound {ecx : Ix.Kernel.Reader.ECx .anon}
    {univs : Array Ixon.Univ} {n : Nat}
    (hunivs : ecx.univs = univs.map (Ix.Kernel.Reader.convUniv id)) :
    ∀ (es : List Ixon.Expr) (shareAcc : Array (Ix.Kernel.Reader.ReadM KExpr))
      (okAcc : Array Bool),
      shareAcc.size = okAcc.size →
      (∀ i E_rd, shareAcc[i]? = some (.ok E_rd) → okAcc.getD i true = true →
        E_rd.allLevelParamsDefined (List.range n) = true) →
      ∀ i E_rd, (L1.buildShareTblGo ecx shareAcc es)[i]? = some (.ok E_rd) →
        (buildUnivsOkTblGo univs n okAcc es).getD i true = true →
        E_rd.allLevelParamsDefined (List.range n) = true
  | [], shareAcc, okAcc, _, hinv, i, E_rd, hs, hok => hinv i E_rd hs hok
  | e :: es, shareAcc, okAcc, hsz, hinv, i, E_rd, hs, hok => by
    refine buildUnivsOkTblGo_sound hunivs es
      (shareAcc.push (Ix.Kernel.Reader.convExpr ecx shareAcc e))
      (okAcc.push (exprUnivsLtGo univs n okAcc e)) (by simp [hsz]) ?_ i E_rd hs hok
    intro j E' hj hokj
    by_cases hlt : j < shareAcc.size
    · rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt] at hj
      have hlt' : j < okAcc.size := by omega
      have hgetd : (okAcc.push (exprUnivsLtGo univs n okAcc e)).getD j true = okAcc.getD j true := by
        simp [Array.getD, hlt', Array.size_push, Nat.lt_succ_of_lt hlt', Array.getElem_push_lt hlt']
      rw [hgetd] at hokj
      exact hinv j E' hj hokj
    · have hj_eq : j = shareAcc.size := by
        have hlt_p := (Array.getElem?_eq_some_iff.mp hj).1
        simp only [Array.size_push] at hlt_p; omega
      subst hj_eq
      rw [Array.getElem?_push_size] at hj
      have hconv := Option.some.inj hj
      have hgetd : (okAcc.push (exprUnivsLtGo univs n okAcc e)).getD shareAcc.size true =
          exprUnivsLtGo univs n okAcc e := by
        simp [Array.getD, hsz]
      rw [hgetd] at hokj
      exact convExpr_allLevelParamsDefined hunivs hinv e E' hokj hconv

private theorem exprUnivsOk_sound {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)} {n : Nat} {e : Ixon.Expr} {E_rd : KExpr}
    (hok : exprUnivsOk src n e = true)
    (hread : (Ix.Kernel.Reader.MemberReader.mk' cx src id self).read e = .ok E_rd) :
    E_rd.allLevelParamsDefined (List.range n) = true := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq cx src id self
  unfold Ix.Kernel.Reader.MemberReader.read at hread
  rw [hecx, htbl] at hread
  have hinv := buildUnivsOkTblGo_sound
    (ecx := ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv id), self⟩)
    (univs := src.univs) (n := n) rfl src.sharing.toList #[] #[] rfl
    (fun i _ h => by simp at h)
  exact convExpr_allLevelParamsDefined rfl hinv e E_rd hok hread

private def constLevelsOkBool (c : Ixon.Constant) : Bool :=
  match c.info with
  | .defn d =>
    if d.kind == .defn then decide (d.lvls.toNat < 4294967296) && exprUnivsOk c d.lvls.toNat d.value
    else true
  | .muts ms =>
    ms.toList.all fun m =>
      match m with
      | .defn d =>
        if d.kind == .defn then decide (d.lvls.toNat < 4294967296) && exprUnivsOk c d.lvls.toNat d.value
        else true
      | .indc ind =>
        decide (ind.lvls.toNat < 4294967296) && exprUnivsOk c ind.lvls.toNat ind.typ &&
          ind.ctors.toList.all fun ct =>
            decide (ct.lvls.toNat < 4294967296) && exprUnivsOk c ct.lvls.toNat ct.typ
      | .recr r =>
        decide (r.lvls.toNat < 4294967296) && exprUnivsOk c r.lvls.toNat r.typ &&
          r.rules.toList.all fun ru => exprUnivsOk c r.lvls.toNat ru.rhs
  | _ => true

private def constIndParamsOkBool (c : Ixon.Constant) : Bool :=
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
private theorem basisRows_levelsOk_bool :
    StoreInhabit.basisRows.all (fun e => constLevelsOkBool e.2) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
private theorem basisRows_indParamsOk_bool :
    StoreInhabit.basisRows.all (fun e => constIndParamsOkBool e.2) = true := by
  decide +kernel

private theorem basisRow_constLevelsOk {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf StoreInhabit.basisStore a = some c) :
    constLevelsOkBool c = true :=
  List.all_eq_true.mp basisRows_levelsOk_bool (a, c) (StoreInhabit.store_record_inv h)

private theorem basisRow_constIndParamsOk {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf StoreInhabit.basisStore a = some c) :
    constIndParamsOkBool c = true :=
  List.all_eq_true.mp basisRows_indParamsOk_bool (a, c) (StoreInhabit.store_record_inv h)

/-- Unit-level bundle capturing all level-parameter and inductive-parameter invariants of a
single record `c` at address `a`. -/
structure UnitLevelsAndParamsOk (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (a : _root_.Address) (c : Ixon.Constant) : Prop where
  defnVal : ∀ (d : Ixon.Definition), c.info = .defn d → d.kind = .defn →
    d.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) c id (soloSelf t a)).read d.value = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range d.lvls.toNat) = true
  mutDefn : ∀ (ms : Array Ixon.MutConst) (i : Nat) (d : Ixon.Definition),
    c.info = .muts ms → ms[i]? = some (.defn d) → d.kind = .defn →
    d.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) c id (blockSelf t a ms)).read d.value = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range d.lvls.toNat) = true
  mutInd : ∀ (ms : Array Ixon.MutConst) (i : Nat) (ind : Ixon.Inductive),
    c.info = .muts ms → ms[i]? = some (.indc ind) →
    (ind.lvls.toNat < 4294967296 ∧
      ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) c id (blockSelf t a ms)).read ind.typ = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range ind.lvls.toNat) = true) ∧
    (∀ (j : Nat) (ct : Ixon.Constructor), ind.ctors[j]? = some ct →
      ct.lvls.toNat < 4294967296 ∧
      (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) c id (blockSelf t a ms)).read ct.typ = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range ct.lvls.toNat) = true) ∧
      ct.params = ind.params) ∧
    (∀ (i₂ : Nat) (ind₂ : Ixon.Inductive), ms[i₂]? = some (.indc ind₂) → ind.params = ind₂.params)
  mutRecr : ∀ (ms : Array Ixon.MutConst) (k : Nat) (r : Ixon.Recursor),
    c.info = .muts ms → ms[k]? = some (.recr r) →
    r.lvls.toNat < 4294967296 ∧
    (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) c id (blockSelf t a ms)).read r.typ = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range r.lvls.toNat) = true) ∧
    (∀ (j : Nat) (ru : Ixon.RecursorRule) E_rd, r.rules[j]? = some ru →
      (exprReader t (fun x => E₀.blobs.get? x) c id (blockSelf t a ms)).read ru.rhs = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range r.lvls.toNat) = true)

private theorem unitLevelsAndParamsOk_of_basis {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {a : _root_.Address} {c : Ixon.Constant}
    (hb : recordOf StoreInhabit.basisStore a = some c) :
    UnitLevelsAndParamsOk t E₀ a c := by
  have hlv := basisRow_constLevelsOk hb
  have hpr := basisRow_constIndParamsOk hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hci hdk
    simp only [constLevelsOkBool, hci, hdk] at hlv
    change (decide (d.lvls.toNat < 4294967296) && exprUnivsOk c d.lvls.toNat d.value) = true at hlv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hlv
    exact ⟨hlv.1, fun E_rd hr => exprUnivsOk_sound hlv.2 hr⟩
  · intro ms i d hci hi hdk
    simp only [constLevelsOkBool, hci, List.all_eq_true] at hlv
    have hm := hlv (.defn d) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    simp only [hdk] at hm
    change (decide (d.lvls.toNat < 4294967296) && exprUnivsOk c d.lvls.toNat d.value) = true at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    exact ⟨hm.1, fun E_rd hr => exprUnivsOk_sound hm.2 hr⟩
  · intro ms i ind hci hi
    simp only [constLevelsOkBool, hci, List.all_eq_true] at hlv
    simp only [constIndParamsOkBool, hci, List.all_eq_true] at hpr
    have hml := hlv (.indc ind) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    have hmp := hpr (.indc ind) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hml hmp
    refine ⟨⟨hml.1.1, fun E_rd hr => exprUnivsOk_sound hml.1.2 hr⟩, ?_, ?_⟩
    · intro j ct hj
      have hct := hml.2 ct (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj))
      have hctp := hmp.1 ct (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj))
      exact ⟨hct.1, fun E_rd hr => exprUnivsOk_sound hct.2 hr, beq_iff_eq.mp hctp⟩
    · intro i₂ ind₂ hi₂
      have hp2 := hmp.2 (.indc ind₂) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi₂))
      exact (beq_iff_eq.mp hp2).symm
  · intro ms k r hci hk
    simp only [constLevelsOkBool, hci, List.all_eq_true] at hlv
    have hm := hlv (.recr r) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hm
    refine ⟨hm.1.1, fun E_rd hr => exprUnivsOk_sound hm.1.2 hr, ?_⟩
    intro j ru E_rd hj hr
    have hru := hm.2 ru (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj))
    exact exprUnivsOk_sound hru hr

/-- **Any `UsedClosed` sub-store `R` of `E₀` whose records satisfy `UnitLevelsAndParamsOk`**
satisfies both `StoreLevelsOk t E₀ (Held R)` and `StoreIndParamsOk E₀ (Held R)`. -/
theorem storeLevelsOk_and_indParamsOk_of_units {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c)
    (hcl : UsedClosed R)
    (hunits : ∀ a c, recordOf R a = some c → UnitLevelsAndParamsOk t E₀ a c) :
    StoreLevelsOk t E₀ (Held R) ∧ StoreIndParamsOk E₀ (Held R) := by
  have held_rec : ∀ a c, Held R a → recordOf E₀ a = some c → recordOf R a = some c := by
    intro a c ha hcE
    obtain ⟨cR, hcR⟩ := Option.isSome_iff_exists.mp ha
    have heq := Option.some.inj ((hRsub a cR hcR).symm.trans hcE)
    exact heq ▸ hcR
  have owner_held : ∀ a c, Held R a → recordOf E₀ a = some c → Held R (Ix.Cert.ownerOf a c) :=
    fun a c ha hcE => (hcl.1 a c (held_rec a c ha hcE)).1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a c d ha hcE hci hdk
    exact (hunits a c (held_rec a c ha hcE)).defnVal d hci hdk
  · intro a c p cb ms d ha hcE hci hcbE hms hi hdk
    have hpb : Held R p.block := by simpa [Ix.Cert.ownerOf, hci] using owner_held a c ha hcE
    exact (hunits p.block cb (held_rec p.block cb hpb hcbE)).mutDefn ms p.idx.toNat d hms hi hdk
  · intro a c p cb ms ind ha hcE hci hcbE hms hi
    have hpb : Held R p.block := by simpa [Ix.Cert.ownerOf, hci] using owner_held a c ha hcE
    exact ((hunits p.block cb (held_rec p.block cb hpb hcbE)).mutInd ms p.idx.toNat ind hms hi).1
  · intro b cb ms i ind j ct hb hcbE hms hi hj
    have hct := ((hunits b cb (held_rec b cb hb hcbE)).mutInd ms i ind hms hi).2.1 j ct hj
    exact ⟨hct.1, hct.2.1⟩
  · intro rb crb rs k r hrb hcrbE hrs hk
    exact (hunits rb crb (held_rec rb crb hrb hcrbE)).mutRecr rs k r hrs hk
  · intro b cb ms i ind j ct hb hcbE hms hi hj
    exact (((hunits b cb (held_rec b cb hb hcbE)).mutInd ms i ind hms hi).2.1 j ct hj).2.2
  · intro b cb ms i₁ i₂ ind₁ ind₂ hb hcbE hms hi₁ hi₂
    exact ((hunits b cb (held_rec b cb hb hcbE)).mutInd ms i₁ ind₁ hms hi₁).2.2 i₂ ind₂ hi₂

/-! ## Part 2: Discharging `UnitLevelsAndParamsOk` from circuit observations -/

private theorem record_eq_of_hashed_l {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hsub : ∀ cl ∈ cs, cl ∈ calls)
    {a : _root_.Address} {c c' : Ixon.Constant} {bytes : ByteArray}
    (hrec : recordOf E₀ a = some c) (hh : Hashed cs bytes)
    (ha : Address.blake3Pure bytes = a) (hde : Ixon.deConstantExact bytes = .ok c') :
    c' = c := by
  rw [hS.recordOf_eq_recordAt] at hrec
  exact hS.record_eq hrec (Core.hashed_mono hsub hh) ha hde

private theorem validate_reader_levels {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {nlvls : Nat} {e : Ixon.Expr} {kp r : SourceValue F} {h₀ h h' : Heap F}
    {cs : List (Call F)}
    (hbd : Bounded calls) (hnl : nlvls < 4294967296)
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h₀ 4294967295 e kp)
    (hext : Heap.Extends h₀ h)
    (ev : ObsFn W "KernelCheck::validate_expr_well_scoped"
      [kp, .field 0, .field (nlvls : F)] h r h' cs)
    (hcall : (⟨"KernelCheck::validate_expr_well_scoped",
      [kp, .field 0, .field (nlvls : F)], h⟩ : Call F) ∈ calls) :
    ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) src id self).read e = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range nlvls) = true := by
  intro E_rd hread
  exact (Assembly.validate_expr_well_scoped_spec hbd hnl raw hext hread ev hcall).2.2

/-- **`CheckedLimAt` on a standalone `.defn` with `d.kind = .defn`** validates `d.value`. -/
theorem checkedLimAt_defnVal_levelsOk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {a : _root_.Address} {lim : Option Nat}
    {c : Ixon.Constant} {d : Ixon.Definition}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hrec : recordOf E₀ a = some c) (hci : c.info = .defn d) (hdk : d.kind = .defn)
    (hchk : Claim.CheckedLimAt calls bAddr t a lim) :
    d.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) c id (soloSelf t a)).read d.value = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range d.lvls.toNat) = true := by
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    -, -, ⟨ab, rab, hab⟩, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hchk
  subst hab
  obtain ⟨-, rawBytes, c', blobs, hh, ha, hde, -, -, -, hrawRes⟩ :=
    L1.get_ci_spec (RomBound.bounded_mono hbd hsub_ld) rab ev_ld
  have hc_eq : c' = c := record_eq_of_hashed_l hS hsub_ld hrec hh ha hde
  subst hc_eq
  simp only [L1.GetCIRawResult, hci] at hrawRes
  obtain ⟨v', hld', hnl, tyPtr, valPtr, hint, rfl, -, raw_val⟩ := hrawRes
  rw [hld'] at hld; injection hld with hv; subst hv
  simp only [L1.defnValShape, hdk] at ev_chk
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Defn (ev14 := ev14) (ev311 := ev311) (ev348 := ev348) (hv269 := hv) (hc520 := hc) .. =>
    injection hv with _ _ hl
    injection hl with h1 hl; injection hl with _ hl; injection hl with h3 _
    subst h1 h3
    exact ⟨hnl, validate_reader_levels hbd hnl raw_val
      (ev14.heap_extends.trans ev311.heap_extends) ev348 (hsub_chk _ (by rw [hc]; simp))⟩
  | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) .. | .Axiom_other_other (hv37 := hv) .. =>
    simp [kciEnum] at hv
  | .Thm (hne521 := hne) .. | .Opaque (hne521 := hne) .. | .Quot (hne521 := hne) ..
  | .Induct_n0 (hne521 := hne) .. | .Induct_other_n0 (hne521 := hne) ..
  | .Induct_other_other (hne521 := hne) ..
  | .Ctor_n0_n0 (hne521 := hne) .. | .Ctor_n0_other (hne521 := hne) ..
  | .Ctor_other_n0 (hne521 := hne) .. | .Ctor_other_other (hne521 := hne) ..
  | .Rec_n0 (hne521 := hne) .. | .Rec_other (hne521 := hne) .. =>
    exact (hne _ rfl rfl).elim

/-- Unpacks `MemberCheckedLimAt` on member `k` of a block `b` into the raw loaded constant of its
projection record together with the observed `KernelCheck::check_const` call. -/
private theorem memberChecked_unpack {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {b : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {k : Nat} {m : Ixon.MutConst} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hcb : recordOf E₀ b = some cb) (hms : cb.info = .muts ms)
    (hk : ms[k]? = some m)
    (hmc : Claim.MemberCheckedLimAt calls bAddr t b ms k lim) :
    k < 72057594037927936 ∧
    ∃ (m_chk h'_chk : Heap F) (rc ap ptr v r_chk : SourceValue F)
      (cs_load cs_chk : List (Call F)) (ba : Bytes.Address)
      (blobs : List (_root_.Address × ByteArray)),
      ixAddr ba = Core.projAddr (Core.Specs.Callees.memberProjInfo b k m) ∧
      Hashed calls (Ixon.serConstant
        ⟨Core.Specs.Callees.memberProjInfo b k m, #[], #[], #[], #[]⟩) ∧
      Bytes.RepAddressRef addrTy m_chk ba ap ∧
      loadValue m_chk ptr = .ok v ∧
      L1.GetCIRawResult cs_load blobs m_chk (ixAddr ba)
        ⟨Core.Specs.Callees.memberProjInfo b k m, #[], #[], #[], #[]⟩ ptr ∧
      (∀ cl ∈ cs_load, cl ∈ calls) ∧
      ObsFn W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk ∧
      (∀ cl ∈ cs_chk, cl ∈ calls) := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem_rep, ⟨bb, rbb, hbb⟩, ev_pa, -, hsub_pa,
    -, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hmc
  subst hbb
  obtain ⟨-, -, -, mc', ba, hget', rba, hba_eq, hh_proj⟩ :=
    L1.projection_addr_hashed_spec hmem_rep rbb ev_pa
  obtain ⟨iv, hiv⟩ : ∃ iv, ((k : F)).val = iv := ⟨_, rfl⟩
  rw [hiv] at hget' hba_eq hh_proj
  obtain ⟨raw, cp, hsz, hh_h, hba_h, hx_h, -, hhead⟩ := Claim.get_ci_head rba ev_ld
  have hX : Address.blake3Pure (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (ixAddr bb) iv mc', #[], #[], #[], #[]⟩) =
      ixAddr ba := hba_eq.symm
  have hraw : raw = Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (ixAddr bb) iv mc', #[], #[], #[], #[]⟩ :=
    hS.hashed_inj (Core.hashed_mono hsub_ld hh_h) (Core.hashed_mono hsub_pa hh_proj)
      (hba_h.trans hX.symm)
  have hwf : (⟨Core.Specs.Callees.memberProjInfo (ixAddr bb) iv mc', #[], #[], #[], #[]⟩ :
      Ixon.Constant).wireWF := by
    cases mc' with
    | defn _ => exact L1.projConstant_wireWF_dPrj iv.toUInt64 bb
    | indc _ => exact L1.projConstant_wireWF_iPrj iv.toUInt64 bb
    | recr _ => exact L1.projConstant_wireWF_rPrj iv.toUInt64 bb
  rw [hraw, Ixon.Verify.deConstantExact_serConstant _ hwf] at hx_h
  injection hx_h with hcp; subst hcp
  have hblock : ∃ cb' ms', Claim.BlockLoad cs_load (ixAddr bb) cb' ms' := by
    cases mc' with
    | defn _ => obtain ⟨cb', ms', _, hbl, _⟩ := hhead.dPrj _ _ rfl; exact ⟨cb', ms', hbl⟩
    | indc _ => obtain ⟨cb', ms', _, hbl, _⟩ := hhead.iPrj _ _ rfl; exact ⟨cb', ms', hbl⟩
    | recr _ => obtain ⟨cb', ms', _, hbl, _⟩ := hhead.rPrj _ _ rfl; exact ⟨cb', ms', hbl⟩
  obtain ⟨cb', ms', hbl⟩ := hblock
  have hres := ((hbl.mono hsub_ld).record hS hcb).2
  have hsize := Claim.muts_size_le hms
  have hk_lt : k < ms.size := (Array.getElem?_eq_some_iff.mp hk).1
  have hk56 : k < 72057594037927936 := by omega
  have hiv' : iv = k := hiv.symm.trans (L1.val_cast_u56_ing hk56)
  subst hiv'
  have hmc_eq : mc' = m := by
    rw [Array.getElem?_toList] at hget'
    exact Option.some.inj (hget'.symm.trans hk)
  subst hmc_eq
  obtain ⟨ext_ld, rawBytes, c_ld, blobs, hh_ld, ha_ld, hde_ld, -, -, -, hrawRes⟩ :=
    L1.get_ci_spec (RomBound.bounded_mono hbd hsub_ld) rba ev_ld
  have hbytes_eq : rawBytes = raw :=
    hS.hashed_inj (Core.hashed_mono hsub_ld hh_ld) (Core.hashed_mono hsub_ld hh_h)
      (ha_ld.trans hba_h.symm)
  rw [hbytes_eq, hraw, Ixon.Verify.deConstantExact_serConstant _ hwf] at hde_ld
  injection hde_ld with hc_ld; subst hc_ld
  exact ⟨hk56, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, ba, blobs,
    hba_eq, Core.hashed_mono hsub_pa hh_proj,
    Bytes.repAddressRef_heapMono₂ addrTy ext_ld rba, hld, hrawRes, hsub_ld, ev_chk, hsub_chk⟩

/-- **`MemberCheckedLimAt` on a definition member `ms[k] = .defn d` with `d.kind = .defn`**
validates `d.value`. -/
theorem memberCheckedLimAt_defnVal_levelsOk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {b : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {k : Nat} {d : Ixon.Definition} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hcb : recordOf E₀ b = some cb) (hms : cb.info = .muts ms)
    (hk : ms[k]? = some (.defn d)) (hdk : d.kind = .defn)
    (hmc : Claim.MemberCheckedLimAt calls bAddr t b ms k lim) :
    d.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t b ms)).read d.value = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range d.lvls.toNat) = true := by
  obtain ⟨hk56, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, ba, blobs,
    -, -, -, hld, hrawRes, hsub_ld, ev_chk, hsub_chk⟩ :=
    memberChecked_unpack hS hbd hcb hms hk hmc
  simp only [L1.GetCIRawResult, Core.Specs.Callees.memberProjInfo] at hrawRes
  obtain ⟨-, blkBytes, cb', ms', d', v', hhB, haB, hdeB, -, hms', hd', hld', hnl, tyPtr, valPtr,
    hint, hv', -, raw_val⟩ := hrawRes
  have hcb_eq : cb' = cb := record_eq_of_hashed_l hS hsub_ld hcb hhB haB hdeB
  subst hcb_eq
  have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
  subst hms_eq
  have hidx_eq : (k.toUInt64).toNat = k := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [hidx_eq, Array.getElem?_toList, hk] at hd'
  injection hd' with hd_mc; injection hd_mc with hd_eq; subst hd_eq
  rw [hld'] at hld; injection hld with hv_eq; subst hv_eq; subst hv'
  simp only [L1.defnValShape, hdk] at ev_chk
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Defn (ev14 := ev14) (ev311 := ev311) (ev348 := ev348) (hv269 := hv) (hc520 := hc) .. =>
    injection hv with _ _ hl
    injection hl with h1 hl; injection hl with _ hl; injection hl with h3 _
    subst h1 h3
    exact ⟨hnl, validate_reader_levels hbd hnl raw_val
      (ev14.heap_extends.trans ev311.heap_extends) ev348 (hsub_chk _ (by rw [hc]; simp))⟩
  | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) .. | .Axiom_other_other (hv37 := hv) .. =>
    simp [kciEnum] at hv
  | .Thm (hne521 := hne) .. | .Opaque (hne521 := hne) .. | .Quot (hne521 := hne) ..
  | .Induct_n0 (hne521 := hne) .. | .Induct_other_n0 (hne521 := hne) ..
  | .Induct_other_other (hne521 := hne) ..
  | .Ctor_n0_n0 (hne521 := hne) .. | .Ctor_n0_other (hne521 := hne) ..
  | .Ctor_other_n0 (hne521 := hne) .. | .Ctor_other_other (hne521 := hne) ..
  | .Rec_n0 (hne521 := hne) .. | .Rec_other (hne521 := hne) .. =>
    exact (hne _ rfl rfl).elim

/-! ### Constructor loops (`check_inductive_shape_ctors`, `check_modeled_ctors`) -/

private theorem check_inductive_shape_ctors_levelsOk {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {ba : Bytes.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {k : Nat} {ind : Ixon.Inductive}
    {xrc xty xni xlv xuns xblk : SourceValue F}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hcb : recordOf E₀ (ixAddr ba) = some cb) (hms : cb.info = .muts ms)
    (hk : ms[k]? = some (.indc ind))
    (hk56 : k < 72057594037927936) (hnc56 : ind.ctors.size < 72057594037927936)
    (hnl32 : ind.lvls.toNat < 4294967296) (hnp56 : ind.params.toNat < 72057594037927936) :
    ∀ (rem c : Nat), c + rem = ind.ctors.size →
      ∀ {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        (∀ cl ∈ cs, cl ∈ calls) →
        Bytes.RepAddressRef addrTy h ba xblk →
        ObsFn W "KernelCheck::check_inductive_shape_ctors"
          [xrc, xty, .field (ind.params.toNat : F), xni, .field (ind.ctors.size : F),
            .field (ind.lvls.toNat : F), xblk, .field (k : F), xlv, xuns, .field (c : F)]
          h r h' cs →
        ∀ j ct, c ≤ j → ind.ctors[j]? = some ct →
          ct.lvls.toNat < 4294967296 ∧
          (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id
              (blockSelf t (ixAddr ba) ms)).read ct.typ = .ok E_rd →
            E_rd.allLevelParamsDefined (List.range ct.lvls.toNat) = true) ∧
          ct.params = ind.params := by
  intro rem
  induction rem with
  | zero =>
    intro c hc _ _ _ _ _ _ _ j ct hcj hj
    have := (Array.getElem?_eq_some_iff.mp hj).1; omega
  | succ rem ih =>
    intro c hc r h h' cs hsub rba ev
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op; omega
    | .other (m34 := m1) (p41 := p1) (cs47 := cs1) (x_c_nlvls := xcnl) (x_cty := xcty)
        (x_c_np := xcnp) (m144 := m2) (cs152 := cs2) (m319 := m3) (cs329 := cs3)
        (m387 := m3a) (m356 := m4) (m400 := m4a) (m430 := m4b) (m476 := m5)
        (m546 := m5a) (m592 := m5b) (m716 := m6) (m725 := m7) (cs765 := cs_rec) (v778 := vc1)
        (ev49 := evc) (ld43 := ldc) (ev154 := evaeq) (heq261 := hnl_eq) (heq289 := hnp_eq)
        (ev331 := evval) (hm395 := hm3a) (ev368 := evs) (ev412 := evsaf) (ev442 := evpa)
        (ev488 := evret) (ev558 := evfu) (ev604 := evpf) (sg723 := sg1) (ev737 := evprj)
        (op862 := op1) (ev767 := evrec) (hc864 := hcs) .. =>
      have sub1 : ∀ cl ∈ cs1, cl ∈ calls := fun cl hcl => hsub cl (mem_of_eq hcs (by call_mem))
      obtain ⟨ext1, -, -, blkBytes, cb', ms', ind', ct', blobs, v', hhB, haB, hdeB, -, hms',
        hind', hct', -, hld', hraw_ct⟩ :=
        L1.get_ci_cprj_spec (RomBound.bounded_mono hbd sub1) rba evc
      have hcb_eq : cb' = cb := record_eq_of_hashed_l hS sub1 hcb hhB haB hdeB
      rcases hcb_eq with rfl
      have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
      rcases hms_eq with rfl
      rw [L1.val_cast_u56_ing hk56, Array.getElem?_toList, hk] at hind'
      injection hind' with hi_mc; injection hi_mc with hi_eq; subst hi_eq
      rw [L1.val_cast_u56_ing (by omega : c < 72057594037927936), Array.getElem?_toList] at hct'
      rw [hld'] at ldc; injection ldc with hv_eq
      obtain ⟨hcnl32, -, hcnp56, -, -, ctyPtr, _, _, -, -, hshape, raw_cty⟩ := hraw_ct
      rw [hshape] at hv_eq
      injection hv_eq with _ _ hl
      injection hl with h1 hl; injection hl with h2 hl; injection hl with _ hl
      injection hl with _ hl; injection hl with _ hl; injection hl with h6 _
      subst h1 h2 h6
      have hnl_nat : ct'.lvls.toNat = ind.lvls.toNat :=
        L1.natCast_inj_56 (by omega) (by omega) (Value.field.inj hnl_eq)
      have hnp_nat : ct'.params.toNat = ind.params.toNat :=
        L1.natCast_inj_56 hcnp56 hnp56 (Value.field.inj hnp_eq)
      have hnp_u64 : ct'.params = ind.params := by
        calc ct'.params = ct'.params.toNat.toUInt64 := UInt64.ofNat_toNat.symm
          _ = ind.params.toNat.toUInt64 := by rw [hnp_nat]
          _ = ind.params := UInt64.ofNat_toNat
      have hval_c : ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id
          (blockSelf t (ixAddr ba) ms)).read ct'.typ = .ok E_rd →
          E_rd.allLevelParamsDefined (List.range ct'.lvls.toNat) = true := by
        rw [hnl_nat]
        exact validate_reader_levels hbd hnl32 raw_cty evaeq.heap_extends evval
          (hsub _ (mem_of_eq hcs (by call_mem)))
      obtain rfl := binop_add_one_nat op1
      have ext_sg : Heap.Extends m5b m6 := by
        cases sg1 with
        | n0 _ _ evp _ => exact evp.heap_extends
        | other _ _ hh _ => rw [hh]
      have ext3a : Heap.Extends m3 m3a := by rw [hm3a]; exact Heap.Extends.snoc _ _
      have ext07 : Heap.Extends h m7 :=
        ext1.trans (evaeq.heap_extends.trans (evval.heap_extends.trans (ext3a.trans
          (evs.heap_extends.trans (evsaf.heap_extends.trans (evpa.heap_extends.trans
            (evret.heap_extends.trans (evfu.heap_extends.trans (evpf.heap_extends.trans
              (ext_sg.trans evprj.heap_extends))))))))))
      intro j ct hcj hj
      by_cases hjc : j = c
      · subst hjc
        have hct_eq : ct' = ct := Option.some.inj (hct'.symm.trans hj)
        subst hct_eq
        exact ⟨hcnl32, hval_c, hnp_u64⟩
      · exact ih (c + 1) (by omega) (fun cl hcl => hsub cl (mem_of_eq hcs (by call_mem)))
          (Bytes.repAddressRef_heapMono₂ addrTy ext07 rba) evrec j ct (by omega) hj

private theorem check_modeled_ctors_levelsOk {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {ba : Bytes.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {k : Nat} {ind : Ixon.Inductive}
    {xrc xni xuns xblk : SourceValue F}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hcb : recordOf E₀ (ixAddr ba) = some cb) (hms : cb.info = .muts ms)
    (hk : ms[k]? = some (.indc ind))
    (hk56 : k < 72057594037927936) (hnc56 : ind.ctors.size < 72057594037927936)
    (hnl32 : ind.lvls.toNat < 4294967296) (hnp56 : ind.params.toNat < 72057594037927936) :
    ∀ (rem c : Nat), c + rem = ind.ctors.size →
      ∀ {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        (∀ cl ∈ cs, cl ∈ calls) →
        Bytes.RepAddressRef addrTy h ba xblk →
        ObsFn W "KernelCheck::check_modeled_ctors"
          [xrc, .field (ind.params.toNat : F), xni, .field (ind.ctors.size : F),
            .field (ind.lvls.toNat : F), xblk, .field (k : F), xuns, .field (c : F)]
          h r h' cs →
        ∀ j ct, c ≤ j → ind.ctors[j]? = some ct →
          ct.lvls.toNat < 4294967296 ∧
          (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id
              (blockSelf t (ixAddr ba) ms)).read ct.typ = .ok E_rd →
            E_rd.allLevelParamsDefined (List.range ct.lvls.toNat) = true) ∧
          ct.params = ind.params := by
  intro rem
  induction rem with
  | zero =>
    intro c hc _ _ _ _ _ _ _ j ct hcj hj
    have := (Array.getElem?_eq_some_iff.mp hj).1; omega
  | succ rem ih =>
    intro c hc r h h' cs hsub rba ev
    match Obs.«KernelCheck::check_modeled_ctors».obs ev with
    | .n0 (op17 := op) .. =>
      have := binop_sub_eq_zero_nat (by omega) (by omega) op; omega
    | .other (m34 := m1) (p41 := p1) (cs47 := cs1) (x_c_nlvls := xcnl) (x_cty := xcty)
        (x_c_np := xcnp) (m144 := m2) (m319 := m3) (m387 := m3a) (m356 := m4) (m400 := m4a)
        (m430 := m4b) (m500 := m5) (m551 := m6) (v599 := vc1)
        (ev49 := evc) (ld43 := ldc) (ev154 := evaeq) (heq261 := hnl_eq) (heq289 := hnp_eq)
        (ev331 := evval) (hm395 := hm3a) (ev368 := evs) (ev412 := evsaf) (ev442 := evret)
        (ev512 := evprj) (ev561 := evri) (op669 := op1) (ev590 := evrec) (hc671 := hcs) .. =>
      have sub1 : ∀ cl ∈ cs1, cl ∈ calls := fun cl hcl => hsub cl (mem_of_eq hcs (by call_mem))
      obtain ⟨ext1, -, -, blkBytes, cb', ms', ind', ct', blobs, v', hhB, haB, hdeB, -, hms',
        hind', hct', -, hld', hraw_ct⟩ :=
        L1.get_ci_cprj_spec (RomBound.bounded_mono hbd sub1) rba evc
      have hcb_eq : cb' = cb := record_eq_of_hashed_l hS sub1 hcb hhB haB hdeB
      rcases hcb_eq with rfl
      have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
      rcases hms_eq with rfl
      rw [L1.val_cast_u56_ing hk56, Array.getElem?_toList, hk] at hind'
      injection hind' with hi_mc; injection hi_mc with hi_eq; subst hi_eq
      rw [L1.val_cast_u56_ing (by omega : c < 72057594037927936), Array.getElem?_toList] at hct'
      rw [hld'] at ldc; injection ldc with hv_eq
      obtain ⟨hcnl32, -, hcnp56, -, -, ctyPtr, _, _, -, -, hshape, raw_cty⟩ := hraw_ct
      rw [hshape] at hv_eq
      injection hv_eq with _ _ hl
      injection hl with h1 hl; injection hl with h2 hl; injection hl with _ hl
      injection hl with _ hl; injection hl with _ hl; injection hl with h6 _
      subst h1 h2 h6
      have hnl_nat : ct'.lvls.toNat = ind.lvls.toNat :=
        L1.natCast_inj_56 (by omega) (by omega) (Value.field.inj hnl_eq)
      have hnp_nat : ct'.params.toNat = ind.params.toNat :=
        L1.natCast_inj_56 hcnp56 hnp56 (Value.field.inj hnp_eq)
      have hnp_u64 : ct'.params = ind.params := by
        calc ct'.params = ct'.params.toNat.toUInt64 := UInt64.ofNat_toNat.symm
          _ = ind.params.toNat.toUInt64 := by rw [hnp_nat]
          _ = ind.params := UInt64.ofNat_toNat
      have hval_c : ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id
          (blockSelf t (ixAddr ba) ms)).read ct'.typ = .ok E_rd →
          E_rd.allLevelParamsDefined (List.range ct'.lvls.toNat) = true := by
        rw [hnl_nat]
        exact validate_reader_levels hbd hnl32 raw_cty evaeq.heap_extends evval
          (hsub _ (mem_of_eq hcs (by call_mem)))
      obtain rfl := binop_add_one_nat op1
      have ext3a : Heap.Extends m3 m3a := by rw [hm3a]; exact Heap.Extends.snoc _ _
      have ext06 : Heap.Extends h m6 :=
        ext1.trans (evaeq.heap_extends.trans (evval.heap_extends.trans (ext3a.trans
          (evs.heap_extends.trans (evsaf.heap_extends.trans (evret.heap_extends.trans
            (evprj.heap_extends.trans evri.heap_extends)))))))
      intro j ct hcj hj
      by_cases hjc : j = c
      · subst hjc
        have hct_eq : ct' = ct := Option.some.inj (hct'.symm.trans hj)
        subst hct_eq
        exact ⟨hcnl32, hval_c, hnp_u64⟩
      · exact ih (c + 1) (by omega) (fun cl hcl => hsub cl (mem_of_eq hcs (by call_mem)))
          (Bytes.repAddressRef_heapMono₂ addrTy ext06 rba) evrec j ct (by omega) hj

/-! ### Mutual block peer parameter agreement (`block_nparams`, `check_block_peer_param_agreement`) -/

private theorem nparams_agree_spec {np : Nat} (hnp56 : np < 72057594037927936) :
    ∀ (rest : List Ixon.MutConst) {xm : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList L1.mutConstListEnum L1.RepMutConst h rest xm →
      ObsFn W "KernelModeled::nparams_agree" [xm, .field (np : F)] h (.field 1) h' cs →
      ∀ ind, .indc ind ∈ rest → ind.params.toNat = np := by
  intro rest
  induction rest with
  | nil => intro _ _ _ _ _ _ _ hm; cases hm
  | cons m rest ih =>
    intro xm h h' cs hrep ev
    match Obs.«KernelModeled::nparams_agree».obs ev with
    | .Nil (ld12 := ld) .. => cases Core.RepList.nil_of_load hrep ld
    | .Cons_Indc_other (he175 := hr) .. | .Cons_other (he183 := hr) .. =>
      exact absurd (Value.field.inj hr) (by decide)
    | .Cons_Indc_n0 (x_rest := xrest) (x_params := xp) (x121 := xf) (m123 := m1)
        (ld12 := ld) (ev134 := evu) (op128 := opsub) (ev153 := evrec) .. =>
      obtain ⟨m', rest', hcons, hm', hrest⟩ := Core.RepList.cons_of_load hrep ld
      injection hcons with h1 h2; subst h1 h2
      cases m with
      | indc ind0 =>
        obtain ⟨iv, hmv, typPtr, ctorsPtr, hiv, -, -⟩ := hm'
        injection hmv with _ _ hml; injection hml with hmv'; subst hmv'
        injection hiv with _ _ hil
        injection hil with _ hil; injection hil with _ hil; injection hil with hxp _
        subst hxp
        obtain ⟨hnp0_56, rfl, hm1⟩ := L1.u64ToField_refines ind0.params.toNat_lt evu.erase
        subst hm1
        have hEq0 : ind0.params.toNat = np := binop_sub_eq_zero_nat (by omega) (by omega) opsub
        have htail := ih hrest evrec
        intro ind hmem
        rcases List.mem_cons.mp hmem with hhead | hmem
        · injection hhead with hi; subst hi; exact hEq0
        · exact htail ind hmem
      | defn d => obtain ⟨_, hmv, -⟩ := hm'; simp at hmv
      | recr r => obtain ⟨_, hmv, -⟩ := hm'; simp at hmv

/-- **`KernelModeled::block_nparams`** proves all inductive members of the block share their
parameter count (and returns it). -/
theorem block_nparams_spec {ms : List Ixon.MutConst} {xm r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hrep : RepList L1.mutConstListEnum L1.RepMutConst h ms xm)
    (ev : ObsFn W "KernelModeled::block_nparams" [xm] h r h' cs) :
    ∃ np : Nat, np < 72057594037927936 ∧ r = .field (np : F) ∧
      ∀ ind, .indc ind ∈ ms → ind.params.toNat = np := by
  match Obs.«KernelModeled::block_nparams».obs ev with
  | .run (x_rest := xrest) (x_params := xp) (v102 := xf) (m103 := m1)
      (ld12 := ld) (ev115 := evu) (ev148 := evag) (heq171 := heq1) (he173 := hr) .. =>
    subst hr heq1
    obtain ⟨m0, rest, rfl, hm0, hrest⟩ := Core.RepList.cons_of_load hrep ld
    cases m0 with
    | indc ind0 =>
      obtain ⟨iv, hmv, typPtr, ctorsPtr, hiv, -, -⟩ := hm0
      injection hmv with _ _ hml; injection hml with hmv'; subst hmv'
      injection hiv with _ _ hil
      injection hil with _ hil; injection hil with _ hil; injection hil with hxp _
      subst hxp
      obtain ⟨hnp0_56, rfl, hm1⟩ := L1.u64ToField_refines ind0.params.toNat_lt evu.erase
      subst hm1
      have htail := nparams_agree_spec hnp0_56 rest hrest evag
      refine ⟨ind0.params.toNat, hnp0_56, rfl, fun ind hmem => ?_⟩
      rcases List.mem_cons.mp hmem with hhead | hmem
      · injection hhead with hi; subst hi; rfl
      · exact htail ind hmem
    | defn d => obtain ⟨_, hmv, -⟩ := hm0; simp at hmv
    | recr r => obtain ⟨_, hmv, -⟩ := hm0; simp at hmv

private theorem peer_agree_walk_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    {ba : Bytes.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {selfIdx selfNp : Nat} {xrc xsty xsni xblk : SourceValue F}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hcb : recordOf E₀ (ixAddr ba) = some cb) (hms : cb.info = .muts ms)
    (hselfIdx56 : selfIdx < 72057594037927936) (hselfNp56 : selfNp < 72057594037927936)
    (hselfAt : ∀ ind, ms[selfIdx]? = some (.indc ind) → ind.params.toNat = selfNp)
    (hms56 : ms.size < 72057594037927936) :
    ∀ (rest : List Ixon.MutConst) (pos : Nat),
      pos + rest.length = ms.size →
      (∀ i m, rest[i]? = some m → ms[pos + i]? = some m) →
      ∀ {xm r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        (∀ cl ∈ cs, cl ∈ calls) →
        RepList L1.mutConstListEnum L1.RepMutConst h rest xm →
        Bytes.RepAddressRef addrTy h ba xblk →
        ObsFn W "KernelCheck::peer_agree_walk"
          [xrc, xm, xsty, .field (selfNp : F), xsni, .field (selfIdx : F), .field (pos : F), xblk]
          h r h' cs →
        ∀ (i : Nat) (ind : Ixon.Inductive), rest[i]? = some (.indc ind) → ind.params.toNat = selfNp := by
  intro rest
  induction rest with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ i ind hi; simp at hi
  | cons m rest ih =>
    intro pos hlen hidx xm r h h' cs hsub hrep rba ev
    have hpos_at : ms[pos]? = some m := by simpa using hidx 0 m rfl
    have hpos56 : pos < 72057594037927936 := by simp only [List.length_cons] at hlen; omega
    have hidx' : ∀ i m', rest[i]? = some m' → ms[(pos + 1) + i]? = some m' := fun i m' hi => by
      have h1 := hidx (i + 1) m' (by simpa using hi)
      rwa [show pos + (i + 1) = (pos + 1) + i by omega] at h1
    match Obs.«KernelCheck::peer_agree_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases Core.RepList.nil_of_load hrep ld
    | .Cons_other (x_m := xm0) (x_rest := xrest) (v708 := vp1)
        (ld12 := ld) (hne692 := hne) (op765 := op1) (ev701 := evrec) (hc774 := hcs) .. =>
      obtain ⟨m', rest', hcons, hm', hrest⟩ := Core.RepList.cons_of_load hrep ld
      injection hcons with h1 h2; subst h1 h2
      obtain rfl := binop_add_one_nat op1
      have htail := ih (pos + 1) (by simp only [List.length_cons] at hlen; omega) hidx'
        (fun cl hcl => hsub cl (mem_of_eq hcs (by call_mem))) hrest rba evrec
      intro i ind hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
        obtain ⟨iv, hmv, -⟩ := hm'
        exact (hne [iv] rfl hmv).elim
      | succ i' => exact htail i' ind (by simpa using hi)
    | .Cons_Indc_n1 (x_rest := xrest) (m65 := m1) (v78 := vdiff) (v121 := vp1)
        (ld12 := ld) (op92 := opsub) (ev77 := evz) (op178 := op1) (ev114 := evrec)
        (hc187 := hcs) .. =>
      obtain ⟨m', rest', hcons, hm', hrest⟩ := Core.RepList.cons_of_load hrep ld
      injection hcons with h1 h2; subst h1 h2
      obtain rfl := binop_add_one_nat op1
      have hv0 : vdiff = .field 0 := by
        cases Obs.«Fields::is_zero».obs evz with
        | n0 hv _ _ _ => exact hv
        | other _ _ hr _ _ => exact absurd (Value.field.inj hr) (by decide)
      subst hv0
      have hpos_eq : pos = selfIdx := binop_sub_eq_zero_nat (by omega) (by omega) opsub
      have htail := ih (pos + 1) (by simp only [List.length_cons] at hlen; omega) hidx'
        (fun cl hcl => hsub cl (mem_of_eq hcs (by call_mem)))
        (RepLinkedList.mono L1.repMutConst_heapMono₂ evz.heap_extends hrest)
        (Bytes.repAddressRef_heapMono₂ addrTy evz.heap_extends rba) evrec
      intro i ind hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
        rw [hpos_eq] at hpos_at
        exact hselfAt ind hpos_at
      | succ i' => exact htail i' ind (by simpa using hi)
    | .Cons_Indc_other_Induct (x_rest := xrest) (m65 := m1) (m193 := m2) (p200 := p2)
        (cs206 := cs2) (x_peer_np := xpnp) (m315 := m3) (m409 := m3a) (m361 := m4) (m470 := m4a)
        (m422 := m5) (m496 := m6) (v542 := vp1)
        (ld12 := ld) (ev77 := evz) (ev208 := evip) (ld202 := ldip) (heq313 := hnp_eq)
        (ev327 := evpa) (hm417 := hm3a) (ev373 := evrs1) (hm478 := hm4a) (ev434 := evrs2)
        (ev506 := evle) (op599 := op1) (ev535 := evrec) (hc608 := hcs) .. =>
      obtain ⟨m', rest', hcons, hm', hrest⟩ := Core.RepList.cons_of_load hrep ld
      injection hcons with h1 h2; subst h1 h2
      have sub2 : ∀ cl ∈ cs2, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      obtain ⟨ext2, -, blkBytes, cb', ms', ind', blobs, v', hhB, haB, hdeB, -, hms', hind', -,
        hld', hraw_i⟩ :=
        L1.get_ci_iprj_spec (RomBound.bounded_mono hbd sub2)
          (Bytes.repAddressRef_heapMono₂ addrTy evz.heap_extends rba) evip
      have hcb_eq : cb' = cb := record_eq_of_hashed_l hS sub2 hcb hhB haB hdeB
      subst hcb_eq
      have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
      subst hms_eq
      rw [L1.val_cast_u56_ing hpos56, Array.getElem?_toList, hpos_at] at hind'
      rw [hld'] at ldip; injection ldip with hv_eq
      obtain ⟨-, hnp'_56, -, -, -, _, _, _, -, -, hshape, -⟩ := hraw_i
      rw [hshape] at hv_eq
      injection hv_eq with _ _ hl
      injection hl with _ hl; injection hl with _ hl; injection hl with h3 _
      subst h3
      have hnp_nat : ind'.params.toNat = selfNp :=
        L1.natCast_inj_56 hnp'_56 hselfNp56 (Value.field.inj hnp_eq)
      obtain rfl := binop_add_one_nat op1
      have ext3a : Heap.Extends m3 m3a := by rw [hm3a]; exact Heap.Extends.snoc _ _
      have ext4a : Heap.Extends m4 m4a := by rw [hm4a]; exact Heap.Extends.snoc _ _
      have ext06 : Heap.Extends h m6 :=
        evz.heap_extends.trans (ext2.trans (evpa.heap_extends.trans (ext3a.trans
          (evrs1.heap_extends.trans (ext4a.trans (evrs2.heap_extends.trans evle.heap_extends))))))
      have htail := ih (pos + 1) (by simp only [List.length_cons] at hlen; omega) hidx'
        (fun cl hcl => hsub cl (mem_of_eq hcs (by call_mem)))
        (RepLinkedList.mono L1.repMutConst_heapMono₂ ext06 hrest)
        (Bytes.repAddressRef_heapMono₂ addrTy ext06 rba) evrec
      intro i ind hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
        injection hind' with hi_mc; injection hi_mc with hi_eq; subst hi_eq
        exact hnp_nat
      | succ i' => exact htail i' ind (by simpa using hi)
    | .Cons_Indc_other_other (m65 := m1) (m193 := m2) (p200 := p2) (cs206 := cs2)
        (ld12 := ld) (ev77 := evz) (ev208 := evip) (ld202 := ldip) (hne609 := hneI)
        (hc691 := hcs) .. =>
      have sub2 : ∀ cl ∈ cs2, cl ∈ calls := fun cl hcl => hsub cl (mem_of_eq hcs (by call_mem))
      obtain ⟨-, -, -, -, -, -, -, v', -, -, -, -, -, -, -, hld', hraw_i⟩ :=
        L1.get_ci_iprj_spec (RomBound.bounded_mono hbd sub2)
          (Bytes.repAddressRef_heapMono₂ addrTy evz.heap_extends rba) evip
      rw [hld'] at ldip; injection ldip with hv_eq; subst hv_eq
      obtain ⟨-, -, -, -, -, _, _, _, -, -, hshape, -⟩ := hraw_i
      exact (hneI _ rfl hshape).elim

/-- **`MemberCheckedLimAt` on an inductive member `ms[k] = .indc ind` of a safe block**
validates `ind.typ`, every constructor `ct.typ`, constructor parameter equality `ct.params = ind.params`,
and mutual block peer parameter equality `ind.params = ind₂.params`. -/
theorem memberCheckedLimAt_ind_levelsOk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {b : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {k : Nat} {ind : Ixon.Inductive} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hcb : recordOf E₀ b = some cb) (hms : cb.info = .muts ms)
    (hlogic : InLogic cb) (hk : ms[k]? = some (.indc ind))
    (hmc : Claim.MemberCheckedLimAt calls bAddr t b ms k lim) :
    (ind.lvls.toNat < 4294967296 ∧
      ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t b ms)).read ind.typ = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range ind.lvls.toNat) = true) ∧
    (∀ (j : Nat) (ct : Ixon.Constructor), ind.ctors[j]? = some ct →
      ct.lvls.toNat < 4294967296 ∧
      (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t b ms)).read ct.typ = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range ct.lvls.toNat) = true) ∧
      ct.params = ind.params) ∧
    (∀ (i₂ : Nat) (ind₂ : Ixon.Inductive), ms[i₂]? = some (.indc ind₂) → ind.params = ind₂.params) := by
  have hsafe : ind.isUnsafe = false := by
    unfold InLogic at hlogic
    rw [hms] at hlogic
    exact (hlogic (.indc ind) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))).1
  obtain ⟨hk56, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, ba_p, blobs,
    hba_p_eq, hh_proj, rba_p, hld, hrawRes, hsub_ld, ev_chk, hsub_chk⟩ :=
    memberChecked_unpack hS hbd hcb hms hk hmc
  simp only [L1.GetCIRawResult, Core.Specs.Callees.memberProjInfo] at hrawRes
  obtain ⟨-, blkBytes, cb', ms', ind', v', hhB, haB, hdeB, -, hms', hind', hld',
    hnl32, hnp56, hni56, hnc56, hidx56, tyPtr, blkPtr, ba_b, hba_b_eq, rba_b, hv', raw_ty⟩ := hrawRes
  have hcb_eq : cb' = cb := record_eq_of_hashed_l hS hsub_ld hcb hhB haB hdeB
  subst cb'
  have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
  subst ms'
  have hidx_eq : (k.toUInt64).toNat = k := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [hidx_eq, Array.getElem?_toList, hk] at hind'
  injection hind' with hi_mc; injection hi_mc with hi_eq; subst hi_eq
  rw [hidx_eq] at hv' hidx56
  rw [hld'] at hld; injection hld with hv_eq; subst hv_eq; subst hv'
  rw [hsafe] at ev_chk
  have hne_bp : ba_b ≠ ba_p := by
    intro heq
    have hha : Address.blake3Pure blkBytes =
        Address.blake3Pure (Ixon.serConstant
          ⟨Core.Specs.Callees.memberProjInfo b k (.indc ind), #[], #[], #[], #[]⟩) := by
      calc Address.blake3Pure blkBytes = b := haB
        _ = ixAddr ba_b := hba_b_eq.symm
        _ = ixAddr ba_p := congrArg ixAddr heq
        _ = Core.projAddr (Core.Specs.Callees.memberProjInfo b k (.indc ind)) := hba_p_eq
        _ = _ := rfl
    have hraw := hS.hashed_inj (Core.hashed_mono hsub_ld hhB) hh_proj hha
    have hwf : (⟨Core.Specs.Callees.memberProjInfo b k (.indc ind), #[], #[], #[], #[]⟩ :
        Ixon.Constant).wireWF := by
      rw [← hba_b_eq]
      exact L1.projConstant_wireWF_iPrj k.toUInt64 ba_b
    rw [hraw, Ixon.Verify.deConstantExact_serConstant _ hwf] at hdeB
    injection hdeB with hce; rw [← hce] at hms; cases hms
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) .. | .Axiom_other_other (hv37 := hv) .. =>
    simp [kciEnum] at hv
  | .Defn (hv269 := hv) .. => simp [kciEnum] at hv
  | .Thm (hv526 := hv) .. => simp [kciEnum] at hv
  | .Opaque (hv825 := hv) .. => simp [kciEnum] at hv
  | .Quot (hv1076 := hv) .. => simp [kciEnum] at hv
  | .Ctor_n0_n0 (hne1984 := hne) .. | .Ctor_n0_other (hne1984 := hne) ..
  | .Ctor_other_n0 (hne1984 := hne) .. | .Ctor_other_other (hne1984 := hne) ..
  | .Rec_n0 (hne1984 := hne) .. | .Rec_other (hne1984 := hne) .. =>
    exact (hne _ rfl rfl).elim
  | .Induct_other_other (hv1240 := hv) (hne1975 := hne) .. =>
    injection hv with _ _ hl
    injection hl with _ hl; injection hl with _ hl; injection hl with _ hl
    injection hl with _ hl; injection hl with _ hl; injection hl with h6 _
    exact (hne h6.symm).elim
  | .Induct_n0 (m2 := m1) (m1283 := m2) (m1354 := m2b) (m1376 := m2a) (m1333 := m3)
      (m1427 := m3a) (m1396 := m4) (m1440 := m5) (m1470 := m6) (m1492 := m7) (m1519 := m8)
      (cs1529 := cs_sh) (cs1607 := cs_pa)
      (ev14 := ev14) (hv1240 := hv) (ev1295 := evval) (hm1362 := hm2b) (hm1384 := hm2a)
      (ev1343 := evmb) (hm1435 := hm3a) (ev1408 := evs) (ev1452 := evsaf) (ev1482 := evmk)
      (ev1505 := evbm) (ev1531 := evsh) (ev1609 := evpa) (hc1634 := hc) .. =>
    injection hv with _ _ hl
    injection hl with h1 hl; injection hl with h2 hl; injection hl with h3 hl
    injection hl with h4 hl; injection hl with h5 hl; injection hl with h6 hl
    injection hl with h7 hl; injection hl with h8 _
    subst h1 h2 h3 h4 h5 h6 h7 h8
    have hty_ok : ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id
        (blockSelf t b ms)).read ind.typ = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range ind.lvls.toNat) = true :=
      validate_reader_levels hbd hnl32 raw_ty ev14.heap_extends evval
        (hsub_chk _ (mem_of_eq hc (by call_mem)))
    have ext2a : Heap.Extends m2 m2a := by rw [hm2a]; exact Heap.Extends.snoc _ _
    have ext2b : Heap.Extends m2a m2b := by rw [hm2b]; exact Heap.Extends.snoc _ _
    have ext3a : Heap.Extends m3 m3a := by rw [hm3a]; exact Heap.Extends.snoc _ _
    have ext07 : Heap.Extends m_chk m7 :=
      ev14.heap_extends.trans (evval.heap_extends.trans (ext2a.trans (ext2b.trans
        (evmb.heap_extends.trans (ext3a.trans (evs.heap_extends.trans (evsaf.heap_extends.trans
          (evmk.heap_extends.trans evbm.heap_extends))))))))
    have hctors_ok : ∀ (j : Nat) (ct : Ixon.Constructor), ind.ctors[j]? = some ct →
        ct.lvls.toNat < 4294967296 ∧
        (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id
            (blockSelf t b ms)).read ct.typ = .ok E_rd →
          E_rd.allLevelParamsDefined (List.range ct.lvls.toNat) = true) ∧
        ct.params = ind.params := by
      match Obs.«KernelCheck::check_inductive_shape».obs evsh with
      | .run (m50 := ms0) (m2 := ms1) (m63 := ms2) (m133 := ms3)
          (hm58 := hms0) (ev14 := evr) (ev75 := evf) (ev145 := evt) (ev200 := evct)
          (hc288 := hc_sh) .. =>
        have ext_s0 : Heap.Extends m7 ms0 := by rw [hms0]; exact Heap.Extends.snoc _ _
        have ext7_s3 := ext_s0.trans (evr.heap_extends.trans (evf.heap_extends.trans evt.heap_extends))
        have evct' : ObsFn W "KernelCheck::check_inductive_shape_ctors"
            [rc, tyPtr, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
              .field (ind.ctors.size : F), .field (ind.lvls.toNat : F), blkPtr,
              .field (k : F), _, repBoolField false, .field ((0 : Nat) : F)]
            ms3 _ m8 _ := by simpa using evct
        have hres := check_inductive_shape_ctors_levelsOk hS hbd
          (by rwa [hba_b_eq]) hms hk hk56 hnc56 hnl32 hnp56
          ind.ctors.size 0 (by omega)
          (fun cl hcl => by
            have h1 := mem_of_eq hc_sh (by call_mem)
            exact hsub_chk cl (mem_of_eq hc (by call_mem)))
          (Bytes.repAddressRef_heapMono₂ addrTy (ext07.trans ext7_s3) rba_b) evct'
        intro j ct hj
        simpa [hba_b_eq] using hres j ct (Nat.zero_le j) hj
    have hpeers_ok : ∀ i₂ ind₂, ms[i₂]? = some (.indc ind₂) → ind.params = ind₂.params := by
      have ext08 := ext07.trans evsh.heap_extends
      match Obs.«KernelCheck::check_block_peer_param_agreement».obs evpa with
      | .other (hne272 := hne) .. => exact (hne _ rfl rfl).elim
      | .Induct_n1 (hv15 := hv2) (ev74 := evaeq) .. =>
        injection hv2 with _ _ hl2
        injection hl2 with _ hl2; injection hl2 with _ hl2; injection hl2 with _ hl2
        injection hl2 with _ hl2; injection hl2 with _ hl2; injection hl2 with _ hl2
        injection hl2 with h7' _; subst h7'
        obtain ⟨hveq, -⟩ := Lib.address_eq_spec evaeq
          (Bytes.repAddressRef_heapMono₂ addrTy ext08 rba_b)
          (Bytes.repAddressRef_heapMono₂ addrTy ext08 rba_p)
        rw [ite_eq_right hne_bp] at hveq
        exact absurd (Value.field.inj hveq) (by decide)
      | .Induct_other_other (hv15 := hv2) (cs115 := cs_lvc)
          (ev74 := evaeq) (ev117 := evlvc) (hne262 := hneM) (hc270 := hc_pa) .. =>
        injection hv2 with _ _ hl2
        injection hl2 with _ hl2; injection hl2 with _ hl2; injection hl2 with _ hl2
        injection hl2 with _ hl2; injection hl2 with _ hl2; injection hl2 with _ hl2
        injection hl2 with h7' _; subst h7'
        have sub_lvc : ∀ cl ∈ cs_lvc, cl ∈ calls :=
          fun cl hcl => by
            have h1 := mem_of_eq hc_pa (by call_mem)
            exact hsub_chk cl (mem_of_eq hc (by call_mem))
        obtain ⟨-, bytes', c'', -, hh', ha', hde', -, -, -, -, -, -, cRep⟩ :=
          L1.load_verified_constant_decode_bounded
            (Bytes.repAddressRef_heapMono₂ addrTy (ext08.trans evaeq.heap_extends) rba_b) evlvc
        have hc'' : c'' = cb := record_eq_of_hashed_l hS sub_lvc (by rwa [hba_b_eq]) hh' ha' hde'
        subst hc''
        obtain ⟨infoVal, -, -, -, -, hceq, hinfoRep, -, -, -, -⟩ := cRep
        injection hceq with _ _ hcl; injection hcl with hinfo_eq _
        rw [hms] at hinfoRep
        obtain ⟨mp, hmp, -⟩ := hinfoRep
        exact (hneM [mp] rfl (hinfo_eq.symm.trans hmp)).elim
      | .Induct_other_Muts (m61 := mp1) (m105 := mp2) (cs115 := cs_lvc) (x_members := xmems)
          (cs195 := cs_w) (hv15 := hv2) (ev74 := evaeq) (ev117 := evlvc) (ev197 := evw)
          (hc261 := hc_pa) .. =>
        injection hv2 with _ _ hl2
        injection hl2 with _ hl2; injection hl2 with h2' hl2; injection hl2 with h3' hl2
        injection hl2 with h4' hl2; injection hl2 with _ hl2; injection hl2 with _ hl2
        injection hl2 with h7' hl2; injection hl2 with h8' _
        subst h2' h3' h4' h7' h8'
        have sub_lvc : ∀ cl ∈ cs_lvc, cl ∈ calls :=
          fun cl hcl => by
            have h1 := mem_of_eq hc_pa (by call_mem)
            exact hsub_chk cl (mem_of_eq hc (by call_mem))
        obtain ⟨cb'', ms'', hbl, hrepM⟩ := Claim.load_block_head
          (Bytes.repAddressRef_heapMono₂ addrTy (ext08.trans evaeq.heap_extends) rba_b) evlvc
        have hrec_eq := (hbl.mono sub_lvc).record hS (by rwa [hba_b_eq])
        obtain ⟨rfl, hres_lt⟩ := hrec_eq
        obtain ⟨-, -, -, -, -, hbl_muts⟩ := hbl
        have hms_eq2 : ms'' = ms := Ixon.ConstantInfo.muts.inj (hbl_muts.symm.trans hms)
        subst ms''
        have hms_lt56 : ms.size < 72057594037927936 := by
          have := Claim.muts_size_le hms; omega
        have evw' : ObsFn W "KernelCheck::peer_agree_walk"
            [rc, xmems, tyPtr, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
              .field (k : F), .field ((0 : Nat) : F), blkPtr] mp2 _ _ cs_w := by simpa using evw
        have hwalk := peer_agree_walk_spec hS hbd (by rwa [hba_b_eq]) hms hk56 hnp56
          (fun ind' h' => by rw [hk] at h'; injection h' with hm; injection hm with hi; subst hi; rfl)
          hms_lt56 ms.toList 0 (by simp) (fun i m hi => by simpa [Array.getElem?_toList] using hi)
          (fun cl hcl => by
            have h1 := mem_of_eq hc_pa (by call_mem)
            exact hsub_chk cl (mem_of_eq hc (by call_mem))) hrepM
          (Bytes.repAddressRef_heapMono₂ addrTy
            (ext08.trans (evaeq.heap_extends.trans evlvc.heap_extends)) rba_b) evw'
        intro i₂ ind₂ hi₂
        have hnat := hwalk i₂ ind₂ (by rwa [Array.getElem?_toList])
        calc ind.params = ind.params.toNat.toUInt64 := UInt64.ofNat_toNat.symm
          _ = ind₂.params.toNat.toUInt64 := by rw [hnat]
          _ = ind₂.params := UInt64.ofNat_toNat
    exact ⟨⟨hnl32, hty_ok⟩, hctors_ok, hpeers_ok⟩
  | .Induct_other_n0 (m2 := m1) (m1283 := m2) (m1354 := m2b) (m1376 := m2a) (m1333 := m3)
      (m1427 := m3a) (m1396 := m4) (m1440 := m5) (m1470 := m6) (m1492 := m7) (m1653 := m8)
      (m1701 := m9) (m1749 := m10) (m1841 := m10a) (m1793 := m11) (m1854 := m12)
      (cs1864 := cs_mc) (cs1955 := cs_mb)
      (ev14 := ev14) (hv1240 := hv) (ev1295 := evval) (hm1362 := hm2b) (hm1384 := hm2a)
      (ev1343 := evmb) (hm1435 := hm3a) (ev1408 := evs) (ev1452 := evsaf) (ev1482 := evmk)
      (ev1505 := evbm) (ev1663 := evri) (ev1711 := evhl) (ev1759 := evft)
      (hm1849 := hm10a) (ev1805 := evrs) (ev1866 := evct) (ev1957 := evcmb) (hc1974 := hc) .. =>
    injection hv with _ _ hl
    injection hl with h1 hl; injection hl with h2 hl; injection hl with h3 hl
    injection hl with h4 hl; injection hl with h5 hl; injection hl with _ hl
    injection hl with h7 hl; injection hl with h8 _
    subst h1 h2 h3 h4 h5 h7 h8
    have hty_ok : ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id
        (blockSelf t b ms)).read ind.typ = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range ind.lvls.toNat) = true :=
      validate_reader_levels hbd hnl32 raw_ty ev14.heap_extends evval
        (hsub_chk _ (mem_of_eq hc (by call_mem)))
    have ext2a : Heap.Extends m2 m2a := by rw [hm2a]; exact Heap.Extends.snoc _ _
    have ext2b : Heap.Extends m2a m2b := by rw [hm2b]; exact Heap.Extends.snoc _ _
    have ext3a : Heap.Extends m3 m3a := by rw [hm3a]; exact Heap.Extends.snoc _ _
    have ext10a : Heap.Extends m10 m10a := by rw [hm10a]; exact Heap.Extends.snoc _ _
    have ext0_11 : Heap.Extends m_chk m11 :=
      ev14.heap_extends.trans (evval.heap_extends.trans (ext2a.trans (ext2b.trans
        (evmb.heap_extends.trans (ext3a.trans (evs.heap_extends.trans (evsaf.heap_extends.trans
          (evmk.heap_extends.trans (evbm.heap_extends.trans (evri.heap_extends.trans
            (evhl.heap_extends.trans (evft.heap_extends.trans
              (ext10a.trans evrs.heap_extends)))))))))))))
    have hctors_ok : ∀ (j : Nat) (ct : Ixon.Constructor), ind.ctors[j]? = some ct →
        ct.lvls.toNat < 4294967296 ∧
        (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id
            (blockSelf t b ms)).read ct.typ = .ok E_rd →
          E_rd.allLevelParamsDefined (List.range ct.lvls.toNat) = true) ∧
        ct.params = ind.params := by
      have evct' : ObsFn W "KernelCheck::check_modeled_ctors"
          [rc, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
            .field (ind.ctors.size : F), .field (ind.lvls.toNat : F), blkPtr,
            .field (k : F), .field 0, .field ((0 : Nat) : F)]
          m11 _ m12 cs_mc := by simpa using evct
      have hres := check_modeled_ctors_levelsOk hS hbd
        (by rwa [hba_b_eq]) hms hk hk56 hnc56 hnl32 hnp56
        ind.ctors.size 0 (by omega)
        (fun cl hcl => hsub_chk cl (mem_of_eq hc (by call_mem)))
        (Bytes.repAddressRef_heapMono₂ addrTy ext0_11 rba_b) evct'
      intro j ct hj
      simpa [hba_b_eq] using hres j ct (Nat.zero_le j) hj
    have hpeers_ok : ∀ i₂ ind₂, ms[i₂]? = some (.indc ind₂) → ind.params = ind₂.params := by
      have ext0_12 := ext0_11.trans evct.heap_extends
      match Obs.«KernelModeled::check_modeled_block».obs evcmb with
      | .run (ev27 := evrp) (ev14 := evga) (ev55 := evcf) (hc80 := hc_mb) .. =>
        match Obs.«KernelModeled::check_family».obs evcf with
        | .run (m105 := mf1) (m114 := mf2) (m136 := mf3) (m184 := mf4) (m_judpcwze := mf5)
            (m219 := mf6) (m254 := mf7) (m297 := mf8) (m332 := mf9) (m391 := mf10)
            (m423 := mf11) (m453 := mf12) (m501 := mf13) (cs511 := cs_lvc) (x_members := xmems)
            (m589 := mf14) (m624 := mf15)
            (sg112 := sg1) (ev126 := evf1) (ev148 := evf2) (ev194 := evf3)
            (ev_yqjbwijz := evf4) (ev231 := evf5) (ev266 := evf6) (ev309 := evf7)
            (ev344 := evf8) (ev403 := evf9) (ev435 := evf10) (ev465 := evf11)
            (ev513 := evlvc) (ev601 := evlen) (ev634 := evmic) (ev664 := evbnp)
            (hc1474 := hc_cf) .. =>
          have ext_sg1 : Heap.Extends _ mf1 := by
            cases sg1 with
            | Nil _ _ evax _ hh _ => rw [hh]; exact evax.heap_extends
            | Node _ _ _ _ _ _ _ _ heq _ _ _ => exact absurd (Value.field.inj heq) (by decide)
          have ext_to_lvc : Heap.Extends m_chk mf12 :=
            ext0_12.trans (evrp.heap_extends.trans (evga.heap_extends.trans (ext_sg1.trans
              (evf1.heap_extends.trans (evf2.heap_extends.trans (evf3.heap_extends.trans
                (evf4.heap_extends.trans (evf5.heap_extends.trans (evf6.heap_extends.trans
                  (evf7.heap_extends.trans (evf8.heap_extends.trans (evf9.heap_extends.trans
                    (evf10.heap_extends.trans evf11.heap_extends)))))))))))))
          have sub_lvc : ∀ cl ∈ cs_lvc, cl ∈ calls :=
            fun cl hcl => by
              have h1 := mem_of_eq hc_cf (by call_mem)
              have h2 := mem_of_eq hc_mb (by call_mem)
              exact hsub_chk cl (mem_of_eq hc (by call_mem))
          obtain ⟨cb'', ms'', hbl, hrepM⟩ := Claim.load_block_head
            (Bytes.repAddressRef_heapMono₂ addrTy ext_to_lvc rba_b) evlvc
          obtain ⟨rfl, -⟩ := (hbl.mono sub_lvc).record hS (by rwa [hba_b_eq])
          obtain ⟨-, -, -, -, -, hbl_muts⟩ := hbl
          have hms_eq2 : ms'' = ms := Ixon.ConstantInfo.muts.inj (hbl_muts.symm.trans hms)
          subst ms''
          have ext_m := evlen.heap_extends.trans evmic.heap_extends
          obtain ⟨np, -, -, hall_np⟩ := block_nparams_spec
            (RepLinkedList.mono L1.repMutConst_heapMono₂ ext_m hrepM) evbnp
          intro i₂ ind₂ hi₂
          have h1 := hall_np ind (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hk))
          have h2 := hall_np ind₂ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi₂))
          calc ind.params = ind.params.toNat.toUInt64 := UInt64.ofNat_toNat.symm
            _ = ind₂.params.toNat.toUInt64 := by rw [h1, h2]
            _ = ind₂.params := UInt64.ofNat_toNat
    exact ⟨⟨hnl32, hty_ok⟩, hctors_ok, hpeers_ok⟩

/-! ### Prefix inversion of `KernelModeled::check_iota_rule` (steps 1–4) -/

private theorem inv_var_find {locals : Environment F Nat} {name : String} {v : SourceValue F}
    {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)}
    (hlkp : locals.find? (·.1 == name) = some (name, v))
    (ev : ObsExpr W [] locals (.var name) h r h' cs) :
    r = v ∧ h' = h ∧ cs = [] := by
  obtain ⟨hl, hr, hc⟩ := ev.var_inv
  rw [hlkp] at hl; injection hl with hp; injection hp with _ hv; exact ⟨hv.symm, hr, hc⟩

private theorem inv_lit {locals : Environment F Nat} {n : F}
    {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)}
    (ev : ObsExpr W [] locals (.literal n) h r h' cs) :
    r = .field n ∧ h' = h ∧ cs = [] := ev.literal_inv

private theorem inv_args1 {locals : Environment F Nat} {e₁ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁] h vs h' cs) :
    ∃ v₁, vs = [v₁] ∧ ObsExpr W [] locals e₁ h v₁ h' cs := by
  obtain ⟨v₁, _, _, c₁, c₂, rfl, d₁, a₂, rfl⟩ := ev.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := a₂.nil_inv
  exact ⟨v₁, rfl, by simpa using d₁⟩

private theorem inv_args2 {locals : Environment F Nat} {e₁ e₂ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁, e₂] h vs h' cs) :
    ∃ v₁ v₂ m₁ c₁ c₂, vs = [v₁, v₂] ∧ cs = c₁ ++ c₂ ∧
      ObsExpr W [] locals e₁ h v₁ m₁ c₁ ∧ ObsExpr W [] locals e₂ m₁ v₂ h' c₂ := by
  obtain ⟨v₁, _, m₁, c₁, c₂, rfl, d₁, a₂, rfl⟩ := ev.cons_inv
  obtain ⟨v₂, rfl, d₂⟩ := inv_args1 a₂
  exact ⟨v₁, v₂, m₁, c₁, c₂, rfl, rfl, d₁, d₂⟩

private theorem inv_args3 {locals : Environment F Nat} {e₁ e₂ e₃ : Aiur.Generic.Expr F}
    {h h' : Heap F} {vs : List (SourceValue F)} {cs : List (Call F)}
    (ev : ObsArgs W [] locals [e₁, e₂, e₃] h vs h' cs) :
    ∃ v₁ v₂ v₃ m₁ m₂ c₁ c₂ c₃, vs = [v₁, v₂, v₃] ∧ cs = c₁ ++ c₂ ++ c₃ ∧
      ObsExpr W [] locals e₁ h v₁ m₁ c₁ ∧ ObsExpr W [] locals e₂ m₁ v₂ m₂ c₂ ∧
      ObsExpr W [] locals e₃ m₂ v₃ h' c₃ := by
  obtain ⟨v₁, _, m₁, c₁, cr, rfl, d₁, a₂, rfl⟩ := ev.cons_inv
  obtain ⟨v₂, v₃, m₂, c₂, c₃, rfl, rfl, d₂, d₃⟩ := inv_args2 a₂
  exact ⟨v₁, v₂, v₃, m₁, m₂, c₁, c₂, c₃, rfl, by simp [List.append_assoc], d₁, d₂, d₃⟩

/-- Extracts the `KernelCheck::validate_expr_well_scoped [rhs, 0, nl]` call (step 4 of
`KernelModeled::check_iota_rule`), its heap extension, and its membership in `calls`. -/
private theorem check_iota_rule_validate_rhs
    {rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst aset r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelModeled::check_iota_rule"
      [rc, rm, nl, ty_r, rp, ni, rhs, cprj, cty, cnp, cnf, ilvls, pins, t_addr, src, dst, aset]
      h r h' calls) :
    ∃ (h_plen h_sc : Heap F) (v_sc : SourceValue F) (cs_sc : List (Call F)),
      Heap.Extends h h_plen ∧
      ObsFn W "KernelCheck::validate_expr_well_scoped" [rhs, .field 0, nl] h_plen v_sc h_sc cs_sc ∧
      (⟨"KernelCheck::validate_expr_well_scoped", [rhs, .field 0, nl], h_plen⟩ : Call F) ∈ calls := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelModeled.check_iota_rule.lookup
    (by simp [IxVM.KernelModeled.check_iota_rule, ControlLower.hasControl]) ev
  simp only [IxVM.KernelModeled.check_iota_rule] at d0
  -- 1. `let mi = rp + ni`
  obtain ⟨mi, _, _, c1a, c1b, d1, mt1, rest1, hc1⟩ := d0.letValue_inv
  obtain ⟨_, _, _, _, _, dl1, dr1, _, _⟩ := d1.binary_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) dl1
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) dr1
  obtain rfl := matchPattern_bind_inv mt1
  -- 2. `let d = rp + cnf`
  obtain ⟨d, _, _, c2a, c2b, d2, mt2, rest2, hc2⟩ := rest1.letValue_inv
  obtain ⟨_, _, _, _, _, dl2, dr2, _, _⟩ := d2.binary_inv
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) dl2
  obtain ⟨rfl, rfl, _⟩ := inv_var_find (by rfl) dr2
  obtain rfl := matchPattern_bind_inv mt2
  -- 3. `assert_eq!(Lists::length(pins), cnp)`
  obtain ⟨_, m3, _, c3a, c3b, d3, mt3, rest3, hc3⟩ := rest2.letValue_inv
  obtain ⟨_, a3, ap3⟩ := d3.builtin_inv
  obtain ⟨v3_l, v3_r, h_plen, c3_l, c3_r, rfl, hc3_args, d3_l, d3_r⟩ := inv_args2 a3
  obtain ⟨_, _, _, cs_plen, a3_la, ev_plen, hc_plen⟩ := d3_l.call_inv
  rw [Obs.Names.n6682477127133607924] at ev_plen hc_plen
  obtain ⟨_, rfl, d3_lv⟩ := inv_args1 a3_la
  obtain ⟨rfl, rfl, rfl⟩ := inv_var_find (by rfl) d3_lv
  obtain ⟨rfl, hm3, rfl⟩ := inv_var_find (by rfl) d3_r; subst m3
  obtain ⟨_, rfl⟩ := Builtin.assertEq_inv ap3
  obtain rfl := matchPattern_wildcard_inv mt3
  -- 4. `KernelCheck::validate_expr_well_scoped(rhs, 0, nl)`
  obtain ⟨v_sc, h_sc, _, c4a, c4b, d4, mt4, _, hc4⟩ := rest3.letValue_inv
  obtain ⟨_, m4_3, _, cs_sc, a4, ev_sc, hc_sc⟩ := d4.call_inv
  rw [instanceName_plain_some] at ev_sc hc_sc
  obtain ⟨_, _, _, m4_1, m4_2, _, _, _, rfl, hc4_args, d4_1, d4_2, d4_3⟩ := inv_args3 a4
  obtain ⟨rfl, hm4_1, rfl⟩ := inv_var_find (by rfl) d4_1; subst m4_1
  obtain ⟨rfl, hm4_2, rfl⟩ := inv_lit d4_2; subst m4_2
  obtain ⟨rfl, hm4_3, rfl⟩ := inv_var_find (by rfl) d4_3; subst m4_3
  refine ⟨h_plen, h_sc, v_sc, cs_sc, ev_plen.heap_extends, ev_sc, ?_⟩
  rw [hc1, hc2, hc3, hc4, hc_sc, hc4_args]
  simp

/-! ### Recursor blocks (`check_family` → `check_recs`, and `MemberCheckedLimAt` → `Rec_n0` / `Rec_other`) -/

private theorem check_rules_go_levelsOk {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {nl : Nat} {blobs : List (_root_.Address × ByteArray)}
    {xrc xrm xty xrp xni xib xiidx xinp xilvls xpins xsrc xdst xaset : SourceValue F}
    (hbd : Bounded calls) (hnl32 : nl < 4294967296) :
    ∀ (rus : List Ixon.RecursorRule) (j : Nat) {xrules xs xj r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      (∀ cl ∈ cs, cl ∈ calls) →
      L1.RawRulesRep crb.refs.toList (L1.blockRecurAddrs rb rs.toList) crb.univs.toList
        crb.sharing.toList blobs h j rus xrules →
      ObsFn W "KernelModeled::check_rules_go"
        [xrc, xrm, .field (nl : F), xty, xrp, xni, xrules, xib, xiidx, xinp, xilvls, xpins,
          xsrc, xdst, xaset, xs, xj] h r h' cs →
      ∀ ru ∈ rus, ∀ E_rd,
        (exprReader t (fun x => E₀.blobs.get? x) crb id (blockSelf t rb rs)).read ru.rhs = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range nl) = true := by
  intro rus
  induction rus with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ hm; cases hm
  | cons ru rest ih =>
    intro j xrules xs xj r h h' cs hsub hraw ev
    rcases hraw with _ | ⟨cell, hru, hrest⟩
    match Obs.«KernelModeled::check_rules_go».obs ev with
    | .Nil (ld12 := ld) .. =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ hc _; simp at hc
    | .Cons (x_rest := xrest) (m42 := m1) (m117 := m2) (m155 := m3) (m77 := m4)
        (x_rhs := xrhs) (cs290 := cs_io) (cs432 := cs_rec)
        (ld12 := ld) (ev54 := evga) (ev129 := evprj) (ev171 := evci) (ev292 := evio)
        (ev434 := evrec) (hc579 := hc) .. =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hl
      injection hl with h1 hl; injection hl with h2 _; subst h2
      obtain ⟨-, rhsPtr, hv_ru, raw_rhs⟩ := hru
      rw [hv_ru] at h1
      injection h1 with _ _ hrl; injection hrl with _ hrl
      injection hrl with _ hrl; injection hrl with hrhs _; subst hrhs
      have ext03 : Heap.Extends h m3 :=
        evga.heap_extends.trans (evprj.heap_extends.trans evci.heap_extends)
      obtain ⟨h_plen, h_sc, v_sc, cs_sc, ext_io, ev_sc, hcall_io⟩ :=
        check_iota_rule_validate_rhs evio
      have hcall_sc : (⟨"KernelCheck::validate_expr_well_scoped",
          [rhsPtr, .field 0, .field (nl : F)], h_plen⟩ : Call F) ∈ calls :=
        hsub _ (mem_of_eq hc (by call_mem))
      have hru_ok : ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) crb id
          (blockSelf t rb rs)).read ru.rhs = .ok E_rd →
          E_rd.allLevelParamsDefined (List.range nl) = true :=
        validate_reader_levels hbd hnl32 raw_rhs (ext03.trans ext_io) ev_sc hcall_sc
      have htail := ih (j + 1) (fun cl hcl => hsub cl (mem_of_eq hc (by call_mem)))
        (hrest.mono (ext03.trans evio.heap_extends) (fun _ hm => hm)) evrec
      intro ru' hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hru_ok
      · exact htail ru' hmem

private theorem build_recur_addrs_walk_hashed_spec {ms : List Ixon.MutConst} {b : Bytes.Address}
    {cur : List Ixon.MutConst} :
    ∀ {k : Nat} {x_all_members x_block_addr x_cur r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      k ≤ 72057594037927936 →
      Core.Specs.Callees.MembersRep h ms x_all_members →
      Bytes.RepAddressRef addrTy h b x_block_addr →
      Core.Specs.Callees.MembersRep h cur x_cur →
      (∀ j m', cur[j]? = some m' → ms[k + j]? = some m') →
      ObsFn W "Ingress::build_recur_addrs_walk"
        [x_all_members, x_block_addr, x_cur, .field (k : F)] h r h' cs →
      Heap.Extends h h' ∧
        ∃ as : List Bytes.Address,
          RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as r ∧
          as.length = cur.length ∧
          ∀ i a, as[i]? = some a →
            ∃ m, cur[i]? = some m ∧
              k + i < 72057594037927936 ∧
              ixAddr a = Core.projAddr (Core.Specs.Callees.memberProjInfo (ixAddr b) (k + i) m) ∧
              Hashed cs (Ixon.serConstant
                ⟨Core.Specs.Callees.memberProjInfo (ixAddr b) (k + i) m, #[], #[], #[], #[]⟩) := by
  induction cur with
  | nil =>
    intro k x_all_members x_block_addr x_cur r h h' cs _ _ _ hcur _ ev
    match Obs.«Ingress::build_recur_addrs_walk».obs ev with
    | .Nil (he24 := he24) (hm23 := hm23) .. =>
      rw [he24, hm23]
      exact ⟨Heap.Extends.snoc h _, [], Lib.rep_store_nil h, rfl, fun _ _ hi => by simp at hi⟩
    | .Cons (ld12 := ld12) .. =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hcur ld12; cases he
  | cons m rest ih =>
    intro k x_all_members x_block_addr x_cur r h h' cs hk hms hb hcur hsuf ev
    match Obs.«Ingress::build_recur_addrs_walk».obs ev with
    | .Nil (ld12 := ld12) .. => cases Lib.rep_nil_of_load hcur ld12
    | .Cons (x_rest := x_rest) (v55 := v55) (v56 := v56) (m58 := m58) (cs66 := cs66)
        (m94 := m94) (cs102 := cs102) (v108 := v108)
        (ld12 := ld12) (he51 := he51) (hm50 := hm50) (ev68 := ev68) (op143 := op143)
        (ev104 := ev104) (hc145 := hc145) .. =>
      obtain ⟨m', rest', he, _, hrest⟩ := Lib.rep_cons_of_load hcur ld12
      injection he with hm_eq hrest_eq; subst hm_eq hrest_eq
      obtain ⟨ext1, hk_lt, -, mc, a₀, hget_mc, ha₀, ha₀_eq, hh₀⟩ :=
        L1.projection_addr_hashed_spec hms hb ev68
      have hk_val : ((k : F)).val = k :=
        ZMod.val_natCast_of_lt (Nat.lt_of_le_of_lt hk (by decide))
      rw [hk_val] at hk_lt hget_mc ha₀_eq hh₀
      have hmc_eq : mc = m := by
        have h0 := hsuf 0 m rfl
        rw [Nat.add_zero, hget_mc] at h0
        exact Option.some.inj h0
      rcases hmc_eq with rfl
      obtain rfl := binop_add_one_nat op143
      obtain ⟨ext2, as_tl, has_tl, hlen_tl, htl⟩ :=
        ih (by omega) (hms.mono (fun _ _ _ _ _ h => h) ext1)
          (Bytes.repAddressRef_heapMono₂ addrTy ext1 hb)
          (hrest.mono (fun _ _ _ _ _ h => h) ext1)
          (fun j m' hj => by
            have hstep := hsuf (j + 1) m' hj
            rwa [show k + 1 + j = k + (j + 1) by omega])
          ev104
      rw [he51, hm50]
      have ext_fin : Heap.Extends m94
          (m94 ++ [.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Cons" [v55, v56]]) :=
        Heap.Extends.snoc m94 _
      have hcons : RepList addrListEnum (Bytes.RepAddressRef addrTy)
          (m94 ++ [.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Cons" [v55, v56]])
          (a₀ :: as_tl) (.ptr (.enum Obs.Names.«Lists::Node<&[Field; 32]>») m94.length) :=
        Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy)
          (Bytes.repAddressRef_heapMono₂ addrTy ext2 ha₀) has_tl
      refine ⟨(ext1.trans ext2).trans ext_fin, a₀ :: as_tl, hcons, by simp [hlen_tl], ?_⟩
      intro i a hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
        exact ⟨mc, rfl, by omega, by simpa using ha₀_eq,
          Core.hashed_mono (fun cl hcl => mem_of_eq hc145 (by call_mem)) (by simpa using hh₀)⟩
      | succ i' =>
        obtain ⟨m', hm', hk', ha', hh'⟩ := htl i' a (by simpa using hi)
        rw [show k + 1 + i' = k + (i' + 1) by omega] at hk' ha' hh'
        exact ⟨m', by simpa using hm', hk', ha',
          Core.hashed_mono (fun cl hcl => mem_of_eq hc145 (by call_mem)) hh'⟩

theorem build_recur_addrs_hashed_spec {ms : List Ixon.MutConst} {b : Bytes.Address}
    {x_members x_block_addr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hms : Core.Specs.Callees.MembersRep h ms x_members)
    (hb : Bytes.RepAddressRef addrTy h b x_block_addr)
    (ev : ObsFn W "Ingress::build_recur_addrs" [x_members, x_block_addr] h r h' cs) :
    Heap.Extends h h' ∧
      ∃ as : List Bytes.Address,
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as r ∧
        as.length = ms.length ∧
        ∀ i a, as[i]? = some a →
          ∃ m, ms[i]? = some m ∧
            i < 72057594037927936 ∧
            ixAddr a = Core.projAddr (Core.Specs.Callees.memberProjInfo (ixAddr b) i m) ∧
            Hashed cs (Ixon.serConstant
              ⟨Core.Specs.Callees.memberProjInfo (ixAddr b) i m, #[], #[], #[], #[]⟩) := by
  match Obs.«Ingress::build_recur_addrs».obs ev with
  | .run (cs4 := cs4) (ev6 := ev6) (hc38 := hc38) =>
    have ev6' : ObsFn W "Ingress::build_recur_addrs_walk"
        [x_members, x_block_addr, x_members, .field ((0 : Nat) : F)] h r h' cs4 := by
      simpa using ev6
    obtain ⟨ext, as, has, hlen, hmem⟩ :=
      build_recur_addrs_walk_hashed_spec (Nat.zero_le _) hms hb hms
        (fun j m' hj => by simpa using hj) ev6'
    refine ⟨ext, as, has, hlen, fun i a hi => ?_⟩
    obtain ⟨m, hm, hi56, ha, hh⟩ := hmem i a hi
    simp only [Nat.zero_add] at hi56 ha hh
    exact ⟨m, hm, hi56, ha, Core.hashed_mono (fun cl hcl => mem_of_eq hc38 (by call_mem)) hh⟩

theorem family_recs_muts_list {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) {b : Bytes.Address} {x_rb v : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hb : Bytes.RepAddressRef addrTy h b x_rb)
    (ev : ObsFn W "KernelModeled::family_recs" [x_rb] h v h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hrec : recordOf E₀ (ixAddr b) = some crb) (hrs : crb.info = .muts rs) :
    ∃ as : List Bytes.Address, RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as v ∧
      as.length = rs.size ∧
      ∀ i a, as[i]? = some a →
        ∃ m, rs[i]? = some m ∧
          i < 72057594037927936 ∧
          ixAddr a = Core.projAddr (Core.Specs.Callees.memberProjInfo (ixAddr b) i m) ∧
          Hashed calls (Ixon.serConstant
            ⟨Core.Specs.Callees.memberProjInfo (ixAddr b) i m, #[], #[], #[], #[]⟩) := by
  match Obs.«KernelModeled::family_recs».obs ev with
  | .Muts (m2 := m2) (m123 := m123) (cs12 := cs12) (cs146 := cs146) (ev14 := ev14)
      (ev113 := ev113) (ev133 := ev133) (ev148 := ev148) (hc165 := hc) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (mem_of_eq hc (by call_mem))
    have hsub146 : ∀ cl ∈ cs146, cl ∈ calls := fun cl hcl => hsub cl (mem_of_eq hc (by call_mem))
    obtain ⟨cb, ms, hbl, hrep⟩ := Claim.load_block_head hb ev14
    obtain ⟨rfl, -⟩ := (hbl.mono hsub12).record hS hrec
    obtain ⟨-, -, -, -, -, hbl_muts⟩ := hbl
    have e2 : ms = rs := Ixon.ConstantInfo.muts.inj (hbl_muts.symm.trans hrs)
    subst ms
    have ext : Heap.Extends m2 m123 := ev113.heap_extends.trans ev133.heap_extends
    have hmems :=
      Route.membersRep_of_repMutConstList (RepLinkedList.mono L1.repMutConst_heapMono₂ ext hrep)
    have hb2 : Bytes.RepAddressRef addrTy m123 b x_rb :=
      Bytes.repAddressRef_heapMono₂ addrTy (ev14.heap_extends.trans ext) hb
    obtain ⟨-, as, has, hlen, hmem⟩ := build_recur_addrs_hashed_spec hmems hb2 ev148
    refine ⟨as, has, by simpa using hlen, fun i a hi => ?_⟩
    obtain ⟨m, hm, hi56, ha, hh⟩ := hmem i a hi
    exact ⟨m, by rwa [Array.getElem?_toList] at hm, hi56, ha, Core.hashed_mono hsub146 hh⟩
  | .Recr (cs12 := cs12) (ev14 := ev14) (hc209 := hc) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (mem_of_eq hc (by call_mem))
    obtain ⟨-, bytes, c, -, hh, ha, hexact, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hb ev14
    have hc_eq : c = crb := record_eq_of_hashed_l hS hsub12 hrec hh ha hexact
    subst c
    obtain ⟨infoVal, _, _, _, _, hceq, hinfoRep, -, -, -, -⟩ := cRep
    injection hceq with _ _ hcl; injection hcl with hi _
    rw [hrs] at hinfoRep
    obtain ⟨mp, hmp, -⟩ := hinfoRep
    rw [← hi] at hmp; simp at hmp

private theorem check_recs_levelsOk {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {rb_b : Bytes.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {xrc xta xsrc xdst xaset xnrecs xnp xuo xbnl xfam : SourceValue F}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hcrb : recordOf E₀ (ixAddr rb_b) = some crb) (hrs : crb.info = .muts rs) :
    ∀ (as : List Bytes.Address) (pos : Nat),
      pos + as.length = rs.size →
      (∀ i a, as[i]? = some a →
        ∃ m, rs[pos + i]? = some m ∧
          pos + i < 72057594037927936 ∧
          ixAddr a = Core.projAddr (Core.Specs.Callees.memberProjInfo (ixAddr rb_b) (pos + i) m) ∧
          Hashed calls (Ixon.serConstant
            ⟨Core.Specs.Callees.memberProjInfo (ixAddr rb_b) (pos + i) m, #[], #[], #[], #[]⟩)) →
      ∀ {xrecs xmods xs xk xform r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        (∀ cl ∈ cs, cl ∈ calls) →
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h as xrecs →
        ObsFn W "KernelModeled::check_recs"
          [xrc, xta, xrecs, xmods, xsrc, xdst, xaset, xs, xnrecs, xk, xnp, xuo, xbnl, xfam, xform]
          h r h' cs →
        ∀ (i : Nat) (rc : Ixon.Recursor), rs[pos + i]? = some (.recr rc) → i < as.length →
          rc.lvls.toNat < 4294967296 ∧
          (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) crb id
              (blockSelf t (ixAddr rb_b) rs)).read rc.typ = .ok E_rd →
            E_rd.allLevelParamsDefined (List.range rc.lvls.toNat) = true) ∧
          (∀ (j : Nat) (ru : Ixon.RecursorRule) E_rd, rc.rules[j]? = some ru →
            (exprReader t (fun x => E₀.blobs.get? x) crb id
                (blockSelf t (ixAddr rb_b) rs)).read ru.rhs = .ok E_rd →
            E_rd.allLevelParamsDefined (List.range rc.lvls.toNat) = true) := by
  intro as
  induction as with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlt; cases hlt
  | cons a rest ih =>
    intro pos hlen hat xrecs xmods xs xk xform r h h' cs hsub hrep ev
    match Obs.«KernelModeled::check_recs».obs ev with
    | .Nil (ld12 := ld) .. => cases Core.RepList.nil_of_load hrep ld
    | .Cons (x_r := xr) (x_rest := xrest) (m67 := m1) (p74 := p1) (cs80 := cs1)
        (x_nl := xnl) (x_ty := xty) (x_rules := xrules)
        (m288 := m2) (m349 := m3) (m335 := m4) (m391 := m5) (m473 := m6)
        (m511 := m7) (m561 := m8) (m_oajaqiwd := m8a) (m_obmhbjvc := m9)
        (m_shkxqcak := m10) (m_raxeqbbt := m10a) (m_yfwcpmwj := m11) (m_cjjqtxxk := m12)
        (m_tsdchhaz := m13) (m_akkqvxxx := m14) (m627 := m14a) (m596 := m15)
        (m640 := m16) (m669 := m17) (m698 := m18) (m_pipdqnib := m19) (m_pzqbkmwo := m20)
        (m838 := m21) (m892 := m22) (cs902 := cs_ru) (cs1014 := cs_rec)
        (ld12 := ld) (ev82 := evci) (ld76 := ldci)
        (ev298 := e2) (ev359 := e3) (ev345 := e4) (ev403 := e5) (ev485 := e6)
        (ev523 := evval) (ev571 := e8) (hm_odcsfbbr := hm8a) (ev_uprevpxl := e9)
        (ev_svgicqcr := e10) (hm_owdmgqhw := hm10a) (ev_oqkxxxxs := e11)
        (ev_eejlfykm := e12) (ev_uoyvrvop := e13) (ev_akrqpecc := e14)
        (hm635 := hm14a) (ev608 := e15) (ev652 := e16) (ev681 := e17) (ev710 := e18)
        (ev_uoummlhs := e19) (ev_tjosvhyt := e20) (ev850 := e21)
        (ev904 := evrules) (ev1016 := evrec) (hc1137 := hcs) .. =>
      obtain ⟨a', rest', hcons, ra, hrest⟩ := Core.RepList.cons_of_load hrep ld
      injection hcons with h1 h2; subst h1 h2
      have sub1 : ∀ cl ∈ cs1, cl ∈ calls := fun cl hcl => hsub cl (mem_of_eq hcs (by call_mem))
      obtain ⟨ext1, rawBytes, cp, blobs, hh_p, ha_p, hde_p, -, -, -, hrawRes⟩ :=
        L1.get_ci_spec (RomBound.bounded_mono hbd sub1) ra evci
      obtain ⟨m0, hm0, hpos56, ha0, hh0⟩ := hat 0 a rfl
      simp only [Nat.add_zero] at hm0 hpos56 ha0 hh0
      have ext1_6 : Heap.Extends m1 m6 :=
        e2.heap_extends.trans <| e3.heap_extends.trans <| e4.heap_extends.trans <|
          e5.heap_extends.trans e6.heap_extends
      have ext1_21 : Heap.Extends m1 m21 := by
        have e8a : Heap.Extends m8 m8a := by rw [hm8a]; exact Heap.Extends.snoc _ _
        have e10a : Heap.Extends m10 m10a := by rw [hm10a]; exact Heap.Extends.snoc _ _
        have e14a : Heap.Extends m14 m14a := by rw [hm14a]; exact Heap.Extends.snoc _ _
        exact ext1_6.trans <| evval.heap_extends.trans <| e8.heap_extends.trans <| e8a.trans <|
          e9.heap_extends.trans <| e10.heap_extends.trans <| e10a.trans <| e11.heap_extends.trans <|
          e12.heap_extends.trans <| e13.heap_extends.trans <| e14.heap_extends.trans <| e14a.trans <|
          e15.heap_extends.trans <| e16.heap_extends.trans <| e17.heap_extends.trans <|
          e18.heap_extends.trans <| e19.heap_extends.trans <| e20.heap_extends.trans e21.heap_extends
      have hsub_all : Heap.Extends h m22 := ext1.trans (ext1_21.trans evrules.heap_extends)
      have hhat' : ∀ i a', rest[i]? = some a' →
          ∃ m, rs[(pos + 1) + i]? = some m ∧
            (pos + 1) + i < 72057594037927936 ∧
            ixAddr a' = Core.projAddr (Core.Specs.Callees.memberProjInfo (ixAddr rb_b) ((pos + 1) + i) m) ∧
            Hashed calls (Ixon.serConstant
              ⟨Core.Specs.Callees.memberProjInfo (ixAddr rb_b) ((pos + 1) + i) m, #[], #[], #[], #[]⟩) := by
        intro i a' hi
        have h1 := hat (i + 1) a' (by simpa using hi)
        rwa [show pos + (i + 1) = (pos + 1) + i by omega] at h1
      have htail := ih (pos + 1) (by simp only [List.length_cons] at hlen; omega) hhat'
        (fun cl hcl => hsub cl (mem_of_eq hcs (by call_mem)))
        (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) hsub_all hrest) evrec
      intro i rc hrc hi_lt
      cases i with
      | succ i' =>
        rw [show pos + (i' + 1) = (pos + 1) + i' by omega] at hrc
        exact htail i' rc hrc (by simp only [List.length_cons] at hi_lt; omega)
      | zero =>
        simp only [Nat.add_zero] at hrc
        have hm0_eq : m0 = .recr rc := Option.some.inj (hm0.symm.trans hrc)
        subst hm0_eq
        have hraw_eq : rawBytes = Ixon.serConstant
            ⟨.rPrj ⟨pos.toUInt64, ixAddr rb_b⟩, #[], #[], #[], #[]⟩ :=
          hS.hashed_inj (Core.hashed_mono sub1 hh_p) hh0 (ha_p.trans ha0)
        rw [hraw_eq, Ixon.Verify.deConstantExact_serConstant _
          (L1.projConstant_wireWF_rPrj pos.toUInt64 rb_b)] at hde_p
        injection hde_p with hcp_eq; subst hcp_eq
        simp only [L1.GetCIRawResult] at hrawRes
        obtain ⟨-, blkBytes, crb', rs', rc', v', hhB, haB, hdeB, -, hrs', hrc', hld', hrawR⟩ := hrawRes
        have hcrb_eq : crb' = crb := record_eq_of_hashed_l hS sub1 hcrb hhB haB hdeB
        subst crb'
        have hrs_eq : rs' = rs := Ixon.ConstantInfo.muts.inj (hrs'.symm.trans hrs)
        subst rs'
        have hpos_eq : pos.toUInt64.toNat = pos := by
          rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
        rw [hpos_eq, Array.getElem?_toList, hrc] at hrc'
        injection hrc' with hrm; injection hrm with hrc_eq; subst rc'
        rw [hld'] at ldci; injection ldci with hv_eq
        obtain ⟨hnl32, -, -, -, -, -, tyPtr, rulesPtr, blkPtr, _, -, -, hv', raw_ty, raw_rules⟩ := hrawR
        rw [hv'] at hv_eq
        injection hv_eq with _ _ hl
        injection hl with h1 hl; injection hl with h2 hl; injection hl with _ hl
        injection hl with _ hl; injection hl with _ hl; injection hl with _ hl
        injection hl with h6 _
        subst h1 h2 h6
        have hty_ok : ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) crb id
            (blockSelf t (ixAddr rb_b) rs)).read rc.typ = .ok E_rd →
            E_rd.allLevelParamsDefined (List.range rc.lvls.toNat) = true :=
          validate_reader_levels hbd hnl32 raw_ty ext1_6 evval
            (hsub _ (mem_of_eq hcs (by call_mem)))
        have hrules_ok : ∀ j ru E_rd, rc.rules[j]? = some ru →
            (exprReader t (fun x => E₀.blobs.get? x) crb id
                (blockSelf t (ixAddr rb_b) rs)).read ru.rhs = .ok E_rd →
            E_rd.allLevelParamsDefined (List.range rc.lvls.toNat) = true := by
          match Obs.«KernelModeled::check_rules».obs evrules with
          | .run (ev14 := evrmp) (ev74 := evgci) (ev157 := evrlen) (ev179 := evgo)
              (hc315 := hc_ru) .. =>
            have ext_go : Heap.Extends m1 _ :=
              ext1_21.trans (evrmp.heap_extends.trans (evgci.heap_extends.trans evrlen.heap_extends))
            have hgo := check_rules_go_levelsOk hbd hnl32 rc.rules.toList 0
              (fun cl hcl => by
                have h1 := mem_of_eq hc_ru (by call_mem)
                exact hsub cl (mem_of_eq hcs (by call_mem)))
              (raw_rules.mono ext_go (fun _ hm => hm)) evgo
            intro j ru E_rd hj hread
            exact hgo ru (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj)) E_rd hread
        exact ⟨hnl32, hty_ok, hrules_ok⟩

/-- **`KernelModeled::check_family` validates every recursor member of its recursor block**
(both `rc.typ` and every `ru.rhs`). -/
theorem check_family_recr_levelsOk {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {rb_b : Bytes.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {xrc xb xrb r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hcrb : recordOf E₀ (ixAddr rb_b) = some crb) (hrs : crb.info = .muts rs)
    (hrb : Bytes.RepAddressRef addrTy h rb_b xrb)
    (ev : ObsFn W "KernelModeled::check_family" [xrc, xb, xrb] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∀ (k : Nat) (rc : Ixon.Recursor), rs[k]? = some (.recr rc) →
      rc.lvls.toNat < 4294967296 ∧
      (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) crb id
          (blockSelf t (ixAddr rb_b) rs)).read rc.typ = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range rc.lvls.toNat) = true) ∧
      (∀ (j : Nat) (ru : Ixon.RecursorRule) E_rd, rc.rules[j]? = some ru →
        (exprReader t (fun x => E₀.blobs.get? x) crb id
            (blockSelf t (ixAddr rb_b) rs)).read ru.rhs = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range rc.lvls.toNat) = true) := by
  match Obs.«KernelModeled::check_family».obs ev with
  | .run (m105 := mf1) (m784 := m_pre_fr) (m840 := m_post_fr) (m1293 := m_pre_cr)
      (cs850 := cs_fr) (cs1341 := cs_cr)
      (sg112 := sg1) (ev126 := e1) (ev148 := e2) (ev194 := e3) (ev_yqjbwijz := e4)
      (ev231 := e5) (ev266 := e6) (ev309 := e7) (ev344 := e8) (ev403 := e9)
      (ev435 := e10) (ev465 := e11) (ev513 := e12) (ev601 := e13) (ev634 := e14)
      (ev664 := e15) (ev686 := e16) (ev716 := e17) (ev759 := e18) (ev817 := e19)
      (ev796 := e20) (ev852 := evfr)
      (ev_ursqbimm := f1) (ev_srfmazjk := f2) (ev874 := f3) (ev896 := f4)
      (ev960 := f5) (ev939 := f6) (ev1011 := f7) (ev990 := f8)
      (ev_edyzsqzv := f9) (ev_gkddqxhv := f10) (ev_ittpynob := f11) (ev_biaifgpd := f12)
      (ev1203 := f13) (ev_cwwgzxtj := f14) (ev1246 := f15) (ev_mitevvsv := f16)
      (ev_rqpeovbn := f17) (ev_xrhmaojz := f18) (ev_whimdwjd := f19) (ev1305 := f20)
      (ev1343 := evcr) (hc1474 := hc) .. =>
    have ext_sg1 : Heap.Extends h mf1 := by
      cases sg1 with
      | Nil _ _ evax _ hh _ => rw [hh]; exact evax.heap_extends
      | Node _ _ _ _ _ _ _ _ heq _ _ _ => exact absurd (Value.field.inj heq) (by decide)
    have ext_to_fr : Heap.Extends h m_pre_fr :=
      ext_sg1.trans <| e1.heap_extends.trans <| e2.heap_extends.trans <| e3.heap_extends.trans <|
        e4.heap_extends.trans <| e5.heap_extends.trans <| e6.heap_extends.trans <|
        e7.heap_extends.trans <| e8.heap_extends.trans <| e9.heap_extends.trans <|
        e10.heap_extends.trans <| e11.heap_extends.trans <| e12.heap_extends.trans <|
        e13.heap_extends.trans <| e14.heap_extends.trans <| e15.heap_extends.trans <|
        e16.heap_extends.trans <| e17.heap_extends.trans <| e18.heap_extends.trans <|
        e19.heap_extends.trans e20.heap_extends
    have ext_fr_to_cr : Heap.Extends m_post_fr m_pre_cr :=
      f1.heap_extends.trans <| f2.heap_extends.trans <| f3.heap_extends.trans <|
        f4.heap_extends.trans <| f5.heap_extends.trans <| f6.heap_extends.trans <|
        f7.heap_extends.trans <| f8.heap_extends.trans <| f9.heap_extends.trans <|
        f10.heap_extends.trans <| f11.heap_extends.trans <| f12.heap_extends.trans <|
        f13.heap_extends.trans <| f14.heap_extends.trans <| f15.heap_extends.trans <|
        f16.heap_extends.trans <| f17.heap_extends.trans <| f18.heap_extends.trans <|
        f19.heap_extends.trans f20.heap_extends
    obtain ⟨as, has, hlen, hmem⟩ := family_recs_muts_list hS
      (Bytes.repAddressRef_heapMono₂ addrTy ext_to_fr hrb) evfr
      (fun cl hcl => hsub cl (mem_of_eq hc (by call_mem))) hcrb hrs
    have hcr := check_recs_levelsOk (t := t) hS hbd hcrb hrs as 0 (by omega)
      (fun i a hi => by simpa using hmem i a hi)
      (fun cl hcl => hsub cl (mem_of_eq hc (by call_mem)))
      (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) ext_fr_to_cr has) evcr
    intro k rc hk
    have hk_lt : k < as.length := by
      have := (Array.getElem?_eq_some_iff.mp hk).1; omega
    exact hcr k rc (by simpa using hk) hk_lt

private theorem check_rec_rules_wellscoped_levelsOk {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {rb : _root_.Address} {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} {nl : Nat} {blobs : List (_root_.Address × ByteArray)}
    {xod : SourceValue F}
    (hbd : Bounded calls) (hnl32 : nl < 4294967296) :
    ∀ (rus : List Ixon.RecursorRule) (j : Nat) {xrules r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      (∀ cl ∈ cs, cl ∈ calls) →
      L1.RawRulesRep crb.refs.toList (L1.blockRecurAddrs rb rs.toList) crb.univs.toList
        crb.sharing.toList blobs h j rus xrules →
      ObsFn W "KernelCheck::check_rec_rules_wellscoped" [xrules, xod, .field (nl : F)] h r h' cs →
      ∀ ru ∈ rus, ∀ E_rd,
        (exprReader t (fun x => E₀.blobs.get? x) crb id (blockSelf t rb rs)).read ru.rhs = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range nl) = true := by
  intro rus
  induction rus with
  | nil => intro _ _ _ _ _ _ _ _ _ _ hm; cases hm
  | cons ru rest ih =>
    intro j xrules r h h' cs hsub hraw ev
    rcases hraw with _ | ⟨cell, hru, hrest⟩
    match Obs.«KernelCheck::check_rec_rules_wellscoped».obs ev with
    | .Nil (ld12 := ld) .. =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ hc _; simp at hc
    | .Cons (x_rest := xrest) (x_rhs := xrhs) (ld12 := ld) (ev87 := evval) (ev116 := evrec)
        (hc141 := hc) .. =>
      rw [Core.loadValue_enum_cell cell] at ld
      injection ld with hv; injection hv with _ _ hl
      injection hl with h1 hl; injection hl with h2 _; subst h2
      obtain ⟨-, rhsPtr, hv_ru, raw_rhs⟩ := hru
      rw [hv_ru] at h1
      injection h1 with _ _ hrl; injection hrl with _ hrl
      injection hrl with _ hrl; injection hrl with hrhs _; subst hrhs
      have hru_ok : ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) crb id
          (blockSelf t rb rs)).read ru.rhs = .ok E_rd →
          E_rd.allLevelParamsDefined (List.range nl) = true :=
        validate_reader_levels hbd hnl32 raw_rhs (Heap.Extends.refl _) evval
          (hsub _ (mem_of_eq hc (by call_mem)))
      have htail := ih (j + 1) (fun cl hcl => hsub cl (mem_of_eq hc (by call_mem)))
        (hrest.mono evval.heap_extends (fun _ hm => hm)) evrec
      intro ru' hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hru_ok
      · exact htail ru' hmem

/-- **`MemberCheckedLimAt` on a recursor member `ms[k] = .recr rc`** validates `rc.typ` and
every `ru.rhs` (both non-modeled via `check_recursor_member` and modeled via `check_family`). -/
theorem memberCheckedLimAt_recr_levelsOk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {b : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {k : Nat} {rc_m : Ixon.Recursor} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hcb : recordOf E₀ b = some cb) (hms : cb.info = .muts ms)
    (hk : ms[k]? = some (.recr rc_m))
    (hmc : Claim.MemberCheckedLimAt calls bAddr t b ms k lim) :
    rc_m.lvls.toNat < 4294967296 ∧
    (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t b ms)).read rc_m.typ = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range rc_m.lvls.toNat) = true) ∧
    (∀ (j : Nat) (ru : Ixon.RecursorRule) E_rd, rc_m.rules[j]? = some ru →
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t b ms)).read ru.rhs = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range rc_m.lvls.toNat) = true) := by
  obtain ⟨hk56, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, ba_p, blobs,
    -, -, -, hld, hrawRes, hsub_ld, ev_chk, hsub_chk⟩ :=
    memberChecked_unpack hS hbd hcb hms hk hmc
  simp only [L1.GetCIRawResult, Core.Specs.Callees.memberProjInfo] at hrawRes
  obtain ⟨-, blkBytes, cb', ms', rc', v', hhB, haB, hdeB, -, hms', hrc', hld', hrawR⟩ := hrawRes
  have hcb_eq : cb' = cb := record_eq_of_hashed_l hS hsub_ld hcb hhB haB hdeB
  subst cb'
  have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
  subst ms'
  have hidx_eq : (k.toUInt64).toNat = k := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [hidx_eq, Array.getElem?_toList, hk] at hrc'
  injection hrc' with hr_mc; injection hr_mc with hr_eq; subst rc'
  rw [hld'] at hld; injection hld with hv_eq; subst hv_eq
  obtain ⟨hnl32, -, -, -, -, -, tyPtr, rulesPtr, blkPtr, ba_b, hba_b_eq, rba_b, hv',
    raw_ty, raw_rules⟩ := hrawR
  subst hv'
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) .. | .Axiom_other_other (hv37 := hv) .. =>
    simp [kciEnum] at hv
  | .Defn (hv269 := hv) .. => simp [kciEnum] at hv
  | .Thm (hv526 := hv) .. => simp [kciEnum] at hv
  | .Opaque (hv825 := hv) .. => simp [kciEnum] at hv
  | .Quot (hv1076 := hv) .. => simp [kciEnum] at hv
  | .Induct_n0 (hv1240 := hv) .. | .Induct_other_n0 (hv1240 := hv) ..
  | .Induct_other_other (hv1240 := hv) .. => simp [kciEnum] at hv
  | .Ctor_n0_n0 (hv1989 := hv) .. | .Ctor_n0_other (hv1989 := hv) ..
  | .Ctor_other_n0 (hv1989 := hv) .. | .Ctor_other_other (hv1989 := hv) .. => simp [kciEnum] at hv
  | .Rec_n0 (m2789 := m_val) (m2857 := m_nil) (m2974 := m_crm)
      (ev14 := e1) (hv2727 := hv) (ev2801 := evval) (hm2865 := hmnil)
      (ev2838 := e3) (ev2882 := e4) (ev2912 := e5) (ev2942 := e6)
      (ev2964 := e7) (ev2986 := e8) (ev3068 := evcrm) (hc3093 := hc) .. =>
    injection hv with _ _ hl
    injection hl with h1 hl; injection hl with h2 hl; injection hl with _ hl
    injection hl with _ hl; injection hl with _ hl; injection hl with _ hl
    injection hl with h6 _
    subst h1 h2 h6
    have hty_ok : ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) cb id
        (blockSelf t b ms)).read rc_m.typ = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range rc_m.lvls.toNat) = true :=
      validate_reader_levels hbd hnl32 raw_ty e1.heap_extends evval
        (hsub_chk _ (mem_of_eq hc (by call_mem)))
    have ext_nil : Heap.Extends m_val m_nil := by rw [hmnil]; exact Heap.Extends.snoc _ _
    have ext0_crm : Heap.Extends m_chk m_crm :=
      e1.heap_extends.trans (evval.heap_extends.trans (ext_nil.trans (e3.heap_extends.trans
        (e4.heap_extends.trans (e5.heap_extends.trans (e6.heap_extends.trans
          (e7.heap_extends.trans e8.heap_extends)))))))
    match Obs.«KernelCheck::check_recursor_member».obs evcrm with
    | .run (hv15 := hv2) (ev85 := f1) (ev142 := f2) (ev233 := f3) (ev278 := f4)
        (ev292 := f5) (ev314 := f6) (ev382 := f7) (ev412 := f8) (ev477 := evws)
        (hc898 := hc_crm) .. =>
      injection hv2 with _ _ hl2
      injection hl2 with h1' hl2; injection hl2 with _ hl2; injection hl2 with _ hl2
      injection hl2 with _ hl2; injection hl2 with _ hl2; injection hl2 with _ hl2
      injection hl2 with h6' _
      subst h1' h6'
      have ext_ws : Heap.Extends m_chk _ :=
        ext0_crm.trans (f1.heap_extends.trans (f2.heap_extends.trans (f3.heap_extends.trans
          (f4.heap_extends.trans (f5.heap_extends.trans (f6.heap_extends.trans
            (f7.heap_extends.trans f8.heap_extends)))))))
      have hws := check_rec_rules_wellscoped_levelsOk hbd hnl32 rc_m.rules.toList 0
        (fun cl hcl => by
          have h1 := mem_of_eq hc_crm (by call_mem)
          exact hsub_chk cl (mem_of_eq hc (by call_mem)))
        (raw_rules.mono ext_ws (fun _ hm => hm)) evws
      exact ⟨hnl32, hty_ok, fun j ru E_rd hj hread =>
        hws ru (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj)) E_rd hread⟩
  | .Rec_other (m2789 := m_val) (m2857 := m_nil) (m2974 := m_cf)
      (ev14 := e1) (hv2727 := hv) (ev2801 := evval) (hm2865 := hmnil)
      (ev2838 := e3) (ev2882 := e4) (ev2912 := e5) (ev2942 := e6)
      (ev2964 := e7) (ev2986 := e8) (ev3157 := evcf) (hc3182 := hc) .. =>
    injection hv with _ _ hl
    injection hl with _ hl; injection hl with _ hl; injection hl with _ hl
    injection hl with _ hl; injection hl with _ hl; injection hl with _ hl
    injection hl with _ hl; injection hl with _ hl; injection hl with _ hl
    injection hl with h9 _
    subst h9
    have ext_nil : Heap.Extends m_val m_nil := by rw [hmnil]; exact Heap.Extends.snoc _ _
    have ext0_cf : Heap.Extends m_chk m_cf :=
      e1.heap_extends.trans (evval.heap_extends.trans (ext_nil.trans (e3.heap_extends.trans
        (e4.heap_extends.trans (e5.heap_extends.trans (e6.heap_extends.trans
          (e7.heap_extends.trans e8.heap_extends)))))))
    have hcf := check_family_recr_levelsOk hS hbd (by rwa [hba_b_eq]) hms
      (Bytes.repAddressRef_heapMono₂ addrTy ext0_cf rba_b) evcf
      (fun cl hcl => hsub_chk cl (mem_of_eq hc (by call_mem))) k rc_m hk
    simpa [hba_b_eq] using hcf

/-- **Any safe record checked by `UnitCheckedAt`** satisfies `UnitLevelsAndParamsOk`. -/
theorem unitCheckedAt_unitLevelsAndParamsOk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    (hrec : recordOf E₀ a = some c) (hlogic : InLogic c)
    (hU : UnitCheckedAt calls bAddr t E₀ a lim) :
    UnitLevelsAndParamsOk t E₀ a c := by
  rcases hU with hchk | ⟨c', ms', hc', hms', hmem⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro d hci hdk
      exact checkedLimAt_defnVal_levelsOk hS hbd hrec hci hdk hchk
    · intro ms i d hms _ _
      exact (Claim.checked_not_block hS hrec hms hchk).elim
    · intro ms i ind hms _
      exact (Claim.checked_not_block hS hrec hms hchk).elim
    · intro ms k r hms _
      exact (Claim.checked_not_block hS hrec hms hchk).elim
  · have hc_eq : c' = c := Option.some.inj (hc'.symm.trans hrec)
    subst hc_eq
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d hci _; rw [hms'] at hci; cases hci
    · intro ms i d hms hi hdk
      have heq : ms = ms' := Ixon.ConstantInfo.muts.inj (hms.symm.trans hms')
      subst heq
      have hi_lt := (Array.getElem?_eq_some_iff.mp hi).1
      exact memberCheckedLimAt_defnVal_levelsOk hS hbd hrec hms hi hdk (hmem i hi_lt)
    · intro ms i ind hms hi
      have heq : ms = ms' := Ixon.ConstantInfo.muts.inj (hms.symm.trans hms')
      subst heq
      have hi_lt := (Array.getElem?_eq_some_iff.mp hi).1
      exact memberCheckedLimAt_ind_levelsOk hS hbd hrec hms hlogic hi (hmem i hi_lt)
    · intro ms k r hms hk
      have heq : ms = ms' := Ixon.ConstantInfo.muts.inj (hms.symm.trans hms')
      subst heq
      have hk_lt := (Array.getElem?_eq_some_iff.mp hk).1
      exact memberCheckedLimAt_recr_levelsOk hS hbd hrec hms hk (hmem k hk_lt)

/-! ## Part 3: `StoreLevelsOk` and `StoreIndParamsOk` over every `groupStore` (`6 ≤ g ≤ 77`) -/

private theorem unitLevelsAndParamsOk_of_nonUnit {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {a : _root_.Address} {c : Ixon.Constant}
    (hnd : ∀ d, c.info ≠ .defn d) (hnm : ∀ ms, c.info ≠ .muts ms) :
    UnitLevelsAndParamsOk t E₀ a c :=
  ⟨fun d h _ => (hnd d h).elim,
   fun ms _ _ h _ _ => (hnm ms h).elim,
   fun ms _ _ h _ => (hnm ms h).elim,
   fun ms _ _ h _ => (hnm ms h).elim⟩

private theorem groupStore_units_levelsAndParamsOk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    (hC : CollisionFreeRun calls E₀)
    (hbd : Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    ∀ g, 6 ≤ g → g ≤ 77 → ∀ a c,
      recordOf (groupStore t E₀ (runPayload calls bAddr t) g) a = some c →
      UnitLevelsAndParamsOk t E₀ a c := by
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hbase : ∀ a c, recordOf (groupStore t E₀ (runPayload calls bAddr t) 6) a = some c →
      UnitLevelsAndParamsOk t E₀ a c := by
    intro a c hc
    rw [groupStore_six] at hc
    exact unitLevelsAndParamsOk_of_basis hc
  intro g hg6 hg77
  obtain ⟨d, rfl⟩ : ∃ d, g = 6 + d := ⟨g - 6, by omega⟩
  induction d with
  | zero => exact hbase
  | succ d ih =>
    have hg6' : 6 ≤ 6 + d := by omega
    have hg77' : 6 + d < 77 := by omega
    have hih := ih (by omega) (by omega)
    intro a c hc
    have hstep_eq : 6 + (d + 1) = (6 + d) + 1 := by omega
    rw [hstep_eq] at hc
    cases hprev : recordOf (groupStore t E₀ (runPayload calls bAddr t) (6 + d)) a with
    | some c' =>
      have h1 := ((groupStore_recordOf hb hg6').mp hprev).2
      have h2 := ((groupStore_recordOf hb (Nat.le_succ_of_le hg6')).mp hc).2
      have hce : c' = c := Option.some.inj (h1.symm.trans h2)
      subst hce
      exact hih a c' hprev
    | none =>
      have hnew : New (groupStore t E₀ (runPayload calls bAddr t) (6 + d))
          (groupStore t E₀ (runPayload calls bAddr t) ((6 + d) + 1)) a :=
        ⟨by rw [hc]; rfl, hprev⟩
      have hE : recordOf E₀ a = some c :=
        ((groupStore_recordOf hb (Nat.le_succ_of_le hg6')).mp hc).2
      have hlogic : InLogic c :=
        logic_of_rootsSafe hC hb hP hval hroots (6 + d) hg6' hg77' a c hnew hc
      by_cases hdm : (∃ d, c.info = .defn d) ∨ (∃ ms, c.info = .muts ms)
      · have hnp : ¬ Typing.IsProj c := by
          rcases hdm with ⟨d, hd⟩ | ⟨ms, hms⟩
          · intro hp; unfold Typing.IsProj at hp; rw [hd] at hp; exact hp
          · exact fun hp => Typing.proj_not_block hp ⟨ms, hms⟩
        have hna : ∀ ax, c.info ≠ .axio ax := by
          intro ax hax'
          rcases hdm with ⟨d, hd⟩ | ⟨ms, hms⟩
          · rw [hd] at hax'; cases hax'
          · rw [hms] at hax'; cases hax'
        obtain ⟨recs, hw⟩ := hws (6 + d)
        have hfromWalk : GroupReach t E₀ (6 + d) a → UnitLevelsAndParamsOk t E₀ a c := by
          intro hgr
          obtain ⟨y, -, hya⟩ := hgr.listed hC.hashedStored hw
          have hU := unitCheckedAt_of_topRec hC.hashedStored y
          rw [hya] at hU
          exact unitCheckedAt_unitLevelsAndParamsOk hC.runStore hbd hE hlogic hU
        rcases new_reach_cases hC hb hax hP hg6' hw hnew hE hnp hna with hgr | hpr
        · exact hfromWalk hgr
        · cases payReach_payClass_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
            hg6' hg77' hpr with
          | stored hst => rw [hprev] at hst; cases hst
          | walked hgr => exact hfromWalk hgr
          | famRec _ _ hex =>
            have hvl : valLimit (6 + d) < 77 := Nat.lt_of_le_of_lt (valLimit_le (6 + d)) hg77'
            have hfc := FamilyCallExact.toCall hex
            obtain ⟨c', rs, hc', -, hrs, -, hall, -⟩ :=
              familyCall_isTwinShape hC.runStore hC.hashedStored hvl hfc
            have hce : c' = c := Option.some.inj (hc'.symm.trans hE)
            subst hce
            obtain ⟨h_cf, h'_cf, xrc_cf, xb_cf, xrb_cf, r_cf, -, -, ⟨rb_b, hrb_b, hrb_eq⟩,
              ev_cf, -, hsub_cf⟩ := hfc
            subst hrb_eq
            have hrecs := check_family_recr_levelsOk (t := t) hC.runStore hbd hE hrs hrb_b ev_cf hsub_cf
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro d' hd'; rw [hrs] at hd'; cases hd'
            · intro ms i d' hms hi _
              have heq : ms = rs := Ixon.ConstantInfo.muts.inj (hms.symm.trans hrs)
              subst heq
              obtain ⟨r', hr'⟩ := hall (.defn d') (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
              cases hr'
            · intro ms i ind hms hi
              have heq : ms = rs := Ixon.ConstantInfo.muts.inj (hms.symm.trans hrs)
              subst heq
              obtain ⟨r', hr'⟩ := hall (.indc ind) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
              cases hr'
            · intro ms k r' hms hk
              have heq : ms = rs := Ixon.ConstantInfo.muts.inj (hms.symm.trans hrs)
              subst heq
              exact hrecs k r' hk
          | directAdv _ _ hex hadv =>
            obtain ⟨outs, hU⟩ := hex.unpack hC hbd
            obtain ⟨ab, habMem, habEq⟩ := hadv
            obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
            have hfacts := hU.adviceFacts k hk
            rw [hgetk, habEq] at hfacts
            obtain ⟨-, ca, hca, -, hkind, -⟩ := hfacts
            have hce : ca = c := Option.some.inj (hca.symm.trans hE)
            subst hce
            have hUnit : UnitCheckedAt calls bAddr t E₀ a (some (valLimit (6 + d))) := by
              rcases hkind with ⟨_, _, hchk⟩ | ⟨_, _, hchk⟩ | ⟨ms, hms, -, hmem, -⟩ | ⟨hp, -⟩
              · exact Or.inl hchk
              · exact Or.inl hchk
              · exact Or.inr ⟨ca, ms, hE, hms, hmem⟩
              · exact (hnp hp).elim
            exact unitCheckedAt_unitLevelsAndParamsOk hC.runStore hbd hE hlogic hUnit
          | directCont _ _ hex hdc =>
            obtain ⟨-, -, -, -, ⟨ib, -, h₁, h₂, rc₁, xx₁, xib₁, r₁, cs₁, hrc₁, hxx₁, -, evCr,
                hsubCr, -⟩, -, -, -⟩ := hdc.unpack hC hbd
            have hchk := (Decl.containerRec_checked hC.runStore hrc₁ hxx₁ evCr hsubCr).1
            exact unitCheckedAt_unitLevelsAndParamsOk hC.runStore hbd hE hlogic (Or.inl hchk)
          | checkedProj hc' hp _ _ _ _ =>
            have hce : _ = c := Option.some.inj (hc'.symm.trans hE)
            rw [hce] at hp
            exact (hnp hp).elim
      · push_neg at hdm
        exact unitLevelsAndParamsOk_of_nonUnit hdm.1 hdm.2

/-- **Both `StoreLevelsOk` and `StoreIndParamsOk` hold over every `groupStore ... g`
(`6 ≤ g ≤ 77`) of a collision-free bounded binding run.** -/
theorem storeLevelsOk_and_indParamsOk_of_groupStore {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    (hC : CollisionFreeRun calls E₀)
    (hbd : Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs)
    {g : Nat} (hg6 : 6 ≤ g) (hg77 : g ≤ 77) :
    StoreLevelsOk t E₀ (Held (groupStore t E₀ (runPayload calls bAddr t) g)) ∧
    StoreIndParamsOk E₀ (Held (groupStore t E₀ (runPayload calls bAddr t) g)) := by
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  exact storeLevelsOk_and_indParamsOk_of_units
    (fun y cy hy => ((groupStore_recordOf hb hg6).mp hy).2)
    (groupStore_usedClosed_all hC hb hbr hax hP hws g hg6)
    (groupStore_units_levelsAndParamsOk hC hbd hb hbr hax hpin hcheck hroots hstep hval hvalAll hws
      g hg6 hg77)

/-- **`StoreLevelsOk` over every `groupStore ... g` (`6 ≤ g ≤ 77`).** -/
theorem storeLevelsOk_of_groupStore {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    (hC : CollisionFreeRun calls E₀)
    (hbd : Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs)
    {g : Nat} (hg6 : 6 ≤ g) (hg77 : g ≤ 77) :
    StoreLevelsOk t E₀ (Held (groupStore t E₀ (runPayload calls bAddr t) g)) :=
  (storeLevelsOk_and_indParamsOk_of_groupStore hC hbd hb hbr hax hpin hcheck hroots hstep
    hval hvalAll hws hg6 hg77).1

/-- **`StoreIndParamsOk` over every `groupStore ... g` (`6 ≤ g ≤ 77`).** -/
theorem storeIndParamsOk_of_groupStore {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    (hC : CollisionFreeRun calls E₀)
    (hbd : Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs)
    {g : Nat} (hg6 : 6 ≤ g) (hg77 : g ≤ 77) :
    StoreIndParamsOk E₀ (Held (groupStore t E₀ (runPayload calls bAddr t) g)) :=
  (storeLevelsOk_and_indParamsOk_of_groupStore hC hbd hb hbr hax hpin hcheck hroots hstep
    hval hvalAll hws hg6 hg77).2

end IxVM.Refinement.Binding.FamilyRecon

