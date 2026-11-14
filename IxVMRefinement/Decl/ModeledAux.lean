import IxVMRefinement.Decl.ModeledRules
import IxVMRefinement.Decl.ModeledSound
import IxC.Kernel.Model.Inductives.DeclRecTwin

/-!
# Auxiliary Model Construction and Positional Lifting for Modeled Inductive Blocks

This module bridges the raw VM rule certificates (`RawIotaRuleVmRun`, `RawIotaRulesVmRun` from
`ModeledRules.lean`) and the semantic soundness engine (`declIndJ_vmF` from `ModeledSound.lean`):

1. **Base keys, `AuxRootSynced`, `DeclInvM`, and `NoNewProjForOld`**:
   Tracks that every derived key `.aux k d` stored in the environment has its root `k.base` stored,
   guaranteeing freshness of generated `.model`, `.iota j`, and `.projTable` keys for fresh block
   declarations, and preserving old projection-table lookups across auxiliary and modeled steps.
2. **Weakening and permutation composition on `posRulesJ`**:
   Lifts `posRulesJ` judgements (and `DefEqListJ`, `TypedListJ`, `LamTeleWalkJ`, `IotaRunsVmJ`)
   both along `EnvExt` extensions and across `posOf lps` renamings (`lps.Perm (List.range n)`).
3. **Phase 1 — Auxiliary `.iota` theorem and `.model` alias installation (`env_adv → env_aux`)**:
   Copies the advice theorems checked by `check_iota_rule` to `auxKey (auxKey r .model) (.iota j)`
   and installs `.model` aliases `auxKey n .model` in topological order (`nonrecs ++ recs`),
   establishing `ModelAliasOk` on `env_aux`.
4. **Phase 2 — Positional modeled block run (`env_aux → env₃_pos`)**:
   Translates `RawIotaRulesVmRun` to `IotaRulesNVmRunJ posRulesJ` at `List.range nl` and applies
   `declIndJ_vmF` to construct `EnvModelM V .verified env₃_pos`.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Library Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Model
open Ix.Kernel.Term Ix.Kernel.Verify Ix.Kernel.SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal BinderMeta RecRule IndCaps
  LevelParam EnvExt ReducibilityHint Derived openPisAtFvars eqName eqA auxKey nestedRuleShape
  recRuleBits isEqHead hasFvar_renameConsts)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

/-! ## Base keys, `AuxRootSynced`, `DeclInvM`, and `NoNewProjForOld` -/

/-- Whether a key is an underived (`.id` or `.role`) key rather than `.aux`. -/
def isBaseKey : KKey → Bool
  | .aux _ _ => false
  | _ => true

theorem isBaseKey_keyOf (t : Ix.Kernel.RoleTable) (a : _root_.Address) :
    isBaseKey (keyOf t a) = true := by
  unfold keyOf
  cases t.bound.find? (·.2 == a) with
  | none => rfl
  | some p => cases p; rfl

theorem base_of_isBaseKey {k : KKey} (h : isBaseKey k = true) : k.base = k := by
  cases k with
  | id _ => rfl
  | role _ => rfl
  | aux _ _ => exact nomatch h

theorem isModelSuffix_of_isBaseKey {k : KKey} (h : isBaseKey k = true) :
    k.isModelSuffix = false := by
  cases k with
  | id _ => rfl
  | role _ => rfl
  | aux _ _ => exact nomatch h

theorem isProjFnShape_of_isBaseKey {k : KKey} (h : isBaseKey k = true) :
    k.isProjFnShape = false := by
  cases k with
  | id _ => rfl
  | role _ => rfl
  | aux _ _ => exact nomatch h

theorem ne_projTableName_of_isBaseKey {k T : KKey} (h : isBaseKey k = true) :
    k ≠ Ix.Kernel.projTableName T := by
  intro heq
  rw [heq] at h
  exact nomatch h

theorem ne_projTableName_auxKey_model (k T : KKey) :
    auxKey k .model ≠ Ix.Kernel.projTableName T :=
  Ix.Kernel.auxKey_ne_auxKey nofun

theorem ne_projTableName_auxKey_iota (k T : KKey) (j : Nat) :
    auxKey k (.iota j) ≠ Ix.Kernel.projTableName T :=
  Ix.Kernel.auxKey_ne_auxKey nofun

/-- Every stored key in `env` has its root `k.base` stored in `env`. -/
def AuxRootSynced (env : Env .anon) : Prop :=
  ∀ k : KKey, (env.find? k).isSome = true → (env.find? k.base).isSome = true

theorem AuxRootSynced.empty : AuxRootSynced Env.empty := by
  intro k hk
  simp [Env.find?, Env.empty] at hk

theorem AuxRootSynced.fresh_of_base_none {env : Env .anon} (h : AuxRootSynced env)
    {k : KKey} (hbase : env.find? k.base = none) :
    env.find? k = none := by
  cases hfk : env.find? k with
  | none => rfl
  | some ci =>
    have hs : (env.find? k.base).isSome = true := h k (by rw [hfk]; rfl)
    rw [hbase] at hs
    exact nomatch hs

theorem AuxRootSynced.fresh_auxKey {env : Env .anon} (h : AuxRootSynced env)
    {k : KKey} (hk : isBaseKey k = true) (hf : env.find? k = none) (d : Derived) :
    env.find? (auxKey k d) = none :=
  h.fresh_of_base_none (by show env.find? k.base = none; rw [base_of_isBaseKey hk]; exact hf)

theorem AuxRootSynced.fresh_auxKey2 {env : Env .anon} (h : AuxRootSynced env)
    {k : KKey} (hk : isBaseKey k = true) (hf : env.find? k = none) (d₁ d₂ : Derived) :
    env.find? (auxKey (auxKey k d₁) d₂) = none :=
  h.fresh_of_base_none (by show env.find? k.base = none; rw [base_of_isBaseKey hk]; exact hf)

theorem AuxRootSynced.fresh_projTable {env : Env .anon} (h : AuxRootSynced env)
    {T : KKey} (hT : isBaseKey T = true) (hf : env.find? T = none) :
    env.find? (Ix.Kernel.projTableName T) = none :=
  h.fresh_auxKey hT hf .projTable

theorem env_find?_isSome_of_mem {consts : List (ConstantInfo .anon)} {ci : ConstantInfo .anon}
    (hmem : ci ∈ consts) :
    (Env.find? ⟨consts⟩ ci.name).isSome = true := by
  cases hf : Env.find? ⟨consts⟩ ci.name with
  | some _ => rfl
  | none =>
    have hnone := List.find?_eq_none.mp hf ci hmem
    simp at hnone

theorem env_find?_isSome_of_mem_prefix {new tail : List (ConstantInfo .anon)}
    {ci : ConstantInfo .anon} (hmem : ci ∈ new) :
    (Env.find? ⟨new ++ tail⟩ ci.name).isSome = true :=
  env_find?_isSome_of_mem (List.mem_append_left tail hmem)

theorem env_find?_isSome_of_tail {new tail : List (ConstantInfo .anon)} {k : KKey}
    (h : (Env.find? ⟨tail⟩ k).isSome = true) :
    (Env.find? ⟨new ++ tail⟩ k).isSome = true := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
  rw [← Ix.Kernel.Semantics.Env.find?_name hci]
  exact env_find?_isSome_of_mem (List.mem_append_right new (Ix.Kernel.Semantics.Env.find?_mem hci))

theorem AuxRootSynced.of_prepend {env : Env .anon} (h : AuxRootSynced env)
    {new : List (ConstantInfo .anon)}
    (hroots : ∀ ci ∈ new, (Env.find? ⟨new ++ env.consts⟩ ci.name.base).isSome = true) :
    AuxRootSynced ⟨new ++ env.consts⟩ := by
  intro k hk
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
  have hname : ci.name = k := Ix.Kernel.Semantics.Env.find?_name hci
  have hmem : ci ∈ new ++ env.consts := Ix.Kernel.Semantics.Env.find?_mem hci
  rcases List.mem_append.mp hmem with hnew | hold
  · rw [← hname]
    exact hroots ci hnew
  · have hk_old : (env.find? k).isSome = true := by
      rw [← hname]
      exact env_find?_isSome_of_mem hold
    exact env_find?_isSome_of_tail (h k hk_old)

theorem AuxRootSynced.cons_of_root_stored {env : Env .anon} (h : AuxRootSynced env)
    {c₀ : ConstantInfo .anon}
    (hroot : c₀.name.base = c₀.name ∨ (env.find? c₀.name.base).isSome = true) :
    AuxRootSynced ⟨c₀ :: env.consts⟩ := by
  refine h.of_prepend (new := [c₀]) ?_
  intro ci hci
  rw [List.mem_singleton.mp hci]
  rcases hroot with heq | hold
  · rw [heq]
    exact env_find?_isSome_of_mem_prefix (new := [c₀]) List.mem_cons_self
  · exact env_find?_isSome_of_tail (new := [c₀]) hold

/-- Extended `L5` fold invariant pairing `DeclInv` with `AuxRootSynced`. -/
structure DeclInvM (V : Type u) [Ix.Kernel.SetTheory V] (env : Env .anon) : Prop where
  inv : DeclInv V env
  auxSynced : AuxRootSynced env

theorem DeclInvM.empty (V : Type u) [Ix.Kernel.SetTheory V] :
    DeclInvM V Env.empty :=
  ⟨DeclInv.empty V, AuxRootSynced.empty⟩

theorem DeclInvM.toEnvModelOk {V : Type u} [Ix.Kernel.SetTheory V] {env : Env .anon}
    (h : DeclInvM V env) : EnvModelOk V .verified env :=
  h.inv.toEnvModelOk

/-- No projection table was added for any key already stored in `env₁`. -/
def NoNewProjForOld (env₁ env₂ : Env .anon) : Prop :=
  ∀ T : KKey, (env₁.find? T).isSome = true →
    env₂.find? (Ix.Kernel.projTableName T) = env₁.find? (Ix.Kernel.projTableName T)

theorem NoNewProjForOld.refl (env : Env .anon) : NoNewProjForOld env env :=
  fun _ _ => rfl

theorem NoNewProjForOld.trans {e₁ e₂ e₃ : Env .anon}
    (h₁₂ : NoNewProjForOld e₁ e₂) (h₂₃ : NoNewProjForOld e₂ e₃)
    (hfind : ∀ k, (e₁.find? k).isSome = true → (e₂.find? k).isSome = true) :
    NoNewProjForOld e₁ e₃ :=
  fun T hT => (h₂₃ T (hfind T hT)).trans (h₁₂ T hT)

theorem NoNewProjForOld.findProj?_eq {env₁ env₂ : Env .anon}
    (h : NoNewProjForOld env₁ env₂) {T : KKey} (hT : (env₁.find? T).isSome = true) (i : Nat) :
    env₂.findProj? T i = env₁.findProj? T i := by
  unfold Env.findProj?
  rw [h T hT]

theorem find?_prepend_nonProjTable {new tail : List (ConstantInfo .anon)}
    (hnpt : ∀ ci ∈ new, ∀ T, ci.name ≠ Ix.Kernel.projTableName T) (T : KKey) :
    Env.find? ⟨new ++ tail⟩ (Ix.Kernel.projTableName T) =
      Env.find? ⟨tail⟩ (Ix.Kernel.projTableName T) := by
  induction new with
  | nil => rfl
  | cons c rest ih =>
    change (⟨c :: (rest ++ tail)⟩ : Env .anon).find? (Ix.Kernel.projTableName T) = _
    rw [EnvExt.find?_cons_ne (hnpt c List.mem_cons_self T)]
    exact ih (fun ci hci => hnpt ci (List.mem_cons_of_mem c hci))

theorem NoNewProjForOld.prepend_nonProjTable {env : Env .anon} {new : List (ConstantInfo .anon)}
    (hnpt : ∀ ci ∈ new, ∀ T, ci.name ≠ Ix.Kernel.projTableName T) :
    NoNewProjForOld env ⟨new ++ env.consts⟩ :=
  fun T _ => find?_prepend_nonProjTable hnpt T

theorem envExt_cons_fresh {env : Env .anon} {c₀ : ConstantInfo .anon}
    (hfresh : env.find? c₀.name = none)
    (hnpt : ∀ T, c₀.name ≠ Ix.Kernel.projTableName T) :
    EnvExt env ⟨c₀ :: env.consts⟩ where
  find hf := Env.find?_cons_of_fresh hfresh hf
  tables {T _ _} _ := EnvExt.find?_cons_ne (hnpt T)

theorem envExt_shared_prefix {ms : List (ConstantInfo .anon)} {env₁ env₂ : Env .anon}
    (hext : EnvExt env₁ env₂)
    (hnpt : ∀ ci ∈ ms, ∀ T, ci.name ≠ Ix.Kernel.projTableName T)
    (hms_pt : ∀ ci ∈ ms,
      env₁.find? (Ix.Kernel.projTableName ci.name) = none ∧
      env₂.find? (Ix.Kernel.projTableName ci.name) = none) :
    EnvExt ⟨ms ++ env₁.consts⟩ ⟨ms ++ env₂.consts⟩ where
  find {k c} hf := by
    unfold Env.find? at hf ⊢
    rw [List.find?_append] at hf ⊢
    cases hm : ms.find? (·.name == k) with
    | some cm =>
      dsimp only [Option.or] at hf ⊢
      exact hf
    | none =>
      dsimp only [Option.or] at hf ⊢
      exact hext.find hf
  tables {T cv caps} hf := by
    rw [find?_prepend_nonProjTable hnpt T, find?_prepend_nonProjTable hnpt T]
    unfold Env.find? at hf
    rw [List.find?_append] at hf
    cases hm : ms.find? (·.name == T) with
    | some cm =>
      have hmem : cm ∈ ms := List.mem_of_find?_eq_some hm
      have hbeq : (cm.name == T) = true := List.find?_some hm
      have hname : cm.name = T := eq_of_beq hbeq
      rw [← hname]
      obtain ⟨h1, h2⟩ := hms_pt cm hmem
      rw [h1, h2]
    | none =>
      dsimp only [Option.or] at hf
      exact hext.tables hf

/-! ## Weakening of `posRulesJ` and Modeled Judgement Bundles -/

theorem posRulesJ_infer_weaken {env₁ env₂ : Env .anon} (hext : EnvExt env₁ env₂)
    {d : Nat} {e t : KExpr} (h : posRulesJ.infer env₁ d e t) :
    posRulesJ.infer env₂ d e t := by
  obtain ⟨ps, hp, hi⟩ := h
  exact ⟨ps, hp, Infer.weaken hext hi⟩

theorem posRulesJ_defeq_weaken {env₁ env₂ : Env .anon} (hext : EnvExt env₁ env₂)
    {d : Nat} {a b : KExpr} (h : posRulesJ.defeq env₁ d a b) :
    posRulesJ.defeq env₂ d a b := by
  obtain ⟨ps, hp, hd⟩ := h
  exact ⟨ps, hp, DefEq.weaken hext hd⟩

theorem posRulesJ_sort_weaken {env₁ env₂ : Env .anon} (hext : EnvExt env₁ env₂)
    {d : Nat} {t : KExpr} {u : KLevel} (h : posRulesJ.sort env₁ d t u) :
    posRulesJ.sort env₂ d t u := by
  obtain ⟨ps, hp, hr⟩ := h
  exact ⟨ps, hp, Red.weaken hext hr⟩

theorem defEqListJ_weaken {env₁ env₂ : Env .anon} (hext : EnvExt env₁ env₂) {d : Nat}
    {as bs : List KExpr} (h : DefEqListJ posRulesJ env₁ d as bs) :
    DefEqListJ posRulesJ env₂ d as bs := by
  induction as generalizing bs with
  | nil => cases bs with | nil => trivial | cons _ _ => exact nomatch h
  | cons _ _ ih =>
    cases bs with
    | nil => exact nomatch h
    | cons _ _ => exact ⟨posRulesJ_defeq_weaken hext h.1, ih h.2⟩

theorem typedListJ_weaken {env₁ env₂ : Env .anon} (hext : EnvExt env₁ env₂) {d : Nat}
    {as bs : List KExpr} (h : TypedListJ posRulesJ env₁ d as bs) :
    TypedListJ posRulesJ env₂ d as bs := by
  induction as generalizing bs with
  | nil => cases bs with | nil => trivial | cons _ _ => exact nomatch h
  | cons _ _ ih =>
    cases bs with
    | nil => exact nomatch h
    | cons _ _ =>
      obtain ⟨⟨ty, hi, hd⟩, hs⟩ := h
      exact ⟨⟨ty, posRulesJ_infer_weaken hext hi, posRulesJ_defeq_weaken hext hd⟩, ih hs⟩

theorem lamTeleWalkJ_weaken {env₁ env₂ : Env .anon} (hext : EnvExt env₁ env₂)
    {rP cnF : Nat} {tyA cty : KExpr} {mkPins : List KExpr → List KExpr} {rhs : KExpr}
    (h : LamTeleWalkJ posRulesJ env₁ rP cnF tyA cty mkPins rhs) :
    LamTeleWalkJ posRulesJ env₂ rP cnF tyA cty mkPins rhs := by
  obtain ⟨lfvs, lrest, pdoms1, tyRest, cdomsL, crestL, pdoms2, crestEnd,
    hopen, hir, hic, hopc, hwalk⟩ := h
  exact ⟨lfvs, lrest, pdoms1, tyRest, cdomsL, crestL, pdoms2, crestEnd,
    hopen, hir, hic, hopc, defEqListJ_weaken hext hwalk⟩

theorem iotaRunsVmJ_weaken {env₁ env₂ : Env .anon} (hext : EnvExt env₁ env₂)
    {depth : Nat} {lindices cindices xdoms cfieldDoms fpreDoms rdoms : List KExpr}
    {rhsS applied tyArg lhsS : KExpr}
    (h : IotaRunsVmJ posRulesJ env₁ depth lindices cindices xdoms cfieldDoms fpreDoms rdoms
      rhsS applied tyArg lhsS) :
    IotaRunsVmJ posRulesJ env₂ depth lindices cindices xdoms cfieldDoms fpreDoms rdoms
      rhsS applied tyArg lhsS := by
  obtain ⟨hidx, hfields, hpre, hrhs, ⟨tl, hil, hdl⟩, ⟨tr, hir, hdr⟩⟩ := h
  exact ⟨defEqListJ_weaken hext hidx,
    defEqListJ_weaken hext hfields,
    defEqListJ_weaken hext hpre,
    posRulesJ_defeq_weaken hext hrhs,
    ⟨tl, posRulesJ_infer_weaken hext hil, posRulesJ_defeq_weaken hext hdl⟩,
    ⟨tr, posRulesJ_infer_weaken hext hir, posRulesJ_defeq_weaken hext hdr⟩⟩

/-! ## Permutation Composition on `posOf` and `posRulesJ` -/

private def padPerm (N : Nat) (ps : List LevelParam) : List LevelParam :=
  ps ++ (List.range N).drop ps.length

private theorem padPerm_perm {N : Nat} {ps : List LevelParam}
    (hps : ps.Perm (List.range ps.length)) (hle : ps.length ≤ N) :
    (padPerm N ps).Perm (List.range N) := by
  unfold padPerm
  have hsplit : List.range N = List.range ps.length ++ (List.range N).drop ps.length := by
    have htake : (List.range N).take ps.length = List.range ps.length := by
      apply List.ext_getElem (by simp [Nat.min_eq_left hle])
      intro i hi₁ hi₂
      simp
    have h1 := List.take_append_drop ps.length (List.range N)
    rw [htake] at h1
    exact h1.symm
  have hp := hps.append_right ((List.range N).drop ps.length)
  rwa [← hsplit] at hp

private theorem padPerm_length {N : Nat} {ps : List LevelParam} (hle : ps.length ≤ N) :
    (padPerm N ps).length = N := by
  unfold padPerm
  simp [hle]

private theorem subst_go_self_list :
    ∀ (ks : List LevelParam) (p : LevelParam),
      Level.subst.go ks (ks.map .param) p = .param p
  | [], _ => rfl
  | k :: ks, p => by
    show (if k = p then Level.param k else Level.subst.go ks (ks.map .param) p) = .param p
    by_cases h : k = p
    · rw [ite_eq_left h, h]
    · rw [ite_eq_right h, subst_go_self_list ks p]

private theorem subst_go_append_eq :
    ∀ (ks₁ ks₂ : List LevelParam) (vs₁ vs₂ : List KLevel) (p : LevelParam),
      vs₁.length = ks₁.length →
      Level.subst.go (ks₁ ++ ks₂) (vs₁ ++ vs₂) p =
        if p ∈ ks₁ then Level.subst.go ks₁ vs₁ p else Level.subst.go ks₂ vs₂ p
  | [], ks₂, [], vs₂, p, _ => by simp
  | _ :: _, _, [], _, _, hlen => nomatch hlen
  | [], _, _ :: _, _, _, hlen => nomatch hlen
  | k :: ks₁, ks₂, v :: vs₁, vs₂, p, hlen => by
    show (if k = p then v else Level.subst.go (ks₁ ++ ks₂) (vs₁ ++ vs₂) p) =
      if p ∈ k :: ks₁ then (if k = p then v else Level.subst.go ks₁ vs₁ p)
      else Level.subst.go ks₂ vs₂ p
    by_cases hkp : k = p
    · subst hkp
      simp
    · have hne_pk : p ≠ k := fun h => hkp h.symm
      rw [ite_eq_right hkp, subst_go_append_eq ks₁ ks₂ vs₁ vs₂ p (Nat.succ.inj hlen)]
      by_cases hmem : p ∈ ks₁
      · have hmem' : p ∈ k :: ks₁ := List.mem_cons_of_mem k hmem
        rw [ite_eq_left hmem, ite_eq_left hmem', ite_eq_right hkp]
      · have hmem' : ¬ (p ∈ k :: ks₁) := by
          intro hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hkp rfl
          · exact hmem hc
        rw [ite_eq_right hmem, ite_eq_right hmem']

private theorem subst_go_not_mem :
    ∀ (ks : List LevelParam) (vs : List KLevel) (p : LevelParam),
      p ∉ ks → Level.subst.go ks vs p = .param p
  | [], _, _, _ => rfl
  | k :: ks, [], p, _ => rfl
  | k :: ks, v :: vs, p, hnm => by
    have hne : k ≠ p := fun h => hnm (h ▸ List.mem_cons_self)
    show (if k = p then v else Level.subst.go ks vs p) = .param p
    rw [ite_eq_right hne]
    exact subst_go_not_mem ks vs p (fun h => hnm (List.mem_cons_of_mem k h))

private theorem posLevels_padPerm {N : Nat} {ps : List LevelParam} (hle : ps.length ≤ N) :
    posLevels (padPerm N ps) = posLevels ps ++ ((List.range N).drop ps.length).map .param := by
  unfold posLevels
  rw [padPerm_length hle]
  have hsplit : List.range N = List.range ps.length ++ (List.range N).drop ps.length := by
    have htake : (List.range N).take ps.length = List.range ps.length := by
      apply List.ext_getElem (by simp [Nat.min_eq_left hle])
      intro i hi₁ hi₂
      simp
    have h1 := List.take_append_drop ps.length (List.range N)
    rw [htake] at h1
    exact h1.symm
  show (List.range N).map Level.param =
    (List.range ps.length).map Level.param ++ ((List.range N).drop ps.length).map Level.param
  rw [← List.map_append, ← hsplit]

private theorem subst_padPerm_eq {N : Nat} {ps : List LevelParam} (hle : ps.length ≤ N) :
    ∀ u : KLevel,
      Level.subst (padPerm N ps) (posLevels (padPerm N ps)) u =
        Level.subst ps (posLevels ps) u
  | .zero => rfl
  | .succ u => congrArg Level.succ (subst_padPerm_eq hle u)
  | .max a b => by simp only [Level.subst, subst_padPerm_eq hle a, subst_padPerm_eq hle b]
  | .imax a b => by simp only [Level.subst, subst_padPerm_eq hle a, subst_padPerm_eq hle b]
  | .param p => by
    show Level.subst.go (padPerm N ps) (posLevels (padPerm N ps)) p =
      Level.subst.go ps (posLevels ps) p
    rw [posLevels_padPerm hle]
    unfold padPerm
    rw [subst_go_append_eq ps ((List.range N).drop ps.length) (posLevels ps)
      (((List.range N).drop ps.length).map .param) p (by simp [posLevels])]
    by_cases hp : p ∈ ps
    · rw [ite_eq_left hp]
    · rw [ite_eq_right hp, subst_go_self_list, subst_go_not_mem ps (posLevels ps) p hp]

private theorem substPW_padPerm_eq {N : Nat} {ps : List LevelParam} (hle : ps.length ≤ N)
    (pw : Ix.Kernel.PropWhen) :
    Level.substPW (padPerm N ps) (posLevels (padPerm N ps)) pw =
      Level.substPW ps (posLevels ps) pw := by
  apply Ix.Kernel.PropWhen.eq_of_holds
  intro φ
  rw [Level.holds_substPW, Level.holds_substPW]
  congr 1
  funext p
  rw [← Level.eval_subst_go, ← Level.eval_subst_go]
  exact congrArg (Level.eval φ) (subst_padPerm_eq hle (.param p))

private theorem posOf_padPerm_eq {N : Nat} {ps : List LevelParam} (hle : ps.length ≤ N) :
    ∀ e : KExpr, posOf (padPerm N ps) e = posOf ps e
  | .bvar _ | .lit _ => rfl
  | .fvar i ty => congrArg (Expr.fvar i) (posOf_padPerm_eq hle ty)
  | .sort u => congrArg Expr.sort (subst_padPerm_eq hle u)
  | .const n us => by
    simp only [posOf, Expr.instantiateLevelParams]
    congr 1
    exact List.map_congr_left fun u _ => subst_padPerm_eq hle u
  | .app f a => by
    simp only [posOf, Expr.instantiateLevelParams]
    rw [← posOf, ← posOf, posOf_padPerm_eq hle f, posOf_padPerm_eq hle a]
    rfl
  | .lam ty bo m => by
    simp only [posOf, Expr.instantiateLevelParams, substPW_padPerm_eq hle m.pw]
    rw [← posOf, ← posOf, posOf_padPerm_eq hle ty, posOf_padPerm_eq hle bo]
    rfl
  | .forallE ty bo m => by
    simp only [posOf, Expr.instantiateLevelParams, substPW_padPerm_eq hle m.pw]
    rw [← posOf, ← posOf, posOf_padPerm_eq hle ty, posOf_padPerm_eq hle bo]
    rfl
  | .letE ty v bo m => by
    simp only [posOf, Expr.instantiateLevelParams]
    rw [← posOf, ← posOf, ← posOf,
      posOf_padPerm_eq hle ty, posOf_padPerm_eq hle v, posOf_padPerm_eq hle bo]
    rfl
  | .proj s i e => by
    simp only [posOf, Expr.instantiateLevelParams]
    rw [← posOf, posOf_padPerm_eq hle e]
    rfl

private theorem subst_go_nodup_idxOf :
    ∀ (ks : List LevelParam) (vs : List KLevel) (hnd : ks.Nodup) (hlen : vs.length = ks.length)
      (p : LevelParam) (hp : p ∈ ks) (hlt : ks.idxOf p < vs.length),
      Level.subst.go ks vs p = vs[ks.idxOf p]
  | [], _, _, _, _, hp, _ => nomatch hp
  | k :: ks, [], _, hlen, _, _, _ => nomatch hlen
  | k :: ks, v :: vs, hnd, hlen, p, hp, hlt => by
    obtain ⟨hk_nin, hnd'⟩ := List.nodup_cons.mp hnd
    show (if k = p then v else Level.subst.go ks vs p) = (v :: vs)[(k :: ks).idxOf p]
    by_cases hkp : k = p
    · subst hkp
      have hidx : (k :: ks).idxOf k = 0 := List.idxOf_cons_self
      simp [hidx]
    · rw [ite_eq_right hkp]
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact absurd rfl hkp
      · have hbeq : (k == p) = false := beq_false_of_ne hkp
        have hidx : (k :: ks).idxOf p = ks.idxOf p + 1 := List.idxOf_cons_ne ks hkp
        have hlt' : ks.idxOf p < vs.length := by
          simp only [List.length_cons, hidx] at hlt
          omega
        rw [subst_go_nodup_idxOf ks vs hnd' (Nat.succ.inj hlen) p hp' hlt']
        simp [hidx]

private theorem idxOf_getElem_nodup :
    ∀ (ks : List LevelParam) (hnd : ks.Nodup) (i : Nat) (hi : i < ks.length),
      ks.idxOf ks[i] = i
  | [], _, _, hi => nomatch hi
  | k :: ks, _, 0, _ => List.idxOf_cons_self
  | k :: ks, hnd, i + 1, hi => by
    obtain ⟨hk_nin, hnd'⟩ := List.nodup_cons.mp hnd
    have hi' : i < ks.length := Nat.lt_of_succ_lt_succ hi
    have hne : k ≠ ks[i] := fun heq => hk_nin (heq ▸ List.getElem_mem hi')
    simp only [List.getElem_cons_succ]
    rw [List.idxOf_cons_ne ks hne, idxOf_getElem_nodup ks hnd' i hi']

private theorem map_idxOf_self {ks : List LevelParam} (hnd : ks.Nodup) :
    ks.map ks.idxOf = List.range ks.length := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp only [List.length_map] at hi₁
  simp only [List.getElem_map, List.getElem_range]
  exact idxOf_getElem_nodup ks hnd i hi₁

private theorem compPerm_perm {N : Nat} {ps₁ lps₁ : List LevelParam}
    (hps₁ : ps₁.Perm (List.range N)) (hlps₁ : lps₁.Perm (List.range N)) :
    (ps₁.map lps₁.idxOf).Perm (List.range (ps₁.map lps₁.idxOf).length) := by
  have hlps_len : lps₁.length = N := by simpa using hlps₁.length_eq
  have hps_len : ps₁.length = N := by simpa using hps₁.length_eq
  have hlps_nd : lps₁.Nodup := hlps₁.nodup_iff.mpr List.nodup_range
  have hp1 : (ps₁.map lps₁.idxOf).Perm ((List.range N).map lps₁.idxOf) := hps₁.map lps₁.idxOf
  have hp2 : (lps₁.map lps₁.idxOf).Perm ((List.range N).map lps₁.idxOf) := hlps₁.map lps₁.idxOf
  have hp3 : (ps₁.map lps₁.idxOf).Perm (lps₁.map lps₁.idxOf) := hp1.trans hp2.symm
  rw [map_idxOf_self hlps_nd, hlps_len] at hp3
  simpa [hps_len] using hp3

private theorem subst_compPerm_eq {N : Nat} {ps₁ lps₁ : List LevelParam}
    (hps₁ : ps₁.Perm (List.range N)) (hlps₁ : lps₁.Perm (List.range N)) :
    let qs := ps₁.map lps₁.idxOf
    ∀ u : KLevel,
      Level.subst qs (posLevels qs) (Level.subst lps₁ (posLevels lps₁) u) =
        Level.subst ps₁ (posLevels ps₁) u := by
  intro qs u
  have hlps_len : lps₁.length = N := by simpa using hlps₁.length_eq
  have hps_len : ps₁.length = N := by simpa using hps₁.length_eq
  have hqs_len : qs.length = N := by simp [qs, hps_len]
  have hqs_perm : qs.Perm (List.range N) := by
    have hp := compPerm_perm hps₁ hlps₁
    rwa [show (ps₁.map lps₁.idxOf).length = N from hqs_len] at hp
  have hlps_nd : lps₁.Nodup := hlps₁.nodup_iff.mpr List.nodup_range
  have hps_nd : ps₁.Nodup := hps₁.nodup_iff.mpr List.nodup_range
  have hqs_nd : qs.Nodup := hqs_perm.nodup_iff.mpr List.nodup_range
  induction u with
  | zero => rfl
  | succ u ih => exact congrArg Level.succ ih
  | max a b iha ihb => simp only [Level.subst, iha, ihb]
  | imax a b iha ihb => simp only [Level.subst, iha, ihb]
  | param p =>
    by_cases hp : p < N
    · have hp_range : p ∈ List.range N := List.mem_range.mpr hp
      have hp_lps : p ∈ lps₁ := hlps₁.mem_iff.mpr hp_range
      have hp_ps : p ∈ ps₁ := hps₁.mem_iff.mpr hp_range
      have hi_lt : lps₁.idxOf p < lps₁.length := List.idxOf_lt_length_of_mem hp_lps
      have hk_lt : ps₁.idxOf p < ps₁.length := List.idxOf_lt_length_of_mem hp_ps
      have h1 : Level.subst lps₁ (posLevels lps₁) (.param p) = .param (lps₁.idxOf p) := by
        show Level.subst.go lps₁ (posLevels lps₁) p = .param (lps₁.idxOf p)
        rw [subst_go_nodup_idxOf lps₁ (posLevels lps₁) hlps_nd (by simp [posLevels]) p hp_lps
          (by simp [posLevels, hi_lt])]
        simp [posLevels]
      rw [h1]
      have hqk : qs[ps₁.idxOf p]'(by simp [qs, hk_lt]) = lps₁.idxOf p := by
        simp [qs]
      have hi_qs : lps₁.idxOf p ∈ qs := by
        rw [← hqk]
        exact List.getElem_mem _
      have hqs_idx : qs.idxOf (lps₁.idxOf p) = ps₁.idxOf p := by
        have h := idxOf_getElem_nodup qs hqs_nd (ps₁.idxOf p) (by simp [qs, hk_lt])
        rwa [hqk] at h
      show Level.subst.go qs (posLevels qs) (lps₁.idxOf p) =
        Level.subst.go ps₁ (posLevels ps₁) p
      rw [subst_go_nodup_idxOf qs (posLevels qs) hqs_nd (by simp [posLevels])
          (lps₁.idxOf p) hi_qs (by simp [posLevels, hqs_idx, qs, hk_lt]),
        subst_go_nodup_idxOf ps₁ (posLevels ps₁) hps_nd (by simp [posLevels])
          p hp_ps (by simp [posLevels, hk_lt])]
      simp [posLevels, hqs_idx]
    · have hp_nr : p ∉ List.range N := fun h => hp (List.mem_range.mp h)
      have hp_nlps : p ∉ lps₁ := fun h => hp_nr (hlps₁.mem_iff.mp h)
      have hp_nps : p ∉ ps₁ := fun h => hp_nr (hps₁.mem_iff.mp h)
      have hp_nqs : p ∉ qs := fun h => hp_nr (hqs_perm.mem_iff.mp h)
      have h1 : Level.subst lps₁ (posLevels lps₁) (.param p) = .param p :=
        subst_go_not_mem lps₁ (posLevels lps₁) p hp_nlps
      rw [h1]
      show Level.subst.go qs (posLevels qs) p = Level.subst.go ps₁ (posLevels ps₁) p
      rw [subst_go_not_mem qs (posLevels qs) p hp_nqs,
        subst_go_not_mem ps₁ (posLevels ps₁) p hp_nps]

private theorem substPW_compPerm_eq {N : Nat} {ps₁ lps₁ : List LevelParam}
    (hps₁ : ps₁.Perm (List.range N)) (hlps₁ : lps₁.Perm (List.range N))
    (pw : Ix.Kernel.PropWhen) :
    let qs := ps₁.map lps₁.idxOf
    Level.substPW qs (posLevels qs) (Level.substPW lps₁ (posLevels lps₁) pw) =
      Level.substPW ps₁ (posLevels ps₁) pw := by
  intro qs
  apply Ix.Kernel.PropWhen.eq_of_holds
  intro φ
  rw [Level.holds_substPW, Level.holds_substPW, Level.holds_substPW]
  congr 1
  funext p
  rw [← Level.eval_subst_go, ← Level.eval_subst_go, ← Level.eval_subst]
  exact congrArg (Level.eval φ) (subst_compPerm_eq hps₁ hlps₁ (.param p))

private theorem posOf_compPerm_eq {N : Nat} {ps₁ lps₁ : List LevelParam}
    (hps₁ : ps₁.Perm (List.range N)) (hlps₁ : lps₁.Perm (List.range N)) :
    let qs := ps₁.map lps₁.idxOf
    ∀ e : KExpr, posOf qs (posOf lps₁ e) = posOf ps₁ e := by
  intro qs e
  induction e with
  | bvar _ | lit _ => rfl
  | fvar i ty ih => exact congrArg (Expr.fvar i) ih
  | sort u => exact congrArg Expr.sort (subst_compPerm_eq hps₁ hlps₁ u)
  | const n us =>
    simp only [posOf, Expr.instantiateLevelParams, List.map_map]
    congr 1
    exact List.map_congr_left fun u _ => subst_compPerm_eq hps₁ hlps₁ u
  | app f a ihf iha =>
    simp only [posOf] at ihf iha ⊢
    simp only [Expr.instantiateLevelParams, ihf, iha]
  | lam ty bo m iht ihb =>
    simp only [posOf] at iht ihb ⊢
    simp only [Expr.instantiateLevelParams, iht, ihb, substPW_compPerm_eq hps₁ hlps₁ m.pw]
  | forallE ty bo m iht ihb =>
    simp only [posOf] at iht ihb ⊢
    simp only [Expr.instantiateLevelParams, iht, ihb, substPW_compPerm_eq hps₁ hlps₁ m.pw]
  | letE ty v bo m iht ihv ihb =>
    simp only [posOf] at iht ihv ihb ⊢
    simp only [Expr.instantiateLevelParams, iht, ihv, ihb]
  | proj s i e ih =>
    simp only [posOf] at ih ⊢
    simp only [Expr.instantiateLevelParams, ih]

/-- Given permutations `ps` and `lps` of arbitrary lengths, constructs a single permutation `qs`
satisfying `posOf qs (posOf lps e) = posOf ps e` and matching `Level.subst` on all inputs. -/
theorem exists_posOf_comp {ps lps : List LevelParam}
    (hps : ps.Perm (List.range ps.length))
    (hlps : lps.Perm (List.range lps.length)) :
    ∃ qs : List LevelParam,
      qs.Perm (List.range qs.length) ∧
      (∀ e : KExpr, posOf qs (posOf lps e) = posOf ps e) ∧
      (∀ u : KLevel,
        Level.subst qs (posLevels qs) (Level.subst lps (posLevels lps) u) =
          Level.subst ps (posLevels ps) u) := by
  let N := max ps.length lps.length
  have hle_p : ps.length ≤ N := Nat.le_max_left _ _
  have hle_l : lps.length ≤ N := Nat.le_max_right _ _
  have hp₁ : (padPerm N ps).Perm (List.range N) := padPerm_perm hps hle_p
  have hl₁ : (padPerm N lps).Perm (List.range N) := padPerm_perm hlps hle_l
  refine ⟨(padPerm N ps).map (padPerm N lps).idxOf, compPerm_perm hp₁ hl₁, ?_, ?_⟩
  · intro e
    rw [← posOf_padPerm_eq hle_l e, posOf_compPerm_eq hp₁ hl₁ e, posOf_padPerm_eq hle_p e]
  · intro u
    rw [← subst_padPerm_eq hle_l u, subst_compPerm_eq hp₁ hl₁ u, subst_padPerm_eq hle_p u]

theorem posRulesJ_infer_posOf {env : Env .anon} {d : Nat} {lps : List LevelParam}
    (hlps : lps.Perm (List.range lps.length)) {e t : KExpr}
    (h : posRulesJ.infer env d e t) :
    posRulesJ.infer env d (posOf lps e) (posOf lps t) := by
  obtain ⟨ps, hps, hi⟩ := h
  obtain ⟨qs, hqs, heq, _⟩ := exists_posOf_comp hps hlps
  exact ⟨qs, hqs, by rw [heq e, heq t]; exact hi⟩

theorem posRulesJ_defeq_posOf {env : Env .anon} {d : Nat} {lps : List LevelParam}
    (hlps : lps.Perm (List.range lps.length)) {a b : KExpr}
    (h : posRulesJ.defeq env d a b) :
    posRulesJ.defeq env d (posOf lps a) (posOf lps b) := by
  obtain ⟨ps, hps, hd⟩ := h
  obtain ⟨qs, hqs, heq, _⟩ := exists_posOf_comp hps hlps
  exact ⟨qs, hqs, by rw [heq a, heq b]; exact hd⟩

theorem posRulesJ_sort_posOf {env : Env .anon} {d : Nat} {lps : List LevelParam}
    (hlps : lps.Perm (List.range lps.length)) {t : KExpr} {u : KLevel}
    (h : posRulesJ.sort env d t u) :
    posRulesJ.sort env d (posOf lps t) (Level.subst lps (posLevels lps) u) := by
  obtain ⟨ps, hps, hr⟩ := h
  obtain ⟨qs, hqs, heqE, heqL⟩ := exists_posOf_comp hps hlps
  exact ⟨qs, hqs, by rw [heqE t, heqL u]; exact hr⟩

theorem defEqListJ_posOf {env : Env .anon} {d : Nat} {lps : List LevelParam}
    (hlps : lps.Perm (List.range lps.length)) {as bs : List KExpr}
    (h : DefEqListJ posRulesJ env d as bs) :
    DefEqListJ posRulesJ env d (as.map (posOf lps)) (bs.map (posOf lps)) := by
  induction as generalizing bs with
  | nil => cases bs with | nil => trivial | cons _ _ => exact nomatch h
  | cons _ _ ih =>
    cases bs with
    | nil => exact nomatch h
    | cons _ _ => exact ⟨posRulesJ_defeq_posOf hlps h.1, ih h.2⟩

theorem typedListJ_posOf {env : Env .anon} {d : Nat} {lps : List LevelParam}
    (hlps : lps.Perm (List.range lps.length)) {as bs : List KExpr}
    (h : TypedListJ posRulesJ env d as bs) :
    TypedListJ posRulesJ env d (as.map (posOf lps)) (bs.map (posOf lps)) := by
  induction as generalizing bs with
  | nil => cases bs with | nil => trivial | cons _ _ => exact nomatch h
  | cons _ _ ih =>
    cases bs with
    | nil => exact nomatch h
    | cons _ _ =>
      obtain ⟨⟨ty, hi, hd⟩, hs⟩ := h
      exact ⟨⟨posOf lps ty, posRulesJ_infer_posOf hlps hi, posRulesJ_defeq_posOf hlps hd⟩, ih hs⟩

private theorem fold_posOf (lps : List LevelParam) :
    (fun x : KExpr => x.instantiateLevelParams lps (posLevels lps)) = posOf lps := rfl

private theorem getLastD_map_of_ne_nil {α β : Type _} (f : α → β) (d₁ : β) (d₂ : α) :
    ∀ {l : List α}, l ≠ [] → (l.map f).getLastD d₁ = f (l.getLastD d₂)
  | [], h => absurd rfl h
  | [_], _ => rfl
  | _ :: b :: tl, _ => getLastD_map_of_ne_nil f d₁ d₂ (List.cons_ne_nil b tl)

theorem lamTeleWalkJ_posOf {env : Env .anon} {lps : List LevelParam}
    (hlps : lps.Perm (List.range lps.length))
    {rP cnF : Nat} {tyA cty : KExpr} {pins_lps : List KExpr} {rhs : KExpr}
    (h : LamTeleWalkJ posRulesJ env rP cnF tyA cty
      (fun pre => pins_lps.map fun p => Expr.instSpine pre (rP - 1) p) rhs) :
    LamTeleWalkJ posRulesJ env rP cnF (posOf lps tyA) (posOf lps cty)
      (fun pre => (pins_lps.map (posOf lps)).map fun p => Expr.instSpine pre (rP - 1) p)
      (posOf lps rhs) := by
  obtain ⟨lfvs, lrest, pdoms1, tyRest, cdomsL, crestL, pdoms2, crestEnd,
    hopen, hir, hic, hopc, hwalk⟩ := h
  have hopen' := openLamsAtFvars_instantiateLevelParams lps (posLevels lps) (rP + cnF) rhs 0
  rw [fold_posOf lps, hopen, Option.map_some] at hopen'
  have hir' := instPisAt_instantiateLevelParams lps (posLevels lps) (lfvs.take rP) tyA
  rw [fold_posOf lps, hir, Option.map_some, List.map_take] at hir'
  have hpins_map :
      ((pins_lps.map fun p => Expr.instSpine (lfvs.take rP) (rP - 1) p).map (posOf lps)) =
      ((pins_lps.map (posOf lps)).map fun p =>
        Expr.instSpine ((lfvs.map (posOf lps)).take rP) (rP - 1) p) := by
    rw [List.map_map, List.map_map, ← List.map_take]
    apply List.map_congr_left
    intro p _
    exact instantiateLevelParams_instSpine lps (posLevels lps) (lfvs.take rP) (rP - 1) p
  have hic' := instPisAt_instantiateLevelParams lps (posLevels lps)
    (pins_lps.map fun p => Expr.instSpine (lfvs.take rP) (rP - 1) p) cty
  rw [fold_posOf lps, hic, Option.map_some, hpins_map] at hic'
  have hopc' := instPisAt_instantiateLevelParams lps (posLevels lps) (lfvs.drop rP) crestL
  rw [fold_posOf lps, hopc, Option.map_some, List.map_drop] at hopc'
  have hfvd : (lfvs.map Expr.fvarTypeD).map (posOf lps) =
      (lfvs.map (posOf lps)).map Expr.fvarTypeD := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro fv _
    exact instantiateLevelParams_fvarTypeD lps (posLevels lps) fv
  have hwalk' := defEqListJ_posOf hlps hwalk
  rw [hfvd, List.map_append] at hwalk'
  exact ⟨lfvs.map (posOf lps), posOf lps lrest,
    pdoms1.map (posOf lps), posOf lps tyRest,
    cdomsL.map (posOf lps), posOf lps crestL,
    pdoms2.map (posOf lps), posOf lps crestEnd,
    hopen', hir', hic', hopc', hwalk'⟩

theorem iotaRunsVmJ_posOf {env : Env .anon} {lps : List LevelParam}
    (hlps : lps.Perm (List.range lps.length))
    {depth : Nat} {lindices cindices xdoms cfieldDoms fpreDoms rdoms : List KExpr}
    {rhsS applied tyArg lhsS : KExpr}
    (h : IotaRunsVmJ posRulesJ env depth lindices cindices xdoms cfieldDoms fpreDoms rdoms
      rhsS applied tyArg lhsS) :
    IotaRunsVmJ posRulesJ env depth
      (lindices.map (posOf lps)) (cindices.map (posOf lps))
      (xdoms.map (posOf lps)) (cfieldDoms.map (posOf lps))
      (fpreDoms.map (posOf lps)) (rdoms.map (posOf lps))
      (posOf lps rhsS) (posOf lps applied) (posOf lps tyArg) (posOf lps lhsS) := by
  obtain ⟨hidx, hfields, hpre, hrhs, ⟨tl, hil, hdl⟩, ⟨tr, hir, hdr⟩⟩ := h
  exact ⟨defEqListJ_posOf hlps hidx,
    defEqListJ_posOf hlps hfields,
    defEqListJ_posOf hlps hpre,
    posRulesJ_defeq_posOf hlps hrhs,
    ⟨posOf lps tl, posRulesJ_infer_posOf hlps hil, posRulesJ_defeq_posOf hlps hdl⟩,
    ⟨posOf lps tr, posRulesJ_infer_posOf hlps hir, posRulesJ_defeq_posOf hlps hdr⟩⟩

/-! ## Phase 1: Auxiliary `.iota` Theorem and `.model` Alias Installation (`env_adv → env_aux`) -/

/-- Copy an existing theorem `k_old` in `E` to a fresh derived `.iota j` key `k_new = auxKey m (.iota j)`. -/
theorem installIotaThmCopy {V : Type u} [Ix.Kernel.SetTheory V] {E : Env .anon}
    (mpE : EnvModelM V .verified E) (hEE : Ix.Kernel.EtaFamiliesClosed E)
    {m : KKey} {j : Nat} {k_old : KKey} {cvt : ConstantVal .anon} {vt : KExpr}
    (hfresh : E.find? (auxKey m (.iota j)) = none)
    (hsrc : E.find? k_old = some (.thmInfo cvt vt)) :
    let c₀ : ConstantInfo .anon :=
      .thmInfo ⟨auxKey m (.iota j), cvt.levelParams, cvt.type⟩ vt
    ∃ mp' : EnvModelM V .verified ⟨c₀ :: E.consts⟩,
      mp'.base2.acval = acvalWith mpE.base2.acval c₀.name (mpE.base2.acval k_old) ∧
      Ix.Kernel.EtaFamiliesClosed ⟨c₀ :: E.consts⟩ ∧
      EnvExt E ⟨c₀ :: E.consts⟩ ∧
      (∀ k, (E.find? k).isSome = true → mp'.base2.acval k = mpE.base2.acval k) := by
  let k_new := auxKey m (.iota j)
  let c₀ : ConstantInfo .anon := .thmInfo ⟨k_new, cvt.levelParams, cvt.type⟩ vt
  let A := mpE.base2.acval k_old
  have hnres : Ix.Kernel.reservedBasisNames.contains c₀.name = false :=
    Ix.Kernel.reservedBasisNames_contains_auxKey m (.iota j)
  have hmem : ConstantInfo.thmInfo cvt vt ∈ E.consts :=
    Ix.Kernel.Semantics.Env.find?_mem hsrc
  have hnm : cvt.name = k_old := Ix.Kernel.Semantics.Env.find?_name hsrc
  have hwf_src := mpE.base2.wf _ hmem
  have htf : cvt.type.hasFvar = false := hwf_src.1
  have htp : cvt.type.allLevelParamsDefined cvt.levelParams = true := hwf_src.2.1
  have htr : cvt.type.constsResolve E = true := hwf_src.2.2.1
  have htb : cvt.type.looseBVarsBounded 0 = true := hwf_src.2.2.2.1
  have hcbT : ConstsBound E cvt.type := constsBound_of_constsResolve _ htr
  have hcomp : ∀ (ψ : LevelParam → Nat) (e : KExpr), ConstsBound E e →
      ∀ {ea : AnnotTerm}, denoteMeta mpE.base2.acval E ψ 0 e = some ea →
      denoteMeta (acvalWith mpE.base2.acval c₀.name A) ⟨c₀ :: E.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteMeta_cons_fresh_mono (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) ψ 0 e hcb h
  have hstep : ∃ mp' : EnvModelM V .verified ⟨c₀ :: E.consts⟩,
      mp'.base2.acval = acvalWith mpE.base2.acval c₀.name A := by
    refine declStep_preserves_of_cons mpE (c₀ := c₀) (A := A) hfresh
      (ConsHead.ofFresh
        (Ix.Kernel.EnvWF.cons mpE.base2.wf (Ix.Kernel.structConstWF htf htp
          (Ix.Kernel.Expr.constsResolve_mono htr) htb
          (fun _ _ _ heq => nomatch heq)
          (fun _ _ _ _ heq => nomatch heq)
          (fun _ heq => nomatch heq)
          (fun _ _ heq => nomatch heq)))
        (fun ψ => mpE.base2.cval_closedL k_old ψ)
        hnres
        (fun _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq))
      (fun ψ k => mpE.base2.acval_closed k_old ψ k)
      (fun ψ₁ ψ₂ hp => mpE.base2.acval_params k_old _ hsrc ψ₁ ψ₂ hp)
      (fun ψ ρ => mpE.base2.acval_wellDenoted k_old ψ ρ)
      (fun ψ ρ => mpE.acval_validV k_old ψ ρ)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro ψ
      obtain ⟨ta, hta⟩ := mpE.type_reads _ hmem ψ
      exact ⟨ta, hcomp ψ cvt.type hcbT hta⟩
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mpE.type_reads _ hmem ψ
      have htaEq : ta = ta₀ := Option.some.inj (hta.symm.trans (hcomp ψ cvt.type hcbT hta₀))
      rw [htaEq]
      exact mpE.type_wellDenotedV _ hmem ψ ta₀ hta₀ ρ
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mpE.type_reads _ hmem ψ
      have htaEq : ta = ta₀ := Option.some.inj (hta.symm.trans (hcomp ψ cvt.type hcbT hta₀))
      have hm := mpE.mem_type _ hmem ψ ta₀ hta₀ ρ
      change interp V ρ (mpE.base2.acval cvt.name ψ) ∈ˢ interp V ρ ta₀ at hm
      rw [hnm] at hm
      rwa [htaEq]
    · intro ψ cv2 value2 ⟨_, hdt⟩
      exact nomatch hdt
    · exact fun φ => natHeads_cons_fresh mpE (c₀ := c₀) (A := A) hfresh
        ⟨(fun _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)),
          (fun _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))⟩ _ rfl φ
    · exact fun φ => natOps_cons_fresh mpE (mpE.nat_ops φ) (c₀ := c₀) (A := A) hfresh
        (hntc := fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))) _ rfl
    · exact fun φ => divMod_cons_fresh (mpE.div_mod φ) (c₀ := c₀) (A := A) hfresh
        (Or.inl (fun _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))) _ rfl
    · exact eqLaw_cons_valueKind mpE.eq_law (c₀ := c₀) (A := A)
        (fun _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl
    · exact capsOk_cons_fresh mpE mpE.caps_ok (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl
    · exact fun φ => recRules_cons_fresh mpE (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl φ
    · exact fun φ => towerOk_cons_fresh mpE (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl φ
  obtain ⟨mp', hac⟩ := hstep
  refine ⟨mp', hac,
    Ix.Kernel.EtaFamiliesClosed.cons_nonind hEE hfresh (fun _ _ h => nomatch h),
    envExt_cons_fresh hfresh (ne_projTableName_auxKey_iota m · j),
    fun k hk => ?_⟩
  have hne : k ≠ auxKey m (.iota j) := fun heq => by rw [heq, hfresh] at hk; exact nomatch hk
  rw [hac, show c₀.name = auxKey m (.iota j) from rfl, acvalWith_ne hne]

/-- Every `.const` node in `e` satisfies `P`. -/
def ConstNamesIn (P : KKey → Prop) : KExpr → Prop
  | .bvar _ | .sort _ | .lit _ => True
  | .fvar _ ty => ConstNamesIn P ty
  | .const n _ => P n
  | .app f a => ConstNamesIn P f ∧ ConstNamesIn P a
  | .lam ty b _ | .forallE ty b _ => ConstNamesIn P ty ∧ ConstNamesIn P b
  | .letE ty v b _ => ConstNamesIn P ty ∧ ConstNamesIn P v ∧ ConstNamesIn P b
  | .proj _ _ e => ConstNamesIn P e

theorem constNamesIn_of_constsResolve {env : Env .anon} {e : KExpr}
    (h : e.constsResolve env = true) :
    ConstNamesIn (fun n => (env.find? n).isSome = true) e := by
  induction e with
  | bvar _ | sort _ | lit _ => trivial
  | fvar _ _ ih => exact ih h
  | const _ _ => exact h
  | app _ _ ihf iha =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact ⟨iht h.1, ihb h.2⟩
  | letE _ _ _ _ iht ihv ihb =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | proj _ _ _ ihe =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact ihe h.2

theorem constNamesIn_instantiate1 {P : KKey → Prop} {v : KExpr} (hv : ConstNamesIn P v) :
    ∀ {e : KExpr} {k : Nat}, ConstNamesIn P e → ConstNamesIn P (e.instantiate1 v k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> trivial
  | sort _ | lit _ => intro _ _; trivial
  | fvar _ _ => intro _ hp; exact hp
  | const _ _ => intro _ hp; exact hp
  | app _ _ ihf iha => intro _ ⟨hf, ha⟩; exact ⟨ihf hf, iha ha⟩
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro _ ⟨ht, hb⟩; exact ⟨iht ht, ihb hb⟩
  | letE _ _ _ _ iht ihv ihb =>
    intro _ ⟨ht, hval, hb⟩; exact ⟨iht ht, ihv hval, ihb hb⟩
  | proj _ _ _ ihe => intro _ hp; exact ihe hp

theorem allLevelParamsDefined_renameConsts (f : KKey → KKey) (ps : List LevelParam) :
    ∀ e : KExpr, (e.renameConsts f).allLevelParamsDefined ps = e.allLevelParamsDefined ps
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ ty => allLevelParamsDefined_renameConsts f ps ty
  | .app g a => by
    simp only [Expr.renameConsts, Expr.allLevelParamsDefined,
      allLevelParamsDefined_renameConsts f ps g, allLevelParamsDefined_renameConsts f ps a]
  | .lam ty b m | .forallE ty b m => by
    simp only [Expr.renameConsts, Expr.allLevelParamsDefined,
      allLevelParamsDefined_renameConsts f ps ty, allLevelParamsDefined_renameConsts f ps b]
  | .letE ty v b _ => by
    simp only [Expr.renameConsts, Expr.allLevelParamsDefined,
      allLevelParamsDefined_renameConsts f ps ty,
      allLevelParamsDefined_renameConsts f ps v,
      allLevelParamsDefined_renameConsts f ps b]
  | .proj _ _ e => allLevelParamsDefined_renameConsts f ps e

theorem looseBVarsBounded_renameConsts (f : KKey → KKey) :
    ∀ (d : Nat) (e : KExpr), (e.renameConsts f).looseBVarsBounded d = e.looseBVarsBounded d
  | _, .bvar _ | _, .fvar _ _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl
  | d, .app g a => by
    simp only [Expr.renameConsts, Expr.looseBVarsBounded,
      looseBVarsBounded_renameConsts f d g, looseBVarsBounded_renameConsts f d a]
  | d, .lam ty b _ | d, .forallE ty b _ => by
    simp only [Expr.renameConsts, Expr.looseBVarsBounded,
      looseBVarsBounded_renameConsts f d ty, looseBVarsBounded_renameConsts f (d + 1) b]
  | d, .letE ty v b _ => by
    simp only [Expr.renameConsts, Expr.looseBVarsBounded,
      looseBVarsBounded_renameConsts f d ty,
      looseBVarsBounded_renameConsts f d v,
      looseBVarsBounded_renameConsts f (d + 1) b]
  | d, .proj _ _ e => looseBVarsBounded_renameConsts f d e

theorem constsResolve_renameConsts_congr {E : Env .anon} {g₁ g₂ : KKey → KKey}
    {P : KKey → Prop}
    (hg : ∀ n, P n → (E.find? (g₁ n)).isSome = (E.find? (g₂ n)).isSome)
    {e : KExpr} (hp : ConstNamesIn P e) :
    (e.renameConsts g₁).constsResolve E = (e.renameConsts g₂).constsResolve E := by
  induction e with
  | bvar _ | sort _ | lit _ => rfl
  | fvar _ _ ih => exact ih hp
  | const n _ => exact hg n hp
  | app _ _ ihf iha =>
    simp only [Expr.renameConsts, Expr.constsResolve, ihf hp.1, iha hp.2]
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    simp only [Expr.renameConsts, Expr.constsResolve, iht hp.1, ihb hp.2]
  | letE _ _ _ _ iht ihv ihb =>
    simp only [Expr.renameConsts, Expr.constsResolve, iht hp.1, ihv hp.2.1, ihb hp.2.2]
  | proj _ _ _ ihe =>
    simp only [Expr.renameConsts, Expr.constsResolve, ihe hp]

theorem denoteMeta_renameConsts_congr {acval : KKey → (LevelParam → Nat) → AnnotTerm}
    {E : Env .anon} {φ : LevelParam → Nat} {g₁ g₂ : KKey → KKey} {P : KKey → Prop}
    (hlps : ∀ n, P n →
      (E.find? (g₁ n)).map (·.toConstantVal.levelParams) =
      (E.find? (g₂ n)).map (·.toConstantVal.levelParams))
    (hac : ∀ n, P n → acval (g₁ n) = acval (g₂ n)) :
    ∀ (e : KExpr) (d : Nat), ConstNamesIn P e →
      denoteMeta acval E φ d (e.renameConsts g₁) =
        denoteMeta acval E φ d (e.renameConsts g₂)
  | .bvar _, _, _ => by rw [Expr.renameConsts, Expr.renameConsts]
  | .sort _, _, _ => by rw [Expr.renameConsts, Expr.renameConsts]
  | .lit (.natVal _), _, _ => by rw [Expr.renameConsts, Expr.renameConsts]
  | .lit (.strVal _), _, _ => by rw [Expr.renameConsts, Expr.renameConsts]
  | .fvar _ _, _, _ => by
    simp only [Expr.renameConsts]
    rw [denoteMeta, denoteMeta]
  | .const n us, d, hp => by
    simp only [Expr.renameConsts]
    have hl := hlps n hp
    cases hf₁ : E.find? (g₁ n) with
    | none =>
      rw [hf₁] at hl
      cases hf₂ : E.find? (g₂ n) with
      | none => rw [denoteMeta, hf₁, denoteMeta, hf₂]
      | some ci₂ => rw [hf₂] at hl; exact nomatch hl
    | some ci₁ =>
      rw [hf₁] at hl
      cases hf₂ : E.find? (g₂ n) with
      | none => rw [hf₂] at hl; exact nomatch hl
      | some ci₂ =>
        rw [hf₂] at hl
        simp only [Option.map_some, Option.some.injEq] at hl
        rw [denoteMeta, hf₁, denoteMeta, hf₂]
        dsimp only
        by_cases hlen : us.length = ci₁.toConstantVal.levelParams.length
        · rw [ite_eq_left hlen, ite_eq_left (hl ▸ hlen), hl, hac n hp]
        · rw [ite_eq_right hlen, ite_eq_right (fun hh => hlen (hl ▸ hh))]
  | .app f a, d, ⟨hpf, hpa⟩ => by
    simp only [Expr.renameConsts]
    rw [denoteMeta, denoteMeta,
      denoteMeta_renameConsts_congr hlps hac f d hpf,
      denoteMeta_renameConsts_congr hlps hac a d hpa]
  | .lam ty bo m, d, ⟨hpt, hpb⟩ => by
    simp only [Expr.renameConsts]
    rw [denoteMeta, denoteMeta,
      ← Expr.renameConsts_instantiate1, ← Expr.renameConsts_instantiate1,
      denoteMeta_renameConsts_congr hlps hac ty d hpt,
      denoteMeta_renameConsts_congr hlps hac (bo.instantiate1 (.fvar d ty)) (d + 1)
        (constNamesIn_instantiate1 (v := .fvar d ty) hpt hpb)]
  | .forallE ty bo m, d, ⟨hpt, hpb⟩ => by
    simp only [Expr.renameConsts]
    rw [denoteMeta, denoteMeta,
      ← Expr.renameConsts_instantiate1, ← Expr.renameConsts_instantiate1,
      denoteMeta_renameConsts_congr hlps hac ty d hpt,
      denoteMeta_renameConsts_congr hlps hac (bo.instantiate1 (.fvar d ty)) (d + 1)
        (constNamesIn_instantiate1 (v := .fvar d ty) hpt hpb)]
  | .letE _ _ _ _, _, _ => by
    simp only [Expr.renameConsts]
    rw [denoteMeta, denoteMeta]
  | .proj _ _ e, d, hp => by
    simp only [Expr.renameConsts]
    rw [denoteMeta, denoteMeta, denoteMeta_renameConsts_congr hlps hac e d hp]
  termination_by e => e.sizeB
  decreasing_by
    all_goals first
    | (simp [Expr.sizeB]; omega)
    | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
    | (simp [Expr.sizeB])

theorem auxKey_not_mem_natOpNames (k : KKey) (d : Derived) :
    auxKey k d ∉ Ix.Kernel.natOpNames := by
  intro h
  simp [Ix.Kernel.natOpNames, Ix.Kernel.natPredName, Ix.Kernel.natAddName,
    Ix.Kernel.natSubName, Ix.Kernel.natMulName, Ix.Kernel.natPowName,
    Ix.Kernel.natBeqName, Ix.Kernel.natBleName, Ix.Kernel.roleKey, auxKey] at h

theorem auxKey_not_mem_natDivModNames (k : KKey) (d : Derived) :
    auxKey k d ∉ Ix.Kernel.natDivModNames := by
  intro h
  simp [Ix.Kernel.natDivModNames, Ix.Kernel.natDivName, Ix.Kernel.natModName,
    Ix.Kernel.natGcdName, Ix.Kernel.natLandName, Ix.Kernel.natLorName,
    Ix.Kernel.natXorName, Ix.Kernel.natShiftLeftName, Ix.Kernel.natShiftRightName,
    Ix.Kernel.roleKey, auxKey] at h

/-- Install a `.model` alias `auxKey n .model` at positional level parameters `List.range nl`,
with type `ty_pos.renameConsts f_aux` and body `.const (f_id n) ((List.range nl).map .param)`,
inheriting its semantic leaf directly from the advice definition `f_id n`. -/
theorem installModelAlias {V : Type u} [Ix.Kernel.SetTheory V] {E : Env .anon}
    (mpE : EnvModelM V .verified E) (hEE : Ix.Kernel.EtaFamiliesClosed E)
    {blockNames seen : List KKey} {f_id : KKey → KKey}
    (hf_out : ∀ k, blockNames.contains k = false → f_id k = k)
    (hseen : ∀ k ∈ seen, ∃ cvm_k mval_k hint_k cvm_fk mval_fk hint_fk,
      E.find? (auxKey k .model) = some (.defnInfo cvm_k mval_k hint_k) ∧
      E.find? (f_id k) = some (.defnInfo cvm_fk mval_fk hint_fk) ∧
      cvm_k.levelParams = cvm_fk.levelParams ∧
      mpE.base2.acval (auxKey k .model) = mpE.base2.acval (f_id k))
    {n : KKey} {nl : Nat} {ty_pos : KExpr}
    {cvm_f : ConstantVal .anon} {mval_f : KExpr} {hint_f : ReducibilityHint}
    (hbn_n : blockNames.contains n = true)
    (hfresh : E.find? (auxKey n .model) = none)
    (hsrc_f : E.find? (f_id n) = some (.defnInfo cvm_f mval_f hint_f))
    (hlps_f : cvm_f.levelParams = List.range nl)
    (hty_f : cvm_f.type = ty_pos.renameConsts f_id)
    (hnames : ConstNamesIn (fun k => blockNames.contains k = false ∨ k ∈ seen) ty_pos) :
    let f_aux : KKey → KKey := fun k => if blockNames.contains k then auxKey k .model else k
    let c₀ : ConstantInfo .anon :=
      .defnInfo ⟨auxKey n .model, List.range nl, ty_pos.renameConsts f_aux⟩
        (.const (f_id n) ((List.range nl).map .param)) .abbrev
    ∃ mp' : EnvModelM V .verified ⟨c₀ :: E.consts⟩,
      mp'.base2.acval = acvalWith mpE.base2.acval c₀.name (mpE.base2.acval (f_id n)) ∧
      Ix.Kernel.EtaFamiliesClosed ⟨c₀ :: E.consts⟩ ∧
      EnvExt E ⟨c₀ :: E.consts⟩ ∧
      (∀ k, (E.find? k).isSome = true → mp'.base2.acval k = mpE.base2.acval k) := by
  let f_aux : KKey → KKey := fun k => if blockNames.contains k then auxKey k .model else k
  let mval_new : KExpr := .const (f_id n) ((List.range nl).map .param)
  let c₀ : ConstantInfo .anon :=
    .defnInfo ⟨auxKey n .model, List.range nl, ty_pos.renameConsts f_aux⟩ mval_new .abbrev
  let A := mpE.base2.acval (f_id n)
  have hnres : Ix.Kernel.reservedBasisNames.contains c₀.name = false :=
    Ix.Kernel.reservedBasisNames_contains_auxKey n .model
  have hmem_f : ConstantInfo.defnInfo cvm_f mval_f hint_f ∈ E.consts :=
    Ix.Kernel.Semantics.Env.find?_mem hsrc_f
  have hnm_f : cvm_f.name = f_id n := Ix.Kernel.Semantics.Env.find?_name hsrc_f
  have hwf_f := mpE.base2.wf _ hmem_f
  have hf_aux_eq : ∀ k, f_aux k = if blockNames.contains k = true then auxKey k .model else k :=
    fun _ => rfl
  have P_lps : ∀ k, (blockNames.contains k = false ∨ k ∈ seen) →
      (E.find? (f_aux k)).map (·.toConstantVal.levelParams) =
      (E.find? (f_id k)).map (·.toConstantVal.levelParams) := by
    intro k hk
    rw [hf_aux_eq k]
    rcases hk with hout | hink
    · rw [ite_eq_right (by rw [hout]; decide), hf_out k hout]
    · obtain ⟨cvm_k, mval_k, hint_k, cvm_fk, mval_fk, hint_fk, hfk1, hfk2, hlpsk, _⟩ := hseen k hink
      by_cases hbk : blockNames.contains k = true
      · rw [ite_eq_left hbk, hfk1, hfk2, Option.map_some, Option.map_some]
        exact congrArg some hlpsk
      · have hbk' : blockNames.contains k = false := Bool.eq_false_iff.mpr hbk
        rw [ite_eq_right hbk, hf_out k hbk']
  have P_some : ∀ k, (blockNames.contains k = false ∨ k ∈ seen) →
      (E.find? (f_aux k)).isSome = (E.find? (f_id k)).isSome := by
    intro k hk
    have hl := P_lps k hk
    cases hf1 : E.find? (f_aux k) <;> cases hf2 : E.find? (f_id k) <;> simp_all
  have P_ac : ∀ k, (blockNames.contains k = false ∨ k ∈ seen) →
      mpE.base2.acval (f_aux k) = mpE.base2.acval (f_id k) := by
    intro k hk
    rw [hf_aux_eq k]
    rcases hk with hout | hink
    · rw [ite_eq_right (by rw [hout]; decide), hf_out k hout]
    · obtain ⟨_, _, _, _, _, _, _, _, _, hack⟩ := hseen k hink
      by_cases hbk : blockNames.contains k = true
      · rw [ite_eq_left hbk, hack]
      · have hbk' : blockNames.contains k = false := Bool.eq_false_iff.mpr hbk
        rw [ite_eq_right hbk, hf_out k hbk']
  have htf : (ty_pos.renameConsts f_aux).hasFvar = false := by
    have h1 : (ty_pos.renameConsts f_id).hasFvar = false := hty_f ▸ hwf_f.1
    rw [hasFvar_renameConsts] at h1 ⊢
    exact h1
  have htp : (ty_pos.renameConsts f_aux).allLevelParamsDefined (List.range nl) = true := by
    have h1 : (ty_pos.renameConsts f_id).allLevelParamsDefined (List.range nl) = true :=
      hlps_f ▸ hty_f ▸ hwf_f.2.1
    rw [allLevelParamsDefined_renameConsts] at h1 ⊢
    exact h1
  have htr : (ty_pos.renameConsts f_aux).constsResolve E = true := by
    rw [constsResolve_renameConsts_congr P_some hnames, ← hty_f]
    exact hwf_f.2.2.1
  have htb : (ty_pos.renameConsts f_aux).looseBVarsBounded 0 = true := by
    have h1 : (ty_pos.renameConsts f_id).looseBVarsBounded 0 = true := hty_f ▸ hwf_f.2.2.2.1
    rw [looseBVarsBounded_renameConsts] at h1 ⊢
    exact h1
  have hvf : mval_new.hasFvar = false := rfl
  have hvp : mval_new.allLevelParamsDefined (List.range nl) = true := by
    simp only [mval_new, Expr.allLevelParamsDefined, List.all_eq_true]
    intro u hu
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
    simpa [Level.allParamsDefined] using hp
  have hvr : mval_new.constsResolve E = true := by
    simp only [mval_new, Expr.constsResolve, hsrc_f]
    rfl
  have hvb : mval_new.looseBVarsBounded 0 = true := rfl
  have hcbT : ConstsBound E (ty_pos.renameConsts f_aux) := constsBound_of_constsResolve _ htr
  have hcomp : ∀ (ψ : LevelParam → Nat) (e : KExpr), ConstsBound E e →
      ∀ {ea : AnnotTerm}, denoteMeta mpE.base2.acval E ψ 0 e = some ea →
      denoteMeta (acvalWith mpE.base2.acval c₀.name A) ⟨c₀ :: E.consts⟩ ψ 0 e = some ea :=
    fun ψ e hcb {ea} h =>
      denoteMeta_cons_fresh_mono (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) ψ 0 e hcb h
  have hty_den_eq : ∀ ψ : LevelParam → Nat,
      denoteMeta mpE.base2.acval E ψ 0 (ty_pos.renameConsts f_aux) =
      denoteMeta mpE.base2.acval E ψ 0 cvm_f.type := by
    intro ψ
    rw [hty_f]
    exact denoteMeta_renameConsts_congr P_lps P_ac ty_pos 0 hnames
  have hstep : ∃ mp' : EnvModelM V .verified ⟨c₀ :: E.consts⟩,
      mp'.base2.acval = acvalWith mpE.base2.acval c₀.name A := by
    refine declStep_preserves_of_cons mpE (c₀ := c₀) (A := A) hfresh
      (ConsHead.ofFresh
        (Ix.Kernel.EnvWF.cons mpE.base2.wf (Ix.Kernel.structConstWF htf htp
          (Ix.Kernel.Expr.constsResolve_mono htr) htb
          (fun _ _ _ heq => by
            obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj heq
            exact ⟨hvf, hvp, Ix.Kernel.Expr.constsResolve_mono hvr, hvb⟩)
          (fun _ _ _ _ heq => nomatch heq)
          (fun _ heq => nomatch heq)
          (fun _ _ heq => nomatch heq)))
        (fun ψ => mpE.base2.cval_closedL (f_id n) ψ)
        hnres
        (fun _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq))
      (fun ψ k => mpE.base2.acval_closed (f_id n) ψ k)
      (fun ψ₁ ψ₂ hp => mpE.base2.acval_params (f_id n) _ hsrc_f ψ₁ ψ₂ (hlps_f ▸ hp))
      (fun ψ ρ => mpE.base2.acval_wellDenoted (f_id n) ψ ρ)
      (fun ψ ρ => mpE.acval_validV (f_id n) ψ ρ)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro ψ
      obtain ⟨ta, hta⟩ := mpE.type_reads _ hmem_f ψ
      dsimp only [ConstantInfo.toConstantVal] at hta
      rw [← hty_den_eq ψ] at hta
      exact ⟨ta, hcomp ψ (ty_pos.renameConsts f_aux) hcbT hta⟩
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mpE.type_reads _ hmem_f ψ
      have hta₀' : denoteMeta mpE.base2.acval E ψ 0 (ty_pos.renameConsts f_aux) = some ta₀ := by
        rw [hty_den_eq ψ]; exact hta₀
      have htaEq : ta = ta₀ := Option.some.inj
        (hta.symm.trans (hcomp ψ (ty_pos.renameConsts f_aux) hcbT hta₀'))
      rw [htaEq]
      exact mpE.type_wellDenotedV _ hmem_f ψ ta₀ hta₀ ρ
    · intro ψ ta hta ρ
      obtain ⟨ta₀, hta₀⟩ := mpE.type_reads _ hmem_f ψ
      have hta₀' : denoteMeta mpE.base2.acval E ψ 0 (ty_pos.renameConsts f_aux) = some ta₀ := by
        rw [hty_den_eq ψ]; exact hta₀
      have htaEq : ta = ta₀ := Option.some.inj
        (hta.symm.trans (hcomp ψ (ty_pos.renameConsts f_aux) hcbT hta₀'))
      have hm := mpE.mem_type _ hmem_f ψ ta₀ hta₀ ρ
      change interp V ρ (mpE.base2.acval cvm_f.name ψ) ∈ˢ interp V ρ ta₀ at hm
      rw [hnm_f] at hm
      rwa [htaEq]
    · intro ψ cv2 value2 ⟨hint2, hdt⟩
      obtain ⟨_, rfl, _⟩ := ConstantInfo.defnInfo.inj hdt
      have hne_fn : f_id n ≠ auxKey n .model := fun heq => by
        rw [heq, hfresh] at hsrc_f; exact nomatch hsrc_f
      have hfind_fn : (⟨c₀ :: E.consts⟩ : Env .anon).find? (f_id n) =
          some (.defnInfo cvm_f mval_f hint_f) :=
        Env.find?_cons_of_fresh hfresh hsrc_f
      simp only [mval_new]
      rw [denoteMeta, hfind_fn]
      dsimp only
      have hlen_p : ((List.range nl).map Level.param).length =
          (ConstantInfo.defnInfo cvm_f mval_f hint_f).toConstantVal.levelParams.length := by
        simp [ConstantInfo.toConstantVal, hlps_f]
      rw [ite_eq_left hlen_p, show c₀.name = auxKey n .model from rfl, acvalWith_ne hne_fn]
      congr 1
      refine mpE.base2.acval_params (f_id n) _ hsrc_f _ ψ (fun p hp => ?_)
      dsimp only [ConstantInfo.toConstantVal] at hp ⊢
      rw [hlps_f] at hp ⊢
      show Level.eval ψ (Level.subst.go (List.range nl) ((List.range nl).map .param) p) = ψ p
      rw [subst_go_self_list]
      rfl
    · exact fun φ => natHeads_cons_offNat mpE
        (ne_of_notReserved hnres reserved_natName)
        (ne_of_notReserved hnres reserved_natZeroName)
        (ne_of_notReserved hnres reserved_natSuccName) _ rfl φ
    · exact fun φ => natOps_cons_fresh mpE (mpE.nat_ops φ) (c₀ := c₀) (A := A) hfresh
        (hntc := fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (Or.inr (auxKey_not_mem_natOpNames n .model)) _ rfl
    · exact fun φ => divMod_cons_fresh (mpE.div_mod φ) (c₀ := c₀) (A := A) hfresh
        (Or.inr (auxKey_not_mem_natDivModNames n .model)) _ rfl
    · exact eqLaw_cons_valueKind mpE.eq_law (c₀ := c₀) (A := A)
        (fun _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl
    · exact capsOk_cons_fresh mpE mpE.caps_ok (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl
    · exact fun φ => recRules_cons_fresh mpE (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl φ
    · exact fun φ => towerOk_cons_fresh mpE (c₀ := c₀) (A := A) hfresh
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))
        (fun _ h => ConstantInfo.noConfusion rfl (heq_of_eq h)) _ rfl φ
  obtain ⟨mp', hac⟩ := hstep
  refine ⟨mp', hac,
    Ix.Kernel.EtaFamiliesClosed.cons_nonind hEE hfresh (fun _ _ h => nomatch h),
    envExt_cons_fresh hfresh (ne_projTableName_auxKey_model n ·),
    fun k hk => ?_⟩
  have hne : k ≠ auxKey n .model := fun heq => by rw [heq, hfresh] at hk; exact nomatch hk
  rw [hac, show c₀.name = auxKey n .model from rfl, acvalWith_ne hne]

/-! ## `noLetExpr` on `TmExact` and Reflexive `Annot` -/

/-- Whether an expression contains no syntactic `.letE` node. -/
def noLetExpr : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => noLetExpr ty
  | .app f a => noLetExpr f && noLetExpr a
  | .lam ty b _ | .forallE ty b _ => noLetExpr ty && noLetExpr b
  | .letE _ _ _ _ => false
  | .proj _ _ e => noLetExpr e

theorem noLetExpr_liftLooseBVars (n : Nat) :
    ∀ (e : KExpr) (c : Nat), noLetExpr (e.liftLooseBVars n c) = noLetExpr e
  | .bvar i, c => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, c => by
    simp only [Expr.liftLooseBVars, noLetExpr,
      noLetExpr_liftLooseBVars n f c, noLetExpr_liftLooseBVars n a c]
  | .lam ty b _, c | .forallE ty b _, c => by
    simp only [Expr.liftLooseBVars, noLetExpr,
      noLetExpr_liftLooseBVars n ty c, noLetExpr_liftLooseBVars n b (c + 1)]
  | .letE _ _ _ _, _ => rfl
  | .proj _ _ e, c => noLetExpr_liftLooseBVars n e c

theorem noLetExpr_instShift {v : KExpr} (hv : noLetExpr v = true)
    (k : Nat) {b : KExpr} (hb : noLetExpr b = true) :
    noLetExpr (instShift v k b) = true := by
  induction b generalizing k with
  | bvar _ =>
    simp only [instShift, Expr.instantiate1Lift]
    split
    · rw [noLetExpr_liftLooseBVars]; exact hv
    · split <;> rfl
  | sort _ | const _ _ | lit _ => rfl
  | fvar _ _ => exact hb
  | app _ _ ihf iha =>
    simp only [noLetExpr, Bool.and_eq_true] at hb
    simp only [instShift, Expr.instantiate1Lift, noLetExpr, Bool.and_eq_true]
    exact ⟨ihf k hb.1, iha k hb.2⟩
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    simp only [noLetExpr, Bool.and_eq_true] at hb
    simp only [instShift, Expr.instantiate1Lift, noLetExpr, Bool.and_eq_true]
    exact ⟨iht k hb.1, ihb (k + 1) hb.2⟩
  | letE _ _ _ _ => exact nomatch hb
  | proj _ _ _ ihe => exact ihe k hb

theorem noLetExpr_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ e : KExpr, noLetExpr (e.instantiateLevelParams ks us) = noLetExpr e
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ ty => noLetExpr_instantiateLevelParams ks us ty
  | .app f a => by
    simp only [Expr.instantiateLevelParams, noLetExpr,
      noLetExpr_instantiateLevelParams ks us f, noLetExpr_instantiateLevelParams ks us a]
  | .lam ty b _ | .forallE ty b _ => by
    simp only [Expr.instantiateLevelParams, noLetExpr,
      noLetExpr_instantiateLevelParams ks us ty, noLetExpr_instantiateLevelParams ks us b]
  | .letE _ _ _ _ => rfl
  | .proj _ _ e => noLetExpr_instantiateLevelParams ks us e

theorem TmExact.noLet {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F}
    (hΓ : ∀ j, j < d → noLetExpr (Γ j) = true)
    (rep : TmExact κ d Γ h k E p) :
    noLetExpr E = true := by
  induction rep with
  | bvarLocal => rfl
  | @bvarFree k₀ _ i _ _ hk hd =>
    exact hΓ (fvIdx d k₀ (ZMod.val i)) (by unfold fvIdx; omega)
  | sort | const | litNat | litStr => rfl
  | app _ _ _ ihf iha => simp only [noLetExpr, ihf, iha]; rfl
  | lam _ _ _ _ iht ihb => simp only [noLetExpr, iht, ihb]; rfl
  | forallE _ _ _ _ iht ihb => simp only [noLetExpr, iht, ihb]; rfl
  | letE _ _ _ _ _ ihv ihb => exact noLetExpr_instShift ihv 0 ihb
  | proj _ _ _ ihe => exact ihe

theorem TmCExact.noLet {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr} {p : SourceValue F}
    (rep : TmCExact κ h E p) : noLetExpr E = true :=
  (rep 0 (fun _ => .sort .zero)).noLet (fun _ hlt => absurd hlt (Nat.not_lt_zero _))

theorem annotates_refl_of_noLetExpr {e : KExpr} (h : noLetExpr e = true) :
    IxVM.Consistency.Annotates e e := by
  induction e with
  | bvar _ => exact .bvar
  | sort _ => exact .sort
  | const _ _ => exact .const
  | lit _ => exact .lit
  | fvar _ _ ih => exact .fvar (ih h)
  | app _ _ ihf iha =>
    simp only [noLetExpr, Bool.and_eq_true] at h
    exact .app (ihf h.1) (iha h.2)
  | lam _ _ _ iht ihb =>
    simp only [noLetExpr, Bool.and_eq_true] at h
    exact .lam (iht h.1) (ihb h.2)
  | forallE _ _ _ iht ihb =>
    simp only [noLetExpr, Bool.and_eq_true] at h
    exact .forallE (iht h.1) (ihb h.2)
  | letE _ _ _ _ => exact nomatch h
  | proj _ _ _ ihe => exact .proj (ihe h)

theorem annot_refl_of_noLetExpr {e : KExpr} (hnl : noLetExpr e = true)
    (hf : e.hasFvar = false) (hb : e.looseBVarsBounded 0 = true) (d : Nat) :
    Annot d e e :=
  annot_of_annotates (annotates_refl_of_noLetExpr hnl) hf hb d

/-! ## Phase 2: Positional Translation of `RawIotaRuleVmRun` to `IotaRulesNVmRunJ posRulesJ` -/

theorem allLevelParamsDefined_posOf {lps : List LevelParam} {e : KExpr}
    (h : e.allLevelParamsDefined lps = true) :
    (posOf lps e).allLevelParamsDefined (List.range lps.length) = true := by
  refine allLevelParamsDefined_instantiateLevelParams ?_ (by simp [posLevels]) h
  intro u hu
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
  simpa [Level.allParamsDefined] using hi

theorem hasFvar_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ e : KExpr, (e.instantiateLevelParams ks us).hasFvar = e.hasFvar
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lit _ => rfl
  | .app f a => by
    simp only [Expr.instantiateLevelParams, Expr.hasFvar,
      hasFvar_instantiateLevelParams ks us f, hasFvar_instantiateLevelParams ks us a]
  | .lam ty b _ | .forallE ty b _ => by
    simp only [Expr.instantiateLevelParams, Expr.hasFvar,
      hasFvar_instantiateLevelParams ks us ty, hasFvar_instantiateLevelParams ks us b]
  | .letE ty v b _ => by
    simp only [Expr.instantiateLevelParams, Expr.hasFvar,
      hasFvar_instantiateLevelParams ks us ty,
      hasFvar_instantiateLevelParams ks us v,
      hasFvar_instantiateLevelParams ks us b]
  | .proj _ _ e => hasFvar_instantiateLevelParams ks us e

theorem looseBVarsBounded_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (d : Nat) (e : KExpr),
      (e.instantiateLevelParams ks us).looseBVarsBounded d = e.looseBVarsBounded d
  | _, .bvar _ | _, .fvar _ _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl
  | d, .app f a => by
    simp only [Expr.instantiateLevelParams, Expr.looseBVarsBounded,
      looseBVarsBounded_instantiateLevelParams ks us d f,
      looseBVarsBounded_instantiateLevelParams ks us d a]
  | d, .lam ty b _ | d, .forallE ty b _ => by
    simp only [Expr.instantiateLevelParams, Expr.looseBVarsBounded,
      looseBVarsBounded_instantiateLevelParams ks us d ty,
      looseBVarsBounded_instantiateLevelParams ks us (d + 1) b]
  | d, .letE ty v b _ => by
    simp only [Expr.instantiateLevelParams, Expr.looseBVarsBounded,
      looseBVarsBounded_instantiateLevelParams ks us d ty,
      looseBVarsBounded_instantiateLevelParams ks us d v,
      looseBVarsBounded_instantiateLevelParams ks us (d + 1) b]
  | d, .proj _ _ e => looseBVarsBounded_instantiateLevelParams ks us d e

theorem constsResolve_instantiateLevelParams (env : Env .anon)
    (ks : List LevelParam) (us : List KLevel) :
    ∀ e : KExpr, (e.instantiateLevelParams ks us).constsResolve env = e.constsResolve env
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ ty => constsResolve_instantiateLevelParams env ks us ty
  | .app f a => by
    simp only [Expr.instantiateLevelParams, Expr.constsResolve,
      constsResolve_instantiateLevelParams env ks us f,
      constsResolve_instantiateLevelParams env ks us a]
  | .lam ty b _ | .forallE ty b _ => by
    simp only [Expr.instantiateLevelParams, Expr.constsResolve,
      constsResolve_instantiateLevelParams env ks us ty,
      constsResolve_instantiateLevelParams env ks us b]
  | .letE ty v b _ => by
    simp only [Expr.instantiateLevelParams, Expr.constsResolve,
      constsResolve_instantiateLevelParams env ks us ty,
      constsResolve_instantiateLevelParams env ks us v,
      constsResolve_instantiateLevelParams env ks us b]
  | .proj _ _ e => by
    simp only [Expr.instantiateLevelParams, Expr.constsResolve,
      constsResolve_instantiateLevelParams env ks us e]

private theorem stripPis_body_wf {env : Env .anon} {ps : List LevelParam}
    (k d : Nat) {e : KExpr} {bs : List (KExpr × BinderMeta)} {body : KExpr}
    (h : e.stripPis k = some (bs, body))
    (hf : e.hasFvar = false)
    (hb : e.looseBVarsBounded d = true)
    (hcr : e.constsResolve env = true)
    (hlps : e.allLevelParamsDefined ps = true) :
    body.hasFvar = false ∧
    body.looseBVarsBounded (d + k) = true ∧
    body.constsResolve env = true ∧
    body.allLevelParamsDefined ps = true := by
  induction k generalizing d e bs body with
  | zero =>
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simpa using ⟨hf, hb, hcr, hlps⟩
  | succ k ih =>
    cases e with
    | forallE ty b _ =>
      simp only [Expr.stripPis] at h
      cases hsb : b.stripPis k with
      | none => rw [hsb] at h; exact nomatch h
      | some p =>
        rw [hsb] at h
        obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
        simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
        simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hlps
        have hrec := ih (d + 1) hsb hf.2 hb.2 hcr.2 hlps.1.2
        rwa [show d + 1 + k = d + (k + 1) by omega] at hrec
    | _ => exact nomatch h

private theorem app_spine_wf {env : Env .anon} {ps : List LevelParam} {d : Nat} :
    ∀ (e : KExpr),
      e.hasFvar = false →
      e.looseBVarsBounded d = true →
      e.constsResolve env = true →
      e.allLevelParamsDefined ps = true →
      e.getAppFn.allLevelParamsDefined ps = true ∧
      e.getAppFn.constsResolve env = true ∧
      ∀ a ∈ e.getAppArgs,
        a.hasFvar = false ∧
        a.looseBVarsBounded d = true ∧
        a.constsResolve env = true ∧
        a.allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro hf hb hcr hlps
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hlps
    obtain ⟨hfn_lp, hfn_cr, hargs⟩ := ihf hf.1 hb.1 hcr.1 hlps.1
    have hfn_eq : (Expr.app f a).getAppFn = f.getAppFn := rfl
    have hargs_eq : (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] := rfl
    refine ⟨hfn_eq ▸ hfn_lp, hfn_eq ▸ hfn_cr, fun x hx => ?_⟩
    rw [hargs_eq] at hx
    rcases List.mem_append.mp hx with hxf | hxa
    · exact hargs x hxf
    · rw [List.mem_singleton.mp hxa]
      exact ⟨hf.2, hb.2, hcr.2, hlps.2⟩
  | bvar _ | fvar _ _ | sort _ | const _ _ | lam _ _ _ | forallE _ _ _ | letE _ _ _ _
  | lit _ | proj _ _ _ =>
    intro _ _ hcr hlps
    have hargs : ∀ a : KExpr, a ∈ ([] : List KExpr) →
        a.hasFvar = false ∧ a.looseBVarsBounded d = true ∧
        a.constsResolve env = true ∧ a.allLevelParamsDefined ps = true :=
      fun _ hm => nomatch hm
    exact ⟨hlps, hcr, hargs⟩

private theorem constsResolve_instantiate1 {env : Env .anon} {v : KExpr}
    (hv : v.constsResolve env = true) :
    ∀ (e : KExpr) (k : Nat),
      e.constsResolve env = true → (e.instantiate1 v k).constsResolve env = true
  | .bvar i, k => by
    intro _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => fun h => h
  | .app f a, k => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨constsResolve_instantiate1 hv f k h.1, constsResolve_instantiate1 hv a k h.2⟩
  | .lam ty b _, k | .forallE ty b _, k => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨constsResolve_instantiate1 hv ty k h.1, constsResolve_instantiate1 hv b (k + 1) h.2⟩
  | .letE ty val b _, k => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨⟨constsResolve_instantiate1 hv ty k h.1.1,
      constsResolve_instantiate1 hv val k h.1.2⟩,
      constsResolve_instantiate1 hv b (k + 1) h.2⟩
  | .proj s idx e, k => fun h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨h.1, constsResolve_instantiate1 hv e k h.2⟩

private theorem constsResolve_openPisAtFvars {env : Env .anon}
    (n : Nat) {e : KExpr} (i : Nat) {fvs : List KExpr} {body : KExpr}
    (h : openPisAtFvars n e i = some (fvs, body))
    (hcr : e.constsResolve env = true) :
    body.constsResolve env = true := by
  induction n generalizing e i fvs body with
  | zero =>
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hcr
  | succ n ih =>
    cases e with
    | forallE dom b _ =>
      simp only [openPisAtFvars] at h
      simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
      have hb' : (b.instantiate1 (.fvar i dom)).constsResolve env = true :=
        constsResolve_instantiate1 (v := .fvar i dom) hcr.1 b 0 hcr.2
      cases hop : openPisAtFvars n (b.instantiate1 (.fvar i dom)) (i + 1) with
      | none => rw [hop] at h; exact nomatch h
      | some p =>
        rw [hop] at h
        obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ih (i + 1) hop hb'
    | _ => exact nomatch h

/-- Extract `c_adv.env.find? eqName = some eqA` whenever a recursor has at least one rule,
because rule `0`'s advice theorem opens to an `Eq`-headed equality in `c_adv.env`. -/
theorem eqA_of_rawRule {V : Type u} [Ix.Kernel.SetTheory V]
    {c_pub c_rhs c_adv : Ctx}
    (mp_adv : EnvModelM V .verified c_adv.env)
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {lvls_lps : List KLevel} {pins_lps : List KExpr}
    {j : Nat} {r : RecRule .anon}
    (hlps_perm : lps.Perm (List.range lps.length))
    (hraw : RawIotaRuleVmRun c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j r) :
    c_adv.env.find? eqName = some eqA := by
  have hmem_t : ConstantInfo.thmInfo hraw.cvt hraw.vt ∈ c_adv.env.consts :=
    Ix.Kernel.Semantics.Env.find?_mem hraw.hfind_t
  have hcr_cvt : hraw.cvt.type.constsResolve c_adv.env = true :=
    (mp_adv.base2.wf _ hmem_t).2.2.1
  have hop_pos := openPisAtFvars_instantiateLevelParams lps (posLevels lps) (rP + hraw.cnF)
    (invPosOf lps hraw.cvt.type) 0
  rw [hraw.hopen_t, Option.map_some, show (invPosOf lps hraw.cvt.type).instantiateLevelParams
      lps (posLevels lps) = hraw.cvt.type from posOf_invPosOf hlps_perm hraw.cvt.type] at hop_pos
  have hcr_tbody : (posOf lps hraw.tbody).constsResolve c_adv.env = true :=
    constsResolve_openPisAtFvars (rP + hraw.cnF) 0 hop_pos hcr_cvt
  have hfn_pos : (posOf lps hraw.tbody).getAppFn =
      .const eqName [Level.subst lps (posLevels lps) hraw.ell_lps] := by
    show (hraw.tbody.instantiateLevelParams lps (posLevels lps)).getAppFn = _
    rw [Ix.Kernel.Expr.getAppFn_instantiateLevelParams, hraw.heq_head]
    rfl
  have hcr_fn : ((posOf lps hraw.tbody).getAppFn).constsResolve c_adv.env = true := by
    have hfn_cr : ∀ e : KExpr, e.constsResolve c_adv.env = true →
        e.getAppFn.constsResolve c_adv.env = true := by
      intro e
      induction e with
      | app f a ih =>
        intro hh
        simp only [Expr.constsResolve, Bool.and_eq_true] at hh
        exact ih hh.1
      | _ => exact id
    exact hfn_cr _ hcr_tbody
  rw [hfn_pos] at hcr_fn
  obtain ⟨ciE, hfE⟩ := Option.isSome_iff_exists.mp hcr_fn
  have hci : ciE = eqA := by
    rw [(mp_adv.base2.basis_pinned eqName ciE hfE reserved_eqName).1]
    simp [Ix.Kernel.pinnedInfo]
  rwa [hci] at hfE

/-- Lift a single `RawIotaRuleVmRun` certificate to `IotaRuleNVmRunJ posRulesJ` at positional
level parameters `List.range lps.length`. -/
theorem rawIotaRule_to_posNVmRun
    {c_pub c_rhs c_adv : Ctx} {envM_pos envSelf_pos : Env .anon}
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {lvls_lps : List KLevel} {pins_lps : List KExpr}
    {indKey : KKey} {cnP_ind : Nat}
    {bs : List (KExpr × BinderMeta)} {dom body : KExpr} {mb : BinderMeta}
    {j : Nat} {r : RecRule .anon}
    (hlps_perm : lps.Perm (List.range lps.length))
    (hrp_le : rP ≤ mI)
    (hrhs_nolet : noLetExpr (posOf lps r.rhs) = true)
    (hty_wf :
      (posOf lps tyA).hasFvar = false ∧
      (posOf lps tyA).looseBVarsBounded 0 = true ∧
      (posOf lps tyA).constsResolve envSelf_pos = true ∧
      (posOf lps tyA).allLevelParamsDefined (List.range lps.length) = true)
    (hctor_wf : ∀ cvj cnP cnF, c_pub.env.find? r.ctor = some (.ctorInfo cvj cnP cnF) →
      cvj.type.allLevelParamsDefined cvj.levelParams = true)
    (hstrip_ty : tyA.stripPis mI = some (bs, .forallE dom body mb))
    (hdom_fn : dom.getAppFn = .const indKey lvls_lps)
    (hdom_len : dom.getAppArgs.length = cnP_ind + (mI - rP))
    (hdom_nli : ∀ p ∈ dom.getAppArgs.take cnP_ind, noLooseIn 0 (mI - rP) p = true)
    (hdom_drop : dom.getAppArgs.drop cnP_ind =
      (List.range (mI - rP)).map (fun m => .bvar (mI - rP - 1 - m)))
    (hpins_def : pins_lps = (dom.getAppArgs.take cnP_ind).map (Expr.lowerBVars (mI - rP) 0))
    (hfind_pub_M : ∀ k ci, c_pub.env.find? k = some ci → envM_pos.find? k = some ci)
    (hext_pub : EnvExt c_pub.env envSelf_pos)
    (hext_adv : EnvExt c_adv.env envSelf_pos)
    (hraw : RawIotaRuleVmRun c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j r)
    (hrhs_cr : (posOf lps r.rhs).constsResolve envSelf_pos = true)
    (hrhs_typed : ∃ t', posRulesJ.infer envSelf_pos 0 (posOf lps r.rhs) t')
    (hfind_iota : envM_pos.findCV? (auxKey (auxKey cvName .model) (.iota j)) =
      some ⟨auxKey (auxKey cvName .model) (.iota j), List.range lps.length, hraw.cvt.type⟩) :
    let lvls_pos := lvls_lps.map (Level.subst lps (posLevels lps))
    let pins_pos := pins_lps.map (posOf lps)
    let rhs_pos := posOf lps r.rhs
    let r_pos : RecRule .anon :=
      RecRule.mk r.ctor r.nfields r.ctorParams r.fire rhs_pos r.k r.eta r.paramsBlind
    let r'_pos : RecRule .anon :=
      recRuleBits envM_pos.find? cvName
        (RecRule.mk r.ctor r.nfields hraw.cnP (.nested lvls_pos pins_pos) rhs_pos r.k r.eta false)
    IotaRuleNVmRunJ posRulesJ envM_pos envSelf_pos f_id cvName (List.range lps.length)
      (posOf lps tyA) mI rP j r_pos r'_pos ∧
    hraw.cnP = cnP_ind := by
  let lvls_pos := lvls_lps.map (Level.subst lps (posLevels lps))
  let pins_pos := pins_lps.map (posOf lps)
  let ty_pos := posOf lps tyA
  let rhs_pos := posOf lps r.rhs
  let r_pos : RecRule .anon :=
    RecRule.mk r.ctor r.nfields r.ctorParams r.fire rhs_pos r.k r.eta r.paramsBlind
  let r'_pos : RecRule .anon :=
    recRuleBits envM_pos.find? cvName
      (RecRule.mk r.ctor r.nfields hraw.cnP (.nested lvls_pos pins_pos) rhs_pos r.k r.eta false)
  have hlps_nd : lps.Nodup := hlps_perm.nodup_iff.mpr List.nodup_range
  have hcnp_eq : hraw.cnP = cnP_ind := by
    have h1 : pins_lps.length = cnP_ind := by
      rw [hpins_def, List.length_map, List.length_take, hdom_len]
      omega
    exact hraw.hpins_len.symm.trans h1
  have hrhs_bvars : rhs_pos.looseBVarsBounded 0 = true := by
    show (r.rhs.instantiateLevelParams lps (posLevels lps)).looseBVarsBounded 0 = true
    rw [looseBVarsBounded_instantiateLevelParams]
    exact hraw.hrhs_bvars
  have hrhs_nofvar : rhs_pos.hasFvar = false := by
    show (r.rhs.instantiateLevelParams lps (posLevels lps)).hasFvar = false
    rw [hasFvar_instantiateLevelParams]
    exact hraw.hrhs_nofvar
  have hrhs_annot : Annot 0 rhs_pos rhs_pos :=
    annot_refl_of_noLetExpr hrhs_nolet hrhs_nofvar hrhs_bvars 0
  have hrhs_lvls : rhs_pos.allLevelParamsDefined (List.range lps.length) = true :=
    allLevelParamsDefined_posOf hraw.hrhs_lvls
  have hrhs_lams : (rhs_pos.stripLams (rP + hraw.cnF)).isSome = true := by
    show ((r.rhs.instantiateLevelParams lps (posLevels lps)).stripLams (rP + hraw.cnF)).isSome = true
    rw [stripLams_instantiateLevelParams_isSome]
    exact hraw.hrhs_lams
  have hfind_ctor_M : envM_pos.find? r_pos.ctor = some (.ctorInfo hraw.cvj hraw.cnP hraw.cnF) :=
    hfind_pub_M _ _ hraw.hfind_ctor
  -- Prove `nestedRuleShape` at `ty_pos`
  have hshape : nestedRuleShape envM_pos envSelf_pos cvName (List.range lps.length) ty_pos
      mI rP hraw.cnP j = some (lvls_pos, pins_pos) := by
    have hiota_some : (envM_pos.findCV? (auxKey (auxKey cvName .model) (.iota j))).isSome = true := by
      rw [hfind_iota]; rfl
    have hstrip_pos : ty_pos.stripPis mI = some
        (bs.map (fun bm => (posOf lps bm.1, { bm.2 with pw := Level.substPW lps (posLevels lps) bm.2.pw })),
         .forallE (posOf lps dom) (posOf lps body) { mb with pw := Level.substPW lps (posLevels lps) mb.pw }) := by
      have h := stripPis_instantiateLevelParams_full lps (posLevels lps) mI tyA
      rw [hstrip_ty, Option.map_some] at h
      exact h
    have hdom_fn_pos : (posOf lps dom).getAppFn = .const indKey lvls_pos := by
      show (dom.instantiateLevelParams lps (posLevels lps)).getAppFn = _
      rw [Ix.Kernel.Expr.getAppFn_instantiateLevelParams, hdom_fn]
      rfl
    have hdom_args_pos : (posOf lps dom).getAppArgs = dom.getAppArgs.map (posOf lps) :=
      Ix.Kernel.Expr.getAppArgs_instantiateLevelParams lps (posLevels lps) dom
    have hforall_wf := stripPis_body_wf mI 0 hstrip_pos hty_wf.1 hty_wf.2.1 hty_wf.2.2.1 hty_wf.2.2.2
    simp only [Expr.hasFvar, Bool.or_eq_false_iff, Expr.looseBVarsBounded,
      Expr.constsResolve, Expr.allLevelParamsDefined, Bool.and_eq_true] at hforall_wf
    have hdom_wf : (posOf lps dom).hasFvar = false ∧
        (posOf lps dom).looseBVarsBounded mI = true ∧
        (posOf lps dom).constsResolve envSelf_pos = true ∧
        (posOf lps dom).allLevelParamsDefined (List.range lps.length) = true :=
      ⟨hforall_wf.1.1, by simpa using hforall_wf.2.1.1, hforall_wf.2.2.1.1, hforall_wf.2.2.2.1.1⟩
    obtain ⟨hfn_lp, _, hargs_wf⟩ := app_spine_wf (posOf lps dom)
      hdom_wf.1 hdom_wf.2.1 hdom_wf.2.2.1 hdom_wf.2.2.2
    rw [hdom_fn_pos] at hfn_lp
    have hlvls_all : lvls_pos.all (Level.allParamsDefined (List.range lps.length)) = true := hfn_lp
    have hpins_eq : ((posOf lps dom).getAppArgs.take hraw.cnP).map (Expr.lowerBVars (mI - rP) 0) =
        pins_pos := by
      rw [hcnp_eq, hdom_args_pos, ← List.map_take, List.map_map, hpins_def, List.map_map]
      apply List.map_congr_left
      intro p _
      exact (instantiateLevelParams_lowerBVars lps (posLevels lps) p (mI - rP) 0).symm
    have htake_eq : ((posOf lps dom).getAppArgs.take hraw.cnP ==
        pins_pos.map (Expr.liftLooseBVars (mI - rP) 0)) = true := by
      apply beq_iff_eq.mpr
      rw [hcnp_eq, hdom_args_pos, ← List.map_take]
      simp only [pins_pos, hpins_def, List.map_map]
      apply List.map_congr_left
      intro p hp
      show posOf lps p = (posOf lps (p.lowerBVars (mI - rP) 0)).liftLooseBVars (mI - rP) 0
      rw [← instantiateLevelParams_liftLooseBVars,
        liftLooseBVars_lowerBVars_of_noLooseIn (hdom_nli p hp)]
    have hdrop_eq : ((posOf lps dom).getAppArgs.drop hraw.cnP ==
        (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i))) = true := by
      apply beq_iff_eq.mpr
      rw [hcnp_eq, hdom_args_pos, ← List.map_drop, hdom_drop, List.map_map]
      rfl
    have hpins_all : pins_pos.all (fun p =>
        !p.hasFvar && p.looseBVarsBounded rP && p.constsResolve envSelf_pos &&
          p.allLevelParamsDefined (List.range lps.length)) = true := by
      rw [← hpins_eq, List.all_eq_true]
      intro q hq
      obtain ⟨arg, harg_tk, rfl⟩ := List.mem_map.mp hq
      have harg_mem : arg ∈ (posOf lps dom).getAppArgs := List.mem_of_mem_take harg_tk
      obtain ⟨haf, hab, hacr, halp⟩ := hargs_wf arg harg_mem
      have hnli_arg : noLooseIn 0 (mI - rP) arg = true := by
        rw [hcnp_eq, hdom_args_pos, ← List.map_take] at harg_tk
        obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp harg_tk
        show noLooseIn 0 (mI - rP) (p₀.instantiateLevelParams lps (posLevels lps)) = true
        rw [noLooseIn_instantiateLevelParams]
        exact hdom_nli p₀ hp₀
      have h1 : !(arg.lowerBVars (mI - rP) 0).hasFvar = true := by
        rw [hasFvar_lowerBVars, haf]; rfl
      have h2 : (arg.lowerBVars (mI - rP) 0).looseBVarsBounded rP = true := by
        have hab' : arg.looseBVarsBounded (rP + 0 + (mI - rP)) = true := by
          rwa [show rP + 0 + (mI - rP) = mI by omega]
        exact looseBVarsBounded_lowerBVars (rp := rP) hnli_arg hab'
      have h3 : (arg.lowerBVars (mI - rP) 0).constsResolve envSelf_pos = true := by
        rw [constsResolve_lowerBVars]; exact hacr
      have h4 : (arg.lowerBVars (mI - rP) 0).allLevelParamsDefined (List.range lps.length) = true := by
        rw [allLevelParamsDefined_lowerBVars]; exact halp
      simp [h1, h2, h3, h4]
    have hlen_args : (posOf lps dom).getAppArgs.length = hraw.cnP + (mI - rP) := by
      rw [hdom_args_pos, List.length_map, hdom_len, hcnp_eq]
    unfold nestedRuleShape
    rw [ite_eq_left ⟨hiota_some, hrp_le⟩, hstrip_pos]
    dsimp only
    rw [hdom_fn_pos]
    dsimp only
    rw [hpins_eq, ite_eq_left ⟨hlen_args, htake_eq, hdrop_eq, hpins_all, hlvls_all⟩]
  -- Assemble `IotaThmNVmRunJ`
  have hcvj_lps : hraw.cvj.type.allLevelParamsDefined hraw.cvj.levelParams = true :=
    hctor_wf hraw.cvj hraw.cnP hraw.cnF hraw.hfind_ctor
  have hcty_pos : posOf lps (hraw.cvj.type.instantiateLevelParams hraw.cvj.levelParams lvls_lps) =
      hraw.cvj.type.instantiateLevelParams hraw.cvj.levelParams lvls_pos :=
    instantiateLevelParams_comp hraw.hlvls_len hcvj_lps
  have hop_t_pos : openPisAtFvars (rP + hraw.cnF) hraw.cvt.type 0 =
      some (hraw.fvs.map (posOf lps), posOf lps hraw.tbody) := by
    have h := openPisAtFvars_instantiateLevelParams lps (posLevels lps) (rP + hraw.cnF)
      (invPosOf lps hraw.cvt.type) 0
    rw [hraw.hopen_t, Option.map_some,
      show (invPosOf lps hraw.cvt.type).instantiateLevelParams lps (posLevels lps) = hraw.cvt.type
        from posOf_invPosOf hlps_perm hraw.cvt.type] at h
    exact h
  let fvs_pos := hraw.fvs.map (posOf lps)
  let tbody_pos := posOf lps hraw.tbody
  have heqH_pos : isEqHead tbody_pos.getAppFn = true := by
    have h : tbody_pos.getAppFn = .const eqName [Level.subst lps (posLevels lps) hraw.ell_lps] := by
      show (hraw.tbody.instantiateLevelParams lps (posLevels lps)).getAppFn = _
      rw [Ix.Kernel.Expr.getAppFn_instantiateLevelParams, hraw.heq_head]
      rfl
    rw [h]; rfl
  have htargs_pos : tbody_pos.getAppArgs = hraw.tbody.getAppArgs.map (posOf lps) :=
    Ix.Kernel.Expr.getAppArgs_instantiateLevelParams lps (posLevels lps) hraw.tbody
  have htargs_len_pos : tbody_pos.getAppArgs.length = 3 := by
    rw [htargs_pos, List.length_map, hraw.htargs_len]
  have hgetD_pos : ∀ k, k < 3 →
      tbody_pos.getAppArgs.getD k (.bvar 0) =
        posOf lps (hraw.tbody.getAppArgs.getD k (.bvar 0)) := by
    intro k hk
    rw [htargs_pos]
    have hk' : k < hraw.tbody.getAppArgs.length := by rw [hraw.htargs_len]; exact hk
    simp [List.getD, List.getElem?_eq_getElem hk', List.getElem?_map]
  have hlhs_pos : tbody_pos.getAppArgs.getD 1 (.bvar 0) =
      posOf lps (hraw.tbody.getAppArgs.getD 1 (.bvar 0)) := hgetD_pos 1 (by omega)
  have hrhsS_pos : tbody_pos.getAppArgs.getD 2 (.bvar 0) =
      posOf lps (hraw.tbody.getAppArgs.getD 2 (.bvar 0)) := hgetD_pos 2 (by omega)
  have htyArg_pos : tbody_pos.getAppArgs.getD 0 (.bvar 0) =
      posOf lps (hraw.tbody.getAppArgs.getD 0 (.bvar 0)) := hgetD_pos 0 (by omega)
  let lhsS := hraw.tbody.getAppArgs.getD 1 (.bvar 0)
  let lhsS_pos := tbody_pos.getAppArgs.getD 1 (.bvar 0)
  have hlhs_fn_pos : (lhsS_pos.getAppFn ==
      Expr.const (f_id cvName) ((List.range lps.length).map .param)) = true := by
    apply beq_iff_eq.mpr
    change (tbody_pos.getAppArgs.getD 1 (.bvar 0)).getAppFn = _
    rw [hlhs_pos,
      show (posOf lps lhsS).getAppFn = posOf lps lhsS.getAppFn from
        Ix.Kernel.Expr.getAppFn_instantiateLevelParams lps (posLevels lps) lhsS,
      hraw.hlhs_fn]
    exact posOf_const_self_levels lps (f_id cvName) hlps_nd
  have hlargs_pos : lhsS_pos.getAppArgs = lhsS.getAppArgs.map (posOf lps) := by
    change (tbody_pos.getAppArgs.getD 1 (.bvar 0)).getAppArgs = _
    rw [hlhs_pos]
    exact Ix.Kernel.Expr.getAppArgs_instantiateLevelParams lps (posLevels lps) lhsS
  have hlargs_len_pos : lhsS_pos.getAppArgs.length = mI + 1 := by
    rw [hlargs_pos, List.length_map, hraw.hlargs_len]
  have hlargs_pre_pos : (lhsS_pos.getAppArgs.take rP == fvs_pos.take rP) = true := by
    apply beq_iff_eq.mpr
    rw [hlargs_pos, ← List.map_take, hraw.hlargs_pre, List.map_take]
  have hpinsF_pos :
      ((pins_lps.map fun p => Expr.instSpine (hraw.fvs.take rP) (rP - 1) (p.renameConsts f_id)) ++
        hraw.fvs.drop rP).map (posOf lps) =
      (pins_pos.map fun p => Expr.instSpine (fvs_pos.take rP) (rP - 1) (p.renameConsts f_id)) ++
        fvs_pos.drop rP := by
    rw [List.map_append, List.map_drop, List.map_map, List.map_map, ← List.map_take]
    congr 1
    apply List.map_congr_left
    intro p _
    show (Expr.instSpine (hraw.fvs.take rP) (rP - 1) (p.renameConsts f_id)).instantiateLevelParams
        lps (posLevels lps) = _
    rw [instantiateLevelParams_instSpine, instantiateLevelParams_renameConsts]
    rfl
  have hmajor_pos : Expr.ErasedEq (lhsS_pos.getAppArgs.getLastD (.bvar 0))
      (Expr.mkAppN (.const (f_id r_pos.ctor) lvls_pos)
        ((pins_pos.map fun p => Expr.instSpine (fvs_pos.take rP) (rP - 1) (p.renameConsts f_id)) ++
          fvs_pos.drop rP)) := by
    apply Expr.ErasedEq.of_eq
    have hne : lhsS.getAppArgs ≠ [] := by
      intro he
      have hl := hraw.hlargs_len
      rw [he] at hl
      exact nomatch hl
    have hlast : lhsS_pos.getAppArgs.getLastD (.bvar 0) =
        posOf lps (lhsS.getAppArgs.getLastD (.bvar 0)) := by
      rw [hlargs_pos]
      exact getLastD_map_of_ne_nil (posOf lps) (.bvar 0) (.bvar 0) hne
    rw [hlast, hraw.hmajor_eq]
    show ((Expr.mkAppN (.const (f_id r.ctor) lvls_lps) _).instantiateLevelParams lps (posLevels lps)) = _
    rw [mkAppN_instantiateLevelParams, fold_posOf lps, hpinsF_pos]
    rfl
  have hinst_c_pos : Expr.instPisAt
      ((pins_pos.map fun p => Expr.instSpine (fvs_pos.take rP) (rP - 1) (p.renameConsts f_id)) ++
        fvs_pos.drop rP)
      ((hraw.cvj.type.instantiateLevelParams hraw.cvj.levelParams lvls_pos).renameConsts f_id) =
      some (hraw.cdoms.map (posOf lps), posOf lps hraw.cres) := by
    have h := instPisAt_instantiateLevelParams lps (posLevels lps)
      ((pins_lps.map fun p => Expr.instSpine (hraw.fvs.take rP) (rP - 1) (p.renameConsts f_id)) ++
        hraw.fvs.drop rP)
      ((hraw.cvj.type.instantiateLevelParams hraw.cvj.levelParams lvls_lps).renameConsts f_id)
    rw [fold_posOf lps, hraw.hinst_c, Option.map_some, hpinsF_pos,
      instantiateLevelParams_renameConsts] at h
    rwa [show (hraw.cvj.type.instantiateLevelParams hraw.cvj.levelParams lvls_lps).instantiateLevelParams
        lps (posLevels lps) = hraw.cvj.type.instantiateLevelParams hraw.cvj.levelParams lvls_pos
        from hcty_pos] at h
  have hcres_len_pos : (posOf lps hraw.cres).getAppArgs.length = hraw.cnP + (mI - rP) := by
    show (hraw.cres.instantiateLevelParams lps (posLevels lps)).getAppArgs.length = _
    rw [Ix.Kernel.Expr.getAppArgs_instantiateLevelParams, List.length_map, hraw.hcres_len]
  have hinst_r_pos : Expr.instPisAt (fvs_pos.take rP) (ty_pos.renameConsts f_id) =
      some (hraw.rdoms.map (posOf lps), posOf lps hraw.lrest) := by
    have h := instPisAt_instantiateLevelParams lps (posLevels lps) (hraw.fvs.take rP)
      (tyA.renameConsts f_id)
    rw [fold_posOf lps, hraw.hinst_r, Option.map_some, List.map_take,
      instantiateLevelParams_renameConsts] at h
    exact h
  have hopen_p_pos : openPisAtFvars rP ty_pos 0 =
      some (hraw.fvsP.map (posOf lps), posOf lps hraw.crest2) := by
    have h := openPisAtFvars_instantiateLevelParams lps (posLevels lps) rP tyA 0
    rw [fold_posOf lps, hraw.hopen_p, Option.map_some] at h
    exact h
  let fvsP_pos := hraw.fvsP.map (posOf lps)
  have hpinsP_pos :
      (pins_lps.map fun p => Expr.instSpine (hraw.fvsP.take rP) (rP - 1) p).map (posOf lps) =
      (pins_pos.map fun p => Expr.instSpine (fvsP_pos.take rP) (rP - 1) p) := by
    rw [List.map_map, List.map_map, ← List.map_take]
    apply List.map_congr_left
    intro p _
    exact instantiateLevelParams_instSpine lps (posLevels lps) (hraw.fvsP.take rP) (rP - 1) p
  have hinst_p_pos : Expr.instPisAt
      (pins_pos.map fun p => Expr.instSpine (fvsP_pos.take rP) (rP - 1) p)
      (hraw.cvj.type.instantiateLevelParams hraw.cvj.levelParams lvls_pos) =
      some (hraw.cdomsP.map (posOf lps), posOf lps hraw.crestP) := by
    have h := instPisAt_instantiateLevelParams lps (posLevels lps)
      (pins_lps.map fun p => Expr.instSpine (hraw.fvsP.take rP) (rP - 1) p)
      (hraw.cvj.type.instantiateLevelParams hraw.cvj.levelParams lvls_lps)
    rw [fold_posOf lps, hraw.hinst_p, Option.map_some, hpinsP_pos] at h
    rwa [show (hraw.cvj.type.instantiateLevelParams hraw.cvj.levelParams lvls_lps).instantiateLevelParams
        lps (posLevels lps) = hraw.cvj.type.instantiateLevelParams hraw.cvj.levelParams lvls_pos
        from hcty_pos] at h
  have hopen_cf_pos : openPisAtFvars hraw.cnF (posOf lps hraw.crestP) rP =
      some (hraw.xFvsP.map (posOf lps), posOf lps hraw.ldoms) := by
    have h := openPisAtFvars_instantiateLevelParams lps (posLevels lps) hraw.cnF hraw.crestP rP
    rw [fold_posOf lps, hraw.hopen_cf, Option.map_some] at h
    exact h
  have hldoms_len_pos :
      ((posOf lps hraw.ldoms).getAppArgs.length == hraw.cnP + (mI - rP)) = true := by
    apply beq_iff_eq.mpr
    show (hraw.ldoms.instantiateLevelParams lps (posLevels lps)).getAppArgs.length = _
    rw [Ix.Kernel.Expr.getAppArgs_instantiateLevelParams, List.length_map, hraw.hldoms_len]
  have hlam_walk_pos : LamTeleWalkJ posRulesJ envSelf_pos rP hraw.cnF ty_pos
      (hraw.cvj.type.instantiateLevelParams hraw.cvj.levelParams lvls_pos)
      (fun pre => pins_pos.map fun p => Expr.instSpine pre (rP - 1) p) rhs_pos := by
    have hw := lamTeleWalkJ_posOf hlps_perm hraw.hlam_walk
    rw [hcty_pos] at hw
    exact lamTeleWalkJ_weaken hext_pub hw
  have hpins_typed_pos : TypedListJ posRulesJ envSelf_pos (rP + hraw.cnF)
      (pins_pos.map fun p => Expr.instSpine (fvsP_pos.take rP) (rP - 1) p)
      (hraw.cdomsP.map (posOf lps)) := by
    have ht := typedListJ_posOf hlps_perm hraw.hpins_typed
    rw [hpinsP_pos] at ht
    exact typedListJ_weaken hext_pub ht
  have hruns_pos : IotaRunsVmJ posRulesJ envSelf_pos (rP + hraw.cnF)
      ((lhsS_pos.getAppArgs.drop rP).take (mI - rP))
      ((posOf lps hraw.cres).getAppArgs.drop hraw.cnP)
      ((fvs_pos.drop rP).map Expr.fvarTypeD)
      ((hraw.cdoms.map (posOf lps)).drop hraw.cnP)
      ((fvs_pos.take rP).map Expr.fvarTypeD)
      (hraw.rdoms.map (posOf lps))
      (tbody_pos.getAppArgs.getD 2 (.bvar 0))
      (Expr.mkAppN (rhs_pos.renameConsts f_id) fvs_pos)
      (tbody_pos.getAppArgs.getD 0 (.bvar 0))
      lhsS_pos := by
    have hr := iotaRunsVmJ_weaken hext_adv (iotaRunsVmJ_posOf hlps_perm hraw.hruns)
    have h1 : ((lhsS.getAppArgs.drop rP).take (mI - rP)).map (posOf lps) =
        (lhsS_pos.getAppArgs.drop rP).take (mI - rP) := by
      rw [hlargs_pos, List.map_take, List.map_drop]
    have h2 : (hraw.cres.getAppArgs.drop hraw.cnP).map (posOf lps) =
        (posOf lps hraw.cres).getAppArgs.drop hraw.cnP := by
      rw [List.map_drop]
      congr 1
      exact (Ix.Kernel.Expr.getAppArgs_instantiateLevelParams lps (posLevels lps) hraw.cres).symm
    have h3 : ((hraw.fvs.drop rP).map Expr.fvarTypeD).map (posOf lps) =
        (fvs_pos.drop rP).map Expr.fvarTypeD := by
      rw [← List.map_drop, List.map_map, List.map_map]
      apply List.map_congr_left
      intro fv _
      exact instantiateLevelParams_fvarTypeD lps (posLevels lps) fv
    have h4 : (hraw.cdoms.drop hraw.cnP).map (posOf lps) =
        (hraw.cdoms.map (posOf lps)).drop hraw.cnP := List.map_drop
    have h5 : ((hraw.fvs.take rP).map Expr.fvarTypeD).map (posOf lps) =
        (fvs_pos.take rP).map Expr.fvarTypeD := by
      rw [← List.map_take, List.map_map, List.map_map]
      apply List.map_congr_left
      intro fv _
      exact instantiateLevelParams_fvarTypeD lps (posLevels lps) fv
    have h6 : posOf lps (Expr.mkAppN (r.rhs.renameConsts f_id) hraw.fvs) =
        Expr.mkAppN (rhs_pos.renameConsts f_id) fvs_pos := by
      show (Expr.mkAppN (r.rhs.renameConsts f_id) hraw.fvs).instantiateLevelParams lps (posLevels lps) = _
      rw [mkAppN_instantiateLevelParams, fold_posOf lps, instantiateLevelParams_renameConsts]
      rfl
    rwa [h1, h2, h3, h4, h5, ← hrhsS_pos, h6, ← htyArg_pos, ← hlhs_pos] at hr
  refine ⟨⟨hraw.cvj, hraw.cnP, hraw.cnF, rhs_pos, lvls_pos, pins_pos,
    hfind_ctor_M, hraw.hnfields, hrhs_bvars, hrhs_nofvar, hrhs_annot, hrhs_lvls,
    hrhs_cr, hrhs_lams, hrhs_typed, rfl, ?_⟩, hcnp_eq⟩
  exact ⟨hshape,
    ⟨auxKey (auxKey cvName .model) (.iota j), List.range lps.length, hraw.cvt.type⟩,
    fvs_pos, tbody_pos, hfind_iota, rfl, hop_t_pos, heqH_pos, htargs_len_pos,
    hlhs_fn_pos, hlargs_len_pos, hlargs_pre_pos, hmajor_pos, hraw.hctor_head,
    hraw.cdoms.map (posOf lps), posOf lps hraw.cres,
    hraw.rdoms.map (posOf lps), posOf lps hraw.lrest,
    fvsP_pos, posOf lps hraw.crest2,
    hraw.cdomsP.map (posOf lps), posOf lps hraw.crestP,
    hraw.xFvsP.map (posOf lps), posOf lps hraw.ldoms,
    hinst_c_pos, hcres_len_pos, hinst_r_pos, hopen_p_pos,
    ⟨hinst_p_pos, hopen_cf_pos, hldoms_len_pos⟩,
    hlam_walk_pos, hpins_typed_pos, hruns_pos⟩

/-- Checked rule stored in positional auxiliary space `env₃_pos`. -/
def posCheckedRule (find? : KKey → Option (ConstantInfo .anon))
    (cvName : KKey) (lps : List LevelParam) (cnP : Nat)
    (lvls_lps : List KLevel) (pins_lps : List KExpr) (r : RecRule .anon) : RecRule .anon :=
  let lvls_pos := lvls_lps.map (Level.subst lps (posLevels lps))
  let pins_pos := pins_lps.map (posOf lps)
  let rhs_pos := posOf lps r.rhs
  recRuleBits find? cvName
    (RecRule.mk r.ctor r.nfields cnP (.nested lvls_pos pins_pos) rhs_pos r.k r.eta false)

/-- Checked rule stored in real environment `env₂` (at original `lps`). -/
def realCheckedRule (find? : KKey → Option (ConstantInfo .anon))
    (cvName : KKey) (cnP : Nat)
    (lvls_lps : List KLevel) (pins_lps : List KExpr) (r : RecRule .anon) : RecRule .anon :=
  recRuleBits find? cvName
    (RecRule.mk r.ctor r.nfields cnP (.nested lvls_lps pins_lps) r.rhs r.k r.eta false)

/-- Bundled witness that rule `(j, r)` has a `RawIotaRuleVmRun` certificate whose `.iota j`
theorem copy is stored in `E`. -/
def IotaRuleReady (E : Env .anon)
    (c_pub c_rhs c_adv : Ctx)
    (blockNames : List KKey) (f_id : KKey → KKey) (advSet : Bytes.Address → Prop)
    (cvName : KKey) (lps : List LevelParam) (tyA : KExpr) (mI rP : Nat)
    (lvls_lps : List KLevel) (pins_lps : List KExpr)
    (j : Nat) (r : RecRule .anon) : Prop :=
  ∃ hraw : RawIotaRuleVmRun c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j r,
    E.find? (auxKey (auxKey cvName .model) (.iota j)) =
      some (.thmInfo
        ⟨auxKey (auxKey cvName .model) (.iota j), List.range lps.length, hraw.cvt.type⟩ hraw.vt)

theorem IotaRuleReady.mono {E₁ E₂ : Env .anon}
    (hfind : ∀ k ci, E₁.find? k = some ci → E₂.find? k = some ci)
    {c_pub c_rhs c_adv : Ctx}
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {lvls_lps : List KLevel} {pins_lps : List KExpr}
    {j : Nat} {r : RecRule .anon}
    (h : IotaRuleReady E₁ c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j r) :
    IotaRuleReady E₂ c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j r :=
  let ⟨hraw, hf⟩ := h
  ⟨hraw, hfind _ _ hf⟩

/-- List fold of `IotaRuleReady` starting at index `j`. -/
def IotaRulesReady (E : Env .anon)
    (c_pub c_rhs c_adv : Ctx)
    (blockNames : List KKey) (f_id : KKey → KKey) (advSet : Bytes.Address → Prop)
    (cvName : KKey) (lps : List LevelParam) (tyA : KExpr) (mI rP : Nat)
    (lvls_lps : List KLevel) (pins_lps : List KExpr) :
    Nat → List (RecRule .anon) → Prop
  | _, [] => True
  | j, r :: rest =>
    IotaRuleReady E c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j r ∧
    IotaRulesReady E c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps (j + 1) rest

theorem IotaRulesReady.mono {E₁ E₂ : Env .anon}
    (hfind : ∀ k ci, E₁.find? k = some ci → E₂.find? k = some ci)
    {c_pub c_rhs c_adv : Ctx}
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {lvls_lps : List KLevel} {pins_lps : List KExpr}
    {j : Nat} {rls : List (RecRule .anon)}
    (h : IotaRulesReady E₁ c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j rls) :
    IotaRulesReady E₂ c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j rls := by
  induction rls generalizing j with
  | nil => trivial
  | cons _ _ ih => exact ⟨h.1.mono hfind, ih h.2⟩

/-- Install `.iota j` theorem copies for every rule of `cvName` from `RawIotaRulesVmRun`,
extending `(E, mpE)` while preserving lookups outside `{auxKey (auxKey cvName .model) (.iota j') | j' ≥ j}`. -/
theorem installRecIotaThms {V : Type u} [Ix.Kernel.SetTheory V]
    {c_pub c_rhs c_adv : Ctx}
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {lvls_lps : List KLevel} {pins_lps : List KExpr} :
    ∀ (rls : List (RecRule .anon)) (j : Nat) {E : Env .anon}
      (mpE : EnvModelM V .verified E) (hEE : Ix.Kernel.EtaFamiliesClosed E)
      (hfind_adv : ∀ k ci, c_adv.env.find? k = some ci → E.find? k = some ci)
      (hfresh_ge : ∀ j' ≥ j, E.find? (auxKey (auxKey cvName .model) (.iota j')) = none)
      (hraws : RawIotaRulesVmRun c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
        lvls_lps pins_lps j rls),
      ∃ (E' : Env .anon) (mp' : EnvModelM V .verified E'),
        Ix.Kernel.EtaFamiliesClosed E' ∧
        EnvExt E E' ∧
        (∀ k, (E.find? k).isSome = true → mp'.base2.acval k = mpE.base2.acval k) ∧
        (∀ k, (∀ j' ≥ j, k ≠ auxKey (auxKey cvName .model) (.iota j')) → E'.find? k = E.find? k) ∧
        IotaRulesReady E' c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
          lvls_lps pins_lps j rls
  | [], j, _, mpE, hEE, _, _, _ =>
    ⟨_, mpE, hEE, EnvExt.refl _, fun _ _ => rfl, fun _ _ => rfl, trivial⟩
  | r :: rest, j, E, mpE, hEE, hfind_adv, hfresh_ge, ⟨⟨hraw⟩, hrest⟩ => by
    have hfresh_j : E.find? (auxKey (auxKey cvName .model) (.iota j)) = none :=
      hfresh_ge j (Nat.le_refl j)
    have hsrc_j : E.find? (c_adv.κ (ixAddr hraw.a_t)) = some (.thmInfo hraw.cvt hraw.vt) :=
      hfind_adv _ _ hraw.hfind_t
    obtain ⟨mp₁, _, hE₁, hext₁, hac₁⟩ := installIotaThmCopy mpE hEE hfresh_j hsrc_j
    let c₀ : ConstantInfo .anon :=
      .thmInfo ⟨auxKey (auxKey cvName .model) (.iota j), hraw.cvt.levelParams, hraw.cvt.type⟩ hraw.vt
    let E₁ : Env .anon := ⟨c₀ :: E.consts⟩
    have hf_self : E₁.find? (auxKey (auxKey cvName .model) (.iota j)) =
        some (.thmInfo
          ⟨auxKey (auxKey cvName .model) (.iota j), List.range lps.length, hraw.cvt.type⟩ hraw.vt) := by
      have h0 : E₁.find? c₀.name = some c₀ := Ix.Kernel.Env.find?_cons_self c₀ E
      dsimp only [c₀, ConstantInfo.name, ConstantInfo.toConstantVal] at h0
      rwa [hraw.ht_lps] at h0
    have hready_j : IotaRuleReady E₁ c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
        lvls_lps pins_lps j r :=
      ⟨hraw, hf_self⟩
    have hfresh_next : ∀ j' ≥ j + 1, E₁.find? (auxKey (auxKey cvName .model) (.iota j')) = none := by
      intro j' hj'
      have hne : c₀.name ≠ auxKey (auxKey cvName .model) (.iota j') := by
        intro heq
        change auxKey (auxKey cvName .model) (.iota j) = _ at heq
        injection heq with _ hd
        injection hd with hjj
        omega
      rw [EnvExt.find?_cons_ne hne]
      exact hfresh_ge j' (by omega)
    obtain ⟨E₂, mp₂, hE₂, hext₂, hac₂, hout₂, hready_rest⟩ :=
      installRecIotaThms rest (j + 1) mp₁ hE₁
        (fun k ci hk => hext₁.find (hfind_adv k ci hk))
        hfresh_next hrest
    refine ⟨E₂, mp₂, hE₂, hext₁.trans hext₂, ?_, ?_,
      ⟨hready_j.mono (fun _ _ => hext₂.find), hready_rest⟩⟩
    · intro k hk
      have hk₁ : (E₁.find? k).isSome = true := by
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
        rw [hext₁.find hci]; rfl
      rw [hac₂ k hk₁, hac₁ k hk]
    · intro k hk_ne
      rw [hout₂ k (fun j' hj' => hk_ne j' (by omega))]
      have hne₀ : c₀.name ≠ k := fun hh => hk_ne j (Nat.le_refl j) hh.symm
      exact EnvExt.find?_cons_ne hne₀

/-- Lift `IotaRulesReady` across `rls` to `IotaRulesNVmRunJ posRulesJ` at `List.range lps.length`. -/
theorem rawIotaRules_to_posNVmRun
    {c_pub c_rhs c_adv : Ctx} {envM_pos envSelf_pos : Env .anon}
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {lvls_lps : List KLevel} {pins_lps : List KExpr}
    {indKey : KKey} {cnP_ind : Nat}
    {bs : List (KExpr × BinderMeta)} {dom body : KExpr} {mb : BinderMeta}
    (hlps_perm : lps.Perm (List.range lps.length))
    (hrp_le : rP ≤ mI)
    (hty_wf :
      (posOf lps tyA).hasFvar = false ∧
      (posOf lps tyA).looseBVarsBounded 0 = true ∧
      (posOf lps tyA).constsResolve envSelf_pos = true ∧
      (posOf lps tyA).allLevelParamsDefined (List.range lps.length) = true)
    (hctor_wf : ∀ (ck : KKey) cvj cnP cnF, c_pub.env.find? ck = some (.ctorInfo cvj cnP cnF) →
      cvj.type.allLevelParamsDefined cvj.levelParams = true)
    (hstrip_ty : tyA.stripPis mI = some (bs, .forallE dom body mb))
    (hdom_fn : dom.getAppFn = .const indKey lvls_lps)
    (hdom_len : dom.getAppArgs.length = cnP_ind + (mI - rP))
    (hdom_nli : ∀ p ∈ dom.getAppArgs.take cnP_ind, noLooseIn 0 (mI - rP) p = true)
    (hdom_drop : dom.getAppArgs.drop cnP_ind =
      (List.range (mI - rP)).map (fun m => .bvar (mI - rP - 1 - m)))
    (hpins_def : pins_lps = (dom.getAppArgs.take cnP_ind).map (Expr.lowerBVars (mI - rP) 0))
    (hfind_pub_M : ∀ k ci, c_pub.env.find? k = some ci → envM_pos.find? k = some ci)
    (hext_pub : EnvExt c_pub.env envSelf_pos)
    (hext_adv : EnvExt c_adv.env envSelf_pos)
    {j : Nat} {rls : List (RecRule .anon)}
    (hnolet : ∀ r ∈ rls, noLetExpr (posOf lps r.rhs) = true)
    (hrhs_self : ∀ r ∈ rls,
      (posOf lps r.rhs).constsResolve envSelf_pos = true ∧
      (∀ t', posRulesJ.infer c_rhs.env 0 r.rhs t' →
        ∃ t'', posRulesJ.infer envSelf_pos 0 (posOf lps r.rhs) t''))
    (hready : IotaRulesReady envM_pos c_pub c_rhs c_adv blockNames f_id advSet cvName lps tyA mI rP
      lvls_lps pins_lps j rls) :
    IotaRulesNVmRunJ posRulesJ envM_pos envSelf_pos f_id cvName (List.range lps.length)
      (posOf lps tyA) mI rP j
      (rls.map fun r =>
        RecRule.mk r.ctor r.nfields r.ctorParams r.fire (posOf lps r.rhs) r.k r.eta r.paramsBlind)
      (rls.map (posCheckedRule envM_pos.find? cvName lps cnP_ind lvls_lps pins_lps)) := by
  induction rls generalizing j with
  | nil => rfl
  | cons r rest ih =>
    obtain ⟨⟨hraw, hf_iota⟩, hrest⟩ := hready
    have hfind_cv : envM_pos.findCV? (auxKey (auxKey cvName .model) (.iota j)) =
        some ⟨auxKey (auxKey cvName .model) (.iota j), List.range lps.length, hraw.cvt.type⟩ := by
      unfold Env.findCV?
      rw [hf_iota]
      rfl
    obtain ⟨hr_cr, hr_inf⟩ := hrhs_self r List.mem_cons_self
    obtain ⟨t'_rhs, ht'_rhs⟩ := hraw.hrhs_typed
    obtain ⟨hrule, hcnp⟩ := rawIotaRule_to_posNVmRun hlps_perm hrp_le
      (hnolet r List.mem_cons_self) hty_wf (hctor_wf r.ctor) hstrip_ty hdom_fn hdom_len
      hdom_nli hdom_drop hpins_def hfind_pub_M hext_pub hext_adv hraw
      hr_cr (hr_inf t'_rhs ht'_rhs) hfind_cv
    have hr'_eq :
        recRuleBits envM_pos.find? cvName
          (RecRule.mk r.ctor r.nfields hraw.cnP
            (.nested (lvls_lps.map (Level.subst lps (posLevels lps))) (pins_lps.map (posOf lps)))
            (posOf lps r.rhs) r.k r.eta false) =
        posCheckedRule envM_pos.find? cvName lps cnP_ind lvls_lps pins_lps r := by
      unfold posCheckedRule
      rw [hcnp]
    rw [hr'_eq] at hrule
    exact ⟨posCheckedRule envM_pos.find? cvName lps cnP_ind lvls_lps pins_lps r,
      rest.map (posCheckedRule envM_pos.find? cvName lps cnP_ind lvls_lps pins_lps),
      hrule,
      ih (fun r' hr' => hnolet r' (List.mem_cons_of_mem r hr'))
        (fun r' hr' => hrhs_self r' (List.mem_cons_of_mem r hr')) hrest,
      rfl⟩

end IxVM.Refinement.Decl

