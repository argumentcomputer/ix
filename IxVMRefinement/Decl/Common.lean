import IxVMRefinement.Core.Seams
import IxVMRefinement.Core.Open
import IxVMRefinement.Infer.Close
import IxVMRefinement.Nat.Levels
import IxVMRefinement.Infer.Leaves
import IxVMRefinement.Obs.KernelCheck0
import IxVMRefinement.Obs.KernelCheck3
import IxVMRefinement.Lib.Bytes
import IxC.Kernel.Model.JudgeRules
import IxC.Kernel.Model.StoreCompanions
import IxC.Kernel.Model.StoreRecShape
import IxC.Kernel.Model.StoreFold

/-! # Declaration refinement: shared fold invariant and structural helpers

Shared infrastructure for the `L5` declaration refinement at `S₀`:

* **`DeclStoreInv` and `DeclInv`**: the store-level invariant bundle (`StoreInv`, `ThmTyped`,
  `RecK`, `EtaTowers`, `TableBodies`, `RecShape`) and the full set-theoretic fold invariant
  `DeclInv V env` (`EnvModelT V .verified env ∧ DeclStoreInv env`), together with empty-environment
  initialization, `EnvModelOk` extraction, and one-step preservation along `DeclRunJ rulesJ`.
* **`EnvFacts` projection**: `CtxRoleFacts` isolates the role/record companions owed by L6/L7,
  and `DeclStoreInv.toEnvFacts` combines them with `DeclStoreInv` to supply `EnvFacts` to `Core`.
* **Positional level parameters (`posOf`)**: `posOf_range`, `posOf_perm_inv`,
  `allLevelParamsDefined_of_posOf_perm`, and `constsResolve_posOf`.
* **Annotation and resolution bridges**: `annot_of_annotates` bridges `IxVM.Consistency.Annotates`
  to `Ix.Kernel.Rules.Annot`, and `infer_constsResolve` extracts `Expr.constsResolve` from a
  full-grade `Rules.Infer` derivation under `StoreInv`.
* **`InstallStep` constructors**: `InstallStep` witnesses for empty installs, single-constant
  value/axiom/opaque/theorem installs, `DeclBasisRun` basis installs, and fallback witnesses when
  `¬ DeclStoreInv env`.
* **`Core S₀` and `Levels` wrappers**: collision-free wrappers for `whnf`, `k_is_def_eq`,
  `k_infer`, `k_ensure_sort`, `k_check`, and `level_equal`.
* **Exact heap representations and syntactic checks**: `TmExact` / `CIRepExact`,
  `validate_expr_well_scoped`, `level_list_struct_eq`, `kexpr_struct_eq`, and
  `spec_params_ptr_eq`. -/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂
  levelStructEq_refines glistCmp_refines)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo Declaration RecRule BasisKind)
open Ix.Kernel.Rules (Annot Red DefEq Infer)
open Ix.Kernel.Semantics (DeclRunJ DeclBasisRun BasisInstallRun IndRoutesJ)
open Ix.Kernel.Model (rulesJ EnvModelT EnvModelOk)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Store invariant and fold invariant -/

/-- **Store-level companion invariants** carried alongside `EnvModelT` across declarations. -/
structure DeclStoreInv (env : Ix.Kernel.Env .anon) : Prop where
  store : Ix.Kernel.Open.StoreInv env
  thmTyped : Ix.Kernel.Model.ThmTyped env
  recK : Ix.Kernel.Model.RecK env
  etaTowers : Ix.Kernel.Model.EtaTowers env
  tableBodies : Ix.Kernel.Model.TableBodies env
  recShape : Ix.Kernel.Model.RecShape env

/-- All store-level invariants hold of the empty environment. -/
theorem DeclStoreInv.empty : DeclStoreInv Ix.Kernel.Env.empty :=
  ⟨.empty, .empty, .empty, .empty, .empty, .empty⟩

/-- Every `DeclRunJ rulesJ (IndRoutesJ rulesJ env)` step preserves `DeclStoreInv`. -/
theorem DeclStoreInv.step {env env₂ : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (h : DeclStoreInv env)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    DeclStoreInv env₂ where
  store :=
    Ix.Kernel.Model.storeInv_declRunJ
      (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e)
      (fun hI => Ix.Kernel.Model.storeInv_indRoutesJ
        (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e) h.store hI)
      h.store hd
  thmTyped := Ix.Kernel.Model.thmTyped_declRunJ h.thmTyped hd
  recK := Ix.Kernel.Model.recK_declRunJ h.store h.recK hd
  etaTowers := Ix.Kernel.Model.etaTowers_declRunJ h.etaTowers hd
  tableBodies := Ix.Kernel.Model.tableBodies_declRunJ h.store h.tableBodies hd
  recShape := Ix.Kernel.Model.recShape_declRunJ h.store h.recShape hd

/-- **The `L5` fold invariant**: the rules-tier environment model (including theorem-value
denotations) together with the store-level companion invariants. -/
structure DeclInv (V : Type u) [Ix.Kernel.SetTheory V] (env : Ix.Kernel.Env .anon) : Prop where
  model : EnvModelT V .verified env
  store : DeclStoreInv env

/-- `DeclInv` holds of the empty environment in every set theory. -/
theorem DeclInv.empty (V : Type u) [Ix.Kernel.SetTheory V] :
    DeclInv V Ix.Kernel.Env.empty :=
  ⟨EnvModelT.empty, DeclStoreInv.empty⟩

/-- `DeclInv` projects to `EnvModelOk V .verified env` as required by `IxVM.Consistency.Decls`. -/
theorem DeclInv.toEnvModelOk {V : Type u} [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env .anon}
    (h : DeclInv V env) : EnvModelOk V .verified env := by
  obtain ⟨⟨mp, _⟩, hE⟩ := h.model
  exact ⟨⟨mp⟩, hE⟩

/-- One-step preservation of `DeclInv` along any `DeclRunJ rulesJ (IndRoutesJ rulesJ env)` step. -/
theorem DeclInv.step_declRunJ {V : Type u} [Ix.Kernel.SetTheory V]
    {env env₂ : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂)
    (h : DeclInv V env) : DeclInv V env₂ :=
  ⟨Ix.Kernel.Model.foldRulesRoutes (.cons hd .nil) h.model, h.store.step hd⟩

/-- Injection of a modeled inductive step (`DeclIndRunJ`) into `DeclRunJ` when unpinned. -/
theorem declRunJ_of_modeledInd {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hM : Ix.Kernel.Semantics.DeclIndRunJ rulesJ env block env₂) :
    DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
  simp only [DeclRunJ, hpin]
  exact Or.inr (Or.inl hM)

/-! ## Supplying `EnvFacts` from `DeclStoreInv` -/

/-- **Role-table and record-correspondence companions** of `EnvFacts c` owed by the role and
assembly layers (L6/L7), complementing the store invariants carried in `DeclStoreInv c.env`. -/
structure CtxRoleFacts (c : Ctx) : Prop where
  natLit : c.inForce .nat → c.inForce .natZero → c.inForce .natSucc →
    Ix.Kernel.natLitSupported c.env = true
  strLit : c.inForce .string → Ix.Kernel.strLitSupported c.env = true
  natOps : ∀ r, c.inForce r → (.role r : KKey) ∈ Ix.Kernel.Rules.natBinOpNames →
    Ix.Kernel.natOpStored c.env (.role r) = true
  natAdd : c.inForce .natAdd → Ix.Kernel.Rules.natAddTyOk (c.env.find? Ix.Kernel.natAddName) = true
  eqStored : c.inForce .eq → ∃ ci, c.env.find? Ix.Kernel.eqName = some ci
  evidence : ∀ r es i a, c.inForce r → (r, es) ∈ c.t.evidence.toList → es[i]? = some (.proof a) →
    ∀ stmt, roleStatement r i = some stmt →
      ∃ cv v, c.env.find? (c.κ a) = some (.thmInfo cv v) ∧ DefEq c.env 0 cv.type stmt
  quotBasis : c.inForce .quot → ∀ ci ∈ BasisKind.declsA (md := .anon) .quotK,
    c.env.find? ci.name = some ci
  recMajorRecord : ∀ k cv mI rP rls (p : _root_.Address) us,
    c.env.find? k = some (.recInfo cv mI rP rls) → rls ≠ [] →
    (piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
    ∃ cm, Ix.Cert.recordAt c.E p = some cm
  recRulesNodupAndProj : ∀ k cv mI rP rls, c.env.find? k = some (.recInfo cv mI rP rls) →
    (rls.map (·.ctor)).Nodup ∧
    ∀ (p : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj) (us : List KLevel),
      (piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
      Ix.Cert.recordAt c.E p = some cm → cm.info = .iPrj ip →
      ∀ j rl, rls[j]? = some rl → rl.ctor = c.κ (cprjAddr ip.block ip.idx.toNat j)
  recPlain : ∀ k cv mI rP rls rl cvj nP nF, c.env.find? k = some (.recInfo cv mI rP rls) →
    rl ∈ rls → rl.fire = .plain → c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
    ∃ D T, piDomAt mI cv.type = some D ∧
      D.getAppFn = .const T (cvj.levelParams.map .param) ∧
      D.getAppArgs.take nP = (List.range nP).map (fun i => .bvar (mI - 1 - i)) ∧
      D.getAppArgs.drop nP = (List.range (mI - rP)).map fun i => .bvar (mI - rP - 1 - i)
  ruleCtorHead : ∀ k cv mI rP rls rl cvj nP nF T us,
    c.env.find? k = some (.recInfo cv mI rP rls) → rl ∈ rls →
    c.env.find? rl.ctor = some (.ctorInfo cvj nP nF) →
    (piDomAt mI cv.type).map (·.getAppFn) = some (.const T us) →
    ∃ tus, (Expr.piResult cvj.type).getAppFn = .const T tus
  etaType : ∀ (T kc : KKey) (cvT cvc : ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (nP nF : Nat),
    c.env.find? T = some (.indInfo cvT caps) → caps.eta = true → caps.etaCtor = some kc →
    c.env.find? kc = some (.ctorInfo cvc nP nF) →
    ∀ (d : Nat) (us : List KLevel) (Ss : List KExpr) (ta : KExpr), Ss.length = nP + nF →
      Infer c.env .io d (Expr.mkAppN (.const kc us) Ss) ta →
      Red c.env d ta (Expr.mkAppN (.const T us) (Ss.take nP))
  etaSort : ∀ T cvT caps, c.env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    ∃ bs l, cvT.type.stripPis caps.etaParams = some (bs, .sort l) ∧
      caps.sortZ = Level.zeronessOf l

/-- Combine `DeclStoreInv c.env` with `c.t.wf = true` and `CtxRoleFacts c` to build `EnvFacts c`. -/
theorem DeclStoreInv.toEnvFacts {c : Ctx} (hS : DeclStoreInv c.env) (htwf : c.t.wf = true)
    (hR : CtxRoleFacts c) : EnvFacts c where
  tableWf := htwf
  storeClosed := hS.store.storeClosed
  thmTyped := hS.thmTyped
  natLit := hR.natLit
  strLit := hR.strLit
  natOps := hR.natOps
  natAdd := hR.natAdd
  eqStored := hR.eqStored
  evidence := hR.evidence
  recRules := fun k cv mI rP rls hf =>
    let ⟨hnodup, hprj⟩ := hR.recRulesNodupAndProj k cv mI rP rls hf
    ⟨hnodup, fun rl hrl => hS.store.recRules_fire hf hrl, hprj⟩
  recPlain := hR.recPlain
  store := hS.store
  recMajorRecord := hR.recMajorRecord
  ruleCtorHead := hR.ruleCtorHead
  quotBasis := hR.quotBasis
  etaTowers := hS.etaTowers
  etaType := hR.etaType
  recEta := fun k cv mI rP rl hf =>
    (hS.recShape k cv mI rP [rl] hf).eta rl (List.mem_cons.mpr (Or.inl rfl))
  etaSort := hR.etaSort
  recArity := fun k cv mI rP rls hf rl hrl => hS.store.recArity hf hrl
  ruleCtorArity := fun k cv mI rP rls hf rl hrl cvj nP nF hc => hS.store.ruleCtor_arity hf hrl hc
  tableCtorArity := fun sn i entry hp cvC nP nF hc => hS.store.tableCtor_arity hp hc
  familyArity := fun T cvT caps hf => hS.store.familyArity hf

/-! ## Positional level parameters (`posOf`) -/

private theorem subst_go_self :
    ∀ (ps : List LevelParam) (p : LevelParam),
      Level.subst.go ps (ps.map .param) p = .param p
  | [], _ => rfl
  | k :: ks, p => by
    show (if k = p then Level.param k else Level.subst.go ks (ks.map .param) p) = .param p
    by_cases h : k = p
    · rw [ite_eq_left h, h]
    · rw [ite_eq_right h, subst_go_self ks p]

private theorem level_subst_self (ps : List LevelParam) :
    ∀ l : KLevel, Level.subst ps (ps.map .param) l = l
  | .zero => rfl
  | .succ l => congrArg Level.succ (level_subst_self ps l)
  | .max a b => by simp only [Level.subst, level_subst_self ps a, level_subst_self ps b]
  | .imax a b => by simp only [Level.subst, level_subst_self ps a, level_subst_self ps b]
  | .param p => subst_go_self ps p

private theorem substPW_self (ps : List LevelParam) (pw : Ix.Kernel.PropWhen) :
    Level.substPW ps (ps.map .param) pw = pw := by
  apply Ix.Kernel.PropWhen.eq_of_holds
  intro φ
  rw [Level.holds_substPW]
  congr 1
  funext p
  rw [← Level.eval_subst_go, subst_go_self ps p, Level.eval]

/-- Instantiating a term's level parameters by themselves is the identity. -/
theorem instantiateLevelParams_self (ps : List LevelParam) :
    ∀ e : KExpr, e.instantiateLevelParams ps (ps.map .param) = e := by
  intro e
  induction e with
  | bvar _ | lit _ => rfl
  | fvar idx ty ih => simp only [Expr.instantiateLevelParams, ih]
  | sort u => simp only [Expr.instantiateLevelParams, level_subst_self ps u]
  | const n us =>
    simp only [Expr.instantiateLevelParams]
    congr 1
    have hmap : us.map (Level.subst ps (ps.map .param)) = us.map id :=
      List.map_congr_left fun u _ => level_subst_self ps u
    simpa using hmap
  | app f a ihf iha => simp only [Expr.instantiateLevelParams, ihf, iha]
  | lam ty body m iht ihb =>
    simp only [Expr.instantiateLevelParams, iht, ihb, substPW_self ps m.pw]
  | forallE ty body m iht ihb =>
    simp only [Expr.instantiateLevelParams, iht, ihb, substPW_self ps m.pw]
  | letE ty val body l iht ihv ihb =>
    simp only [Expr.instantiateLevelParams, iht, ihv, ihb]
  | proj s i e ih => simp only [Expr.instantiateLevelParams, ih]

/-- On `List.range n`, `posOf` is the identity. -/
theorem posOf_range (n : Nat) (e : KExpr) : posOf (List.range n) e = e := by
  unfold posOf posLevels
  rw [List.length_range]
  exact instantiateLevelParams_self (List.range n) e

/-- Undoing `posOf ps` when `ps.Perm (List.range ps.length)`. -/
theorem posOf_perm_inv {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (e : KExpr) :
    (posOf ps e).instantiateLevelParams (List.range ps.length) (ps.map .param) = e := by
  have h := InferAux.posOf_instantiateLevelParams_perm (us := ps.map .param) hperm
    (List.length_map ..) (T := e)
  rw [List.length_map, instantiateLevelParams_self ps e] at h
  exact h

private theorem subst_go_allParamsDefined {ks ps' : List LevelParam} {us : List KLevel}
    (hus : ∀ u ∈ us, u.allParamsDefined ps' = true) :
    ∀ {p : LevelParam}, p ∈ ks → us.length = ks.length →
      (Level.subst.go ks us p).allParamsDefined ps' = true := by
  induction ks generalizing us with
  | nil => intro _ hp _; nomatch hp
  | cons k ks ih =>
    intro p hp hlen
    cases us with
    | nil => cases hlen
    | cons u us =>
      show (if k = p then u else Level.subst.go ks us p).allParamsDefined ps' = true
      by_cases hkp : k = p
      · rw [ite_eq_left hkp]
        exact hus u (List.mem_cons.mpr (Or.inl rfl))
      · rw [ite_eq_right hkp]
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact absurd rfl hkp
        · exact ih (fun v hv => hus v (List.mem_cons.mpr (Or.inr hv))) hp' (Nat.succ.inj hlen)

private theorem level_subst_allParamsDefined {ks ps' : List LevelParam} {us : List KLevel}
    (hus : ∀ u ∈ us, u.allParamsDefined ps' = true) (hlen : us.length = ks.length) :
    ∀ {l : KLevel}, l.allParamsDefined ks = true →
      (Level.subst ks us l).allParamsDefined ps' = true
  | .zero, _ => rfl
  | .succ l, h => by
    simp only [Level.allParamsDefined] at h
    simp only [Level.subst, Level.allParamsDefined]
    exact level_subst_allParamsDefined hus hlen h
  | .max a b, h => by
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Level.subst, Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨level_subst_allParamsDefined hus hlen h.1, level_subst_allParamsDefined hus hlen h.2⟩
  | .imax a b, h => by
    simp only [Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Level.subst, Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨level_subst_allParamsDefined hus hlen h.1, level_subst_allParamsDefined hus hlen h.2⟩
  | .param p, h => by
    simp only [Level.allParamsDefined, List.contains_eq_mem, decide_eq_true_eq] at h
    exact subst_go_allParamsDefined hus h hlen

theorem allLevelParamsDefined_instantiateLevelParams {ks ps' : List LevelParam} {us : List KLevel}
    (hus : ∀ u ∈ us, u.allParamsDefined ps' = true) (hlen : us.length = ks.length) :
    ∀ {e : KExpr}, e.allLevelParamsDefined ks = true →
      (e.instantiateLevelParams ks us).allLevelParamsDefined ps' = true := by
  intro e
  induction e with
  | bvar _ | lit _ => intro _; rfl
  | fvar _ ty ih =>
    intro h; simp only [Expr.allLevelParamsDefined] at h ⊢; exact ih h
  | sort u =>
    intro h; simp only [Expr.allLevelParamsDefined] at h ⊢
    exact level_subst_allParamsDefined hus hlen h
  | const _ ls =>
    intro h
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Expr.instantiateLevelParams, Expr.allLevelParamsDefined, List.all_map,
      List.all_eq_true]
    intro l hl
    exact level_subst_allParamsDefined hus hlen (h l hl)
  | app f a ihf iha =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty body m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht h.1.1, ihb h.1.2⟩, Level.substPW_paramsDefined hlen hus h.2⟩
  | forallE ty body m iht ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht h.1.1, ihb h.1.2⟩, Level.substPW_paramsDefined hlen hus h.2⟩
  | letE ty val body _ iht ihv ihb =>
    intro h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj _ _ e ih =>
    intro h
    simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiateLevelParams, Expr.allLevelParamsDefined]
    exact ih h

/-- If `(posOf ps e).allLevelParamsDefined (List.range ps.length) = true` for a permutation
`ps.Perm (List.range ps.length)`, then `e.allLevelParamsDefined ps = true`. -/
theorem allLevelParamsDefined_of_posOf_perm {ps : List LevelParam} {e : KExpr}
    (hperm : ps.Perm (List.range ps.length))
    (hdef : (posOf ps e).allLevelParamsDefined (List.range ps.length) = true) :
    e.allLevelParamsDefined ps = true := by
  rw [← posOf_perm_inv hperm e]
  apply allLevelParamsDefined_instantiateLevelParams _ (by rw [List.length_map, List.length_range]) hdef
  intro u hu
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
  simp [Level.allParamsDefined, hp]

/-- `posOf` leaves `constsResolve` unchanged. -/
theorem constsResolve_posOf (ps : List LevelParam) (env : Ix.Kernel.Env .anon) (e : KExpr) :
    (posOf ps e).constsResolve env = e.constsResolve env :=
  Expr.constsResolve_instantiateLevelParams ..

/-! ## Bridging `IxVM.Consistency.Annotates` to `Ix.Kernel.Rules.Annot` -/

theorem annotates_hasFvar_false {e' e : KExpr} (ha : IxVM.Consistency.Annotates e' e) :
    e.hasFvar = false → e'.hasFvar = false := by
  induction ha with
  | bvar | sort | const | lit => intro _; rfl
  | fvar => intro h; simp [Expr.hasFvar] at h
  | app _ _ ihf iha =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ iht ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | forallE _ _ iht ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | proj _ ihe =>
    intro h
    simp only [Expr.hasFvar] at h ⊢
    exact ihe h
  | @letE e' ty v b m _ ih =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    have hlift : ∀ (x : KExpr) (n c : Nat), x.hasFvar = false →
        (x.liftLooseBVars n c).hasFvar = false := by
      intro x
      induction x with
      | bvar _ => intro n c _; simp only [Expr.liftLooseBVars]; split <;> rfl
      | fvar _ _ _ => intro _ _ hx; simp [Expr.hasFvar] at hx
      | sort _ | const _ _ | lit _ => intro _ _ _; rfl
      | app f a ih1 ih2 =>
        intro n c hx
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
        simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 n c hx.1, ih2 n c hx.2⟩
      | lam t bo _ ih1 ih2 =>
        intro n c hx
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
        simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 n c hx.1, ih2 n (c + 1) hx.2⟩
      | forallE t bo _ ih1 ih2 =>
        intro n c hx
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
        simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 n c hx.1, ih2 n (c + 1) hx.2⟩
      | letE t va bo _ ih1 ih2 ih3 =>
        intro n c hx
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
        simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨⟨ih1 n c hx.1.1, ih2 n c hx.1.2⟩, ih3 n (c + 1) hx.2⟩
      | proj _ _ s ih1 =>
        intro n c hx
        simp only [Expr.hasFvar] at hx
        simp only [Expr.liftLooseBVars, Expr.hasFvar]
        exact ih1 n c hx
    have hinst : ∀ (bo : KExpr) (j : Nat), bo.hasFvar = false →
        (bo.instantiate1Lift v j).hasFvar = false := by
      intro bo
      induction bo with
      | bvar i =>
        intro j _
        simp only [Expr.instantiate1Lift]
        split
        · exact hlift v j 0 h.1.2
        · split <;> rfl
      | fvar _ _ _ => intro _ hbo; simp [Expr.hasFvar] at hbo
      | sort _ | const _ _ | lit _ => intro _ _; rfl
      | app f a ih1 ih2 =>
        intro j hbo
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
        simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 j hbo.1, ih2 j hbo.2⟩
      | lam t bo _ ih1 ih2 =>
        intro j hbo
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
        simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 j hbo.1, ih2 (j + 1) hbo.2⟩
      | forallE t bo _ ih1 ih2 =>
        intro j hbo
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
        simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 j hbo.1, ih2 (j + 1) hbo.2⟩
      | letE t va bo _ ih1 ih2 ih3 =>
        intro j hbo
        simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
        simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨⟨ih1 j hbo.1.1, ih2 j hbo.1.2⟩, ih3 (j + 1) hbo.2⟩
      | proj _ _ s ih1 =>
        intro j hbo
        simp only [Expr.hasFvar] at hbo
        simp only [Expr.instantiate1Lift, Expr.hasFvar]
        exact ih1 j hbo
    exact ih (hinst b 0 h.2)

theorem annotates_looseBVarsBounded {e' e : KExpr} (ha : IxVM.Consistency.Annotates e' e) :
    ∀ k, e.looseBVarsBounded k = true → e'.looseBVarsBounded k = true := by
  induction ha with
  | bvar => intro _ h; exact h
  | fvar _ _ => intro _ _; rfl
  | sort | const | lit => intro _ _; rfl
  | app _ _ ihf iha =>
    intro k h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam _ _ iht ihb =>
    intro k h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE _ _ iht ihb =>
    intro k h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | proj _ ihe =>
    intro k h
    simp only [Expr.looseBVarsBounded] at h ⊢
    exact ihe k h
  | @letE e' ty v b m _ ih =>
    intro k h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    exact ih k (looseBVarsBounded_instantiate1Lift (Nat.zero_le k) h.2 (by simpa using h.1.2))

private def instAt (fvs : List KExpr) (k : Nat) : KExpr → KExpr
  | .bvar i =>
    if i < k then .bvar i
    else if h : i - k < fvs.length then fvs[i - k]
    else .bvar (i - fvs.length)
  | .fvar idx ty => .fvar idx (instAt fvs k ty)
  | .sort u => .sort u
  | .const n us => .const n us
  | .lit l => .lit l
  | .app f a => .app (instAt fvs k f) (instAt fvs k a)
  | .lam ty body m => .lam (instAt fvs k ty) (instAt fvs (k + 1) body) m
  | .forallE ty body m => .forallE (instAt fvs k ty) (instAt fvs (k + 1) body) m
  | .letE ty v body m => .letE (instAt fvs k ty) (instAt fvs k v) (instAt fvs (k + 1) body) m
  | .proj s i e => .proj s i (instAt fvs k e)

private def FVarsLt (d : Nat) : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar idx ty => decide (idx < d) && FVarsLt d ty
  | .app f a => FVarsLt d f && FVarsLt d a
  | .lam ty b _ | .forallE ty b _ => FVarsLt d ty && FVarsLt d b
  | .letE ty v b _ => FVarsLt d ty && FVarsLt d v && FVarsLt d b
  | .proj _ _ e => FVarsLt d e

private theorem fvarsLt_mono {d₁ d₂ : Nat} (hle : d₁ ≤ d₂) :
    ∀ {e : KExpr}, FVarsLt d₁ e = true → FVarsLt d₂ e = true := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _; rfl
  | fvar idx ty ih =>
    intro h
    simp only [FVarsLt, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨by omega, ih h.2⟩
  | app f a ihf iha =>
    intro h; simp only [FVarsLt, Bool.and_eq_true] at h ⊢; exact ⟨ihf h.1, iha h.2⟩
  | lam ty b _ iht ihb =>
    intro h; simp only [FVarsLt, Bool.and_eq_true] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b _ iht ihb =>
    intro h; simp only [FVarsLt, Bool.and_eq_true] at h ⊢; exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b _ iht ihv ihb =>
    intro h; simp only [FVarsLt, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj _ _ e ih => intro h; simp only [FVarsLt] at h ⊢; exact ih h

private theorem fvarsLt_of_hasFvar_false (d : Nat) :
    ∀ {e : KExpr}, e.hasFvar = false → FVarsLt d e = true := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _; rfl
  | fvar _ _ _ => intro h; simp [Expr.hasFvar] at h
  | app f a ihf iha =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [FVarsLt, Bool.and_eq_true]; exact ⟨ihf h.1, iha h.2⟩
  | lam ty b _ iht ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [FVarsLt, Bool.and_eq_true]; exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b _ iht ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [FVarsLt, Bool.and_eq_true]; exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b _ iht ihv ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [FVarsLt, Bool.and_eq_true]; exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj _ _ e ih =>
    intro h; simp only [Expr.hasFvar] at h; simp only [FVarsLt]; exact ih h

private theorem fvarsLt_instAt {fvs : List KExpr} {d : Nat}
    (hfvs : ∀ fv ∈ fvs, FVarsLt d fv = true) :
    ∀ {e : KExpr} (k : Nat), e.hasFvar = false → FVarsLt d (instAt fvs k e) = true := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [instAt]
    split
    · rfl
    · split
      · next hlt => exact hfvs _ (List.getElem_mem hlt)
      · rfl
  | fvar _ _ _ => intro _ h; simp [Expr.hasFvar] at h
  | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro k h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, FVarsLt, Bool.and_eq_true]; exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b _ iht ihb =>
    intro k h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, FVarsLt, Bool.and_eq_true]; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b _ iht ihb =>
    intro k h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, FVarsLt, Bool.and_eq_true]; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v b _ iht ihv ihb =>
    intro k h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, FVarsLt, Bool.and_eq_true]
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj _ _ e ih =>
    intro k h; simp only [Expr.hasFvar] at h; simp only [instAt, FVarsLt]; exact ih k h

private theorem abstract1_of_fvarsLt {d : Nat} :
    ∀ {e : KExpr} (k : Nat), FVarsLt d e = true → e.abstract1 d k = e := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | fvar idx ty ih =>
    intro k h
    simp only [FVarsLt, Bool.and_eq_true, decide_eq_true_eq] at h
    show (if idx = d then Expr.bvar k else Expr.fvar idx ty) = Expr.fvar idx ty
    exact ite_eq_right (by omega)
  | app f a ihf iha =>
    intro k h; simp only [FVarsLt, Bool.and_eq_true] at h
    simp only [Expr.abstract1, ihf k h.1, iha k h.2]
  | lam ty b m iht ihb =>
    intro k h; simp only [FVarsLt, Bool.and_eq_true] at h
    simp only [Expr.abstract1, iht k h.1, ihb (k + 1) h.2]
  | forallE ty b m iht ihb =>
    intro k h; simp only [FVarsLt, Bool.and_eq_true] at h
    simp only [Expr.abstract1, iht k h.1, ihb (k + 1) h.2]
  | letE ty v b m iht ihv ihb =>
    intro k h; simp only [FVarsLt, Bool.and_eq_true] at h
    simp only [Expr.abstract1, iht k h.1.1, ihv k h.1.2, ihb (k + 1) h.2]
  | proj s i e ih =>
    intro k h; simp only [FVarsLt] at h; simp only [Expr.abstract1, ih k h]

private theorem liftLooseBVars_of_bounded :
    ∀ {e : KExpr} (n c : Nat), e.looseBVarsBounded c = true → e.liftLooseBVars n c = e := by
  intro e
  induction e with
  | bvar i =>
    intro n c h
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
    show (if i ≥ c then Expr.bvar (i + n) else Expr.bvar i) = Expr.bvar i
    exact ite_eq_right (by omega)
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro n c h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, ihf n c h.1, iha n c h.2]
  | lam ty b m iht ihb =>
    intro n c h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, iht n c h.1, ihb n (c + 1) h.2]
  | forallE ty b m iht ihb =>
    intro n c h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, iht n c h.1, ihb n (c + 1) h.2]
  | letE ty v b m iht ihv ihb =>
    intro n c h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, iht n c h.1.1, ihv n c h.1.2, ihb n (c + 1) h.2]
  | proj s i e ih =>
    intro n c h; simp only [Expr.looseBVarsBounded] at h
    simp only [Expr.liftLooseBVars, ih n c h]

private theorem instantiate1_of_bounded :
    ∀ {e : KExpr} (v : KExpr) (k : Nat), e.looseBVarsBounded k = true → e.instantiate1 v k = e := by
  intro e
  induction e with
  | bvar i =>
    intro v k h
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
    show (if i = k then v else if i > k then Expr.bvar (i - 1) else Expr.bvar i) = Expr.bvar i
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro v k h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, ihf v k h.1, iha v k h.2]
  | lam ty b m iht ihb =>
    intro v k h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, iht v k h.1, ihb v (k + 1) h.2]
  | forallE ty b m iht ihb =>
    intro v k h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, iht v k h.1, ihb v (k + 1) h.2]
  | letE ty va b m iht ihv ihb =>
    intro v k h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, iht v k h.1.1, ihv v k h.1.2, ihb v (k + 1) h.2]
  | proj s i e ih =>
    intro v k h; simp only [Expr.looseBVarsBounded] at h
    simp only [Expr.instantiate1, ih v k h]

private theorem instantiate1Lift_of_bounded {v : KExpr} :
    ∀ {e : KExpr} (j : Nat), e.looseBVarsBounded j = true → e.instantiate1Lift v j = e := by
  intro e
  induction e with
  | bvar i =>
    intro j h
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
    show (if i = j then v.liftLooseBVars j 0 else if i > j then Expr.bvar (i - 1) else Expr.bvar i) = Expr.bvar i
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro j h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, ihf j h.1, iha j h.2]
  | lam ty b m iht ihb =>
    intro j h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, iht j h.1, ihb (j + 1) h.2]
  | forallE ty b m iht ihb =>
    intro j h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, iht j h.1, ihb (j + 1) h.2]
  | letE ty va b m iht ihv ihb =>
    intro j h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, iht j h.1.1, ihv j h.1.2, ihb (j + 1) h.2]
  | proj s i e ih =>
    intro j h; simp only [Expr.looseBVarsBounded] at h
    simp only [Expr.instantiate1Lift, ih j h]

private theorem looseBVarsBounded_mono {k₁ k₂ : Nat} (hle : k₁ ≤ k₂) :
    ∀ {e : KExpr}, e.looseBVarsBounded k₁ = true → e.looseBVarsBounded k₂ = true := by
  intro e
  induction e generalizing k₁ k₂ with
  | bvar i =>
    intro h; simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h ⊢; omega
  | fvar _ _ _ => intro _; rfl
  | sort _ | const _ _ | lit _ => intro _; rfl
  | app f a ihf iha =>
    intro h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨ihf hle h.1, iha hle h.2⟩
  | lam ty b _ iht ihb =>
    intro h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht hle h.1, ihb (by omega) h.2⟩
  | forallE ty b _ iht ihb =>
    intro h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨iht hle h.1, ihb (by omega) h.2⟩
  | letE ty v b _ iht ihv ihb =>
    intro h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht hle h.1.1, ihv hle h.1.2⟩, ihb (by omega) h.2⟩
  | proj _ _ e ih =>
    intro h; simp only [Expr.looseBVarsBounded] at h ⊢; exact ih hle h

private theorem instAt_nil : ∀ (e : KExpr) (k : Nat), instAt [] k e = e := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [instAt, List.length_nil, Nat.not_lt_zero, dite_false, Nat.sub_zero]
    split <;> rfl
  | fvar idx ty ih => intro k; simp only [instAt, ih k]
  | sort _ | const _ _ | lit _ => intro _; rfl
  | app f a ihf iha => intro k; simp only [instAt, ihf k, iha k]
  | lam ty b m iht ihb => intro k; simp only [instAt, iht k, ihb (k + 1)]
  | forallE ty b m iht ihb => intro k; simp only [instAt, iht k, ihb (k + 1)]
  | letE ty v b m iht ihv ihb => intro k; simp only [instAt, iht k, ihv k, ihb (k + 1)]
  | proj s i e ih => intro k; simp only [instAt, ih k]

private theorem looseBVarsBounded_instAt {fvs : List KExpr}
    (hfvs : ∀ fv ∈ fvs, fv.looseBVarsBounded 0 = true) :
    ∀ {e : KExpr} (k : Nat), e.looseBVarsBounded (k + fvs.length) = true →
      (instAt fvs k e).looseBVarsBounded k = true := by
  intro e
  induction e with
  | bvar i =>
    intro k h
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
    simp only [instAt]
    by_cases hik : i < k
    · rw [ite_eq_left hik]; simpa [Expr.looseBVarsBounded] using hik
    · rw [ite_eq_right hik, dite_eq_left (by omega)]
      exact looseBVarsBounded_mono (Nat.zero_le k) (hfvs _ (List.getElem_mem (by omega)))
  | fvar _ _ _ => intro _ _; rfl
  | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro k h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [instAt, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b _ iht ihb =>
    intro k h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [instAt, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) (by rw [show k + 1 + fvs.length = k + fvs.length + 1 by omega]; exact h.2)⟩
  | forallE ty b _ iht ihb =>
    intro k h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [instAt, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) (by rw [show k + 1 + fvs.length = k + fvs.length + 1 by omega]; exact h.2)⟩
  | letE ty v b _ iht ihv ihb =>
    intro k h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [instAt, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩,
      ihb (k + 1) (by rw [show k + 1 + fvs.length = k + fvs.length + 1 by omega]; exact h.2)⟩
  | proj _ _ e ih =>
    intro k h
    simp only [Expr.looseBVarsBounded] at h
    simp only [instAt, Expr.looseBVarsBounded]
    exact ih k h

private theorem instantiate1_instAt {fvs : List KExpr} {fv : KExpr}
    (hfvs : ∀ x ∈ fvs, x.looseBVarsBounded 0 = true) :
    ∀ {b : KExpr} (j : Nat), b.hasFvar = false →
      (instAt fvs (j + 1) b).instantiate1 fv j = instAt (fv :: fvs) j b := by
  intro b
  induction b with
  | bvar i =>
    intro j _
    simp only [instAt, List.length_cons]
    by_cases hij : i < j
    · rw [ite_eq_left (by omega), ite_eq_left hij]
      show (if i = j then fv else if i > j then Expr.bvar (i - 1) else Expr.bvar i) = Expr.bvar i
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · by_cases heq : i = j
      · subst heq
        rw [ite_eq_left (by omega), ite_eq_right (Nat.lt_irrefl i), dite_eq_left (by omega)]
        simp [Expr.instantiate1]
      · rw [ite_eq_right (by omega), ite_eq_right hij]
        by_cases hlen : i - (j + 1) < fvs.length
        · rw [dite_eq_left hlen, dite_eq_left (by omega)]
          have hidx : i - j = (i - (j + 1)) + 1 := by omega
          simp only [hidx, List.getElem_cons_succ]
          exact instantiate1_of_bounded fv j
            (looseBVarsBounded_mono (Nat.zero_le j) (hfvs _ (List.getElem_mem hlen)))
        · rw [dite_eq_right hlen, dite_eq_right (by omega)]
          show (if i - fvs.length = j then fv
            else if i - fvs.length > j then Expr.bvar (i - fvs.length - 1)
            else Expr.bvar (i - fvs.length)) = Expr.bvar (i - (fvs.length + 1))
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
          congr 1
  | fvar _ _ _ => intro _ h; simp [Expr.hasFvar] at h
  | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro j h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, Expr.instantiate1, ihf j h.1, iha j h.2]
  | lam ty bo m iht ihb =>
    intro j h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, Expr.instantiate1, iht j h.1, ihb (j + 1) h.2]
  | forallE ty bo m iht ihb =>
    intro j h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, Expr.instantiate1, iht j h.1, ihb (j + 1) h.2]
  | letE ty va bo m iht ihv ihb =>
    intro j h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, Expr.instantiate1, iht j h.1.1, ihv j h.1.2, ihb (j + 1) h.2]
  | proj s i e ih =>
    intro j h; simp only [Expr.hasFvar] at h
    simp only [instAt, Expr.instantiate1, ih j h]

private theorem instAt_liftLooseBVars {fvs : List KExpr}
    (hfvs : ∀ x ∈ fvs, x.looseBVarsBounded 0 = true) :
    ∀ {v : KExpr} (j k : Nat), v.hasFvar = false →
      instAt fvs (k + j) (v.liftLooseBVars j k) = (instAt fvs k v).liftLooseBVars j k := by
  intro v
  induction v with
  | bvar i =>
    intro j k _
    show instAt fvs (k + j) (if i ≥ k then Expr.bvar (i + j) else Expr.bvar i) =
      Expr.liftLooseBVars j k (instAt fvs k (Expr.bvar i))
    by_cases hik : i < k
    · rw [ite_eq_right (by omega)]
      simp only [instAt, ite_eq_left (show i < k + j by omega), ite_eq_left hik]
      show Expr.bvar i = (if i ≥ k then Expr.bvar (i + j) else Expr.bvar i)
      rw [ite_eq_right (by omega)]
    · rw [ite_eq_left (by omega)]
      simp only [instAt, ite_eq_right (show ¬ (i + j < k + j) by omega), ite_eq_right hik]
      have hsub : i + j - (k + j) = i - k := by omega
      by_cases hlen : i - k < fvs.length
      · rw [dite_eq_left (by omega), dite_eq_left hlen]
        simp only [hsub]
        exact (liftLooseBVars_of_bounded j k
          (looseBVarsBounded_mono (Nat.zero_le k) (hfvs _ (List.getElem_mem hlen)))).symm
      · rw [dite_eq_right (by omega), dite_eq_right hlen]
        show Expr.bvar (i + j - fvs.length) =
          (if i - fvs.length ≥ k then Expr.bvar (i - fvs.length + j) else Expr.bvar (i - fvs.length))
        rw [ite_eq_left (by omega)]
        congr 1; omega
  | fvar _ _ _ => intro _ _ h; simp [Expr.hasFvar] at h
  | sort _ | const _ _ | lit _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro j k h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [Expr.liftLooseBVars, instAt, ihf j k h.1, iha j k h.2]
  | lam ty bo m iht ihb =>
    intro j k h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    have hb := ihb j (k + 1) h.2
    rw [show k + 1 + j = k + j + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, instAt, iht j k h.1, hb]
  | forallE ty bo m iht ihb =>
    intro j k h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    have hb := ihb j (k + 1) h.2
    rw [show k + 1 + j = k + j + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, instAt, iht j k h.1, hb]
  | letE ty va bo m iht ihv ihb =>
    intro j k h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    have hb := ihb j (k + 1) h.2
    rw [show k + 1 + j = k + j + 1 by omega] at hb
    simp only [Expr.liftLooseBVars, instAt, iht j k h.1.1, ihv j k h.1.2, hb]
  | proj s i e ih =>
    intro j k h; simp only [Expr.hasFvar] at h
    simp only [Expr.liftLooseBVars, instAt, ih j k h]

private theorem instantiate1Lift_instAt {fvs : List KExpr} {v : KExpr}
    (hfvs : ∀ x ∈ fvs, x.looseBVarsBounded 0 = true) (hv : v.hasFvar = false) :
    ∀ {b : KExpr} (j : Nat), b.hasFvar = false →
      (instAt fvs (j + 1) b).instantiate1Lift (instAt fvs 0 v) j =
        instAt fvs j (b.instantiate1Lift v j) := by
  intro b
  induction b with
  | bvar i =>
    intro j _
    by_cases hij : i < j
    · have h1 : instAt fvs (j + 1) (Expr.bvar i) = Expr.bvar i := by
        simp only [instAt, ite_eq_left (show i < j + 1 by omega)]
      have h2 : (Expr.bvar i : KExpr).instantiate1Lift (instAt fvs 0 v) j = Expr.bvar i := by
        show (if i = j then _ else if i > j then Expr.bvar (i - 1) else Expr.bvar i) = Expr.bvar i
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      have h3 : (Expr.bvar i : KExpr).instantiate1Lift v j = Expr.bvar i := by
        show (if i = j then _ else if i > j then Expr.bvar (i - 1) else Expr.bvar i) = Expr.bvar i
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      rw [h1, h2, h3]
      simp only [instAt, ite_eq_left hij]
    · by_cases heq : i = j
      · subst heq
        have h1 : instAt fvs (i + 1) (Expr.bvar i) = Expr.bvar i := by
          simp only [instAt, ite_eq_left (Nat.lt_succ_self i)]
        have h2 : (Expr.bvar i : KExpr).instantiate1Lift (instAt fvs 0 v) i =
            (instAt fvs 0 v).liftLooseBVars i 0 := by
          show (if i = i then _ else _) = _; rw [ite_eq_left rfl]
        have h3 : (Expr.bvar i : KExpr).instantiate1Lift v i = v.liftLooseBVars i 0 := by
          show (if i = i then _ else _) = _; rw [ite_eq_left rfl]
        rw [h1, h2, h3]
        have hl := instAt_liftLooseBVars hfvs i 0 hv
        rw [Nat.zero_add] at hl
        exact hl.symm
      · have hgt : i > j := by omega
        have h3 : (Expr.bvar i : KExpr).instantiate1Lift v j = Expr.bvar (i - 1) := by
          show (if i = j then _ else if i > j then Expr.bvar (i - 1) else Expr.bvar i) = _
          rw [ite_eq_right heq, ite_eq_left hgt]
        rw [h3]
        simp only [instAt, ite_eq_right (show ¬ (i < j + 1) by omega),
          ite_eq_right (show ¬ (i - 1 < j) by omega)]
        by_cases hlen : i - (j + 1) < fvs.length
        · rw [dite_eq_left hlen, dite_eq_left (by omega)]
          have hsub : i - 1 - j = i - (j + 1) := by omega
          simp only [hsub]
          exact instantiate1Lift_of_bounded j
            (looseBVarsBounded_mono (Nat.zero_le j) (hfvs _ (List.getElem_mem hlen)))
        · rw [dite_eq_right hlen, dite_eq_right (by omega)]
          show (if i - fvs.length = j then _
            else if i - fvs.length > j then Expr.bvar (i - fvs.length - 1)
            else Expr.bvar (i - fvs.length)) = Expr.bvar (i - 1 - fvs.length)
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
          congr 1; omega
  | fvar _ _ _ => intro _ h; simp [Expr.hasFvar] at h
  | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro j h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, Expr.instantiate1Lift, ihf j h.1, iha j h.2]
  | lam ty bo m iht ihb =>
    intro j h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, Expr.instantiate1Lift, iht j h.1, ihb (j + 1) h.2]
  | forallE ty bo m iht ihb =>
    intro j h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, Expr.instantiate1Lift, iht j h.1, ihb (j + 1) h.2]
  | letE ty va bo m iht ihv ihb =>
    intro j h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp only [instAt, Expr.instantiate1Lift, iht j h.1.1, ihv j h.1.2, ihb (j + 1) h.2]
  | proj s i e ih =>
    intro j h; simp only [Expr.hasFvar] at h
    simp only [instAt, Expr.instantiate1Lift, ih j h]

private theorem abstract1_instAt {fvs : List KExpr} {d : Nat} {ty' : KExpr}
    (hfvs : ∀ x ∈ fvs, FVarsLt d x = true) :
    ∀ {b' : KExpr} (k : Nat), b'.hasFvar = false →
      b'.looseBVarsBounded (k + 1 + fvs.length) = true →
      (instAt (.fvar d ty' :: fvs) k b').abstract1 d k = instAt fvs (k + 1) b' := by
  intro b'
  induction b' with
  | bvar i =>
    intro k _ hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [instAt, List.length_cons]
    by_cases hik : i < k
    · rw [ite_eq_left hik, ite_eq_left (show i < k + 1 by omega)]
      rfl
    · by_cases heq : i = k
      · subst heq
        rw [ite_eq_right (Nat.lt_irrefl i), dite_eq_left (by omega),
          ite_eq_left (Nat.lt_succ_self i)]
        simp [Expr.abstract1]
      · rw [ite_eq_right hik, dite_eq_left (by omega), ite_eq_right (show ¬ (i < k + 1) by omega),
          dite_eq_left (by omega)]
        have hidx : i - k = (i - (k + 1)) + 1 := by omega
        simp only [hidx, List.getElem_cons_succ]
        exact abstract1_of_fvarsLt k (hfvs _ (List.getElem_mem (by omega)))
  | fvar _ _ _ => intro _ h _; simp [Expr.hasFvar] at h
  | sort _ | const _ _ | lit _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro k hf hb
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [instAt, Expr.abstract1, ihf k hf.1 hb.1, iha k hf.2 hb.2]
  | lam t bo m iht ihb =>
    intro k hf hb
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hbo : bo.looseBVarsBounded (k + 1 + 1 + fvs.length) = true := by
      rw [show k + 1 + 1 + fvs.length = k + 1 + fvs.length + 1 by omega]; exact hb.2
    simp only [instAt, Expr.abstract1, iht k hf.1 hb.1, ihb (k + 1) hf.2 hbo]
  | forallE t bo m iht ihb =>
    intro k hf hb
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hbo : bo.looseBVarsBounded (k + 1 + 1 + fvs.length) = true := by
      rw [show k + 1 + 1 + fvs.length = k + 1 + fvs.length + 1 by omega]; exact hb.2
    simp only [instAt, Expr.abstract1, iht k hf.1 hb.1, ihb (k + 1) hf.2 hbo]
  | letE t va bo m iht ihv ihb =>
    intro k hf hb
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    have hbo : bo.looseBVarsBounded (k + 1 + 1 + fvs.length) = true := by
      rw [show k + 1 + 1 + fvs.length = k + 1 + fvs.length + 1 by omega]; exact hb.2
    simp only [instAt, Expr.abstract1, iht k hf.1.1 hb.1.1, ihv k hf.1.2 hb.1.2,
      ihb (k + 1) hf.2 hbo]
  | proj s i e ih =>
    intro k hf hb
    simp only [Expr.hasFvar] at hf
    simp only [Expr.looseBVarsBounded] at hb
    simp only [instAt, Expr.abstract1, ih k hf hb]

private theorem annot_instAt {e' e : KExpr} (ha : IxVM.Consistency.Annotates e' e) :
    ∀ (d : Nat) (fvs : List KExpr),
      e.hasFvar = false →
      e.looseBVarsBounded fvs.length = true →
      (∀ fv ∈ fvs, (∃ idx ty, fv = .fvar idx ty ∧ idx < d) ∧
        fv.looseBVarsBounded 0 = true ∧ FVarsLt d fv = true) →
      Annot d (instAt fvs 0 e) (instAt fvs 0 e') := by
  induction ha with
  | @bvar i =>
    intro d fvs _ hb hfvs
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [instAt, Nat.not_lt_zero, ite_false, Nat.sub_zero, dite_eq_left hb]
    obtain ⟨⟨idx, ty, heq, hlt⟩, _, _⟩ := hfvs _ (List.getElem_mem hb)
    rw [heq]
    exact .fvar hlt
  | fvar => intro _ _ hf _ _; simp [Expr.hasFvar] at hf
  | sort => intro _ _ _ _ _; exact .sort
  | const => intro _ _ _ _ _; exact .const
  | lit => intro _ _ _ _ _; exact .lit
  | app _ _ ihf iha =>
    intro d fvs hf hb hfvs
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact .app (ihf d fvs hf.1 hb.1 hfvs) (iha d fvs hf.2 hb.2 hfvs)
  | proj _ ihe =>
    intro d fvs hf hb hfvs
    simp only [Expr.hasFvar] at hf
    simp only [Expr.looseBVarsBounded] at hb
    exact .proj (ihe d fvs hf hb hfvs)
  | @lam ty' ty b' b m' m hty hb ih_ty ih_b =>
    intro d fvs hf hbd hfvs
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbd
    have hty_a := ih_ty d fvs hf.1 hbd.1 hfvs
    have hty'_nf := annotates_hasFvar_false hty hf.1
    let fv : KExpr := .fvar d (instAt fvs 0 ty')
    have hfv_bd : fv.looseBVarsBounded 0 = true := rfl
    have hfv_lt : FVarsLt (d + 1) fv = true := by
      simp only [fv, FVarsLt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Nat.lt_succ_self d,
        fvarsLt_mono (Nat.le_succ d) (fvarsLt_instAt (fun x hx => (hfvs x hx).2.2) 0 hty'_nf)⟩
    have hfvs' : ∀ x ∈ fv :: fvs, (∃ idx t, x = .fvar idx t ∧ idx < d + 1) ∧
        x.looseBVarsBounded 0 = true ∧ FVarsLt (d + 1) x = true := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨⟨d, _, rfl, Nat.lt_succ_self d⟩, hfv_bd, hfv_lt⟩
      · obtain ⟨⟨idx, t, rfl, hlt⟩, h1, h2⟩ := hfvs x hx'
        exact ⟨⟨idx, t, rfl, by omega⟩, h1, fvarsLt_mono (Nat.le_succ d) h2⟩
    have hb_a := ih_b (d + 1) (fv :: fvs) hf.2
      (by simpa [List.length_cons, Nat.add_comm] using hbd.2) hfvs'
    rw [← instantiate1_instAt (fun x hx => (hfvs x hx).2.1) 0 hf.2] at hb_a
    have habs := abstract1_instAt (d := d) (ty' := instAt fvs 0 ty')
      (fun x hx => (hfvs x hx).2.2) (b' := b') 0 (annotates_hasFvar_false hb hf.2)
      (by simpa [Nat.add_comm] using annotates_looseBVarsBounded hb (fvs.length + 1) hbd.2)
    have hm : { m with pw := m'.pw } = m' := by cases m; cases m'; simp
    simp only [instAt]
    rw [← habs, ← hm]
    exact .lam hty_a hb_a
  | @forallE ty' ty b' b m' m hty hb ih_ty ih_b =>
    intro d fvs hf hbd hfvs
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbd
    have hty_a := ih_ty d fvs hf.1 hbd.1 hfvs
    have hty'_nf := annotates_hasFvar_false hty hf.1
    let fv : KExpr := .fvar d (instAt fvs 0 ty')
    have hfv_bd : fv.looseBVarsBounded 0 = true := rfl
    have hfv_lt : FVarsLt (d + 1) fv = true := by
      simp only [fv, FVarsLt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Nat.lt_succ_self d,
        fvarsLt_mono (Nat.le_succ d) (fvarsLt_instAt (fun x hx => (hfvs x hx).2.2) 0 hty'_nf)⟩
    have hfvs' : ∀ x ∈ fv :: fvs, (∃ idx t, x = .fvar idx t ∧ idx < d + 1) ∧
        x.looseBVarsBounded 0 = true ∧ FVarsLt (d + 1) x = true := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨⟨d, _, rfl, Nat.lt_succ_self d⟩, hfv_bd, hfv_lt⟩
      · obtain ⟨⟨idx, t, rfl, hlt⟩, h1, h2⟩ := hfvs x hx'
        exact ⟨⟨idx, t, rfl, by omega⟩, h1, fvarsLt_mono (Nat.le_succ d) h2⟩
    have hb_a := ih_b (d + 1) (fv :: fvs) hf.2
      (by simpa [List.length_cons, Nat.add_comm] using hbd.2) hfvs'
    rw [← instantiate1_instAt (fun x hx => (hfvs x hx).2.1) 0 hf.2] at hb_a
    have habs := abstract1_instAt (d := d) (ty' := instAt fvs 0 ty')
      (fun x hx => (hfvs x hx).2.2) (b' := b') 0 (annotates_hasFvar_false hb hf.2)
      (by simpa [Nat.add_comm] using annotates_looseBVarsBounded hb (fvs.length + 1) hbd.2)
    have hm : { m with pw := m'.pw } = m' := by cases m; cases m'; simp
    simp only [instAt]
    rw [← habs, ← hm]
    exact .forallE hty_a hb_a
  | @letE e' ty v b m hlet ih =>
    intro d fvs hf hbd hfvs
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbd
    have hv_nf : (b.instantiate1Lift v 0).hasFvar = false := by
      have hlift : ∀ (x : KExpr) (n c : Nat), x.hasFvar = false →
          (x.liftLooseBVars n c).hasFvar = false := by
        intro x
        induction x with
        | bvar _ => intro n c _; simp only [Expr.liftLooseBVars]; split <;> rfl
        | fvar _ _ _ => intro _ _ hx; simp [Expr.hasFvar] at hx
        | sort _ | const _ _ | lit _ => intro _ _ _; rfl
        | app f a ih1 ih2 =>
          intro n c hx; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
          simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
          exact ⟨ih1 n c hx.1, ih2 n c hx.2⟩
        | lam t bo _ ih1 ih2 =>
          intro n c hx; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
          simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
          exact ⟨ih1 n c hx.1, ih2 n (c + 1) hx.2⟩
        | forallE t bo _ ih1 ih2 =>
          intro n c hx; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
          simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
          exact ⟨ih1 n c hx.1, ih2 n (c + 1) hx.2⟩
        | letE t va bo _ ih1 ih2 ih3 =>
          intro n c hx; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
          simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
          exact ⟨⟨ih1 n c hx.1.1, ih2 n c hx.1.2⟩, ih3 n (c + 1) hx.2⟩
        | proj _ _ s ih1 =>
          intro n c hx; simp only [Expr.hasFvar] at hx
          simp only [Expr.liftLooseBVars, Expr.hasFvar]; exact ih1 n c hx
      have hinst : ∀ (bo : KExpr) (j : Nat), bo.hasFvar = false →
          (bo.instantiate1Lift v j).hasFvar = false := by
        intro bo
        induction bo with
        | bvar i =>
          intro j _; simp only [Expr.instantiate1Lift]; split
          · exact hlift v j 0 hf.1.2
          · split <;> rfl
        | fvar _ _ _ => intro _ hbo; simp [Expr.hasFvar] at hbo
        | sort _ | const _ _ | lit _ => intro _ _; rfl
        | app f a ih1 ih2 =>
          intro j hbo; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
          simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
          exact ⟨ih1 j hbo.1, ih2 j hbo.2⟩
        | lam t bo _ ih1 ih2 =>
          intro j hbo; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
          simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
          exact ⟨ih1 j hbo.1, ih2 (j + 1) hbo.2⟩
        | forallE t bo _ ih1 ih2 =>
          intro j hbo; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
          simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
          exact ⟨ih1 j hbo.1, ih2 (j + 1) hbo.2⟩
        | letE t va bo _ ih1 ih2 ih3 =>
          intro j hbo; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
          simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
          exact ⟨⟨ih1 j hbo.1.1, ih2 j hbo.1.2⟩, ih3 (j + 1) hbo.2⟩
        | proj _ _ s ih1 =>
          intro j hbo; simp only [Expr.hasFvar] at hbo
          simp only [Expr.instantiate1Lift, Expr.hasFvar]; exact ih1 j hbo
      exact hinst b 0 hf.2
    have hv_bd : (b.instantiate1Lift v 0).looseBVarsBounded fvs.length = true :=
      looseBVarsBounded_instantiate1Lift (Nat.zero_le _) hbd.2 (by simpa using hbd.1.2)
    have hrec := ih d fvs hv_nf hv_bd hfvs
    rw [← instantiate1Lift_instAt (fun x hx => (hfvs x hx).2.1) hf.1.2 0 hf.2] at hrec
    have hv0_bd : (instAt fvs 0 v).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instAt (fun x hx => (hfvs x hx).2.1) 0 (by simpa using hbd.1.2)
    rw [Expr.instantiate1Lift_eq_instantiate1 hv0_bd] at hrec
    exact .letE hrec

/-- **Bridge from `IxVM.Consistency.Annotates` to `Ix.Kernel.Rules.Annot`**: on any closed raw
expression `e` (`e.hasFvar = false` and `e.looseBVarsBounded 0 = true`), `Annotates e' e` yields
`Annot d e e'` (`rulesJ.annot env d e e'`) at every depth `d`. -/
theorem annot_of_annotates {e' e : KExpr} (ha : IxVM.Consistency.Annotates e' e)
    (hf : e.hasFvar = false) (hb : e.looseBVarsBounded 0 = true) (d : Nat) :
    Annot d e e' := by
  have h := annot_instAt ha d [] hf hb (fun _ hm => nomatch hm)
  rwa [instAt_nil, instAt_nil] at h

/-! ## Extracting `constsResolve` from full-grade `Rules.Infer` -/

/-- Every opened variable inside `e` has a type whose constants resolve in `env`. -/
def FvarConstsResolve (env : Ix.Kernel.Env .anon) : KExpr → Prop
  | .bvar _ | .sort _ | .const _ _ | .lit _ => True
  | .fvar _ ty => ty.constsResolve env = true ∧ FvarConstsResolve env ty
  | .app f a => FvarConstsResolve env f ∧ FvarConstsResolve env a
  | .lam ty b _ | .forallE ty b _ => FvarConstsResolve env ty ∧ FvarConstsResolve env b
  | .letE ty v b _ => FvarConstsResolve env ty ∧ FvarConstsResolve env v ∧ FvarConstsResolve env b
  | .proj _ _ e => FvarConstsResolve env e

theorem fvarConstsResolve_of_hasFvar_false {env : Ix.Kernel.Env .anon} :
    ∀ {e : KExpr}, e.hasFvar = false → FvarConstsResolve env e := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _; trivial
  | fvar _ _ _ => intro h; simp [Expr.hasFvar] at h
  | app f a ihf iha =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h; exact ⟨ihf h.1, iha h.2⟩
  | lam ty b _ iht ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h; exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b _ iht ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h; exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b _ iht ihv ihb =>
    intro h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | proj _ _ e ih =>
    intro h; simp only [Expr.hasFvar] at h; exact ih h

private theorem fvarConstsResolve_instantiate1 {env : Ix.Kernel.Env .anon} {v : KExpr}
    (hv : FvarConstsResolve env v) :
    ∀ {e : KExpr} (k : Nat), FvarConstsResolve env e → FvarConstsResolve env (e.instantiate1 v k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> trivial
  | fvar _ _ _ => intro _ h; exact h
  | sort _ | const _ _ | lit _ => intro _ _; trivial
  | app f a ihf iha => intro k h; exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b _ iht ihb => intro k h; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b _ iht ihb => intro k h; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty va b _ iht ihv ihb => intro k h; exact ⟨iht k h.1, ihv k h.2.1, ihb (k + 1) h.2.2⟩
  | proj _ _ e ih => intro k h; exact ih k h

private theorem constsResolve_of_instantiate1 {env : Ix.Kernel.Env .anon} {v : KExpr} :
    ∀ {e : KExpr} (k : Nat), (e.instantiate1 v k).constsResolve env = true →
      e.constsResolve env = true := by
  intro e
  induction e with
  | bvar _ => intro _ _; rfl
  | sort _ | lit _ | const _ _ => intro _ h; exact h
  | fvar _ _ _ => intro _ h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b _ iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b _ iht ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty va b _ iht ihv ihb =>
    intro k h
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj _ _ e ih =>
    intro k h
    simp only [Expr.instantiate1, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih k h.2⟩

private theorem isSome_of_natLitSupported {env : Ix.Kernel.Env .anon}
    (h : Ix.Kernel.natLitSupported env = true) :
    ((env.find? Ix.Kernel.natName).isSome &&
      (env.find? Ix.Kernel.natZeroName).isSome &&
      (env.find? Ix.Kernel.natSuccName).isSome) = true := by
  simp only [Ix.Kernel.natLitSupported, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  cases hf1 : env.find? Ix.Kernel.natName with
  | none => simp [hf1, Ix.Kernel.natIndOk] at h1
  | some _ =>
    cases hf2 : env.find? Ix.Kernel.natZeroName with
    | none => simp [hf2, Ix.Kernel.natZeroOk] at h2
    | some _ =>
      cases hf3 : env.find? Ix.Kernel.natSuccName with
      | none => simp [hf3, Ix.Kernel.natSuccOk] at h3
      | some _ => rfl

private theorem isSome_of_strLitSupported {env : Ix.Kernel.Env .anon}
    (h : Ix.Kernel.strLitSupported env = true) (s : String) :
    (Expr.lit (md := .anon) (.strVal s)).constsResolve env = true := by
  simp only [Ix.Kernel.strLitSupported, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hnat, hs⟩, hsl⟩, hl⟩, hln⟩, hlc⟩, hc⟩, hcn⟩ := h
  have hnat' := isSome_of_natLitSupported hnat
  simp only [Bool.and_eq_true] at hnat'
  have isSome_s : (env.find? Ix.Kernel.stringName).isSome = true := by
    cases hf : env.find? Ix.Kernel.stringName <;> simp_all [Ix.Kernel.stringTyOk]
  have isSome_sl : (env.find? Ix.Kernel.stringOfListName).isSome = true := by
    cases hf : env.find? Ix.Kernel.stringOfListName <;> simp_all [Ix.Kernel.stringOfListTyOk]
  have isSome_l : (env.find? Ix.Kernel.listName).isSome = true := by
    cases hf : env.find? Ix.Kernel.listName <;> simp_all [Ix.Kernel.listTyOk]
  have isSome_ln : (env.find? Ix.Kernel.listNilName).isSome = true := by
    cases hf : env.find? Ix.Kernel.listNilName <;> simp_all [Ix.Kernel.listNilTyOk]
  have isSome_lc : (env.find? Ix.Kernel.listConsName).isSome = true := by
    cases hf : env.find? Ix.Kernel.listConsName <;> simp_all [Ix.Kernel.listConsTyOk]
  have isSome_c : (env.find? Ix.Kernel.charName).isSome = true := by
    cases hf : env.find? Ix.Kernel.charName <;> simp_all [Ix.Kernel.charTyOk]
  have isSome_cn : (env.find? Ix.Kernel.charOfNatName).isSome = true := by
    cases hf : env.find? Ix.Kernel.charOfNatName <;> simp_all [Ix.Kernel.charOfNatTyOk]
  simp [Expr.constsResolve, hnat'.1.1, hnat'.1.2, hnat'.2, isSome_s, isSome_sl, isSome_l,
    isSome_ln, isSome_lc, isSome_c, isSome_cn]

private def exprDepth : KExpr → Nat
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => 1 + max (exprDepth f) (exprDepth a)
  | .lam ty b _ | .forallE ty b _ => 1 + max (exprDepth ty) (exprDepth b)
  | .letE ty v b _ => 1 + max (max (exprDepth ty) (exprDepth v)) (exprDepth b)
  | .proj _ _ e => 1 + exprDepth e

private theorem exprDepth_instantiate1_fvar (d : Nat) (ty : KExpr) :
    ∀ (e : KExpr) (k : Nat), exprDepth (e.instantiate1 (.fvar d ty) k) = exprDepth e := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app f a ihf iha => intro k; simp only [Expr.instantiate1, exprDepth, ihf k, iha k]
  | lam t b _ iht ihb => intro k; simp only [Expr.instantiate1, exprDepth, iht k, ihb (k + 1)]
  | forallE t b _ iht ihb => intro k; simp only [Expr.instantiate1, exprDepth, iht k, ihb (k + 1)]
  | letE t v b _ iht ihv ihb =>
    intro k; simp only [Expr.instantiate1, exprDepth, iht k, ihv k, ihb (k + 1)]
  | proj _ _ e ih => intro k; simp only [Expr.instantiate1, exprDepth, ih k]

private theorem infer_constsResolve_aux :
    ∀ (n : Nat) {env : Ix.Kernel.Env .anon} {g : Ix.Kernel.Rules.Grade}
      {d : Nat} {e t : KExpr},
      exprDepth e ≤ n → Infer env g d e t → g = .full →
      Ix.Kernel.Open.StoreInv env → FvarConstsResolve env e →
      e.constsResolve env = true := by
  intro n
  induction n with
  | zero =>
    intro env g d e t hdep hinf hg _ hfv
    cases hinf with
    | sort => rfl
    | fvar _ => exact hfv.1
    | const hfind _ _ => simp [Expr.constsResolve, hfind]
    | natLit hnat => exact isSome_of_natLitSupported hnat
    | @strLit _ _ s hstr => exact isSome_of_strLitSupported hstr s
    | forallE => simp only [exprDepth] at hdep; omega
    | lam => simp only [exprDepth] at hdep; omega
    | app => simp only [exprDepth] at hdep; omega
    | appSkip => nomatch hg
    | proj => simp only [exprDepth] at hdep; omega
  | succ n ih =>
    intro env g d e t hdep hinf hg hstore hfv
    cases hinf with
    | sort => rfl
    | fvar _ => exact hfv.1
    | const hfind _ _ => simp [Expr.constsResolve, hfind]
    | natLit hnat => exact isSome_of_natLitSupported hnat
    | @strLit _ _ s hstr => exact isSome_of_strLitSupported hstr s
    | forallE hty _ hbo _ _ =>
      simp only [exprDepth] at hdep
      have hty_res := ih (by omega) hty hg hstore hfv.1
      have hbo_res := ih (by rw [exprDepth_instantiate1_fvar]; omega)
        hbo hg hstore
        (fvarConstsResolve_instantiate1 (v := .fvar _ _) ⟨hty_res, hfv.1⟩ 0 hfv.2)
      simp only [Expr.constsResolve, Bool.and_eq_true]
      exact ⟨hty_res, constsResolve_of_instantiate1 0 hbo_res⟩
    | lam hty _ hbo _ _ _ _ =>
      simp only [exprDepth] at hdep
      have hty_res := ih (by omega) (hty hg) rfl hstore hfv.1
      have hbo_res := ih (by rw [exprDepth_instantiate1_fvar]; omega)
        hbo hg hstore
        (fvarConstsResolve_instantiate1 (v := .fvar _ _) ⟨hty_res, hfv.1⟩ 0 hfv.2)
      simp only [Expr.constsResolve, Bool.and_eq_true]
      exact ⟨hty_res, constsResolve_of_instantiate1 0 hbo_res⟩
    | app hfn _ harg _ =>
      simp only [exprDepth] at hdep
      simp only [Expr.constsResolve, Bool.and_eq_true]
      exact ⟨ih (by omega) hfn hg hstore hfv.1, ih (by omega) harg hg hstore hfv.2⟩
    | appSkip => nomatch hg
    | @proj _ _ sn i pe _ _ _ entry hpe _ _ hent _ _ _ =>
      simp only [exprDepth] at hdep
      simp only [Expr.constsResolve, Bool.and_eq_true]
      refine ⟨?_, ih (by omega) hpe hg hstore hfv⟩
      obtain ⟨tbl, hf, hi, _⟩ := Ix.Kernel.Env.findProj?_some hent
      obtain ⟨_, _, _, ⟨cvT, caps, hT, _, _⟩, _⟩ := hstore.proj_ok _ tbl hf i hi
      have hsn : tbl.structName = sn := by
        have hf' : env.consts.find? (·.name == Ix.Kernel.projTableName sn) =
            some (.projInfo tbl) := hf
        have hname := List.find?_some hf'
        exact Ix.Kernel.projTableName_inj (beq_iff_eq.mp hname)
      simp only [Ix.Kernel.ProjTable.entry, hsn] at hT
      simp [hT]

/-- Full-grade `Rules.Infer` under `StoreInv env` guarantees `e.constsResolve env = true` whenever
all opened variables already in `e` satisfy `FvarConstsResolve env e`. -/
theorem infer_constsResolve_open {env : Ix.Kernel.Env .anon} {g : Ix.Kernel.Rules.Grade}
    {d : Nat} {e t : KExpr} (hinf : Infer env g d e t) (hg : g = .full)
    (hstore : Ix.Kernel.Open.StoreInv env) (hfv : FvarConstsResolve env e) :
    e.constsResolve env = true :=
  infer_constsResolve_aux (exprDepth e) (Nat.le_refl _) hinf hg hstore hfv

/-- Closed specialization: full-grade `Rules.Infer` on an fvar-free expression guarantees
`e.constsResolve env = true`. -/
theorem infer_constsResolve {env : Ix.Kernel.Env .anon} {d : Nat} {e t : KExpr}
    (hinf : Infer env .full d e t) (hstore : Ix.Kernel.Open.StoreInv env)
    (hfv : e.hasFvar = false) :
    e.constsResolve env = true :=
  infer_constsResolve_open hinf rfl hstore (fvarConstsResolve_of_hasFvar_false hfv)

/-! ## `InstallStep` and `DeclBasisRun` constructors -/

/-- Any declaration with `installs d = []` installs into `env` itself (`new = []`), preserving
`DeclInv` identically. -/
theorem installStep_empty {env : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (hempty : IxVM.Consistency.installs d = []) :
    IxVM.Consistency.InstallStep env d env := by
  refine ⟨[], rfl, List.nodup_nil, ?_, ?_, ?_⟩
  · intro _ h; cases h
  · rw [hempty]; intro _ h; cases h
  · intro _ h; cases h

/-- Single-constant install (`new = [ci]`) when `installs d = [ci₀]` and `StoredAs ci ci₀`. -/
theorem installStep_single {env : Ix.Kernel.Env .anon} {d : Declaration .anon}
    {ci ci₀ : ConstantInfo .anon}
    (hinst : IxVM.Consistency.installs d = [ci₀])
    (hst : IxVM.Consistency.StoredAs ci ci₀)
    (hfresh : env.find? ci.name = none) :
    IxVM.Consistency.InstallStep env d ⟨ci :: env.consts⟩ := by
  refine ⟨[ci], rfl, List.nodup_singleton _, ?_, ?_, ?_⟩
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact hfresh
  · rw [hinst]
    intro c hc
    obtain rfl := List.mem_singleton.mp hc
    exact ⟨ci, List.mem_singleton.mpr rfl, hst⟩
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    rw [hinst]
    exact Or.inl ⟨ci₀, List.mem_singleton.mpr rfl, hst.name_eq.symm⟩

private def exprNoLet : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => exprNoLet ty
  | .app f a => exprNoLet f && exprNoLet a
  | .lam ty b _ | .forallE ty b _ => exprNoLet ty && exprNoLet b
  | .letE _ _ _ _ => false
  | .proj _ _ e => exprNoLet e

private theorem annotates_refl_of_noLet :
    ∀ {e : KExpr}, exprNoLet e = true → IxVM.Consistency.Annotates e e := by
  intro e
  induction e with
  | bvar _ => intro _; exact .bvar
  | sort _ => intro _; exact .sort
  | const _ _ => intro _; exact .const
  | lit _ => intro _; exact .lit
  | fvar _ _ ih => intro h; exact .fvar (ih h)
  | app f a ihf iha =>
    intro h; simp only [exprNoLet, Bool.and_eq_true] at h; exact .app (ihf h.1) (iha h.2)
  | lam ty b _ iht ihb =>
    intro h; simp only [exprNoLet, Bool.and_eq_true] at h; exact .lam (iht h.1) (ihb h.2)
  | forallE ty b _ iht ihb =>
    intro h; simp only [exprNoLet, Bool.and_eq_true] at h; exact .forallE (iht h.1) (ihb h.2)
  | letE _ _ _ _ => intro h; cases h
  | proj _ _ e ih => intro h; exact .proj (ih h)

private def ciNoLet : ConstantInfo .anon → Bool
  | .axiomInfo cv => exprNoLet cv.type
  | .defnInfo cv v _ => exprNoLet cv.type && exprNoLet v
  | .thmInfo cv v => exprNoLet cv.type && exprNoLet v
  | .indInfo cv _ => exprNoLet cv.type
  | .ctorInfo cv _ _ => exprNoLet cv.type
  | .recInfo cv _ _ rules => exprNoLet cv.type && rules.all (fun rl => exprNoLet rl.rhs)
  | .projInfo _ => false

private theorem forall₂_ruleStored_refl :
    ∀ (rules : List (RecRule .anon)),
      rules.all (fun rl => exprNoLet rl.rhs) = true →
      List.Forall₂ IxVM.Consistency.RuleStored rules rules
  | [], _ => .nil
  | rl :: rls, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact .cons ⟨rfl, rfl, annotates_refl_of_noLet h.1⟩ (forall₂_ruleStored_refl rls h.2)

private theorem storedAs_refl_of_ciNoLet {ci : ConstantInfo .anon} (h : ciNoLet ci = true) :
    IxVM.Consistency.StoredAs ci ci := by
  cases ci with
  | axiomInfo cv =>
    exact ⟨⟨rfl, rfl, annotates_refl_of_noLet h⟩, trivial⟩
  | defnInfo cv v hint =>
    simp only [ciNoLet, Bool.and_eq_true] at h
    exact ⟨⟨rfl, rfl, annotates_refl_of_noLet h.1⟩, annotates_refl_of_noLet h.2, rfl⟩
  | thmInfo cv v =>
    simp only [ciNoLet, Bool.and_eq_true] at h
    exact ⟨⟨rfl, rfl, annotates_refl_of_noLet h.1⟩, annotates_refl_of_noLet h.2⟩
  | indInfo cv caps =>
    exact ⟨⟨rfl, rfl, annotates_refl_of_noLet h⟩, trivial⟩
  | ctorInfo cv nP nF =>
    exact ⟨⟨rfl, rfl, annotates_refl_of_noLet h⟩, rfl, rfl⟩
  | recInfo cv mI rP rules =>
    simp only [ciNoLet, Bool.and_eq_true] at h
    exact ⟨⟨rfl, rfl, annotates_refl_of_noLet h.1⟩, rfl, rfl, forall₂_ruleStored_refl rules h.2⟩
  | projInfo _ => cases h

theorem basis_declsA_noLet (kind : BasisKind) :
    (kind.declsA (md := .anon)).all ciNoLet = true := by
  cases kind <;> decide

theorem basis_declsA_nodup (kind : BasisKind) :
    ((kind.declsA (md := .anon)).map (·.name)).Nodup := by
  cases kind <;> decide

theorem basisInstallRun_of_fresh :
    ∀ (cs : List (ConstantInfo .anon)) (env : Ix.Kernel.Env .anon),
      (cs.map (·.name)).Nodup →
      (∀ ci ∈ cs, env.find? ci.name = none) →
      BasisInstallRun env cs ⟨cs.reverse ++ env.consts⟩
  | [], env, _, _ => rfl
  | ci :: rest, env, hnd, hfresh => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hci : (env.find? ci.name).isNone = true := by
      rw [hfresh ci (List.mem_cons.mpr (Or.inl rfl))]; rfl
    have hrest : ∀ c ∈ rest, (Ix.Kernel.Env.mk (ci :: env.consts)).find? c.name = none := by
      intro c hc
      have hne : ci.name ≠ c.name := fun he => hnd.1 (he ▸ List.mem_map.mpr ⟨c, hc, rfl⟩)
      simp only [Ix.Kernel.Env.find?, List.find?_cons]
      have hbeq : (ci.name == c.name) = false := beq_false_of_ne hne
      rw [hbeq]
      exact hfresh c (List.mem_cons.mpr (Or.inr hc))
    have ih := basisInstallRun_of_fresh rest ⟨ci :: env.consts⟩ hnd.2 hrest
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact ⟨hci, ih⟩

/-- Construct both `DeclBasisRun env kind ⟨kind.declsA.reverse ++ env.consts⟩` and `InstallStep`
for any declaration whose `installs d = kind.declsA`. -/
theorem basis_step_of_fresh {env : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (kind : BasisKind) (hinst : IxVM.Consistency.installs d = kind.declsA)
    (heq : kind = .quotK → env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    (hfresh : ∀ ci ∈ kind.declsA (md := .anon), env.find? ci.name = none) :
    DeclBasisRun env kind ⟨kind.declsA.reverse ++ env.consts⟩ ∧
      IxVM.Consistency.InstallStep env d ⟨kind.declsA.reverse ++ env.consts⟩ := by
  have hnd := basis_declsA_nodup kind
  have hrun : DeclBasisRun env kind ⟨kind.declsA.reverse ++ env.consts⟩ :=
    ⟨heq, basisInstallRun_of_fresh kind.declsA env hnd hfresh⟩
  refine ⟨hrun, kind.declsA.reverse, rfl, ?_, ?_, ?_, ?_⟩
  · rw [List.map_reverse]
    exact List.nodup_reverse.mpr hnd
  · intro ci hci
    exact hfresh ci (List.mem_reverse.mp hci)
  · rw [hinst]
    intro ci₀ hci₀
    have hnl := List.all_eq_true.mp (basis_declsA_noLet kind) ci₀ hci₀
    exact ⟨ci₀, List.mem_reverse.mpr hci₀, storedAs_refl_of_ciNoLet hnl⟩
  · rw [hinst]
    intro ci hci
    exact Or.inl ⟨ci, List.mem_reverse.mp hci, rfl⟩

private theorem exists_storedAs_list :
    ∀ (l : List (ConstantInfo .anon)),
      (∀ ci₀ ∈ l, ∃ ci, IxVM.Consistency.StoredAs ci ci₀) →
      ∃ new : List (ConstantInfo .anon),
        new.map (·.name) = l.map (·.name) ∧
        (∀ ci₀ ∈ l, ∃ ci ∈ new, IxVM.Consistency.StoredAs ci ci₀) ∧
        (∀ ci ∈ new, ∃ ci₀ ∈ l, ci₀.name = ci.name)
  | [], _ => ⟨[], rfl, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | ci₀ :: tl, h => by
    obtain ⟨ci, hci⟩ := h ci₀ List.mem_cons_self
    obtain ⟨rest, hnames, hcov, hextra⟩ :=
      exists_storedAs_list tl (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨ci :: rest, ?_, ?_, ?_⟩
    · simp [hci.name_eq, hnames]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hxtl
      · exact ⟨ci, List.mem_cons_self, hci⟩
      · obtain ⟨ci', hmem, hs⟩ := hcov x hxtl
        exact ⟨ci', List.mem_cons_of_mem _ hmem, hs⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hytl
      · exact ⟨ci₀, List.mem_cons_self, hci.name_eq.symm⟩
      · obtain ⟨x, hmem, hn⟩ := hextra y hytl
        exact ⟨x, List.mem_cons_of_mem _ hmem, hn⟩

/-- Fallback `InstallStep` from `S0.Checked`'s `StoredAs` witnesses alone (used only in the
vacuous `¬ DeclStoreInv env` branch to satisfy the quantifier order of `Decls`). -/
theorem installStep_of_checked_fresh {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {d : Declaration .anon} (hchk : S0.Checked calls env d)
    (hnd : ((IxVM.Consistency.installs d).map (·.name)).Nodup)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none) :
    ∃ env₀, IxVM.Consistency.InstallStep env d env₀ := by
  obtain ⟨_, _, _, _, _, hall⟩ := hchk
  have hex : ∀ ci₀ ∈ IxVM.Consistency.installs d, ∃ ci, IxVM.Consistency.StoredAs ci ci₀ := by
    intro ci₀ h
    obtain ⟨_, _, _, _, _, _, _, _, ci, _, _, _, _, _, hs⟩ := hall ci₀ h
    exact ⟨ci, hs⟩
  obtain ⟨new, hnames, hcov, hextra⟩ := exists_storedAs_list (IxVM.Consistency.installs d) hex
  refine ⟨⟨new ++ env.consts⟩, new, rfl, hnames ▸ hnd, ?_, hcov, fun ci hci => Or.inl (hextra ci hci)⟩
  intro ci hci
  obtain ⟨ci₀, hmem, hneq⟩ := hextra ci hci
  rw [← hneq]
  exact hfresh ci₀ hmem

/-- Lift a store-assumed declaration step `(DeclStoreInv env → ∃ env₂, InstallStep ∧ DeclRunJ)`
to the full `Decls` step obligation with `∃ env₂` outside `∀ V, DeclInv V env → DeclInv V env₂`. -/
theorem decls_step_of_store {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {d : Declaration .anon} (hchk : S0.Checked calls env d)
    (hnd : ((IxVM.Consistency.installs d).map (·.name)).Nodup)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs d, env.find? ci₀.name = none)
    (hstep : DeclStoreInv env →
      ∃ env₂, IxVM.Consistency.InstallStep env d env₂ ∧
        DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    ∃ env₂, IxVM.Consistency.InstallStep env d env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  by_cases hS : DeclStoreInv env
  · obtain ⟨env₂, hinst, hrun⟩ := hstep hS
    exact ⟨env₂, hinst, fun _ _ hInv => hInv.step_declRunJ hrun⟩
  · obtain ⟨env₀, hinst⟩ := installStep_of_checked_fresh hchk hnd hfresh
    exact ⟨env₀, hinst, fun _ _ hInv => absurd hInv.store hS⟩

/-! ## `Core S₀` and `Levels` collision-free wrappers -/

/-- Allocating `"Nil"` on `h` represents the empty context at depth `0` for any ghost `Γ`. -/
theorem typesRep_alloc_nil (κ : _root_.Address → KKey) (Γ : Nat → KExpr) (h : Heap F) :
    TypesRep κ Γ (h ++ [.construct kexprListEnum "Nil" []]) 0
      (.ptr (.enum kexprListEnum) h.length) :=
  .nil (by simp)

/-- Any ghost context is vacuously `GhostScoped` at depth `0`. -/
theorem ghostScoped_zero (Γ : Nat → KExpr) : GhostScoped Γ 0 :=
  fun _ hj => absurd hj (Nat.not_lt_zero _)

/-- Extending a heap by appending cells is a `Heap.Extends`. -/
theorem heap_extends_append (h extra : Heap F) : Heap.Extends h (h ++ extra) :=
  ⟨extra, rfl⟩

/-- Collision-free `whnf` from `Core S₀` under `Good`. -/
theorem core_whnf (hCore : IxVM.Consistency.Core S₀) {c : Ctx} {Γ : Nat → KExpr} {d : Nat}
    {rc types e r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {te : KExpr}
    (hrc : RCRep c.t c.lim h rc) (hty : TypesRep c.κ Γ h d types) (hsc : GhostScoped Γ d)
    (hef : EnvFacts c) (hlf : LoadFacts c) (hgood : Good c cs)
    (ev : ObsFn W "KernelWhnf::whnf" [rc, e, types] h r h' cs)
    (hte : Tm c.κ d Γ h 0 te e) :
    ∃ te', Tm c.κ d Γ h' 0 te' r ∧ Red c.env d te te' := by
  have hctx : S0.ctx c.E c.env ⟨c.κ, Γ⟩ d h rc types :=
    ⟨c.t, c.lim, rfl, hrc, hty, hsc, hef, hlf⟩
  rcases (hCore c.E c.env ⟨c.κ, Γ⟩ d rc types h h' cs hctx hgood.2).1 e r te ev hte with
    hcol | hres
  · exact absurd hcol hgood.1
  · exact hres

/-- Collision-free `k_is_def_eq` from `Core S₀` under `Good`. -/
theorem core_defeq (hCore : IxVM.Consistency.Core S₀) {c : Ctx} {Γ : Nat → KExpr} {d : Nat}
    {rc types a b : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {ta tb : KExpr}
    (hrc : RCRep c.t c.lim h rc) (hty : TypesRep c.κ Γ h d types) (hsc : GhostScoped Γ d)
    (hef : EnvFacts c) (hlf : LoadFacts c) (hgood : Good c cs)
    (ev : ObsFn W "KernelDefEq::k_is_def_eq" [rc, a, b, types] h (.field 1) h' cs)
    (hta : Tm c.κ d Γ h 0 ta a) (htb : Tm c.κ d Γ h 0 tb b) :
    DefEq c.env d ta tb := by
  have hctx : S0.ctx c.E c.env ⟨c.κ, Γ⟩ d h rc types :=
    ⟨c.t, c.lim, rfl, hrc, hty, hsc, hef, hlf⟩
  rcases (hCore c.E c.env ⟨c.κ, Γ⟩ d rc types h h' cs hctx hgood.2).2.1 a b ta tb ev hta htb with
    hcol | hres
  · exact absurd hcol hgood.1
  · exact hres

/-- Collision-free `k_infer` from `Core S₀` under `Good`. -/
theorem core_infer (hCore : IxVM.Consistency.Core S₀) {c : Ctx} {Γ : Nat → KExpr} {d : Nat}
    {rc types e r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {te : KExpr}
    (hrc : RCRep c.t c.lim h rc) (hty : TypesRep c.κ Γ h d types) (hsc : GhostScoped Γ d)
    (hef : EnvFacts c) (hlf : LoadFacts c) (hgood : Good c cs)
    (ev : ObsFn W "KernelInfer::k_infer" [rc, e, types] h r h' cs)
    (hte : Tm c.κ d Γ h 0 te e) :
    ∃ tt, Tm c.κ d Γ h' 0 tt r ∧ Infer c.env .full d te tt := by
  have hctx : S0.ctx c.E c.env ⟨c.κ, Γ⟩ d h rc types :=
    ⟨c.t, c.lim, rfl, hrc, hty, hsc, hef, hlf⟩
  rcases (hCore c.E c.env ⟨c.κ, Γ⟩ d rc types h h' cs hctx hgood.2).2.2 e r te ev hte with
    hcol | hres
  · exact absurd hcol hgood.1
  · exact hres

/-- Collision-free `KernelInfer::k_ensure_sort` derived from `Core S₀` (`k_infer` + `whnf`). -/
theorem core_ensure_sort (hCore : IxVM.Consistency.Core S₀) {c : Ctx} {Γ : Nat → KExpr} {d : Nat}
    {rc types e r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {te : KExpr}
    (hrc : RCRep c.t c.lim h rc) (hty : TypesRep c.κ Γ h d types) (hsc : GhostScoped Γ d)
    (hef : EnvFacts c) (hlf : LoadFacts c) (hgood : Good c cs)
    (ev : ObsFn W "KernelInfer::k_ensure_sort" [rc, e, types] h r h' cs)
    (hte : Tm c.κ d Γ h 0 te e) :
    ∃ stype u ℓ, Infer c.env .full d te stype ∧ Red c.env d stype (.sort u) ∧
      RepKLevel h' ℓ r ∧ LvEq u ℓ := by
  obtain ⟨v1, m2, cs12, v39, m40, cs50, x_l, ev14, ev52, ld88, he102, he103, hc104⟩ :=
    Obs.«KernelInfer::k_ensure_sort».obs ev
  subst hc104
  obtain ⟨T, hT, hinf⟩ := core_infer hCore hrc hty hsc hef hlf
    (hgood.sub fun x hx => by simp [hx]) ev14 hte
  have e1 := ObsFn.heap_extends ev14
  obtain ⟨T', hT', hred⟩ := core_whnf hCore (hrc.mono e1) (hty.mono e1) hsc hef hlf
    (hgood.sub fun x hx => by simp [hx]) ev52 hT
  obtain ⟨u, rfl, ℓ, hℓ, hu⟩ := hT'.sort_of_load ld88
  rw [he102, he103]
  exact ⟨T, u, ℓ, hinf, hred, hℓ, hu⟩

/-- Collision-free `KernelInfer::k_check` derived from `Core S₀` (`k_infer` + `k_is_def_eq`). -/
theorem core_check (hCore : IxVM.Consistency.Core S₀) {c : Ctx} {Γ : Nat → KExpr} {d : Nat}
    {rc types e x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {te tx : KExpr}
    (hrc : RCRep c.t c.lim h rc) (hty : TypesRep c.κ Γ h d types) (hsc : GhostScoped Γ d)
    (hef : EnvFacts c) (hlf : LoadFacts c) (hgood : Good c cs)
    (ev : ObsFn W "KernelInfer::k_check" [rc, e, x, types] h r h' cs)
    (hte : Tm c.κ d Γ h 0 te e) (htx : Tm c.κ d Γ h 0 tx x) :
    ∃ tt, Infer c.env .full d te tt ∧ DefEq c.env d tt tx := by
  obtain ⟨v1, m2, cs12, v39, m40, cs50, ev14, ev52, heq111, -, -, hc116⟩ :=
    Obs.«KernelInfer::k_check».obs ev
  subst hc116 heq111
  obtain ⟨T, hT, hinf⟩ := core_infer hCore hrc hty hsc hef hlf
    (hgood.sub fun z hz => by simp [hz]) ev14 hte
  have e1 := ObsFn.heap_extends ev14
  have hde := core_defeq hCore (hrc.mono e1) (hty.mono e1) hsc hef hlf
    (hgood.sub fun z hz => by simp [hz]) ev52 hT (htx.mono e1)
  exact ⟨T, hinf, hde⟩

/-- Wrapper for `KernelLevels::level_equal` returning `1` from `L2` (`IxVM.Consistency.Levels`). -/
theorem levels_equal_one (hLevels : IxVM.Consistency.Levels) {a b : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {la lb : KLevel}
    (ev : ObsFn W "KernelLevels::level_equal" [a, b] h (.field 1) h' cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (ha : RepKLevel h la a) (hb : RepKLevel h lb b) :
    ∀ φ, Level.eval φ la = Level.eval φ lb :=
  hLevels.2.1 a b h h' cs la lb ev hbnd ha hb

/-! ## `Tm.hasFvar_false` at depth `0` -/

theorem Tm.hasFvar_false {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ 0 Γ h k E p) :
    E.hasFvar = false := by
  induction rep with
  | bvarLocal | sort | const | litNat | litStr => rfl
  | bvarFree _ _ _ hd => omega
  | app _ _ _ ihf iha => simp [Expr.hasFvar, ihf, iha]
  | lam _ _ _ _ iht ihb => simp [Expr.hasFvar, iht, ihb]
  | forallE _ _ _ _ iht ihb => simp [Expr.hasFvar, iht, ihb]
  | proj _ _ _ ihe => simpa [Expr.hasFvar] using ihe
  | @letE k _ _ _ _ T V B _ _ _ _ _ ihv ihb =>
    have hlift : ∀ (x : KExpr) (n c : Nat), x.hasFvar = false →
        (x.liftLooseBVars n c).hasFvar = false := by
      intro x
      induction x with
      | bvar _ => intro n c _; simp only [Expr.liftLooseBVars]; split <;> rfl
      | fvar _ _ _ => intro _ _ hx; simp [Expr.hasFvar] at hx
      | sort _ | const _ _ | lit _ => intro _ _ _; rfl
      | app f a ih1 ih2 =>
        intro n c hx; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
        simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 n c hx.1, ih2 n c hx.2⟩
      | lam t bo _ ih1 ih2 =>
        intro n c hx; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
        simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 n c hx.1, ih2 n (c + 1) hx.2⟩
      | forallE t bo _ ih1 ih2 =>
        intro n c hx; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
        simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 n c hx.1, ih2 n (c + 1) hx.2⟩
      | letE t va bo _ ih1 ih2 ih3 =>
        intro n c hx; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hx
        simp only [Expr.liftLooseBVars, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨⟨ih1 n c hx.1.1, ih2 n c hx.1.2⟩, ih3 n (c + 1) hx.2⟩
      | proj _ _ s ih1 =>
        intro n c hx; simp only [Expr.hasFvar] at hx
        simp only [Expr.liftLooseBVars, Expr.hasFvar]; exact ih1 n c hx
    have hinst : ∀ (bo : KExpr) (j : Nat), bo.hasFvar = false →
        (bo.instantiate1Lift V j).hasFvar = false := by
      intro bo
      induction bo with
      | bvar i =>
        intro j _; simp only [Expr.instantiate1Lift]; split
        · exact hlift V j 0 ihv
        · split <;> rfl
      | fvar _ _ _ => intro _ hbo; simp [Expr.hasFvar] at hbo
      | sort _ | const _ _ | lit _ => intro _ _; rfl
      | app f a ih1 ih2 =>
        intro j hbo; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
        simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 j hbo.1, ih2 j hbo.2⟩
      | lam t bo _ ih1 ih2 =>
        intro j hbo; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
        simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 j hbo.1, ih2 (j + 1) hbo.2⟩
      | forallE t bo _ ih1 ih2 =>
        intro j hbo; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
        simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨ih1 j hbo.1, ih2 (j + 1) hbo.2⟩
      | letE t va bo _ ih1 ih2 ih3 =>
        intro j hbo; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hbo
        simp only [Expr.instantiate1Lift, Expr.hasFvar, Bool.or_eq_false_iff]
        exact ⟨⟨ih1 j hbo.1.1, ih2 j hbo.1.2⟩, ih3 (j + 1) hbo.2⟩
      | proj _ _ s ih1 =>
        intro j hbo; simp only [Expr.hasFvar] at hbo
        simp only [Expr.instantiate1Lift, Expr.hasFvar]; exact ih1 j hbo
    exact hinst B 0 ihb

/-! ## Exact heap representation (`TmExact` and `CIRepExact`)

`Tm` relaxes `Srt` and `Const` levels up to semantic equivalence (`LvEq` / `LvEqList`) so that
`Core` outputs after level reduction remain represented. Freshly converted constant records from
`Ingress` carry exact syntactic `RepKLevel` / `RepKLevelList` levels (`TmExact`), which both
refined syntactic checks (`validate_expr_well_scoped`, `kexpr_struct_eq`) read and weaken
immediately to `Tm` (`TmExact.toTm`) for `Core`. -/

inductive TmExact (κ : _root_.Address → KKey) (d : Nat) (Γ : Nat → KExpr) (h : Heap F) :
    Nat → KExpr → SourceValue F → Prop where
  | bvarLocal {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hsmall : ZMod.val i < 9223372036854775808) (hi : ZMod.val i < k) :
      TmExact κ d Γ h k (.bvar (ZMod.val i)) (.ptr (.enum kexprEnum) addr)
  | bvarFree {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hsmall : ZMod.val i < 9223372036854775808) (hk : k ≤ ZMod.val i)
      (hd : ZMod.val i - k < d) :
      TmExact κ d Γ h k (.fvar (fvIdx d k (ZMod.val i)) (Γ (fvIdx d k (ZMod.val i))))
        (.ptr (.enum kexprEnum) addr)
  | sort {k addr : Nat} {lp : SourceValue F} {l : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Srt" [lp]))
      (rl : RepKLevel h l lp) :
      TmExact κ d Γ h k (.sort l) (.ptr (.enum kexprEnum) addr)
  | const {k addr : Nat} {ap lsp : SourceValue F} {a : Bytes.Address} {ls : List KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, lsp]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (rls : RepKLevelList h ls lsp) :
      TmExact κ d Γ h k (.const (κ (ixAddr a)) ls) (.ptr (.enum kexprEnum) addr)
  | app {k addr : Nat} {fp ap : SourceValue F} {Ef Ea : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
      (rf : TmExact κ d Γ h k Ef fp) (ra : TmExact κ d Γ h k Ea ap) :
      TmExact κ d Γ h k (.app Ef Ea) (.ptr (.enum kexprEnum) addr)
  | lam {k addr : Nat} {tp bp lp : SourceValue F} {T B : KExpr} {ℓ : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Lam" [tp, bp, lp]))
      (rt : TmExact κ d Γ h k T tp) (rb : TmExact κ d Γ h (k + 1) B bp)
      (rl : RepKLevel h ℓ lp) :
      TmExact κ d Γ h k (.lam T B (bmeta ℓ)) (.ptr (.enum kexprEnum) addr)
  | forallE {k addr : Nat} {tp bp lp : SourceValue F} {T B : KExpr} {ℓ : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp]))
      (rt : TmExact κ d Γ h k T tp) (rb : TmExact κ d Γ h (k + 1) B bp)
      (rl : RepKLevel h ℓ lp) :
      TmExact κ d Γ h k (.forallE T B (bmeta ℓ)) (.ptr (.enum kexprEnum) addr)
  | letE {k addr : Nat} {tp vp bp : SourceValue F} {T V B : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Let" [tp, vp, bp]))
      (rt : TmExact κ d Γ h k T tp) (rv : TmExact κ d Γ h k V vp)
      (rb : TmExact κ d Γ h (k + 1) B bp) :
      TmExact κ d Γ h k (instShift V 0 B) (.ptr (.enum kexprEnum) addr)
  | litNat {k addr : Nat} {lp : SourceValue F} {limbs : List UInt64}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Nat" [lp]]))
      (rl : RepList limbListEnum RepU64 h limbs lp) (hc : limbs.getLast? ≠ some 0) :
      TmExact κ d Γ h k (.lit (.natVal (limbsVal limbs))) (.ptr (.enum kexprEnum) addr)
  | litStr {k addr : Nat} {bp : SourceValue F} {bytes : List UInt8} {s : String}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Str" [bp]]))
      (rb : Bytes.RepByteStream byteListEnum h bytes bp) (hs : StrBytes s bytes) :
      TmExact κ d Γ h k (.lit (.strVal s)) (.ptr (.enum kexprEnum) addr)
  | proj {k addr : Nat} {ap ep : SourceValue F} {a : Bytes.Address} {i : F} {E : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Proj" [ap, .field i, ep]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (re : TmExact κ d Γ h k E ep) :
      TmExact κ d Γ h k (.proj (κ (ixAddr a)) (ZMod.val i) E) (.ptr (.enum kexprEnum) addr)

def TmCExact (κ : _root_.Address → KKey) (h : Heap F) (E : KExpr) (p : SourceValue F) : Prop :=
  ∀ d Γ, TmExact κ d Γ h 0 E p

theorem TmExact.toTm {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : TmExact κ d Γ h k E p) :
    Tm κ d Γ h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact .bvarFree cell hs hk hd
  | sort cell rl => exact .sort cell rl (LvEq.refl _)
  | const cell ra rls => exact .const cell ra rls (LvEqList.refl _)
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

theorem TmCExact.toTmC {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr} {p : SourceValue F}
    (rep : TmCExact κ h E p) : TmC κ h E p :=
  fun d Γ => (rep d Γ).toTm

theorem TmExact.mono {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h₁ h₂ : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : TmExact κ d Γ h₁ k E p) : TmExact κ d Γ h₂ k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal (ext.getElem?_eq cell) hs hi
  | bvarFree cell hs hk hd => exact .bvarFree (ext.getElem?_eq cell) hs hk hd
  | sort cell rl => exact .sort (ext.getElem?_eq cell) (rl.mono ext)
  | const cell ra rls =>
    exact .const (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra)
      (rls.mono ext)
  | app cell _ _ ihf iha => exact .app (ext.getElem?_eq cell) ihf iha
  | lam cell _ _ rl iht ihb => exact .lam (ext.getElem?_eq cell) iht ihb (rl.mono ext)
  | forallE cell _ _ rl iht ihb => exact .forallE (ext.getElem?_eq cell) iht ihb (rl.mono ext)
  | letE cell _ _ _ iht ihv ihb => exact .letE (ext.getElem?_eq cell) iht ihv ihb
  | litNat cell rl hc =>
    exact .litNat (ext.getElem?_eq cell) (repList_heapMono₂ _ repU64_heapMono₂ ext rl) hc
  | litStr cell rb hs =>
    exact .litStr (ext.getElem?_eq cell) (Bytes.repByteStream_heapMono₂ _ ext rb) hs
  | proj cell ra _ ihe =>
    exact .proj (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra) ihe

theorem TmCExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {E : KExpr}
    {p : SourceValue F} (ext : Heap.Extends h₁ h₂) (rep : TmCExact κ h₁ E p) :
    TmCExact κ h₂ E p :=
  fun d Γ => (rep d Γ).mono ext

def ValRepExact (κ : _root_.Address → KKey) (h : Heap F) (nl ty : SourceValue F)
    (cv : ConstantVal .anon) : Prop :=
  nl = .field (cv.levelParams.length : F) ∧ cv.levelParams.length < 4294967296 ∧
    cv.levelParams.Perm (List.range cv.levelParams.length) ∧
    TmCExact κ h (posOf cv.levelParams cv.type) ty

def RuleRepExact (κ : _root_.Address → KKey) (h : Heap F) (ps : List LevelParam) (j : Nat)
    (v : SourceValue F) (rl : RecRule .anon) : Prop :=
  ∃ rhs : SourceValue F, v = .construct krrEnum "Mk" [.field (j : F), .field (rl.nfields : F), rhs] ∧
    rl.nfields < 72057594037927936 ∧ TmCExact κ h (posOf ps rl.rhs) rhs

inductive RulesRepExact (κ : _root_.Address → KKey) (h : Heap F) (ps : List LevelParam) :
    Nat → SourceValue F → List (RecRule .anon) → Prop where
  | nil {j addr : Nat} (cell : h[addr]? = some (.construct krrListEnum "Nil" [])) :
      RulesRepExact κ h ps j (.ptr (.enum krrListEnum) addr) []
  | cons {j addr : Nat} {v rest : SourceValue F} {rl : RecRule .anon} {rls : List (RecRule .anon)}
      (cell : h[addr]? = some (.construct krrListEnum "Cons" [v, rest]))
      (hr : RuleRepExact κ h ps j v rl) (rs : RulesRepExact κ h ps (j + 1) rest rls) :
      RulesRepExact κ h ps j (.ptr (.enum krrListEnum) addr) (rl :: rls)

inductive CIRepExact (κ : _root_.Address → KKey) (h : Heap F) :
    SourceValue F → ConstantInfo .anon → Prop where
  | axio {nl ty u : SourceValue F} {cv : ConstantVal .anon}
      (hv : ValRepExact κ h nl ty cv) :
      CIRepExact κ h (.construct kciEnum "Axiom" [nl, ty, u]) (.axiomInfo cv)
  | opaq {nl ty val u : SourceValue F} {cv : ConstantVal .anon} {V : KExpr}
      (hv : ValRepExact κ h nl ty cv)
      (hval : TmCExact κ h (posOf cv.levelParams V) val) :
      CIRepExact κ h (.construct kciEnum "Opaque" [nl, ty, val, u]) (.axiomInfo cv)
  | defn {nl ty val sf hint : SourceValue F} {cv : ConstantVal .anon}
      {V : KExpr} {hn : Ix.Kernel.ReducibilityHint}
      (hv : ValRepExact κ h nl ty cv) (hV : TmCExact κ h (posOf cv.levelParams V) val) :
      CIRepExact κ h (.construct kciEnum "Defn" [nl, ty, val, sf, hint]) (.defnInfo cv V hn)
  | thm {nl ty val : SourceValue F} {cv : ConstantVal .anon} {V : KExpr}
      (hv : ValRepExact κ h nl ty cv) (hV : TmCExact κ h (posOf cv.levelParams V) val) :
      CIRepExact κ h (.construct kciEnum "Thm" [nl, ty, val]) (.thmInfo cv V)
  | quot {nl ty kind : SourceValue F} {ci : ConstantInfo .anon}
      (hv : ValRepExact κ h nl ty ci.toConstantVal) (hk : QuotKindRep kind ci) :
      CIRepExact κ h (.construct kciEnum "Quot" [nl, ty, kind]) ci
  | induct {nl ty np ni nc u blk idx : SourceValue F} {cv : ConstantVal .anon}
      {caps : Ix.Kernel.IndCaps .anon}
      (hv : ValRepExact κ h nl ty cv)
      (hcounts : ∃ nP nI nC : Nat, np = .field (nP : F) ∧ ni = .field (nI : F) ∧
        nc = .field (nC : F) ∧ nP < 72057594037927936 ∧ nI < 72057594037927936 ∧
        nC < 72057594037927936)
      (hkey : ∃ (b : Bytes.Address) (i : F), Bytes.RepAddressRef addrTy h b blk ∧ idx = .field i ∧
        cv.name = κ (iprjAddr (ixAddr b) (ZMod.val i))) :
      CIRepExact κ h (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx])
        (.indInfo cv caps)
  | ctor {nl ty blk ind cidx np nf u : SourceValue F} {cv : ConstantVal .anon}
      {nP nF : Nat}
      (hv : ValRepExact κ h nl ty cv) (hnp : np = .field (nP : F)) (hnf : nf = .field (nF : F))
      (hcounts : nP < 72057594037927936 ∧ nF < 72057594037927936)
      (hkey : ∃ (b : Bytes.Address) (i j : F), Bytes.RepAddressRef addrTy h b blk ∧ ind = .field i ∧
        cidx = .field j ∧ cv.name = κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j))) :
      CIRepExact κ h (.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u])
        (.ctorInfo cv nP nF)
  | recr {nl ty np ni nm nmi rules k u blk idx : SourceValue F}
      {cv : ConstantVal .anon} {mI rP : Nat} {rls : List (RecRule .anon)}
      {p i m mi : F}
      (hv : ValRepExact κ h nl ty cv) (hnp : np = .field p) (hni : ni = .field i)
      (hnm : nm = .field m) (hnmi : nmi = .field mi) (hrP : (rP : F) = p + m + mi)
      (hmI : (mI : F) = p + m + mi + i) (hcounts : rP ≤ mI ∧ mI < 288230376151711744)
      (hrules : RulesRepExact κ h cv.levelParams 0 rules rls)
      (hk : k = .field 1 → ∃ rl, rls = [rl] ∧ rl.k = true ∧ rl.ctorParams = ZMod.val p)
      (hkey : ∃ (b : Bytes.Address) (i : F), Bytes.RepAddressRef addrTy h b blk ∧ idx = .field i ∧
        (cv.name = κ (ixAddr b) ∨ cv.name = κ (rprjAddr (ixAddr b) (ZMod.val i)))) :
      CIRepExact κ h (.construct kciEnum "Rec"
        [nl, ty, np, ni, nm, nmi, rules, k, u, blk, idx]) (.recInfo cv mI rP rls)

theorem ValRepExact.toValRep {κ : _root_.Address → KKey} {h : Heap F} {nl ty : SourceValue F}
    {cv : ConstantVal .anon} (hv : ValRepExact κ h nl ty cv) : ValRep κ h nl ty cv :=
  ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.toTmC⟩

theorem RulesRepExact.toRulesRep {κ : _root_.Address → KKey} {h : Heap F} {ps : List LevelParam}
    {j : Nat} {v : SourceValue F} {rls : List (RecRule .anon)}
    (hr : RulesRepExact κ h ps j v rls) : RulesRep κ h ps j v rls := by
  induction hr with
  | nil cell => exact .nil cell
  | cons cell hh _ ih =>
    obtain ⟨rhs, hrhs, hnf, htm⟩ := hh
    exact .cons cell ⟨rhs, hrhs, hnf, htm.toTmC⟩ ih

theorem CIRepExact.toCIRep {κ : _root_.Address → KKey} {h : Heap F} {v : SourceValue F}
    {ci : ConstantInfo .anon} (hci : CIRepExact κ h v ci) : CIRep κ h v ci := by
  cases hci with
  | axio hv => exact .axio hv.toValRep
  | opaq hv _ => exact .opaq hv.toValRep
  | defn hv hV => exact .defn hv.toValRep hV.toTmC
  | thm hv hV => exact .thm hv.toValRep hV.toTmC
  | quot hv hk => exact .quot hv.toValRep hk
  | induct hv hcounts hkey => exact .induct hv.toValRep hcounts hkey
  | ctor hv hnp hnf hcounts hkey => exact .ctor hv.toValRep hnp hnf hcounts hkey
  | recr hv hnp hni hnm hnmi hrP hmI hcounts hrules hk hkey =>
    exact .recr hv.toValRep hnp hni hnm hnmi hrP hmI hcounts hrules.toRulesRep hk hkey

def CIPtrRepExact (κ : _root_.Address → KKey) (h : Heap F) (p : SourceValue F)
    (ci : ConstantInfo .anon) : Prop :=
  ∃ v, loadValue h p = .ok v ∧ CIRepExact κ h v ci

theorem CIPtrRepExact.toCIPtrRep {κ : _root_.Address → KKey} {h : Heap F} {p : SourceValue F}
    {ci : ConstantInfo .anon} (r : CIPtrRepExact κ h p ci) : CIPtrRep κ h p ci :=
  let ⟨v, hl, hr⟩ := r; ⟨v, hl, hr.toCIRep⟩

theorem ValRepExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {nl ty : SourceValue F}
    {cv : ConstantVal .anon} (ext : Heap.Extends h₁ h₂) (r : ValRepExact κ h₁ nl ty cv) :
    ValRepExact κ h₂ nl ty cv :=
  ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.mono ext⟩

theorem RulesRepExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {ps : List LevelParam}
    {j : Nat} {v : SourceValue F} {rls : List (RecRule .anon)} (ext : Heap.Extends h₁ h₂)
    (r : RulesRepExact κ h₁ ps j v rls) : RulesRepExact κ h₂ ps j v rls := by
  induction r with
  | nil cell => exact .nil (ext.getElem?_eq cell)
  | cons cell hr _ ih =>
    obtain ⟨rhs, hv, hn, hrhs⟩ := hr
    exact .cons (ext.getElem?_eq cell) ⟨rhs, hv, hn, hrhs.mono ext⟩ ih

theorem CIRepExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {v : SourceValue F}
    {ci : ConstantInfo .anon} (ext : Heap.Extends h₁ h₂) (r : CIRepExact κ h₁ v ci) :
    CIRepExact κ h₂ v ci := by
  cases r with
  | axio hv => exact .axio (hv.mono ext)
  | opaq hv hval => exact .opaq (hv.mono ext) (hval.mono ext)
  | defn hv hV => exact .defn (hv.mono ext) (hV.mono ext)
  | thm hv hV => exact .thm (hv.mono ext) (hV.mono ext)
  | quot hv hk => exact .quot (hv.mono ext) hk
  | induct hv hcounts hkey =>
    obtain ⟨b, i, hb, hi, hn⟩ := hkey
    exact .induct (hv.mono ext) hcounts ⟨b, i, Bytes.repAddressRef_heapMono₂ addrTy ext hb, hi, hn⟩
  | ctor hv hnp hnf hcounts hkey =>
    obtain ⟨b, i, j, hb, hi, hj, hn⟩ := hkey
    exact .ctor (hv.mono ext) hnp hnf hcounts
      ⟨b, i, j, Bytes.repAddressRef_heapMono₂ addrTy ext hb, hi, hj, hn⟩
  | recr hv hnp hni hnm hnmi hrP hmI hcounts hrules hk hkey =>
    obtain ⟨b, i, hb, hi, hn⟩ := hkey
    exact .recr (hv.mono ext) hnp hni hnm hnmi hrP hmI hcounts (hrules.mono ext) hk
      ⟨b, i, Bytes.repAddressRef_heapMono₂ addrTy ext hb, hi, hn⟩

theorem CIPtrRepExact.mono {κ : _root_.Address → KKey} {h₁ h₂ : Heap F} {p : SourceValue F}
    {ci : ConstantInfo .anon} (ext : Heap.Extends h₁ h₂) (r : CIPtrRepExact κ h₁ p ci) :
    CIPtrRepExact κ h₂ p ci :=
  let ⟨v, hl, hr⟩ := r; ⟨v, ext.loadValue_eq hl, hr.mono ext⟩

/-! ## Cell-load inversions for `TmExact` -/

section TmExactInversion
variable {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
  {E : KExpr} {p : SourceValue F}

theorem TmExact.bvar_of_load {x : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "BVar" [x])) :
    ∃ i : F, x = .field i ∧ ZMod.val i < 9223372036854775808 ∧
      ((ZMod.val i < k ∧ E = .bvar (ZMod.val i)) ∨
        (k ≤ ZMod.val i ∧ ZMod.val i - k < d ∧
          E = .fvar (fvIdx d k (ZMod.val i)) (Γ (fvIdx d k (ZMod.val i))))) :=
  rep.toTm.bvar_of_load hl

theorem TmExact.sort_of_load {x : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Srt" [x])) :
    ∃ l, E = .sort l ∧ RepKLevel h l x := by
  cases rep with
  | sort cell rl =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with hx; subst hx
    exact ⟨_, rfl, rl⟩
  | bvarLocal cell | bvarFree cell | const cell | app cell | lam cell | forallE cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.const_of_load {ap lsp : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Const" [ap, lsp])) :
    ∃ a ls, E = .const (κ (ixAddr a)) ls ∧ Bytes.RepAddressRef addrTy h a ap ∧
      RepKLevelList h ls lsp := by
  cases rep with
  | const cell ra rls =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2; subst h1 h2
    exact ⟨_, _, rfl, ra, rls⟩
  | bvarLocal cell | bvarFree cell | sort cell | app cell | lam cell | forallE cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.app_of_load {fp ap : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "App" [fp, ap])) :
    ∃ Ef Ea, E = .app Ef Ea ∧ TmExact κ d Γ h k Ef fp ∧ TmExact κ d Γ h k Ea ap := by
  cases rep with
  | app cell rf ra =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2; subst h1 h2
    exact ⟨_, _, rfl, rf, ra⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | lam cell | forallE cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.lam_of_load {tp bp lp : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Lam" [tp, bp, lp])) :
    ∃ T B ℓ, E = .lam T B (bmeta ℓ) ∧ TmExact κ d Γ h k T tp ∧
      TmExact κ d Γ h (k + 1) B bp ∧ RepKLevel h ℓ lp := by
  cases rep with
  | lam cell rt rb rl =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rt, rb, rl⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | app cell | forallE cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.forallE_of_load {tp bp lp : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Forall" [tp, bp, lp])) :
    ∃ T B ℓ, E = .forallE T B (bmeta ℓ) ∧ TmExact κ d Γ h k T tp ∧
      TmExact κ d Γ h (k + 1) B bp ∧ RepKLevel h ℓ lp := by
  cases rep with
  | forallE cell rt rb rl =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rt, rb, rl⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | app cell | lam cell | letE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.letE_of_load {tp vp bp : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Let" [tp, vp, bp])) :
    ∃ T V B, E = instShift V 0 B ∧ TmExact κ d Γ h k T tp ∧ TmExact κ d Γ h k V vp ∧
      TmExact κ d Γ h (k + 1) B bp := by
  cases rep with
  | letE cell rt rv rb =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rt, rv, rb⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | app cell | lam cell | forallE cell
  | litNat cell | litStr cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.lit_of_load {lv : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Lit" [lv])) :
    (∃ lp limbs, lv = .construct klitEnum "Nat" [lp] ∧
      E = .lit (.natVal (limbsVal limbs)) ∧ RepList limbListEnum RepU64 h limbs lp) ∨
    (∃ bp bytes s, lv = .construct klitEnum "Str" [bp] ∧
      E = .lit (.strVal s) ∧ Bytes.RepByteStream byteListEnum h bytes bp ∧ StrBytes s bytes) := by
  cases rep with
  | litNat cell rl _ =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with hx; subst hx
    exact .inl ⟨_, _, rfl, rfl, rl⟩
  | litStr cell rb hs =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with hx; subst hx
    exact .inr ⟨_, _, _, rfl, rfl, rb, hs⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | app cell | lam cell | forallE cell
  | letE cell | proj cell =>
    exact (load_cell_ne cell hl (by decide)).elim

theorem TmExact.proj_of_load {ap fp ep : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Proj" [ap, fp, ep])) :
    ∃ (a : Bytes.Address) (i : F) (E₁ : KExpr),
      fp = .field i ∧ E = .proj (κ (ixAddr a)) (ZMod.val i) E₁ ∧
      Bytes.RepAddressRef addrTy h a ap ∧ TmExact κ d Γ h k E₁ ep := by
  cases rep with
  | proj cell ra re =>
    obtain ⟨_, hxs⟩ := load_cell cell hl
    injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
    subst h1 h2 h3
    exact ⟨_, _, _, rfl, rfl, ra, re⟩
  | bvarLocal cell | bvarFree cell | sort cell | const cell | app cell | lam cell | forallE cell
  | letE cell | litNat cell | litStr cell =>
    exact (load_cell_ne cell hl (by decide)).elim

end TmExactInversion

/-! ## `validate_expr_well_scoped` -/

local macro "decl_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

private theorem validate_univ_params_seen_aux :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelCheck::validate_univ_params_seen" →
      ∀ (u : KLevel) (nl : Nat) (pu : SourceValue F),
        args = [pu, .field (nl : F)] → nl < 4294967296 → RepKLevel h u pu →
        u.allParamsDefined (List.range nl) = true :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelCheck::validate_univ_params_seen" →
      ∀ (u : KLevel) (nl : Nat) (pu : SourceValue F),
        args = [pu, .field (nl : F)] → nl < 4294967296 → RepKLevel h u pu →
        u.allParamsDefined (List.range nl) = true)
    (fun fname args h r h' cs ev ih hfn u nl pu hargs hnl hu => by
      subst hfn hargs
      rcases Obs.«KernelCheck::validate_univ_params_seen».obs ev with
        ⟨ld12, _, _, _⟩ |
        ⟨x_inner, cs40, ld12, ev42, hc59⟩ |
        ⟨x_a, x_b, v77, m78, cs88, cs110, ld12, ev90, ev112, hc129⟩ |
        ⟨x_a, x_b, v147, m148, cs158, cs180, ld12, ev160, ev182, hc199⟩ |
        ⟨x_i, v223, m226, cs234, ld12, ev236, heq259, _, _, _⟩
      · obtain rfl := LevelsAux.zero_of_load hu ld12; rfl
      · obtain ⟨inner, rfl, hinner⟩ := LevelsAux.succ_of_load hu ld12
        subst hc59
        exact ih _ _ _ _ _ _ (by decl_lt_calls) ev42 rfl inner nl x_inner rfl hnl hinner
      · obtain ⟨a, b, rfl, ha, hb⟩ := LevelsAux.max_of_load hu ld12
        subst hc129
        simp only [Level.allParamsDefined, Bool.and_eq_true]
        exact ⟨ih _ _ _ _ _ _ (by decl_lt_calls) ev90 rfl a nl x_a rfl hnl ha,
          ih _ _ _ _ _ _ (by decl_lt_calls) ev112 rfl b nl x_b rfl hnl
            (hb.mono (ObsFn.heap_extends ev90))⟩
      · obtain ⟨a, b, rfl, ha, hb⟩ := LevelsAux.imax_of_load hu ld12
        subst hc199
        simp only [Level.allParamsDefined, Bool.and_eq_true]
        exact ⟨ih _ _ _ _ _ _ (by decl_lt_calls) ev160 rfl a nl x_a rfl hnl ha,
          ih _ _ _ _ _ _ (by decl_lt_calls) ev182 rfl b nl x_b rfl hnl
            (hb.mono (ObsFn.heap_extends ev160))⟩
      · obtain ⟨p, rfl, hp, rfl⟩ := LevelsAux.param_of_load hu ld12
        subst heq259
        obtain ⟨_, _, hlt, _, _⟩ := Lib.less_than_fields_field ev236
        have hplt : p < nl := by
          have hp' : (p : Nat) < 4294967296 := hp
          have h1 : ((p : F)).val = p :=
            ZMod.val_natCast_of_lt (Nat.lt_trans hp' (by decide))
          have h2 : ((nl : F)).val = nl :=
            ZMod.val_natCast_of_lt (Nat.lt_trans hnl (by decide))
          simpa [h1, h2] using hlt.mp rfl
        simp [Level.allParamsDefined, hplt])

theorem validate_univ_params_seen_spec {u : KLevel} {nl : Nat} {pu r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hnl : nl < 4294967296) (hu : RepKLevel h u pu)
    (ev : ObsFn W "KernelCheck::validate_univ_params_seen" [pu, .field (nl : F)] h r h' cs) :
    u.allParamsDefined (List.range nl) = true :=
  validate_univ_params_seen_aux _ _ _ _ _ _ ev rfl u nl pu rfl hnl hu

private theorem validate_univ_params_list_aux :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelCheck::validate_univ_params_list" →
      ∀ (us : List KLevel) (nl : Nat) (pus : SourceValue F),
        args = [pus, .field (nl : F)] → nl < 4294967296 → RepKLevelList h us pus →
        us.all (Level.allParamsDefined (List.range nl)) = true :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelCheck::validate_univ_params_list" →
      ∀ (us : List KLevel) (nl : Nat) (pus : SourceValue F),
        args = [pus, .field (nl : F)] → nl < 4294967296 → RepKLevelList h us pus →
        us.all (Level.allParamsDefined (List.range nl)) = true)
    (fun fname args h r h' cs ev ih hfn us nl pus hargs hnl hus => by
      subst hfn hargs
      rcases Obs.«KernelCheck::validate_univ_params_list».obs ev with
        ⟨ld12, _, _, _⟩ |
        ⟨x_u, x_rest, v42, m43, cs53, cs75, ld12, ev55, ev77, hc94⟩
      · have hrep : RepList klevelListEnum RepKLevel h us pus := by
          rwa [klevelListEnum_eq]
        obtain rfl := RepList.nil_of_load hrep ld12
        rfl
      · have hrep : RepList klevelListEnum RepKLevel h us pus := by
          rwa [klevelListEnum_eq]
        obtain ⟨u, rest, rfl, hu, hrest⟩ := RepList.cons_of_load hrep ld12
        have hrest' : RepKLevelList m43 rest x_rest := by
          rw [klevelListEnum_eq] at hrest
          exact repList_heapMono₂ _ repKLevel_heapMono₂ (ObsFn.heap_extends ev55) hrest
        subst hc94
        simp only [List.all_cons, Bool.and_eq_true]
        exact ⟨validate_univ_params_seen_spec hnl hu ev55,
          ih _ _ _ _ _ _ (by decl_lt_calls) ev77 rfl rest nl x_rest rfl hnl hrest'⟩)

theorem validate_univ_params_list_spec {us : List KLevel} {nl : Nat} {pus r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hnl : nl < 4294967296) (hus : RepKLevelList h us pus)
    (ev : ObsFn W "KernelCheck::validate_univ_params_list" [pus, .field (nl : F)] h r h' cs) :
    us.all (Level.allParamsDefined (List.range nl)) = true :=
  validate_univ_params_list_aux _ _ _ _ _ _ ev rfl us nl pus rfl hnl hus

private theorem allLevelParamsDefined_liftLooseBVars {ps : List LevelParam} :
    ∀ {e : KExpr} (n c : Nat), e.allLevelParamsDefined ps = true →
      (e.liftLooseBVars n c).allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | bvar _ => intro _ _ _; simp only [Expr.liftLooseBVars]; split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _ h; exact h
  | app f a ihf iha =>
    intro n c h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨ihf n c h.1, iha n c h.2⟩
  | lam t b m iht ihb =>
    intro n c h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht n c h.1.1, ihb n (c + 1) h.1.2⟩, h.2⟩
  | forallE t b m iht ihb =>
    intro n c h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht n c h.1.1, ihb n (c + 1) h.1.2⟩, h.2⟩
  | letE t v b _ iht ihv ihb =>
    intro n c h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht n c h.1.1, ihv n c h.1.2⟩, ihb n (c + 1) h.2⟩
  | proj _ _ e ih =>
    intro n c h; simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined]; exact ih n c h

private theorem allLevelParamsDefined_instantiate1Lift {ps : List LevelParam} {v : KExpr}
    (hv : v.allLevelParamsDefined ps = true) :
    ∀ {b : KExpr} (j : Nat), b.allLevelParamsDefined ps = true →
      (b.instantiate1Lift v j).allLevelParamsDefined ps = true := by
  intro b
  induction b with
  | bvar i =>
    intro j _
    simp only [Expr.instantiate1Lift]
    split
    · exact allLevelParamsDefined_liftLooseBVars j 0 hv
    · split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ h; exact h
  | app f a ihf iha =>
    intro j h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨ihf j h.1, iha j h.2⟩
  | lam t bo m iht ihb =>
    intro j h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht j h.1.1, ihb (j + 1) h.1.2⟩, h.2⟩
  | forallE t bo m iht ihb =>
    intro j h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht j h.1.1, ihb (j + 1) h.1.2⟩, h.2⟩
  | letE t va bo _ iht ihv ihb =>
    intro j h; simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht j h.1.1, ihv j h.1.2⟩, ihb (j + 1) h.2⟩
  | proj _ _ e ih =>
    intro j h; simp only [Expr.allLevelParamsDefined] at h
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined]; exact ih j h

private theorem validate_expr_well_scoped_aux {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelCheck::validate_expr_well_scoped" →
      ∀ (k nl : Nat) (E : KExpr) (pe pdepth : SourceValue F),
        args = [pe, pdepth, .field (nl : F)] → nl < 4294967296 →
        TmExact κ 0 Γ h k E pe →
        E.allLevelParamsDefined (List.range nl) = true :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelCheck::validate_expr_well_scoped" →
      ∀ (k nl : Nat) (E : KExpr) (pe pdepth : SourceValue F),
        args = [pe, pdepth, .field (nl : F)] → nl < 4294967296 →
        TmExact κ 0 Γ h k E pe →
        E.allLevelParamsDefined (List.range nl) = true)
    (fun fname args h r h' cs ev ih hfn k nl E pe pdepth hargs hnl hE => by
      subst hfn hargs
      rcases Obs.«KernelCheck::validate_expr_well_scoped».obs ev with
        ⟨x_i, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨x_l, cs93, ld12, ev95, _⟩ |
        ⟨x_addr, x_lvls, v130, m131, p138, cs144, v155, m156, cs166, v188, m191, cs199, cs221,
          ld12, ev146, _, ev168, ev201, _, ev223, _⟩ |
        ⟨x_f, x_a, v258, m259, cs269, cs299, ld12, ev271, ev301, hc326⟩ |
        ⟨x_t, x_b, x_l, v349, m350, cs360, v379, m380, cs390, cs420, v424,
          ld12, ev362, ev392, _, ev422, hc455⟩ |
        ⟨x_t, x_b, x_l, v478, m479, cs489, v508, m509, cs519, cs549, v553,
          ld12, ev491, ev521, _, ev551, hc584⟩ |
        ⟨x_t, x_v, x_b, v607, m608, cs618, v645, m646, cs656, cs686, v690,
          ld12, ev620, ev658, _, ev688, hc721⟩ |
        ⟨_, ld12, _, _, _⟩ |
        ⟨_, _, x_e1, cs767, ld12, ev769, hc794⟩
      · obtain ⟨_, _, _, ⟨_, rfl⟩ | ⟨_, hd, _⟩⟩ := hE.bvar_of_load ld12
        · rfl
        · omega
      · obtain ⟨l, rfl, hl⟩ := hE.sort_of_load ld12
        exact validate_univ_params_seen_spec hnl hl ev95
      · obtain ⟨a, ls, rfl, _, hls⟩ := hE.const_of_load ld12
        have e1 := (ObsFn.heap_extends ev146).trans
          ((ObsFn.heap_extends ev168).trans (ObsFn.heap_extends ev201))
        exact validate_univ_params_list_spec hnl (hls.mono e1) ev223
      · obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld12
        subst hc326
        simp only [Expr.allLevelParamsDefined, Bool.and_eq_true]
        exact ⟨ih _ _ _ _ _ _ (by decl_lt_calls) ev271 rfl k nl Ef x_f pdepth rfl hnl hf,
          ih _ _ _ _ _ _ (by decl_lt_calls) ev301 rfl k nl Ea x_a pdepth rfl hnl
            (ha.mono (ObsFn.heap_extends ev271))⟩
      · obtain ⟨T, B, ℓ, rfl, ht, hb, hℓ⟩ := hE.lam_of_load ld12
        subst hc455
        have e1 := ObsFn.heap_extends ev362
        have e2 := ObsFn.heap_extends ev392
        have hℓ_def := validate_univ_params_seen_spec hnl hℓ ev362
        simp only [Expr.allLevelParamsDefined, Bool.and_eq_true]
        exact ⟨⟨ih _ _ _ _ _ _ (by decl_lt_calls) ev392 rfl k nl T x_t pdepth rfl hnl (ht.mono e1),
          ih _ _ _ _ _ _ (by decl_lt_calls) ev422 rfl (k + 1) nl B x_b v424 rfl hnl
            (hb.mono (e1.trans e2))⟩,
          Level.zeronessOf_paramsDefined hℓ_def⟩
      · obtain ⟨T, B, ℓ, rfl, ht, hb, hℓ⟩ := hE.forallE_of_load ld12
        subst hc584
        have e1 := ObsFn.heap_extends ev491
        have e2 := ObsFn.heap_extends ev521
        have hℓ_def := validate_univ_params_seen_spec hnl hℓ ev491
        simp only [Expr.allLevelParamsDefined, Bool.and_eq_true]
        exact ⟨⟨ih _ _ _ _ _ _ (by decl_lt_calls) ev521 rfl k nl T x_t pdepth rfl hnl (ht.mono e1),
          ih _ _ _ _ _ _ (by decl_lt_calls) ev551 rfl (k + 1) nl B x_b v553 rfl hnl
            (hb.mono (e1.trans e2))⟩,
          Level.zeronessOf_paramsDefined hℓ_def⟩
      · obtain ⟨T, V, B, rfl, _, hv, hb⟩ := hE.letE_of_load ld12
        subst hc721
        have e1 := ObsFn.heap_extends ev620
        have e2 := ObsFn.heap_extends ev658
        have hv_def := ih _ _ _ _ _ _ (by decl_lt_calls) ev658 rfl k nl V x_v pdepth rfl hnl
          (hv.mono e1)
        have hb_def := ih _ _ _ _ _ _ (by decl_lt_calls) ev688 rfl (k + 1) nl B x_b v690 rfl hnl
          (hb.mono (e1.trans e2))
        exact allLevelParamsDefined_instantiate1Lift hv_def 0 hb_def
      · rcases hE.lit_of_load ld12 with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _, _⟩ <;> rfl
      · obtain ⟨a, i, E₁, _, rfl, _, he₁⟩ := hE.proj_of_load ld12
        subst hc794
        exact ih _ _ _ _ _ _ (by decl_lt_calls) ev769 rfl k nl E₁ x_e1 pdepth rfl hnl he₁)

/-- `KernelCheck::validate_expr_well_scoped` on an exact closed heap expression certifies
`E.allLevelParamsDefined (List.range nl) = true`. -/
theorem validate_expr_well_scoped_spec {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {k nl : Nat} {E : KExpr} {pe pdepth r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnl : nl < 4294967296) (hE : TmExact κ 0 Γ h k E pe)
    (ev : ObsFn W "KernelCheck::validate_expr_well_scoped" [pe, pdepth, .field (nl : F)] h r h' cs) :
    E.allLevelParamsDefined (List.range nl) = true :=
  validate_expr_well_scoped_aux _ _ _ _ _ _ ev rfl k nl E pe pdepth rfl hnl hE

/-! ## Standalone structural equality specs (`level_list_struct_eq`, `kexpr_struct_eq`, `spec_params_ptr_eq`) -/

theorem pw_eq_one {la lb : KLevel} {pa pb : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : RepKLevel h la pa) (hb : RepKLevel h lb pb)
    (ev : ObsFn W "KernelLevels::pw_eq" [pa, pb] h (.field 1) h' cs) :
    la.zeronessOf = lb.zeronessOf := by
  rw [LevelsAux.zeronessOf_eq la, LevelsAux.zeronessOf_eq lb]
  rcases Obs.«KernelLevels::pw_eq».obs ev with
    ⟨m2, cs12, x_sa, m37, cs47, x_nb, x_sb, ev14, ev49, op87, _, _, _⟩ |
    ⟨m2, cs12, x_na, x_sa, m37, cs47, x_nb, x_sb, cs118, v121, m123, cs131, ev14, ev49, op87,
      hne111, ev133, ev120, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he155, _, _⟩
  · obtain ⟨spa, hra, _⟩ := LevelsAux.zero_set_spec ha ev14
    obtain ⟨spb, hrb, _⟩ := LevelsAux.zero_set_spec (hb.mono (ObsFn.heap_extends ev14)) ev49
    have fa : (LevelsAux.zeroSet la).1 = true :=
      LevelsAux.flag_eq_one (LevelsAux.pair_inj hra).1.symm
    obtain ⟨rfl, _⟩ := LevelsAux.pair_inj hrb
    have fb : (LevelsAux.zeroSet lb).1 = true :=
      ((LevelsAux.flag_sub_inv (a := true) op87).mp rfl).symm
    rw [LevelsAux.toPW_never fa, LevelsAux.toPW_never fb]
  · have e14 := ObsFn.heap_extends ev14
    have e49 := ObsFn.heap_extends ev49
    obtain ⟨spa, hra, hsa⟩ := LevelsAux.zero_set_spec ha ev14
    obtain ⟨spb, hrb, hsb⟩ := LevelsAux.zero_set_spec (hb.mono e14) ev49
    obtain ⟨rfl, rfl⟩ := LevelsAux.pair_inj hra
    obtain ⟨rfl, rfl⟩ := LevelsAux.pair_inj hrb
    have fa : (LevelsAux.zeroSet la).1 = false := LevelsAux.flag_ne_one hne111
    have fb : (LevelsAux.zeroSet lb).1 = false := by
      rw [← fa]; exact ((LevelsAux.flag_sub_inv op87).mp rfl).symm
    obtain ⟨hv, rfl⟩ := glistCmp_refines (LevelsAux.repGL_mono hsa e49) hsb ev133.erase
    subst hv
    obtain ⟨hr, _⟩ := Lib.is_zero_field ev120
    have hpw := LevelsAux.ifAllZero_eq_iff_eq
      (LevelsAux.zeroSet_pairwise la) (LevelsAux.zeroSet_pairwise lb)
    rw [LevelsAux.toPW_ifAllZero fa, LevelsAux.toPW_ifAllZero fb]
    by_cases hab : (LevelsAux.zeroSet la).2 = (LevelsAux.zeroSet lb).2
    · exact hpw.mpr hab
    · rw [ite_eq_right (fun e => hab ((LevelsAux.glistCmp_cast_eq_zero_iff _ _).mp e))] at hr
      exact absurd (Value.field.inj hr) one_ne_zero
  · exact absurd (Value.field.inj he155) one_ne_zero

private theorem klimbs_eq_one :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelLevels::klimbs_eq" → r = .field 1 →
      ∀ (la lb : List UInt64) (pa pb : SourceValue F),
        args = [pa, pb] → RepList limbListEnum RepU64 h la pa →
        RepList limbListEnum RepU64 h lb pb → la = lb :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelLevels::klimbs_eq" → r = .field 1 →
      ∀ (la lb : List UInt64) (pa pb : SourceValue F),
        args = [pa, pb] → RepList limbListEnum RepU64 h la pa →
        RepList limbListEnum RepU64 h lb pb → la = lb)
    (fun fname args h r h' cs ev ih hfn hr la lb pa pb hargs ha hb => by
      subst hfn hr hargs
      rcases Obs.«KernelLevels::klimbs_eq».obs ev with
        ⟨ld12, ld31, _, _, _⟩ |
        ⟨_, _, _, _, he46, _, _⟩ |
        ⟨_, _, _, _, he85, _, _⟩ |
        ⟨x_la, x_ra, x_lb, x_rb, m106, cs116, cs152, ld12, ld77, ev118, ev154, hc171⟩ |
        ⟨_, _, _, _, _, _, _, _, _, he177, _, _⟩
      · obtain rfl := RepList.nil_of_load ha ld12
        obtain rfl := RepList.nil_of_load hb ld31
        rfl
      · exact absurd (Value.field.inj he46) one_ne_zero
      · exact absurd (Value.field.inj he85) one_ne_zero
      · obtain ⟨x, xs, rfl, hx, hxs⟩ := RepList.cons_of_load ha ld12
        obtain ⟨y, ys, rfl, hy, hys⟩ := RepList.cons_of_load hb ld77
        subst hc171
        obtain ⟨heq, rfl⟩ := Lib.u64_eq_spec hx hy ev118
        have hxy : x = y := by
          by_contra hne
          rw [ite_eq_right (fun e => hne (UInt64.toNat_inj.mp e))] at heq
          exact one_ne_zero (Value.field.inj heq)
        subst hxy
        congr 1
        exact ih _ _ _ _ _ _ (by decl_lt_calls) ev154 rfl rfl xs ys x_ra x_rb rfl hxs hys
      · exact absurd (Value.field.inj he177) one_ne_zero)

private theorem bytestream_eq_one :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelLevels::bytestream_eq" → r = .field 1 →
      ∀ (xs ys : List UInt8) (pa pb : SourceValue F),
        args = [pa, pb] → Bytes.RepByteStream byteListEnum h xs pa →
        Bytes.RepByteStream byteListEnum h ys pb → xs = ys :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelLevels::bytestream_eq" → r = .field 1 →
      ∀ (xs ys : List UInt8) (pa pb : SourceValue F),
        args = [pa, pb] → Bytes.RepByteStream byteListEnum h xs pa →
        Bytes.RepByteStream byteListEnum h ys pb → xs = ys)
    (fun fname args h r h' cs ev ih hfn hr xs ys pa pb hargs ha hb => by
      subst hfn hr hargs
      rcases Obs.«KernelLevels::bytestream_eq».obs ev with
        ⟨ld12, ld31, _, _, _⟩ |
        ⟨_, _, _, _, he46, _, _⟩ |
        ⟨_, _, _, _, he85, _, _⟩ |
        ⟨x_ba, x_ra, x_bb, x_rb, m106, x114, y115, m116, cs125, cs139, cs157, ld12, ld77, ev127,
          ev141, op121, ev159, hc176⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he181, _, _⟩
      · obtain rfl := RepList.nil_of_load ha ld12
        obtain rfl := RepList.nil_of_load hb ld31
        rfl
      · exact absurd (Value.field.inj he46) one_ne_zero
      · exact absurd (Value.field.inj he85) one_ne_zero
      · obtain ⟨x, xs', rfl, hx, hxs⟩ := RepList.cons_of_load ha ld12
        obtain ⟨y, ys', rfl, hy, hys⟩ := RepList.cons_of_load hb ld77
        subst hc176
        obtain ⟨e1, rfl⟩ := Lib.u8_to_field_spec ev127
        obtain ⟨e2, rfl⟩ := Lib.u8_to_field_spec ev141
        have hx' : x114 = .field (x.toNat : F) := e1.trans hx
        have hy' : y115 = .field (y.toNat : F) := e2.trans hy
        rw [hx', hy'] at op121
        have hxy : x = y := (LevelsAux.byte_sub_inv op121).mp rfl
        subst hxy
        congr 1
        exact ih _ _ _ _ _ _ (by decl_lt_calls) ev159 rfl rfl xs' ys' x_ra x_rb rfl hxs hys
      · exact absurd (Value.field.inj he181) one_ne_zero)

private theorem level_list_struct_eq_aux :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelCheck::level_list_struct_eq" → r = .field 1 →
      ∀ (ua ub : List KLevel) (pa pb : SourceValue F),
        args = [pa, pb] → RepKLevelList h ua pa → RepKLevelList h ub pb →
        ua = ub ∧ h' = h :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelCheck::level_list_struct_eq" → r = .field 1 →
      ∀ (ua ub : List KLevel) (pa pb : SourceValue F),
        args = [pa, pb] → RepKLevelList h ua pa → RepKLevelList h ub pb →
        ua = ub ∧ h' = h)
    (fun fname args h r h' cs ev ih hfn hr ua ub pa pb hargs ha hb => by
      subst hfn hr hargs
      have ha' : RepList klevelListEnum RepKLevel h ua pa := by rwa [klevelListEnum_eq]
      have hb' : RepList klevelListEnum RepKLevel h ub pb := by rwa [klevelListEnum_eq]
      rcases Obs.«KernelCheck::level_list_struct_eq».obs ev with
        ⟨ld12, ld31, _, he40, _⟩ |
        ⟨_, _, _, _, he46, _, _⟩ |
        ⟨_, _, _, _, he85, _, _⟩ |
        ⟨x_x, x_xr, x_y, x_yr, m106, cs117, cs143, ld12, ld77, ev119, ev145, hc162⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, he167, _, _⟩
      · obtain rfl := RepList.nil_of_load ha' ld12
        obtain rfl := RepList.nil_of_load hb' ld31
        exact ⟨rfl, he40⟩
      · exact absurd (Value.field.inj he46) one_ne_zero
      · exact absurd (Value.field.inj he85) one_ne_zero
      · obtain ⟨x, xr, rfl, hx, hxr⟩ := RepList.cons_of_load ha' ld12
        obtain ⟨y, yr, rfl, hy, hyr⟩ := RepList.cons_of_load hb' ld77
        subst hc162
        obtain ⟨hlv, rfl⟩ := levelStructEq_refines hx hy ev119.erase
        have hxy : x = y := by
          by_cases hbeq : (x == y) = true
          · exact beq_iff_eq.mp hbeq
          · simp [hbeq] at hlv
        subst hxy
        rw [klevelListEnum_eq] at hxr hyr
        obtain ⟨htl, hh⟩ := ih _ _ _ _ _ _ (by decl_lt_calls) ev145 rfl rfl xr yr x_xr x_yr rfl
          hxr hyr
        exact ⟨congrArg (x :: ·) htl, hh⟩
      · exact absurd (Value.field.inj he167) one_ne_zero)

theorem level_list_struct_eq_one {ua ub : List KLevel} {pa pb : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ha : RepKLevelList h ua pa) (hb : RepKLevelList h ub pb)
    (ev : ObsFn W "KernelCheck::level_list_struct_eq" [pa, pb] h (.field 1) h' cs) :
    ua = ub ∧ h' = h :=
  level_list_struct_eq_aux _ _ _ _ _ _ ev rfl rfl ua ub pa pb rfl ha hb

private theorem kexpr_struct_eq_aux {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → r = .field 1 →
      ((fname = "KernelCheck::kexpr_struct_eq" →
        ∀ (k : Nat) (Ea Eb : KExpr) (pa pb : SourceValue F),
          args = [pa, pb] → TmExact κ d Γ h k Ea pa → TmExact κ d Γ h k Eb pb → Ea = Eb) ∧
       (fname = "KernelCheck::kexpr_binder_struct_eq" →
        ∀ (k : Nat) (Ta Ba Tb Bb : KExpr) (ℓa ℓb : KLevel)
          (pta pba pla ptb pbb plb : SourceValue F),
          args = [pta, pba, pla, ptb, pbb, plb] →
          TmExact κ d Γ h k Ta pta → TmExact κ d Γ h (k + 1) Ba pba → RepKLevel h ℓa pla →
          TmExact κ d Γ h k Tb ptb → TmExact κ d Γ h (k + 1) Bb pbb → RepKLevel h ℓb plb →
          Ta = Tb ∧ Ba = Bb ∧ bmeta ℓa = bmeta ℓb)) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => r = .field 1 →
      ((fname = "KernelCheck::kexpr_struct_eq" →
        ∀ (k : Nat) (Ea Eb : KExpr) (pa pb : SourceValue F),
          args = [pa, pb] → TmExact κ d Γ h k Ea pa → TmExact κ d Γ h k Eb pb → Ea = Eb) ∧
       (fname = "KernelCheck::kexpr_binder_struct_eq" →
        ∀ (k : Nat) (Ta Ba Tb Bb : KExpr) (ℓa ℓb : KLevel)
          (pta pba pla ptb pbb plb : SourceValue F),
          args = [pta, pba, pla, ptb, pbb, plb] →
          TmExact κ d Γ h k Ta pta → TmExact κ d Γ h (k + 1) Ba pba → RepKLevel h ℓa pla →
          TmExact κ d Γ h k Tb ptb → TmExact κ d Γ h (k + 1) Bb pbb → RepKLevel h ℓb plb →
          Ta = Tb ∧ Ba = Bb ∧ bmeta ℓa = bmeta ℓb)))
    (fun fname args h r h' cs ev ih hr => by
      subst hr
      refine ⟨fun hfn k Ea Eb pa pb hargs ha hb => ?_,
        fun hfn k Ta Ba Tb Bb ℓa ℓb pta pba pla ptb pbb plb hargs hta hba hla htb hbb hlb => ?_⟩
      · subst hfn hargs
        rcases Obs.«KernelCheck::kexpr_struct_eq».obs ev with
          ⟨x_ia, x_ib, ld12, ld36, op65, _, _, _⟩ |
          ⟨_, _, _, _, _, _, _, he79, _, _⟩ |
          ⟨_, _, _, _, _, he86, _, _⟩ |
          ⟨x_la, x_lb, cs128, ld12, ld112, ev130, _⟩ |
          ⟨_, _, _, _, _, he152, _, _⟩ |
          ⟨x_ca, x_lsa, x_cb, x_lsb, m202, cs213, cs239, ld12, ld183, ev215, ev241, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, he263, _, _⟩ |
          ⟨_, _, _, _, _, _, he270, _, _⟩ |
          ⟨x_fa, x_aa, x_fb, x_ab, m320, cs331, cs357, ld12, ld301, ev333, ev359, hc376⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, he381, _, _⟩ |
          ⟨_, _, _, _, _, _, he388, _, _⟩ |
          ⟨x_ta, x_ba, x_la, x_tb, x_bb, x_lb, cs450, ld12, ld424, ev452, hc501⟩ |
          ⟨_, _, _, _, _, _, _, he506, _, _⟩ |
          ⟨x_da, x_xa, x_la, x_db, x_xb, x_lb, cs568, ld12, ld542, ev570, hc619⟩ |
          ⟨_, _, _, _, _, _, _, he624, _, _⟩ |
          ⟨x_ta, x_va, x_ba, x_tb, x_vb, x_bb, m684, cs695, m719, cs730, cs756,
            ld12, ld660, ev697, ev732, ev758, hc775⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he780, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he787, _, _⟩ |
          ⟨_, _, _, _, _, _, _, he794, _, _⟩ |
          ⟨x_la, x_lb, cs836, ld12, ld820, ev838, hc855⟩ |
          ⟨_, _, _, _, _, he860, _, _⟩ |
          ⟨x_sa, x_fa2, x_ea, x_sb, x_fb2, x_eb, m920, cs931, cs980,
            ld12, ld896, ev933, op970, ev982, hc999⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, he1004, _, _⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, he1011, _, _⟩ |
          ⟨_, _, _, _, _, _, _, he1018, _, _⟩
        · obtain ⟨ia, rfl, _, hba_c⟩ := ha.bvar_of_load ld12
          obtain ⟨ib, rfl, _, hbb_c⟩ := hb.bvar_of_load ld36
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, Value.field.injEq] at op65
          have hiab : ia = ib := sub_eq_zero.mp op65
          subst hiab
          rcases hba_c with ⟨hlt, rfl⟩ | ⟨hge, _, rfl⟩
          · rcases hbb_c with ⟨_, rfl⟩ | ⟨hge, _, _⟩
            · rfl
            · omega
          · rcases hbb_c with ⟨hlt, _⟩ | ⟨_, _, rfl⟩
            · omega
            · rfl
        · exact absurd (Value.field.inj he79) one_ne_zero
        · exact absurd (Value.field.inj he86) one_ne_zero
        · obtain ⟨la, rfl, hla⟩ := ha.sort_of_load ld12
          obtain ⟨lb, rfl, hlb⟩ := hb.sort_of_load ld112
          obtain ⟨hlv, _⟩ := levelStructEq_refines hla hlb ev130.erase
          by_cases hbeq : (la == lb) = true
          · exact congrArg Expr.sort (beq_iff_eq.mp hbeq)
          · simp [hbeq] at hlv
        · exact absurd (Value.field.inj he152) one_ne_zero
        · obtain ⟨aa, lsa, rfl, hra, hrlsa⟩ := ha.const_of_load ld12
          obtain ⟨ab, lsb, rfl, hrb, hrlsb⟩ := hb.const_of_load ld183
          obtain ⟨haddr, rfl⟩ := Lib.address_eq_spec ev215 hra hrb
          have haeq : aa = ab := by
            by_cases hab : aa = ab
            · exact hab
            · rw [ite_eq_right hab] at haddr
              exact absurd (Value.field.inj haddr) one_ne_zero
          subst haeq
          obtain ⟨hlseq, _⟩ := level_list_struct_eq_one hrlsa hrlsb ev241
          rw [hlseq]
        · exact absurd (Value.field.inj he263) one_ne_zero
        · exact absurd (Value.field.inj he270) one_ne_zero
        · obtain ⟨Efa, Eaa, rfl, hfa, haa⟩ := ha.app_of_load ld12
          obtain ⟨Efb, Eab, rfl, hfb, hab⟩ := hb.app_of_load ld301
          subst hc376
          have e1 := ObsFn.heap_extends ev333
          have hfeq := (ih _ _ _ _ _ _ (by decl_lt_calls) ev333 rfl).1 rfl k Efa Efb x_fa x_fb rfl
            hfa hfb
          have haeq := (ih _ _ _ _ _ _ (by decl_lt_calls) ev359 rfl).1 rfl k Eaa Eab x_aa x_ab rfl
            (haa.mono e1) (hab.mono e1)
          rw [hfeq, haeq]
        · exact absurd (Value.field.inj he381) one_ne_zero
        · exact absurd (Value.field.inj he388) one_ne_zero
        · obtain ⟨Ta, Ba, ℓa, rfl, hta, hba, hla⟩ := ha.lam_of_load ld12
          obtain ⟨Tb, Bb, ℓb, rfl, htb, hbb, hlb⟩ := hb.lam_of_load ld424
          subst hc501
          obtain ⟨ht, hb', hm⟩ := (ih _ _ _ _ _ _ (by decl_lt_calls) ev452 rfl).2 rfl k
            Ta Ba Tb Bb ℓa ℓb x_ta x_ba x_la x_tb x_bb x_lb rfl hta hba hla htb hbb hlb
          rw [ht, hb', hm]
        · exact absurd (Value.field.inj he506) one_ne_zero
        · obtain ⟨Ta, Ba, ℓa, rfl, hta, hba, hla⟩ := ha.forallE_of_load ld12
          obtain ⟨Tb, Bb, ℓb, rfl, htb, hbb, hlb⟩ := hb.forallE_of_load ld542
          subst hc619
          obtain ⟨ht, hb', hm⟩ := (ih _ _ _ _ _ _ (by decl_lt_calls) ev570 rfl).2 rfl k
            Ta Ba Tb Bb ℓa ℓb x_da x_xa x_la x_db x_xb x_lb rfl hta hba hla htb hbb hlb
          rw [ht, hb', hm]
        · exact absurd (Value.field.inj he624) one_ne_zero
        · obtain ⟨Ta, Va, Ba, rfl, hta, hva, hba⟩ := ha.letE_of_load ld12
          obtain ⟨Tb, Vb, Bb, rfl, htb, hvb, hbb⟩ := hb.letE_of_load ld660
          subst hc775
          have e1 := ObsFn.heap_extends ev697
          have e2 := ObsFn.heap_extends ev732
          have hveq := (ih _ _ _ _ _ _ (by decl_lt_calls) ev732 rfl).1 rfl k Va Vb x_va x_vb rfl
            (hva.mono e1) (hvb.mono e1)
          have hbeq := (ih _ _ _ _ _ _ (by decl_lt_calls) ev758 rfl).1 rfl (k + 1) Ba Bb x_ba x_bb
            rfl (hba.mono (e1.trans e2)) (hbb.mono (e1.trans e2))
          rw [hveq, hbeq]
        · exact absurd (Value.field.inj he780) one_ne_zero
        · exact absurd (Value.field.inj he787) one_ne_zero
        · exact absurd (Value.field.inj he794) one_ne_zero
        · subst hc855
          rcases Obs.«KernelLevels::literal_eq».obs ev838 with
            ⟨x_na, x_nb, cs46, hv15, hv36, ev48, _⟩ |
            ⟨_, _, _, he70, _, _⟩ |
            ⟨x_sa, x_sb, cs109, _, hv78, hv99, ev111, _⟩ |
            ⟨_, _, _, _, he133, _, _⟩
          · rcases ha.lit_of_load ld12 with ⟨lp_a, limbs_a, hva, rfl, rla⟩ | ⟨_, _, _, hva, _, _, _⟩
            · rw [hv15] at hva; injection hva with _ _ hxs; injection hxs with hxa; subst hxa
              rcases hb.lit_of_load ld820 with ⟨lp_b, limbs_b, hvb, rfl, rlb⟩ | ⟨_, _, _, hvb, _, _, _⟩
              · rw [hv36] at hvb; injection hvb with _ _ hys; injection hys with hxb; subst hxb
                rw [klimbs_eq_one _ _ _ _ _ _ ev48 rfl rfl limbs_a limbs_b x_na x_nb rfl rla rlb]
              · rw [hv36] at hvb; injection hvb with _ hc; exact absurd hc (by decide)
            · rw [hv15] at hva; injection hva with _ hc; exact absurd hc (by decide)
          · exact absurd (Value.field.inj he70) one_ne_zero
          · rcases ha.lit_of_load ld12 with ⟨_, _, hva, _, _⟩ | ⟨bp_a, bytes_a, sa, hva, rfl, rba, hsa⟩
            · rw [hv78] at hva; injection hva with _ hc; exact absurd hc (by decide)
            · rw [hv78] at hva; injection hva with _ _ hxs; injection hxs with hxa; subst hxa
              rcases hb.lit_of_load ld820 with ⟨_, _, hvb, _, _⟩ | ⟨bp_b, bytes_b, sb, hvb, rfl, rbb, hsb⟩
              · rw [hv99] at hvb; injection hvb with _ hc; exact absurd hc (by decide)
              · rw [hv99] at hvb; injection hvb with _ _ hys; injection hys with hxb; subst hxb
                have hbytes := bytestream_eq_one _ _ _ _ _ _ ev111 rfl rfl bytes_a bytes_b x_sa x_sb
                  rfl rba rbb
                subst hbytes
                rw [Option.some.inj (hsa.symm.trans hsb)]
          · exact absurd (Value.field.inj he133) one_ne_zero
        · exact absurd (Value.field.inj he860) one_ne_zero
        · obtain ⟨aa, fa, Ea₁, rfl, rfl, hra, hEa₁⟩ := ha.proj_of_load ld12
          obtain ⟨ab, fb, Eb₁, rfl, rfl, hrb, hEb₁⟩ := hb.proj_of_load ld896
          subst hc999
          obtain ⟨haddr, rfl⟩ := Lib.address_eq_spec ev933 hra hrb
          have haeq : aa = ab := by
            by_cases hab : aa = ab
            · exact hab
            · rw [ite_eq_right hab] at haddr
              exact absurd (Value.field.inj haddr) one_ne_zero
          subst haeq
          simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
            Except.ok.injEq, Value.field.injEq] at op970
          have hfeq : fa = fb := sub_eq_zero.mp op970
          subst hfeq
          have heeq := (ih _ _ _ _ _ _ (by decl_lt_calls) ev982 rfl).1 rfl k Ea₁ Eb₁ x_ea x_eb rfl
            hEa₁ hEb₁
          rw [heeq]
        · exact absurd (Value.field.inj he1004) one_ne_zero
        · exact absurd (Value.field.inj he1011) one_ne_zero
        · exact absurd (Value.field.inj he1018) one_ne_zero
      · subst hfn hargs
        rcases Obs.«KernelCheck::kexpr_binder_struct_eq».obs ev with
          ⟨m2, cs13, m37, cs48, cs74, ev15, ev50, ev76, hc93⟩ |
          ⟨_, _, _, _, _, _, _, _, he98, _, _⟩ |
          ⟨_, _, _, _, _, he105, _, _⟩
        · subst hc93
          have e1 := ObsFn.heap_extends ev15
          have e2 := ObsFn.heap_extends ev50
          have hpw := pw_eq_one hla hlb ev15
          have hbm : bmeta ℓa = bmeta ℓb := by unfold bmeta; rw [hpw]
          have hteq := (ih _ _ _ _ _ _ (by decl_lt_calls) ev50 rfl).1 rfl k Ta Tb pta ptb rfl
            (hta.mono e1) (htb.mono e1)
          have hbeq := (ih _ _ _ _ _ _ (by decl_lt_calls) ev76 rfl).1 rfl (k + 1) Ba Bb pba pbb rfl
            (hba.mono (e1.trans e2)) (hbb.mono (e1.trans e2))
          exact ⟨hteq, hbeq, hbm⟩
        · exact absurd (Value.field.inj he98) one_ne_zero
        · exact absurd (Value.field.inj he105) one_ne_zero)

/-- `KernelCheck::kexpr_struct_eq` returning `1` on two `TmExact` heap terms implies syntactic
equality of their kernel expressions (`Ea = Eb`), without requiring `κ` injectivity. -/
theorem kexpr_struct_eq_one {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {Ea Eb : KExpr} {pa pb : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : TmExact κ d Γ h k Ea pa) (hb : TmExact κ d Γ h k Eb pb)
    (ev : ObsFn W "KernelCheck::kexpr_struct_eq" [pa, pb] h (.field 1) h' cs) :
    Ea = Eb :=
  (kexpr_struct_eq_aux _ _ _ _ _ _ ev rfl).1 rfl k Ea Eb pa pb rfl ha hb

private theorem spec_params_ptr_eq_aux {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelCheck::spec_params_ptr_eq" → r = .field 1 →
      ∀ (k : Nat) (as_ bs : List KExpr) (pa pb : SourceValue F),
        args = [pa, pb] →
        RepList kexprListEnum (fun h e p => TmExact κ d Γ h k e p) h as_ pa →
        RepList kexprListEnum (fun h e p => TmExact κ d Γ h k e p) h bs pb →
        as_ = bs :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => fname = "KernelCheck::spec_params_ptr_eq" → r = .field 1 →
      ∀ (k : Nat) (as_ bs : List KExpr) (pa pb : SourceValue F),
        args = [pa, pb] →
        RepList kexprListEnum (fun h e p => TmExact κ d Γ h k e p) h as_ pa →
        RepList kexprListEnum (fun h e p => TmExact κ d Γ h k e p) h bs pb →
        as_ = bs)
    (fun fname args h r h' cs ev ih hfn hr k as_ bs pa pb hargs ha hb => by
      subst hfn hr hargs
      rcases Obs.«KernelCheck::spec_params_ptr_eq».obs ev with
        ⟨ld12, ld31, _, _, _⟩ |
        ⟨_, _, _, _, he46, _, _⟩ |
        ⟨_, _, _, _, he85, _, _⟩ |
        ⟨x_x, x_xr, x_y, x_yr, m106, cs117, cs143, ld12, ld77, ev119, ev145, hc162⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, he167, _, _⟩
      · obtain rfl := RepList.nil_of_load ha ld12
        obtain rfl := RepList.nil_of_load hb ld31
        rfl
      · exact absurd (Value.field.inj he46) one_ne_zero
      · exact absurd (Value.field.inj he85) one_ne_zero
      · obtain ⟨x, xr, rfl, hx, hxr⟩ := RepList.cons_of_load ha ld12
        obtain ⟨y, yr, rfl, hy, hyr⟩ := RepList.cons_of_load hb ld77
        subst hc162
        have e1 := ObsFn.heap_extends ev119
        have hxy := kexpr_struct_eq_one hx hy ev119
        subst hxy
        have hmono : HeapMono₂ (fun h e p => TmExact κ d Γ h k e p) :=
          fun _ _ _ _ ext r => r.mono ext
        congr 1
        exact ih _ _ _ _ _ _ (by decl_lt_calls) ev145 rfl rfl k xr yr x_xr x_yr rfl
          (repList_heapMono₂ _ hmono e1 hxr) (repList_heapMono₂ _ hmono e1 hyr)
      · exact absurd (Value.field.inj he167) one_ne_zero)

/-- `KernelCheck::spec_params_ptr_eq` returning `1` on two `TmExact` lists implies list equality. -/
theorem spec_params_ptr_eq_one {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {as_ bs : List KExpr} {pa pb : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : RepList kexprListEnum (fun h e p => TmExact κ d Γ h k e p) h as_ pa)
    (hb : RepList kexprListEnum (fun h e p => TmExact κ d Γ h k e p) h bs pb)
    (ev : ObsFn W "KernelCheck::spec_params_ptr_eq" [pa, pb] h (.field 1) h' cs) :
    as_ = bs :=
  spec_params_ptr_eq_aux _ _ _ _ _ _ ev rfl rfl k as_ bs pa pb rfl ha hb

end IxVM.Refinement.Decl
