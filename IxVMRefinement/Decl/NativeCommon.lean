import IxVMRefinement.Decl.Common
import IxVMRefinement.Subst.Steps
import IxVMRefinement.Levels.Smart
import IxVMRefinement.Infer.Core
import IxC.Kernel.Semantics.Inductives.DeclNativeJ

/-! # Shared helpers for native inductive and twin recursor declaration refinement

Foundational lemmas shared across the non-modeled `.indDecl` routes (`DeclNativeRunJ`,
`DeclNativeNoRecRunJ`, and `DeclRecTwinRunJ`):

* **`letFree` invariants**: every `Tm` and `TmExact` heap image is `letFree`, and `letFree` is
  preserved by `liftLooseBVars`, `instantiate1Lift`, `instantiate1`, and `instantiateLevelParams`.
* **Route injectors into `DeclRunJ`**: unpinned injection lemmas for the three non-modeled
  `IndRoutesJ` disjuncts.
* **Reduction normal-form inversions**: `.sort` and `.forallE` reduce only to themselves under
  `Rules.Red`.
* **Staging environment extensions and `DeclStoreInv` steps**: `EnvExt` and `DeclStoreInv`
  preservation when staging fresh empty-capability inductives (`.indInfo cv {}`), constructors
  (`.ctorInfo cv nP nF`), and rule-less provisioned recursors (`.recInfo cv mI rP []`).
* **`CapsUpgradeAt` transport**: mutual transport of `Red`, `DefEq`, `Infer`, `Certs`,
  `DefEqList`, and `EtaProjCerts` from an environment storing `.indInfo cvS {}` to one storing
  `.indInfo cvS caps`.
* **`ConstantValCheckJ` constructor**: refines `validate_expr_well_scoped` + `k_ensure_sort` on a
  `ValRepExact` constant to `ConstantValCheckJ rulesJ`.
* **`ExprSemEq` and `WrapRelSem`**: semantic-level structural equality and wrapper consumption
  relations matching `Tm`, `kexpr_struct_eq`, and `expr_inst_levels`.
* **Telescope & parameter-level helpers**: `peel_n_foralls` (on `TmExact` and `Tm`) and
  `assert_lvls_are_params`. -/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂
  levelExplicitVal levelOffsetOf levelMaxOffsets levelMaxSubsumes levelMaxGo levelMax levelIMax
  levelReduce substLevel substLevelList ParamsLt)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo Declaration RecRule)
open Ix.Kernel.Rules (Annot Red DefEq Infer Certs DefEqList EtaProjCerts Grade)
open Ix.Kernel.Semantics (DeclRunJ IndRoutesJ DeclNativeRunJ DeclNativeNoRecRunJ DeclRecTwinRunJ
  ConstantValRunJ ConstantValCheckJ letFree nativePartsNoRec?)
open Ix.Kernel.Model (rulesJ NewSat)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## `letFree` on heap-represented and substituted expressions -/

theorem letFree_liftLooseBVars :
    ∀ {e : KExpr} (n c : Nat), letFree e = true → letFree (e.liftLooseBVars n c) = true := by
  intro e
  induction e with
  | bvar _ => intro _ _ _; simp only [Expr.liftLooseBVars]; split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro n c h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, letFree, Bool.and_eq_true]
    exact ⟨ihf n c h.1, iha n c h.2⟩
  | lam t b _ iht ihb =>
    intro n c h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, letFree, Bool.and_eq_true]
    exact ⟨iht n c h.1, ihb n (c + 1) h.2⟩
  | forallE t b _ iht ihb =>
    intro n c h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, letFree, Bool.and_eq_true]
    exact ⟨iht n c h.1, ihb n (c + 1) h.2⟩
  | letE _ _ _ _ _ _ _ => intro _ _ h; cases h
  | proj _ _ e ih =>
    intro n c h
    simp only [letFree] at h
    simp only [Expr.liftLooseBVars, letFree]
    exact ih n c h

theorem letFree_instantiate1Lift {v : KExpr} (hv : letFree v = true) :
    ∀ {b : KExpr} (j : Nat), letFree b = true → letFree (b.instantiate1Lift v j) = true := by
  intro b
  induction b with
  | bvar i =>
    intro j _
    simp only [Expr.instantiate1Lift]
    split
    · exact letFree_liftLooseBVars j 0 hv
    · split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro j h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, letFree, Bool.and_eq_true]
    exact ⟨ihf j h.1, iha j h.2⟩
  | lam t bo _ iht ihb =>
    intro j h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, letFree, Bool.and_eq_true]
    exact ⟨iht j h.1, ihb (j + 1) h.2⟩
  | forallE t bo _ iht ihb =>
    intro j h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiate1Lift, letFree, Bool.and_eq_true]
    exact ⟨iht j h.1, ihb (j + 1) h.2⟩
  | letE _ _ _ _ _ _ _ => intro _ h; cases h
  | proj _ _ e ih =>
    intro j h
    simp only [letFree] at h
    simp only [Expr.instantiate1Lift, letFree]
    exact ih j h

theorem letFree_instantiate1 {v : KExpr} (hv : letFree v = true) :
    ∀ {e : KExpr} (j : Nat), letFree e = true → letFree (e.instantiate1 v j) = true := by
  intro e
  induction e with
  | bvar i =>
    intro j _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro j h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, letFree, Bool.and_eq_true]
    exact ⟨ihf j h.1, iha j h.2⟩
  | lam t bo _ iht ihb =>
    intro j h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, letFree, Bool.and_eq_true]
    exact ⟨iht j h.1, ihb (j + 1) h.2⟩
  | forallE t bo _ iht ihb =>
    intro j h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiate1, letFree, Bool.and_eq_true]
    exact ⟨iht j h.1, ihb (j + 1) h.2⟩
  | letE _ _ _ _ _ _ _ => intro _ h; cases h
  | proj _ _ e ih =>
    intro j h
    simp only [letFree] at h
    simp only [Expr.instantiate1, letFree]
    exact ih j h

theorem letFree_instantiateLevelParams (ps : List LevelParam) (us : List KLevel) :
    ∀ {e : KExpr}, letFree e = true → letFree (e.instantiateLevelParams ps us) = true := by
  intro e
  induction e with
  | bvar _ | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app f a ihf iha =>
    intro h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, letFree, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | lam t b _ iht ihb =>
    intro h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, letFree, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | forallE t b _ iht ihb =>
    intro h
    simp only [letFree, Bool.and_eq_true] at h
    simp only [Expr.instantiateLevelParams, letFree, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | letE _ _ _ _ _ _ _ => intro h; cases h
  | proj _ _ e ih =>
    intro h
    simp only [letFree] at h
    simp only [Expr.instantiateLevelParams, letFree]
    exact ih h

/-- Every kernel expression represented by `Tm` is `letFree` (`Let` cells expand via `instShift`). -/
theorem Tm.letFree {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ d Γ h k E p) :
    letFree E = true := by
  induction rep with
  | bvarLocal | bvarFree | sort | const | litNat | litStr => rfl
  | app _ _ _ ihf iha => simp [Ix.Kernel.Semantics.letFree, ihf, iha]
  | lam _ _ _ _ iht ihb => simp [Ix.Kernel.Semantics.letFree, iht, ihb]
  | forallE _ _ _ _ iht ihb => simp [Ix.Kernel.Semantics.letFree, iht, ihb]
  | proj _ _ _ ihe => simpa [Ix.Kernel.Semantics.letFree] using ihe
  | letE _ _ _ _ _ ihv ihb => exact letFree_instantiate1Lift ihv 0 ihb

theorem TmExact.letFree {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : TmExact κ d Γ h k E p) :
    letFree E = true :=
  Tm.letFree rep.toTm

/-! ## Route injectors into `DeclRunJ` -/

/-- Injection of a native one-type inductive step with recursor (`DeclNativeRunJ`) into
`DeclRunJ` when unpinned. -/
theorem declRunJ_of_native {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hparts : Ix.Kernel.nativeParts? nP block = some p₀)
    (hN : DeclNativeRunJ rulesJ env p₀ env₂) :
    DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
  simp only [DeclRunJ, hpin]
  exact Or.inl ⟨p₀, hparts, hN⟩

/-- Injection of a recursor-less native one-type inductive step (`DeclNativeNoRecRunJ`) into
`DeclRunJ` when unpinned. -/
theorem declRunJ_of_nativeNoRec {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hparts : nativePartsNoRec? nP block = some p₀)
    (hN : DeclNativeNoRecRunJ rulesJ env p₀ env₂) :
    DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
  simp only [DeclRunJ, hpin]
  exact Or.inr (Or.inr (Or.inl ⟨p₀, hparts, hN⟩))

/-- Injection of a twin recursor step (`DeclRecTwinRunJ`) into `DeclRunJ` when unpinned. -/
theorem declRunJ_of_twinRec {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hT : DeclRecTwinRunJ rulesJ env block env₂) :
    DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
  simp only [DeclRunJ, hpin]
  exact Or.inr (Or.inr (Or.inr hT))

/-! ## Normal-form inversions for `Rules.Red` on sorts and `∀`-types -/

theorem Red.sort_eq {env : Ix.Kernel.Env .anon} {d : Nat} {u : KLevel} {e' : KExpr}
    (h : Red env d (.sort u) e') : e' = .sort u :=
  Ix.Kernel.Rules.Red.rigid h rfl

theorem Red.forallE_eq {env : Ix.Kernel.Env .anon} {d : Nat} {ty b : KExpr}
    {m : Ix.Kernel.BinderMeta} {e' : KExpr}
    (h : Red env d (.forallE ty b m) e') : e' = .forallE ty b m :=
  Ix.Kernel.Rules.Red.rigid h rfl

/-! ## Role-key and projection-shape helpers -/

theorem keyOf_not_aux (t : Ix.Kernel.RoleTable) (a : _root_.Address)
    (k : KKey) (tk : Ix.Kernel.Derived) :
    keyOf t a ≠ .aux k tk := by
  unfold keyOf
  split <;> intro h <;> nomatch h

theorem keyOf_isProjFnShape_false (t : Ix.Kernel.RoleTable) (a : _root_.Address) :
    (keyOf t a).isProjFnShape = false := by
  unfold keyOf
  split <;> rfl

theorem ne_projTableName_of_isProjFnShape_false {k : KKey} (h : k.isProjFnShape = false) :
    ∀ T, k ≠ Ix.Kernel.projTableName T := by
  intro T heq
  rw [heq] at h
  exact Bool.noConfusion h

/-! ## Staging `EnvExt` and `DeclStoreInv` step helpers -/

/-- Any fresh constant whose key is not a projection-table auxiliary key extends `env`. -/
theorem envExt_cons_nonProj {env : Ix.Kernel.Env .anon} {c : ConstantInfo .anon}
    (hfresh : env.find? c.name = none)
    (hnp : ∀ T, c.name ≠ Ix.Kernel.projTableName T) :
    Ix.Kernel.EnvExt env ⟨c :: env.consts⟩ :=
  Ix.Kernel.EnvExt.cons hfresh (fun _ => hnp _)

/-- Staging an empty-capability `.indInfo cv {}` preserves `DeclStoreInv`. -/
theorem DeclStoreInv.consIndEmpty {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon}
    (hS : DeclStoreInv env) (hfresh : env.find? cv.name = none)
    (hnp : ∀ T, cv.name ≠ Ix.Kernel.projTableName T)
    (hty : cv.type.hasFvar = false ∧
      cv.type.allLevelParamsDefined cv.levelParams = true ∧
      cv.type.constsResolve env = true ∧
      cv.type.looseBVarsBounded 0 = true) :
    DeclStoreInv ⟨.indInfo cv {} :: env.consts⟩ := by
  have hext : Ix.Kernel.EnvExt env ⟨.indInfo cv {} :: env.consts⟩ :=
    envExt_cons_nonProj hfresh hnp
  refine
    { store := Ix.Kernel.Model.storeInv_consTyped (c := .indInfo cv {}) hS.store hfresh hty
        (fun _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h)
        (Ix.Kernel.IndCapsWF.of_caps (fun h => nomatch h) (fun h => nomatch h))
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext hS.thmTyped
        (NewSat.cons fun _ _ h => nomatch h)
      recK := Ix.Kernel.Model.recK_step_noRec hS.store hS.recK hext.find
        (NewSat.cons fun _ _ _ _ h => nomatch h)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext hS.etaTowers
        (NewSat.cons fun _ caps' heq heta => by
          injection heq with _ hcaps
          subst hcaps
          exact nomatch heta)
      tableBodies := Ix.Kernel.Model.tableBodies_step_noProj hext.find hS.tableBodies
        (NewSat.cons fun _ h => nomatch h)
      recShape := Ix.Kernel.Model.recShape_step_noRec hS.store hS.recShape hext.find
        (NewSat.cons fun _ _ _ _ h => nomatch h) }

/-- Staging a checked `.ctorInfo cv nP nF` preserves `DeclStoreInv`. -/
theorem DeclStoreInv.consCtor {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon} {nP nF : Nat}
    (hS : DeclStoreInv env) (hfresh : env.find? cv.name = none)
    (hnp : ∀ T, cv.name ≠ Ix.Kernel.projTableName T)
    (hty : cv.type.hasFvar = false ∧
      cv.type.allLevelParamsDefined cv.levelParams = true ∧
      cv.type.constsResolve env = true ∧
      cv.type.looseBVarsBounded 0 = true) :
    DeclStoreInv ⟨.ctorInfo cv nP nF :: env.consts⟩ := by
  have hext : Ix.Kernel.EnvExt env ⟨.ctorInfo cv nP nF :: env.consts⟩ :=
    envExt_cons_nonProj hfresh hnp
  refine
    { store := Ix.Kernel.Model.storeInv_consTyped (c := .ctorInfo cv nP nF) hS.store hfresh hty
        (fun _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ h => nomatch h)
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext hS.thmTyped
        (NewSat.cons fun _ _ h => nomatch h)
      recK := Ix.Kernel.Model.recK_step_noRec hS.store hS.recK hext.find
        (NewSat.cons fun _ _ _ _ h => nomatch h)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext hS.etaTowers
        (NewSat.cons fun _ _ h => nomatch h)
      tableBodies := Ix.Kernel.Model.tableBodies_step_noProj hext.find hS.tableBodies
        (NewSat.cons fun _ h => nomatch h)
      recShape := Ix.Kernel.Model.recShape_step_noRec hS.store hS.recShape hext.find
        (NewSat.cons fun _ _ _ _ h => nomatch h) }

/-- Staging a provisioned empty-rule `.recInfo cv mI rP []` preserves `DeclStoreInv`. -/
theorem DeclStoreInv.consRecNil {env : Ix.Kernel.Env .anon} {cv : ConstantVal .anon} {mI rP : Nat}
    (hS : DeclStoreInv env) (hfresh : env.find? cv.name = none)
    (hnp : ∀ T, cv.name ≠ Ix.Kernel.projTableName T)
    (hty : cv.type.hasFvar = false ∧
      cv.type.allLevelParamsDefined cv.levelParams = true ∧
      cv.type.constsResolve env = true ∧
      cv.type.looseBVarsBounded 0 = true) :
    DeclStoreInv ⟨.recInfo cv mI rP [] :: env.consts⟩ := by
  have hext : Ix.Kernel.EnvExt env ⟨.recInfo cv mI rP [] :: env.consts⟩ :=
    envExt_cons_nonProj hfresh hnp
  refine
    { store := Ix.Kernel.Model.storeInv_consRecNil hS.store hfresh hty
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext hS.thmTyped
        (NewSat.cons fun _ _ h => nomatch h)
      recK := Ix.Kernel.Model.recK_step hS.store hS.recK hext.find
        (fun n cv' mI' rP' rules hf hn => by
          rw [Ix.Kernel.Env.find?_cons] at hf
          split at hf
          · injection hf with heq
            injection heq with _ _ _ hrls
            subst hrls
            exact And.intro (fun _ hr => nomatch hr) (fun _ _ hr _ => nomatch hr)
          · rw [hf] at hn; exact nomatch hn)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext hS.etaTowers
        (NewSat.cons fun _ _ h => nomatch h)
      tableBodies := Ix.Kernel.Model.tableBodies_step_noProj hext.find hS.tableBodies
        (NewSat.cons fun _ h => nomatch h)
      recShape := Ix.Kernel.Model.recShape_step hS.store hS.recShape hext.find
        (fun n cv' mI' rP' rules hf hn => by
          rw [Ix.Kernel.Env.find?_cons] at hf
          split at hf
          · injection hf with heq
            injection heq with _ _ _ hrls
            subst hrls
            refine { eta := fun _ hr => nomatch hr
                     plainIdx := fun _ _ hr => nomatch hr
                     ctorHead := fun _ _ hr => nomatch hr
                     kParams := fun _ _ hr => nomatch hr }
          · rw [hf] at hn; exact nomatch hn) }

/-! ## `CapsUpgradeAt`: transporting rules derivations from `{}` capabilities to `caps` -/

/-- Two environments `envₐ` and `envᵦ` agree everywhere except at a fresh inductive key `T`, where
`envₐ` stores `.indInfo cvS {}` and `envᵦ` stores `.indInfo cvS caps`, and no single-rule recursor
stored in `envₐ` has a constructor returning `T`. -/
structure CapsUpgradeAt (T : KKey) (cvS : ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon)
    (envₐ envᵦ : Ix.Kernel.Env .anon) : Prop where
  find_self_a : envₐ.find? T = some (.indInfo cvS {})
  find_self_b : envᵦ.find? T = some (.indInfo cvS caps)
  find_ne : ∀ {k : KKey}, k ≠ T → envᵦ.find? k = envₐ.find? k
  no_rec_head :
    ∀ {recName : KKey} {cv : ConstantVal .anon} {mI rP : Nat} {rl : RecRule .anon}
      {cvj : ConstantVal .anon} {cnP cnF : Nat} {tus : List KLevel},
      envₐ.find? recName = some (.recInfo cv mI rP [rl]) →
      envₐ.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
      (cvj.type.piResult).getAppFn ≠ .const T tus
  not_basis : Ix.Kernel.reservedBasisNames.contains T = false

namespace CapsUpgradeAt

variable {T : KKey} {cvS : ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}
  {envₐ envᵦ : Ix.Kernel.Env .anon}

theorem ne_of_find_not_ind (h : CapsUpgradeAt T cvS caps envₐ envᵦ) {k : KKey}
    {c : ConstantInfo .anon} (hf : envₐ.find? k = some c)
    (hnot : ∀ cv' caps', c ≠ .indInfo cv' caps') : k ≠ T := by
  intro heq
  subst heq
  rw [h.find_self_a] at hf
  injection hf with heq'
  exact hnot cvS {} heq'.symm

theorem find_non_ind (h : CapsUpgradeAt T cvS caps envₐ envᵦ) {k : KKey}
    {c : ConstantInfo .anon} (hf : envₐ.find? k = some c)
    (hnot : ∀ cv' caps', c ≠ .indInfo cv' caps') : envᵦ.find? k = some c := by
  rw [h.find_ne (h.ne_of_find_not_ind hf hnot)]
  exact hf

theorem ne_of_basis (h : CapsUpgradeAt T cvS caps envₐ envᵦ) {k : KKey}
    (hb : k ∈ Ix.Kernel.reservedBasisNames) : k ≠ T := by
  intro heq
  subst heq
  have hc : Ix.Kernel.reservedBasisNames.contains k = true := List.contains_iff_mem.mpr hb
  rw [h.not_basis] at hc
  cases hc

theorem find_basis (h : CapsUpgradeAt T cvS caps envₐ envᵦ) {k : KKey}
    (hb : k ∈ Ix.Kernel.reservedBasisNames) : envᵦ.find? k = envₐ.find? k :=
  h.find_ne (h.ne_of_basis hb)

/-- Any boolean guard on `Option ConstantInfo` that ignores `IndCaps` agrees on `envₐ` and `envᵦ`. -/
theorem pred_caps_inv (h : CapsUpgradeAt T cvS caps envₐ envᵦ)
    (p : Option (ConstantInfo .anon) → Bool)
    (hinv : ∀ cv c₁ c₂, p (some (.indInfo cv c₁)) = p (some (.indInfo cv c₂)))
    (k : KKey) : p (envᵦ.find? k) = p (envₐ.find? k) := by
  by_cases hk : k = T
  · subst hk
    rw [h.find_self_b, h.find_self_a]
    exact hinv cvS caps {}
  · rw [h.find_ne hk]

theorem findProj?_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (sn : KKey) (i : Nat) :
    envᵦ.findProj? sn i = envₐ.findProj? sn i := by
  unfold Ix.Kernel.Env.findProj?
  by_cases hne : Ix.Kernel.projTableName sn = T
  · rw [hne, h.find_self_b, h.find_self_a]
  · rw [h.find_ne hne]

theorem towerSlotsAll_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (sn : KKey) (nF : Nat) :
    Ix.Kernel.towerSlotsAll envᵦ sn nF = Ix.Kernel.towerSlotsAll envₐ sn nF := by
  unfold Ix.Kernel.towerSlotsAll
  simp only [h.findProj?_eq]

theorem recSlotsAll_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (sn : KKey) (nF : Nat) :
    Ix.Kernel.recSlotsAll envᵦ sn nF = Ix.Kernel.recSlotsAll envₐ sn nF := by
  unfold Ix.Kernel.recSlotsAll
  congr 1
  funext j
  by_cases hne : Ix.Kernel.projFnName sn j = T
  · rw [hne, h.find_self_b, h.find_self_a]
  · rw [h.find_ne hne]

theorem etaProjs_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (sn : KKey) (us : List KLevel)
    (targs : List KExpr) (b : KExpr) (nF : Nat) :
    Ix.Kernel.etaProjs envᵦ sn us targs b nF = Ix.Kernel.etaProjs envₐ sn us targs b nF := by
  unfold Ix.Kernel.etaProjs
  rw [h.towerSlotsAll_eq]

theorem etaFabArgsE_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (sn : KKey) (us : List KLevel)
    (targs : List KExpr) (b : KExpr) (nF : Nat) :
    Ix.Kernel.etaFabArgsE envᵦ sn us targs b nF = Ix.Kernel.etaFabArgsE envₐ sn us targs b nF := by
  unfold Ix.Kernel.etaFabArgsE
  rw [h.etaProjs_eq]

theorem andRescueSlotsSem_iff (h : CapsUpgradeAt T cvS caps envₐ envᵦ) {ctor : KKey} {nP : Nat}
    {ust : List KLevel} :
    Ix.Kernel.Rules.AndRescueSlotsSem envₐ ctor nP ust →
      Ix.Kernel.Rules.AndRescueSlotsSem envᵦ ctor nP ust := by
  intro hand j hj
  obtain ⟨e, hp, rest⟩ := hand j hj
  rw [← h.findProj?_eq] at hp
  exact ⟨e, hp, rest⟩

theorem unfoldDefinition_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (e : KExpr) :
    Ix.Kernel.unfoldDefinition envᵦ e = Ix.Kernel.unfoldDefinition envₐ e := by
  unfold Ix.Kernel.unfoldDefinition
  split
  · rename_i n _ _
    by_cases hn : n = T
    · subst hn; rw [h.find_self_b, h.find_self_a]
    · rw [h.find_ne hn]
  · rfl

theorem natLitSupported_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) :
    Ix.Kernel.natLitSupported envᵦ = Ix.Kernel.natLitSupported envₐ := by
  unfold Ix.Kernel.natLitSupported
  rw [h.find_basis (by simp [Ix.Kernel.reservedBasisNames]),
    h.find_basis (by simp [Ix.Kernel.reservedBasisNames]),
    h.find_basis (by simp [Ix.Kernel.reservedBasisNames])]

theorem strLitSupported_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) :
    Ix.Kernel.strLitSupported envᵦ = Ix.Kernel.strLitSupported envₐ := by
  unfold Ix.Kernel.strLitSupported
  rw [h.natLitSupported_eq,
    h.pred_caps_inv Ix.Kernel.stringTyOk (fun _ _ _ => rfl),
    h.pred_caps_inv Ix.Kernel.stringOfListTyOk (fun _ _ _ => rfl),
    h.pred_caps_inv Ix.Kernel.listTyOk (fun _ _ _ => rfl),
    h.pred_caps_inv Ix.Kernel.listNilTyOk (fun _ _ _ => rfl),
    h.pred_caps_inv Ix.Kernel.listConsTyOk (fun _ _ _ => rfl),
    h.pred_caps_inv Ix.Kernel.charTyOk (fun _ _ _ => rfl),
    h.pred_caps_inv Ix.Kernel.charOfNatTyOk (fun _ _ _ => rfl)]

theorem natOpStored_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (c : KKey) :
    Ix.Kernel.natOpStored envᵦ c = Ix.Kernel.natOpStored envₐ c := by
  unfold Ix.Kernel.natOpStored
  by_cases hc : c = T
  · subst hc; rw [h.find_self_b, h.find_self_a]
  · rw [h.find_ne hc]

theorem natAddTyOk_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) :
    Ix.Kernel.Rules.natAddTyOk (envᵦ.find? Ix.Kernel.natAddName) =
      Ix.Kernel.Rules.natAddTyOk (envₐ.find? Ix.Kernel.natAddName) :=
  h.pred_caps_inv Ix.Kernel.Rules.natAddTyOk (fun _ _ _ => rfl) Ix.Kernel.natAddName

theorem isUnitLikeTy_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (e : KExpr) :
    Ix.Kernel.isUnitLikeTy envᵦ e = Ix.Kernel.isUnitLikeTy envₐ e := by
  cases e with
  | const c us =>
    unfold Ix.Kernel.isUnitLikeTy
    rw [h.find_basis (by simp [Ix.Kernel.reservedBasisNames]),
      h.find_basis (by simp [Ix.Kernel.reservedBasisNames])]
  | _ => rfl

theorem headTypePW_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (e : KExpr) (n : Nat) :
    Ix.Kernel.headTypePW envᵦ.find? e n = Ix.Kernel.headTypePW envₐ.find? e n := by
  cases e with
  | const I us =>
    simp only [Ix.Kernel.headTypePW]
    by_cases hI : I = T
    · subst hI; rw [h.find_self_b, h.find_self_a]; rfl
    · rw [h.find_ne hI]
  | _ => rfl

theorem typeSortPW_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (E : KExpr) :
    Ix.Kernel.typeSortPW envᵦ.find? E = Ix.Kernel.typeSortPW envₐ.find? E := by
  unfold Ix.Kernel.typeSortPW
  split
  · rfl
  · rfl
  · exact h.headTypePW_eq E.getAppFn E.numArgs

theorem headProofPW_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (e : KExpr) :
    Ix.Kernel.headProofPW envᵦ.find? e = Ix.Kernel.headProofPW envₐ.find? e := by
  cases e with
  | const c us =>
    simp only [Ix.Kernel.headProofPW, h.typeSortPW_eq]
    by_cases hc : c = T
    · subst hc; rw [h.find_self_b, h.find_self_a]; rfl
    · rw [h.find_ne hc]
  | fvar _ ty => exact h.typeSortPW_eq ty
  | _ => rfl

theorem isProofFast_eq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) (a : KExpr) :
    Ix.Kernel.isProofFast envᵦ.find? a = Ix.Kernel.isProofFast envₐ.find? a := by
  unfold Ix.Kernel.isProofFast
  have hpw : Ix.Kernel.proofPW envᵦ.find? a = Ix.Kernel.proofPW envₐ.find? a := by
    unfold Ix.Kernel.proofPW
    split
    · rfl
    · exact h.headProofPW_eq a.getAppFn
  rw [hpw]

theorem find_ind_any (h : CapsUpgradeAt T cvS caps envₐ envᵦ) {T₀ : KKey}
    {cvT' : ConstantVal .anon} {caps' : Ix.Kernel.IndCaps .anon}
    (hT : envₐ.find? T₀ = some (.indInfo cvT' caps')) :
    ∃ cvT'' caps'', envᵦ.find? T₀ = some (.indInfo cvT'' caps'') := by
  by_cases hT₀ : T₀ = T
  · subst hT₀; exact ⟨cvS, caps, h.find_self_b⟩
  · rw [h.find_ne hT₀]; exact ⟨cvT', caps', hT⟩

theorem find_ind_of_no_rec_head (h : CapsUpgradeAt T cvS caps envₐ envᵦ)
    {recName : KKey} {cv : ConstantVal .anon} {mI rP : Nat} {rl : RecRule .anon}
    {cvj : ConstantVal .anon} {cnP cnF : Nat} {T₀ : KKey} {tus : List KLevel}
    {cvT' : ConstantVal .anon} {caps' : Ix.Kernel.IndCaps .anon}
    (hrec : envₐ.find? recName = some (.recInfo cv mI rP [rl]))
    (hctor : envₐ.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hhead : (cvj.type.piResult).getAppFn = .const T₀ tus)
    (hT : envₐ.find? T₀ = some (.indInfo cvT' caps')) :
    envᵦ.find? T₀ = some (.indInfo cvT' caps') := by
  have hne : T₀ ≠ T := fun heq => by
    subst heq
    exact h.no_rec_head hrec hctor hhead
  rwa [h.find_ne hne]

theorem find_ind_of_eta (h : CapsUpgradeAt T cvS caps envₐ envᵦ) {T₀ : KKey}
    {cvT' : ConstantVal .anon} {caps' : Ix.Kernel.IndCaps .anon}
    (hT : envₐ.find? T₀ = some (.indInfo cvT' caps')) (heta : caps'.eta = true) :
    envᵦ.find? T₀ = some (.indInfo cvT' caps') := by
  have hne : T₀ ≠ T := fun heq => by
    subst heq
    rw [h.find_self_a] at hT
    injection hT with heq'
    injection heq' with _ hcaps
    subst hcaps
    exact nomatch heta
  rwa [h.find_ne hne]

theorem find_ind_of_unit (h : CapsUpgradeAt T cvS caps envₐ envᵦ) {T₀ : KKey}
    {cvT' : ConstantVal .anon} {caps' : Ix.Kernel.IndCaps .anon}
    (hT : envₐ.find? T₀ = some (.indInfo cvT' caps')) (hu : caps'.unitlike = true) :
    envᵦ.find? T₀ = some (.indInfo cvT' caps') := by
  have hne : T₀ ≠ T := fun heq => by
    subst heq
    rw [h.find_self_a] at hT
    injection hT with heq'
    injection heq' with _ hcaps
    subst hcaps
    exact nomatch hu
  rwa [h.find_ne hne]

theorem infer_const_upgrade (h : CapsUpgradeAt T cvS caps envₐ envᵦ)
    {g : Grade} {d : Nat} {n : KKey} {us : List KLevel} {ci : ConstantInfo .anon}
    (hf : envₐ.find? n = some ci) (htw : ci.isTowerEntry = false)
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    Infer envᵦ g d (.const n us)
      (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us) := by
  by_cases hn : n = T
  · subst hn
    rw [h.find_self_a] at hf
    injection hf with hci
    subst hci
    change Infer envᵦ g d (.const n us) (cvS.type.instantiateLevelParams cvS.levelParams us)
    exact Infer.const (ci := .indInfo cvS caps) h.find_self_b rfl hlen
  · exact Infer.const (by rwa [h.find_ne hn]) htw hlen

mutual

theorem upgradeRed (h : CapsUpgradeAt T cvS caps envₐ envᵦ) :
    ∀ {d : Nat} {e₁ e₂ : KExpr}, Red envₐ d e₁ e₂ → Red envᵦ d e₁ e₂
  | _, _, _, .refl => .refl
  | _, _, _, .trans r₁ r₂ => .trans (h.upgradeRed r₁) (h.upgradeRed r₂)
  | _, _, _, .appFn r => .appFn (h.upgradeRed r)
  | _, _, _, .projArg r => .projArg (h.upgradeRed r)
  | _, _, _, .appArg r => .appArg (h.upgradeRed r)
  | _, _, _, .betaGate hg => .betaGate hg
  | _, _, _, .beta hi hd => .beta (h.upgradeInfer hi) (h.upgradeDefEq hd)
  | _, _, _, .delta hu => .delta (by rwa [h.unfoldDefinition_eq])
  | _, _, _, .deltaThm hf hl hfv hlb hi hd hs hr hz =>
    .deltaThm (h.find_non_ind hf fun _ _ e => nomatch e) hl hfv hlb
      (h.upgradeInfer hi) (h.upgradeDefEq hd) (h.upgradeInfer hs) (h.upgradeRed hr) hz
  | _, _, _, .eqProof hfn heq hp hws hlb hfl ha hda hb hdb hT hrT hev => by
    have heq' : ∃ ci', envᵦ.find? Ix.Kernel.eqName = some ci' := by
      rw [h.find_basis (by simp [Ix.Kernel.reservedBasisNames])]
      exact ⟨_, heq⟩
    obtain ⟨ci', heq'⟩ := heq'
    exact .eqProof hfn heq' (h.upgradeInfer hp) hws hlb hfl
      (h.upgradeInfer ha) (h.upgradeDefEq hda)
      (h.upgradeInfer hb) (h.upgradeDefEq hdb)
      (h.upgradeInfer hT) (h.upgradeRed hrT) hev
  | _, _, _, .natLit hn => .natLit (by rwa [h.natLitSupported_eq])
  | _, _, _, .natZeroLit hn => .natZeroLit (by rwa [h.natLitSupported_eq])
  | _, _, _, .strLit hs => .strLit (by rwa [h.strLitSupported_eq])
  | _, _, _, .natSucc hn hr hraw => .natSucc (by rwa [h.natLitSupported_eq]) (h.upgradeRed hr) hraw
  | _, _, _, .natOp hm hs hra hna hrb hnb hres =>
    .natOp hm (by rwa [h.natOpStored_eq]) (h.upgradeRed hra) hna (h.upgradeRed hrb) hnb hres
  | _, _, _, .natAddSucc hn ha =>
    .natAddSucc (by rwa [h.natLitSupported_eq]) (by rwa [h.natAddTyOk_eq])
  | _, _, _, .natAddZero hn ha hr hraw =>
    .natAddZero (by rwa [h.natLitSupported_eq]) (by rwa [h.natAddTyOk_eq]) (h.upgradeRed hr) hraw
  | _, _, _, .proj hp hfn hi hlen hus hfire hc hcerts =>
    .proj (by rwa [h.findProj?_eq]) hfn hi hlen hus hfire
      (h.find_non_ind hc fun _ _ e => nomatch e) (h.upgradeCerts hcerts)
  | _, _, _, .iota hfn hrec hlen hus hmaj hmfn hctor hrl hmlen hnf hcmp hpc hc1 hc2 hres hideq =>
    .iota hfn (h.find_non_ind hrec fun _ _ e => nomatch e) hlen hus (h.upgradeRed hmaj) hmfn
      (h.find_non_ind hctor fun _ _ e => nomatch e) hrl hmlen hnf hcmp
      (fun hp => h.upgradeDefEqList (hpc hp))
      (h.upgradeCerts hc1) (h.upgradeCerts hc2) hres
      (fun hm => h.upgradeDefEqList (hideq hm))
  | _, _, _, .rescueK hrec hk hctor hhead hT hm hrm htfn hust hle hfab hws hlb hfl hcerts hif
      hdf1 hdf2 => by
    obtain ⟨_, _, hT'⟩ := h.find_ind_any hT
    exact .rescueK (h.find_non_ind hrec fun _ _ e => nomatch e) hk
      (h.find_non_ind hctor fun _ _ e => nomatch e) hhead hT'
      (h.upgradeInfer hm) (h.upgradeRed hrm) htfn hust hle hfab hws hlb hfl
      (h.upgradeCerts hcerts) (h.upgradeInfer hif) (h.upgradeDefEq hdf1) (h.upgradeDefEq hdf2)
  | _, _, _, .rescueEta hrec heta hctor hhead hT hm hrm htfn hlen hust hnz hfab hws hlb hfl
      hcerts hepc hdf => by
    have hT' := h.find_ind_of_no_rec_head hrec hctor hhead hT
    have hc := h.upgradeCerts hcerts
    rw [← h.etaFabArgsE_eq] at hfab hc
    exact .rescueEta (h.find_non_ind hrec fun _ _ e => nomatch e) heta
      (h.find_non_ind hctor fun _ _ e => nomatch e) hhead hT'
      (h.upgradeInfer hm) (h.upgradeRed hrm) htfn hlen hust hnz hfab hws hlb hfl
      hc
      (fun htw => h.upgradeEtaProjCerts (hepc (by rwa [← h.towerSlotsAll_eq])))
      (h.upgradeDefEq hdf)
  | _, _, _, .rescueAnd hrec hctor hhead hT hm hrm htfn hlen hust hand hfab hws hlb hfl hcerts
      hif hdf1 hdf2 => by
    obtain ⟨_, _, hT'⟩ := h.find_ind_any hT
    exact .rescueAnd (h.find_non_ind hrec fun _ _ e => nomatch e)
      (h.find_non_ind hctor fun _ _ e => nomatch e) hhead hT'
      (h.upgradeInfer hm) (h.upgradeRed hrm) htfn hlen hust (h.andRescueSlotsSem_iff hand)
      hfab hws hlb hfl (h.upgradeCerts hcerts) (h.upgradeInfer hif)
      (h.upgradeDefEq hdf1) (h.upgradeDefEq hdf2)

theorem upgradeDefEq (h : CapsUpgradeAt T cvS caps envₐ envᵦ) :
    ∀ {d : Nat} {a b : KExpr}, DefEq envₐ d a b → DefEq envᵦ d a b
  | _, _, _, .refl => .refl
  | _, _, _, .symm hd => .symm (h.upgradeDefEq hd)
  | _, _, _, .redL hr hd => .redL (h.upgradeRed hr) (h.upgradeDefEq hd)
  | _, _, _, .sort hev => .sort hev
  | _, _, _, .fvar => .fvar
  | _, _, _, .const hev => .const hev
  | _, _, _, .natZero => .natZero
  | _, _, _, .natSucc hd => .natSucc (h.upgradeDefEq hd)
  | _, _, _, .natOffset hn hadd hoa hob hd =>
    .natOffset (by rwa [h.natLitSupported_eq])
      (fun hor => by rw [h.natAddTyOk_eq]; exact hadd hor) hoa hob (h.upgradeDefEq hd)
  | _, _, _, .forallE hty hbo hpw =>
    .forallE (h.upgradeDefEq hty) (h.upgradeDefEq hbo) hpw
  | _, _, _, .lam hty hbo hpw =>
    .lam (h.upgradeDefEq hty) (h.upgradeDefEq hbo) hpw
  | _, _, _, .app hf ha => .app (h.upgradeDefEq hf) (h.upgradeDefEq ha)
  | _, _, _, .proj hd => .proj (h.upgradeDefEq hd)
  | _, _, _, .eta hib hrb hty hbo hpw =>
    .eta (h.upgradeInfer hib) (h.upgradeRed hrb) (h.upgradeDefEq hty) (h.upgradeDefEq hbo) hpw
  | _, _, _, .proofFast hpa hpb =>
    .proofFast (by rwa [h.isProofFast_eq]) (by rwa [h.isProofFast_eq])
  | _, _, _, .proofIrrel hia hta hra hza hib htb hrb hzb =>
    .proofIrrel (h.upgradeInfer hia) (h.upgradeInfer hta) (h.upgradeRed hra) hza
      (h.upgradeInfer hib) (h.upgradeInfer htb) (h.upgradeRed hrb) hzb
  | _, _, _, .unitLike hia hra hua hib hrb hub =>
    .unitLike (h.upgradeInfer hia) (h.upgradeRed hra) (by rwa [h.isUnitLikeTy_eq])
      (h.upgradeInfer hib) (h.upgradeRed hrb) (by rwa [h.isUnitLikeTy_eq])
  | _, _, _, .structEta hib hrb hafn hc halen hwfn hT heta hec hnbT hnbc hwlen hus hlps hslots
      hev hcerts hepc hdp hdf => by
    have hT' := h.find_ind_of_eta hT heta
    have hdf' := h.upgradeDefEqList hdf
    rw [← h.etaProjs_eq] at hdf'
    exact .structEta (h.upgradeInfer hib) (h.upgradeRed hrb) hafn
      (h.find_non_ind hc fun _ _ e => nomatch e) halen hwfn hT' heta hec hnbT hnbc hwlen hus hlps
      (by rwa [h.towerSlotsAll_eq, h.recSlotsAll_eq]) hev (h.upgradeCerts hcerts)
      (fun htw => h.upgradeEtaProjCerts (hepc (by rwa [← h.towerSlotsAll_eq])))
      (h.upgradeDefEqList hdp) hdf'
  | _, _, _, .structUnit hia hra hwfn hT hu hnbT hwlen hus hib hrb hde hcerts => by
    have hT' := h.find_ind_of_unit hT hu
    exact .structUnit (h.upgradeInfer hia) (h.upgradeRed hra) hwfn hT' hu hnbT hwlen hus
      (h.upgradeInfer hib) (h.upgradeRed hrb) (h.upgradeDefEq hde) (h.upgradeCerts hcerts)
  | _, _, _, .proofIrrelTy hia hta hra hza hib hde =>
    .proofIrrelTy (h.upgradeInfer hia) (h.upgradeInfer hta) (h.upgradeRed hra) hza
      (h.upgradeInfer hib) (h.upgradeDefEq hde)
  | _, _, _, .unitLikeTy hia hra hwfn hT hu hwlen hcerts hnb hib hde => by
    have hT' := h.find_ind_of_unit hT hu
    exact .unitLikeTy (h.upgradeInfer hia) (h.upgradeRed hra) hwfn hT' hu hwlen
      (h.upgradeCerts hcerts) (hnb.imp id (by rw [h.isUnitLikeTy_eq]; exact id))
      (h.upgradeInfer hib) (h.upgradeDefEq hde)
  | _, _, _, .structEtaTy hafn hc halen hT heta hec hpos htw hia hra hcerts hib hde hdf => by
    have hT' := h.find_ind_of_eta hT heta
    exact .structEtaTy hafn (h.find_non_ind hc fun _ _ e => nomatch e) halen hT' heta hec hpos
      (by rwa [h.towerSlotsAll_eq]) (h.upgradeInfer hia) (h.upgradeRed hra)
      (h.upgradeCerts hcerts) (h.upgradeInfer hib) (h.upgradeDefEq hde) (h.upgradeDefEqList hdf)

theorem upgradeInfer (h : CapsUpgradeAt T cvS caps envₐ envᵦ) :
    ∀ {g : Grade} {d : Nat} {e t : KExpr}, Infer envₐ g d e t → Infer envᵦ g d e t
  | _, _, _, _, .sort => .sort
  | _, _, _, _, .fvar hlt => .fvar hlt
  | _, _, _, _, .const hf htw hlen => h.infer_const_upgrade hf htw hlen
  | _, _, _, _, .natLit hn => .natLit (by rwa [h.natLitSupported_eq])
  | _, _, _, _, .strLit hs => .strLit (by rwa [h.strLitSupported_eq])
  | _, _, _, _, .forallE hty hrty hbo hrbo hz =>
    .forallE (h.upgradeInfer hty) (h.upgradeRed hrty)
      (h.upgradeInfer hbo) (h.upgradeRed hrbo) hz
  | _, _, _, _, .lam hty hrty hbo hpw hbt hrbt hz =>
    .lam (fun hg => h.upgradeInfer (hty hg)) (fun hg => h.upgradeRed (hrty hg))
      (h.upgradeInfer hbo) hpw
      (fun hn => h.upgradeInfer (hbt hn)) (fun hn => h.upgradeRed (hrbt hn)) hz
  | _, _, _, _, .app hf hrf ha hda =>
    .app (h.upgradeInfer hf) (h.upgradeRed hrf) (h.upgradeInfer ha) (h.upgradeDefEq hda)
  | _, _, _, _, .appSkip hf hrf hnev =>
    .appSkip (h.upgradeInfer hf) (h.upgradeRed hrf) hnev
  | _, _, _, _, .proj hpe hrpe hfn hp hlen hus hfire =>
    .proj (h.upgradeInfer hpe) (h.upgradeRed hrpe) hfn (by rwa [h.findProj?_eq]) hlen hus hfire

theorem upgradeCerts (h : CapsUpgradeAt T cvS caps envₐ envᵦ) :
    ∀ {d : Nat} {lic : Bool} {E : KExpr} {args : List KExpr},
      Certs envₐ d lic E args → Certs envᵦ d lic E args
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .skip hlic hnev hc => .skip hlic hnev (h.upgradeCerts hc)
  | _, _, _, _, .cert hi hd hc => .cert (h.upgradeInfer hi) (h.upgradeDefEq hd) (h.upgradeCerts hc)

theorem upgradeDefEqList (h : CapsUpgradeAt T cvS caps envₐ envᵦ) :
    ∀ {d : Nat} {as_ bs : List KExpr}, DefEqList envₐ d as_ bs → DefEqList envᵦ d as_ bs
  | _, _, _, .nil => .nil
  | _, _, _, .cons hd hds => .cons (h.upgradeDefEq hd) (h.upgradeDefEqList hds)

theorem upgradeEtaProjCerts (h : CapsUpgradeAt T cvS caps envₐ envᵦ) :
    ∀ {d : Nat} {sn : KKey} {us' : List KLevel} {targs : List KExpr} {b : KExpr}
      {lpsT : List LevelParam} {idxs : List Nat},
      EtaProjCerts envₐ d sn us' targs b lpsT idxs →
        EtaProjCerts envᵦ d sn us' targs b lpsT idxs
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons hf hlps hsp hc hrest =>
    .cons (h.find_non_ind hf fun _ _ e => nomatch e) hlps hsp (h.upgradeCerts hc)
      (h.upgradeEtaProjCerts hrest)

end

end CapsUpgradeAt

private theorem constsResolve_piResult {env : Ix.Kernel.Env .anon} :
    ∀ {e : KExpr}, e.constsResolve env = true → e.piResult.constsResolve env = true
  | .forallE _ b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    unfold Expr.piResult
    exact constsResolve_piResult h.2
  | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
  | .lam _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h => h

private theorem constsResolve_getAppFn {env : Ix.Kernel.Env .anon} :
    ∀ {e : KExpr}, e.constsResolve env = true → e.getAppFn.constsResolve env = true
  | .app f _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    unfold Expr.getAppFn
    exact constsResolve_getAppFn h.1
  | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h
  | .lam _ _ _, h | .forallE _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h => h

private theorem env_find?_cons_ne {c : ConstantInfo .anon} {env : Ix.Kernel.Env .anon} {k : KKey}
    (hne : c.name ≠ k) :
    (Ix.Kernel.Env.mk (c :: env.consts)).find? k = env.find? k := by
  rw [Ix.Kernel.Env.find?_cons, ite_eq_right hne]

/-- Construct `CapsUpgradeAt` between `⟨.indInfo cvS {} :: env.consts⟩` and
`⟨.indInfo cvS caps :: env.consts⟩` for a fresh unpinned inductive `cvS.name`. -/
theorem CapsUpgradeAt.of_fresh_ind {env : Ix.Kernel.Env .anon} {cvS : ConstantVal .anon}
    (caps : Ix.Kernel.IndCaps .anon) (hstore : Ix.Kernel.Open.StoreInv env)
    (hfresh : env.find? cvS.name = none)
    (hnb : Ix.Kernel.reservedBasisNames.contains cvS.name = false) :
    CapsUpgradeAt cvS.name cvS caps
      ⟨.indInfo cvS {} :: env.consts⟩ ⟨.indInfo cvS caps :: env.consts⟩ where
  find_self_a := Ix.Kernel.Env.find?_cons_self (.indInfo cvS {}) env
  find_self_b := Ix.Kernel.Env.find?_cons_self (.indInfo cvS caps) env
  find_ne := fun {k} hne => by
    have hne' : cvS.name ≠ k := fun e => hne e.symm
    rw [env_find?_cons_ne (c := .indInfo cvS caps) hne',
      env_find?_cons_ne (c := .indInfo cvS {}) hne']
  no_rec_head := fun {recName cv mI rP rl cvj cnP cnF tus} hrec hctor hhead => by
    have hrec_env : env.find? recName = some (.recInfo cv mI rP [rl]) := by
      rw [Ix.Kernel.Env.find?_cons] at hrec
      split at hrec
      · exact nomatch hrec
      · exact hrec
    have hctor_env : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) := by
      rw [Ix.Kernel.Env.find?_cons] at hctor
      split at hctor
      · exact nomatch hctor
      · exact hctor
    have hwf := hstore.wf _ (List.mem_of_find?_eq_some hctor_env)
    have hcr : cvj.type.constsResolve env = true := hwf.2.2.1
    have hfn := constsResolve_getAppFn (constsResolve_piResult hcr)
    rw [hhead] at hfn
    simp only [Expr.constsResolve, hfresh] at hfn
    exact absurd hfn Bool.false_ne_true
  not_basis := hnb

/-- Extending both sides of `CapsUpgradeAt` with a fresh constructor preserves `CapsUpgradeAt`. -/
theorem CapsUpgradeAt.consCtor {T : KKey} {cvS : ConstantVal .anon}
    {caps : Ix.Kernel.IndCaps .anon} {envₐ envᵦ : Ix.Kernel.Env .anon}
    (h : CapsUpgradeAt T cvS caps envₐ envᵦ)
    (hrec_ctors : Ix.Kernel.RecCtorsStored envₐ)
    {cvC : ConstantVal .anon} {nP nF : Nat}
    (hC_ne : cvC.name ≠ T) (hfresh_a : envₐ.find? cvC.name = none) :
    CapsUpgradeAt T cvS caps
      ⟨.ctorInfo cvC nP nF :: envₐ.consts⟩ ⟨.ctorInfo cvC nP nF :: envᵦ.consts⟩ where
  find_self_a := by
    rw [env_find?_cons_ne (c := .ctorInfo cvC nP nF) hC_ne]
    exact h.find_self_a
  find_self_b := by
    rw [env_find?_cons_ne (c := .ctorInfo cvC nP nF) hC_ne]
    exact h.find_self_b
  find_ne := fun {k} hne => by
    by_cases hk : cvC.name = k
    · subst hk
      simp only [Ix.Kernel.Env.find?_cons, ConstantInfo.name, ConstantInfo.toConstantVal, ↓reduceIte]
    · rw [env_find?_cons_ne (c := .ctorInfo cvC nP nF) hk,
        env_find?_cons_ne (c := .ctorInfo cvC nP nF) hk]
      exact h.find_ne hne
  no_rec_head := fun {recName cv mI rP rl cvj cnP cnF tus} hrec hctor => by
    have hrec_a : envₐ.find? recName = some (.recInfo cv mI rP [rl]) := by
      rw [Ix.Kernel.Env.find?_cons] at hrec
      split at hrec
      · exact nomatch hrec
      · exact hrec
    have hctor_a : envₐ.find? rl.ctor = some (.ctorInfo cvj cnP cnF) := by
      rw [Ix.Kernel.Env.find?_cons] at hctor
      split at hctor
      · rename_i heq
        have heq' : cvC.name = rl.ctor := heq
        obtain ⟨⟨cvj', hfc, -⟩, -, -⟩ :=
          hrec_ctors recName cv mI rP [rl] hrec_a rl List.mem_cons_self
        rw [← heq', hfresh_a] at hfc
        exact nomatch hfc
      · exact hctor
    exact h.no_rec_head hrec_a hctor_a
  not_basis := h.not_basis

/-- Extending `env` by `consSumCtors` over fresh non-projection-table constructors is an `EnvExt`,
preserves `DeclStoreInv`, and preserves `CapsUpgradeAt`. -/
theorem envExt_consSumCtors (nP : Nat) :
    ∀ (ctorsA : List (ConstantVal .anon × Nat)) {env : Ix.Kernel.Env .anon},
      (ctorsA.map (·.1.name)).Nodup →
      (∀ c ∈ ctorsA, env.find? c.1.name = none) →
      (∀ c ∈ ctorsA, c.1.name.isProjFnShape = false) →
      Ix.Kernel.EnvExt env (Ix.Kernel.consSumCtors nP ctorsA env)
  | [], _, _, _, _ => Ix.Kernel.EnvExt.refl _
  | c :: cs, env, hnd, hfresh, hsh => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hext₁ : Ix.Kernel.EnvExt env ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩ :=
      envExt_cons_nonProj (hfresh c List.mem_cons_self)
        (ne_projTableName_of_isProjFnShape_false (hsh c List.mem_cons_self))
    have hfresh' : ∀ c' ∈ cs,
        (Ix.Kernel.Env.mk (.ctorInfo c.1 nP c.2 :: env.consts)).find? c'.1.name = none := by
      intro c' hc'
      have hne : c.1.name ≠ c'.1.name := fun he =>
        hnd.1 (by rw [he]; exact List.mem_map.mpr ⟨c', hc', rfl⟩)
      rw [env_find?_cons_ne (c := .ctorInfo c.1 nP c.2) hne]
      exact hfresh c' (List.mem_cons_of_mem _ hc')
    exact hext₁.trans (envExt_consSumCtors nP cs hnd.2 hfresh'
      (fun c' hc' => hsh c' (List.mem_cons_of_mem _ hc')))

theorem DeclStoreInv.consSumCtors (nP : Nat) :
    ∀ (ctorsA : List (ConstantVal .anon × Nat)) {env : Ix.Kernel.Env .anon},
      DeclStoreInv env →
      (ctorsA.map (·.1.name)).Nodup →
      (∀ c ∈ ctorsA, env.find? c.1.name = none) →
      (∀ c ∈ ctorsA, c.1.name.isProjFnShape = false) →
      (∀ c ∈ ctorsA,
        c.1.type.hasFvar = false ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve env = true ∧
        c.1.type.looseBVarsBounded 0 = true) →
      DeclStoreInv (Ix.Kernel.consSumCtors nP ctorsA env)
  | [], _, hS, _, _, _, _ => hS
  | c :: cs, env, hS, hnd, hfresh, hsh, hty => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hnp := ne_projTableName_of_isProjFnShape_false (hsh c List.mem_cons_self)
    have hS₁ : DeclStoreInv ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩ :=
      hS.consCtor (hfresh c List.mem_cons_self) hnp (hty c List.mem_cons_self)
    have hfresh' : ∀ c' ∈ cs,
        (Ix.Kernel.Env.mk (.ctorInfo c.1 nP c.2 :: env.consts)).find? c'.1.name = none := by
      intro c' hc'
      have hne : c.1.name ≠ c'.1.name := fun he =>
        hnd.1 (by rw [he]; exact List.mem_map.mpr ⟨c', hc', rfl⟩)
      rw [env_find?_cons_ne (c := .ctorInfo c.1 nP c.2) hne]
      exact hfresh c' (List.mem_cons_of_mem _ hc')
    refine DeclStoreInv.consSumCtors nP cs hS₁ hnd.2 hfresh'
      (fun c' hc' => hsh c' (List.mem_cons_of_mem _ hc')) (fun c' hc' => ?_)
    obtain ⟨hfv, hlpd, hcr, hlbd⟩ := hty c' (List.mem_cons_of_mem _ hc')
    exact ⟨hfv, hlpd, Ix.Kernel.Expr.constsResolve_mono hcr, hlbd⟩

theorem CapsUpgradeAt.consSumCtors (nP : Nat) {T : KKey} {cvS : ConstantVal .anon}
    {caps : Ix.Kernel.IndCaps .anon} :
    ∀ (ctorsA : List (ConstantVal .anon × Nat)) {envₐ envᵦ : Ix.Kernel.Env .anon},
      CapsUpgradeAt T cvS caps envₐ envᵦ →
      DeclStoreInv envₐ →
      (ctorsA.map (·.1.name)).Nodup →
      (∀ c ∈ ctorsA, envₐ.find? c.1.name = none) →
      (∀ c ∈ ctorsA, c.1.name.isProjFnShape = false) →
      (∀ c ∈ ctorsA,
        c.1.type.hasFvar = false ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve envₐ = true ∧
        c.1.type.looseBVarsBounded 0 = true) →
      CapsUpgradeAt T cvS caps
        (Ix.Kernel.consSumCtors nP ctorsA envₐ)
        (Ix.Kernel.consSumCtors nP ctorsA envᵦ)
  | [], _, _, hup, _, _, _, _, _ => hup
  | c :: cs, envₐ, envᵦ, hup, hSₐ, hnd, hfresh, hsh, hty => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hfc := hfresh c List.mem_cons_self
    have hC_ne : c.1.name ≠ T := by
      intro heq
      rw [heq, hup.find_self_a] at hfc
      exact nomatch hfc
    have hnp := ne_projTableName_of_isProjFnShape_false (hsh c List.mem_cons_self)
    have hup₁ := hup.consCtor (cvC := c.1) (nP := nP) (nF := c.2) hSₐ.store.rec_ctors hC_ne hfc
    have hSₐ₁ : DeclStoreInv ⟨.ctorInfo c.1 nP c.2 :: envₐ.consts⟩ :=
      hSₐ.consCtor hfc hnp (hty c List.mem_cons_self)
    have hfresh' : ∀ c' ∈ cs,
        (Ix.Kernel.Env.mk (.ctorInfo c.1 nP c.2 :: envₐ.consts)).find? c'.1.name = none := by
      intro c' hc'
      have hne : c.1.name ≠ c'.1.name := fun he =>
        hnd.1 (by rw [he]; exact List.mem_map.mpr ⟨c', hc', rfl⟩)
      rw [env_find?_cons_ne (c := .ctorInfo c.1 nP c.2) hne]
      exact hfresh c' (List.mem_cons_of_mem _ hc')
    refine CapsUpgradeAt.consSumCtors nP cs hup₁ hSₐ₁ hnd.2 hfresh'
      (fun c' hc' => hsh c' (List.mem_cons_of_mem _ hc')) (fun c' hc' => ?_)
    obtain ⟨hfv, hlpd, hcr, hlbd⟩ := hty c' (List.mem_cons_of_mem _ hc')
    exact ⟨hfv, hlpd, Ix.Kernel.Expr.constsResolve_mono hcr, hlbd⟩

/-! ## `ConstantValCheckJ` from `validate_expr_well_scoped` + `k_ensure_sort` -/

theorem levelParam_nodup_of_nodup :
    ∀ {ps : List LevelParam}, ps.Nodup → LevelParam.nodup ps = true
  | [], _ => rfl
  | p :: ps, h => by
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp h
    have hc : ps.contains p = false := by
      cases hc' : ps.contains p
      · rfl
      · exact absurd (List.contains_iff_mem.mp hc') hnot
    simp only [LevelParam.nodup, hc, Bool.not_false, Bool.true_and]
    exact levelParam_nodup_of_nodup hnd

/-- Lifting a sort typing derivation from `posOf cv'.levelParams cv'.type` back to `cv'.type`.
Holds by `rfl` (`posOf_range`) whenever `cv'.levelParams = List.range n` (all `Induct`, `Ctor`,
`Defn`, and small `Rec` constants); isolated as a clean bridge for `large = true` recursors where
`cv'.levelParams = k :: List.range k`. -/
def PosSortLift (env : Ix.Kernel.Env .anon) (cv' : ConstantVal .anon) : Prop :=
  ∀ sty₀ u₀,
    Infer env .full 0 (posOf cv'.levelParams cv'.type) sty₀ →
    Red env 0 sty₀ (.sort u₀) →
    ∃ sty u, Infer env .full 0 cv'.type sty ∧ Red env 0 sty (.sort u)

theorem PosSortLift.of_range {env : Ix.Kernel.Env .anon} {cv' : ConstantVal .anon} {n : Nat}
    (hlps : cv'.levelParams = List.range n) : PosSortLift env cv' := by
  intro sty₀ u₀ hinf hred
  rw [hlps, posOf_range] at hinf
  exact ⟨sty₀, u₀, hinf, hred⟩

/-- Refine `validate_expr_well_scoped` + `k_ensure_sort` on a `ValRepExact` constant `cv'` storing
`cv` (`ValStored cv' cv`) to `ConstantValCheckJ rulesJ c.env cv cv'`, also returning the heap sort
level `ℓ` and its semantic agreement `LvEq u₀ ℓ` with the sort `u₀` of `posOf cv'.levelParams cv'.type`. -/
theorem constantValCheckJ_of_checked (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    {Γ : Nat → KExpr} {cv cv' : ConstantVal .anon}
    {nl ty rc types r₁ r₂ : SourceValue F} {h h₁ h₂ h₃ : Heap F} {cs₁ cs₂ : List (Call F)}
    (hvs : IxVM.Consistency.ValStored cv' cv)
    (hv : ValRepExact c.κ h nl ty cv')
    (hlbd : cv.type.looseBVarsBounded 0 = true)
    (hfv : cv.type.hasFvar = false)
    (hfresh : c.env.find? cv.name = none)
    (hbasis : Ix.Kernel.reservedBasisNames.contains cv.name = false)
    (hshape : cv.name.isProjFnShape = false)
    (hstore : Ix.Kernel.Open.StoreInv c.env)
    (hpos : PosSortLift c.env cv')
    (ev_ws : ObsFn W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl] h r₁ h₁ cs₁)
    (ext : Heap.Extends h h₂)
    (hrc : RCRep c.t c.lim h₂ rc) (hty : TypesRep c.κ Γ h₂ 0 types)
    (hef : EnvFacts c) (hlf : LoadFacts c) (hgood : Good c cs₂)
    (ev_sort : ObsFn W "KernelInfer::k_ensure_sort" [rc, ty, types] h₂ r₂ h₃ cs₂) :
    ConstantValCheckJ rulesJ c.env cv cv' ∧
      ∃ sty₀ u₀ ℓ,
        Infer c.env .full 0 (posOf cv'.levelParams cv'.type) sty₀ ∧
        Red c.env 0 sty₀ (.sort u₀) ∧
        RepKLevel h₃ ℓ r₂ ∧ LvEq u₀ ℓ := by
  have hnd_cv' : cv'.levelParams.Nodup := hv.2.2.1.nodup_iff.mpr List.nodup_range
  have hnd_cv : LevelParam.nodup cv.levelParams = true := by
    rw [← hvs.2.1]
    exact levelParam_nodup_of_nodup hnd_cv'
  have ev_ws' : ObsFn W "KernelCheck::validate_expr_well_scoped"
      [ty, .field 0, .field (cv'.levelParams.length : F)] h r₁ h₁ cs₁ := by
    rwa [← hv.1]
  have hlpd_pos := validate_expr_well_scoped_spec hv.2.1 (hv.2.2.2 0 Γ) ev_ws'
  have hlpd' := allLevelParamsDefined_of_posOf_perm hv.2.2.1 hlpd_pos
  rw [hvs.2.1] at hlpd'
  obtain ⟨sty₀, u₀, ℓ, hinf₀, hred₀, hℓ, hu₀⟩ :=
    core_ensure_sort hCore hrc hty (ghostScoped_zero Γ) hef hlf hgood ev_sort
      (((hv.2.2.2 0 Γ).mono ext).toTm)
  have hfv_pos : (posOf cv'.levelParams cv'.type).hasFvar = false := by
    unfold posOf
    rw [Ix.Kernel.Expr.hasFvar_instantiateLevelParams]
    exact annotates_hasFvar_false hvs.2.2 hfv
  have hcr_pos := infer_constsResolve hinf₀ hstore hfv_pos
  rw [constsResolve_posOf] at hcr_pos
  obtain ⟨sty, u, hinf, hred⟩ := hpos sty₀ u₀ hinf₀ hred₀
  have hcv_eq : cv' = { cv with type := cv'.type } := by
    cases cv; cases cv'
    cases hvs.1; cases hvs.2.1
    rfl
  refine ⟨⟨cv'.type, ⟨Option.isNone_iff_eq_none.mpr hfresh, hbasis, hshape, hnd_cv,
    hlbd, hfv,
    annot_of_annotates hvs.2.2 hfv hlbd 0, hlpd', hcr_pos,
    ⟨sty, u, hinf, hred⟩⟩, hcv_eq⟩, sty₀, u₀, ℓ, hinf₀, hred₀, hℓ, hu₀⟩

/-! ## Semantic level-list equivalence, `ExprSemEq`, and `WrapRelSem` -/

private theorem evalEqList_symm (φ : LevelParam → Nat) :
    ∀ {us vs : List KLevel}, Level.EvalEqList φ us vs → Level.EvalEqList φ vs us
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨h1.symm, evalEqList_symm φ h2⟩

private theorem evalEqList_trans (φ : LevelParam → Nat) :
    ∀ {us vs ws : List KLevel},
      Level.EvalEqList φ us vs → Level.EvalEqList φ vs ws → Level.EvalEqList φ us ws
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, ⟨k1, k2⟩ => ⟨h1.trans k1, evalEqList_trans φ h2 k2⟩

theorem LvEqList.symm {us vs : List KLevel} (h : LvEqList us vs) : LvEqList vs us :=
  fun φ => evalEqList_symm φ (h φ)

theorem LvEqList.trans {us vs ws : List KLevel} (h₁ : LvEqList us vs) (h₂ : LvEqList vs ws) :
    LvEqList us ws :=
  fun φ => evalEqList_trans φ (h₁ φ) (h₂ φ)

/-- Structural equality of kernel expressions up to semantic level equivalence (`LvEq` on `.sort`
and `LvEqList` on `.const`). Captures what `kexpr_struct_eq` returning `1` certifies on two `Tm`
terms. -/
inductive ExprSemEq : KExpr → KExpr → Prop
  | bvar (i : Nat) : ExprSemEq (.bvar i) (.bvar i)
  | fvar {i : Nat} {t t' : KExpr} : ExprSemEq t t' → ExprSemEq (.fvar i t) (.fvar i t')
  | sort {u u' : KLevel} : LvEq u u' → ExprSemEq (.sort u) (.sort u')
  | const {n : KKey} {us us' : List KLevel} :
      LvEqList us us' → ExprSemEq (.const n us) (.const n us')
  | lit (l : Ix.Kernel.Literal) : ExprSemEq (.lit l) (.lit l)
  | app {f a f' a' : KExpr} :
      ExprSemEq f f' → ExprSemEq a a' → ExprSemEq (.app f a) (.app f' a')
  | lam {t b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ExprSemEq t t' → ExprSemEq b b' →
      ExprSemEq (.lam t b m) (.lam t' b' m')
  | forallE {t b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ExprSemEq t t' → ExprSemEq b b' →
      ExprSemEq (.forallE t b m) (.forallE t' b' m')
  | letE {t v b t' v' b' : KExpr} {l l' : Ix.Kernel.LetMeta} :
      ExprSemEq t t' → ExprSemEq v v' → ExprSemEq b b' →
      ExprSemEq (.letE t v b l) (.letE t' v' b' l')
  | proj {s : KKey} {i : Nat} {e e' : KExpr} :
      ExprSemEq e e' → ExprSemEq (.proj s i e) (.proj s i e')

theorem ExprSemEq.refl : ∀ e : KExpr, ExprSemEq e e
  | .bvar i => .bvar i
  | .fvar _ t => .fvar (ExprSemEq.refl t)
  | .sort u => .sort (LvEq.refl u)
  | .const _ us => .const (LvEqList.refl us)
  | .lit l => .lit l
  | .app f a => .app (ExprSemEq.refl f) (ExprSemEq.refl a)
  | .lam t b _ => .lam rfl (ExprSemEq.refl t) (ExprSemEq.refl b)
  | .forallE t b _ => .forallE rfl (ExprSemEq.refl t) (ExprSemEq.refl b)
  | .letE t v b _ => .letE (ExprSemEq.refl t) (ExprSemEq.refl v) (ExprSemEq.refl b)
  | .proj _ _ e => .proj (ExprSemEq.refl e)

theorem ExprSemEq.liftLooseBVars {e e' : KExpr} (h : ExprSemEq e e') :
    ∀ (n c : Nat), ExprSemEq (e.liftLooseBVars n c) (e'.liftLooseBVars n c) := by
  induction h with
  | bvar i =>
    intro n c
    simp only [Expr.liftLooseBVars]
    split <;> exact .bvar _
  | fvar ht _ => intro _ _; exact .fvar ht
  | sort hu => intro _ _; exact .sort hu
  | const hus => intro _ _; exact .const hus
  | lit l => intro _ _; exact .lit l
  | app _ _ ihf iha => intro n c; exact .app (ihf n c) (iha n c)
  | lam hpw _ _ iht ihb => intro n c; exact .lam hpw (iht n c) (ihb n (c + 1))
  | forallE hpw _ _ iht ihb => intro n c; exact .forallE hpw (iht n c) (ihb n (c + 1))
  | letE _ _ _ iht ihv ihb => intro n c; exact .letE (iht n c) (ihv n c) (ihb n (c + 1))
  | proj _ ihe => intro n c; exact .proj (ihe n c)

theorem ExprSemEq.instantiate1Lift {v v' : KExpr} (hv : ExprSemEq v v') {b b' : KExpr}
    (hb : ExprSemEq b b') :
    ∀ (j : Nat), ExprSemEq (b.instantiate1Lift v j) (b'.instantiate1Lift v' j) := by
  induction hb with
  | bvar i =>
    intro j
    simp only [Expr.instantiate1Lift]
    split
    · exact hv.liftLooseBVars j 0
    · split <;> exact .bvar _
  | fvar ht _ => intro _; exact .fvar ht
  | sort hu => intro _; exact .sort hu
  | const hus => intro _; exact .const hus
  | lit l => intro _; exact .lit l
  | app _ _ ihf iha => intro j; exact .app (ihf j) (iha j)
  | lam hpw _ _ iht ihb => intro j; exact .lam hpw (iht j) (ihb (j + 1))
  | forallE hpw _ _ iht ihb => intro j; exact .forallE hpw (iht j) (ihb (j + 1))
  | letE _ _ _ iht ihv ihb => intro j; exact .letE (iht j) (ihv j) (ihb (j + 1))
  | proj _ ihe => intro j; exact .proj (ihe j)

mutual

/-- Circuit-exact semantic counterpart of `Ix.Kernel.Semantics.WrapRel`, relaxing `.sort` and
`.const` levels to semantic equivalence (`LvEq` / `LvEqList`) as produced by `Tm` and
`KernelSubst::expr_inst_levels`. -/
inductive WrapRelSem (find? : KKey → Option (ConstantInfo .anon)) : KExpr → KExpr → Prop
  | bvar (i : Nat) : WrapRelSem find? (.bvar i) (.bvar i)
  | fvar {i : Nat} {t t' : KExpr} :
      WrapRelSem find? t t' → WrapRelSem find? (.fvar i t) (.fvar i t')
  | sort {u u' : KLevel} :
      LvEq u u' → WrapRelSem find? (.sort u) (.sort u')
  | const {n : KKey} {us us' : List KLevel} :
      LvEqList us us' → WrapRelSem find? (.const n us) (.const n us')
  | lit (l : Ix.Kernel.Literal) : WrapRelSem find? (.lit l) (.lit l)
  | app {f a f' a' : KExpr} :
      WrapRelSem find? f f' → WrapRelSem find? a a' →
      WrapRelSem find? (.app f a) (.app f' a')
  | lam {t b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → WrapDomSem find? t t' → WrapRelSem find? b b' →
      WrapRelSem find? (.lam t b m) (.lam t' b' m')
  | forallE {t b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → WrapDomSem find? t t' → WrapRelSem find? b b' →
      WrapRelSem find? (.forallE t b m) (.forallE t' b' m')
  | letE {t v b t' v' b' : KExpr} {l l' : Ix.Kernel.LetMeta} :
      WrapRelSem find? t t' → WrapRelSem find? v v' → WrapRelSem find? b b' →
      WrapRelSem find? (.letE t v b l) (.letE t' v' b' l')
  | proj {s : KKey} {i : Nat} {e e' : KExpr} :
      WrapRelSem find? e e' → WrapRelSem find? (.proj s i e) (.proj s i e')
  | zeta {g t v b : KExpr} {l : Ix.Kernel.LetMeta} :
      WrapRelSem find? g (b.instantiate1Lift v) → WrapRelSem find? g (.letE t v b l)

/-- Binder-domain counterpart of `Ix.Kernel.Semantics.WrapDom` over `WrapRelSem`. -/
inductive WrapDomSem (find? : KKey → Option (ConstantInfo .anon)) : KExpr → KExpr → Prop
  | keep {t t' : KExpr} : WrapRelSem find? t t' → WrapDomSem find? t t'
  | consume {t a t' : KExpr} :
      Ix.Kernel.Semantics.consumeWrapper find? t = some a →
      WrapDomSem find? a t' → WrapDomSem find? t t'

end

theorem ExprSemEq.toWrapRelSem (find? : KKey → Option (ConstantInfo .anon)) {e e' : KExpr}
    (h : ExprSemEq e e') : WrapRelSem find? e e' := by
  induction h with
  | bvar i => exact .bvar i
  | fvar _ iht => exact .fvar iht
  | sort hu => exact .sort hu
  | const hus => exact .const hus
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw _ _ iht ihb => exact .lam hpw (.keep iht) ihb
  | forallE hpw _ _ iht ihb => exact .forallE hpw (.keep iht) ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ihe => exact .proj ihe

theorem WrapRelSem.refl (find? : KKey → Option (ConstantInfo .anon)) (e : KExpr) :
    WrapRelSem find? e e :=
  (ExprSemEq.refl e).toWrapRelSem find?

mutual

theorem WrapRel.toWrapRelSem {find? : KKey → Option (ConstantInfo .anon)} :
    ∀ {g d : KExpr}, Ix.Kernel.Semantics.WrapRel find? g d → WrapRelSem find? g d
  | _, _, .bvar i => .bvar i
  | _, _, .fvar ht => .fvar (WrapRel.toWrapRelSem ht)
  | _, _, .sort u => .sort (LvEq.refl u)
  | _, _, .const _ us => .const (LvEqList.refl us)
  | _, _, .lit l => .lit l
  | _, _, .app hf ha => .app (WrapRel.toWrapRelSem hf) (WrapRel.toWrapRelSem ha)
  | _, _, .lam hpw hd hb => .lam hpw (WrapDom.toWrapDomSem hd) (WrapRel.toWrapRelSem hb)
  | _, _, .forallE hpw hd hb => .forallE hpw (WrapDom.toWrapDomSem hd) (WrapRel.toWrapRelSem hb)
  | _, _, .letE ht hv hb =>
    .letE (WrapRel.toWrapRelSem ht) (WrapRel.toWrapRelSem hv) (WrapRel.toWrapRelSem hb)
  | _, _, .proj he => .proj (WrapRel.toWrapRelSem he)
  | _, _, .zeta hz => .zeta (WrapRel.toWrapRelSem hz)

theorem WrapDom.toWrapDomSem {find? : KKey → Option (ConstantInfo .anon)} :
    ∀ {t t' : KExpr}, Ix.Kernel.Semantics.WrapDom find? t t' → WrapDomSem find? t t'
  | _, _, .keep hr => .keep (WrapRel.toWrapRelSem hr)
  | _, _, .consume hc hd => .consume hc (WrapDom.toWrapDomSem hd)

end

/-! ## `kexpr_struct_eq` on `Tm` (semantic level equivalence) -/

local macro "native_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

private theorem klimbs_eq_one_tm :
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
        exact ih _ _ _ _ _ _ (by native_lt_calls) ev154 rfl rfl xs ys x_ra x_rb rfl hxs hys
      · exact absurd (Value.field.inj he177) one_ne_zero)

private theorem bytestream_eq_one_tm :
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
        exact ih _ _ _ _ _ _ (by native_lt_calls) ev159 rfl rfl xs' ys' x_ra x_rb rfl hxs hys
      · exact absurd (Value.field.inj he181) one_ne_zero)

private theorem kexpr_struct_eq_tm_aux {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → r = .field 1 →
      ((fname = "KernelCheck::kexpr_struct_eq" →
        ∀ (k : Nat) (Ea Eb : KExpr) (pa pb : SourceValue F),
          args = [pa, pb] → Tm κ d Γ h k Ea pa → Tm κ d Γ h k Eb pb → ExprSemEq Ea Eb) ∧
       (fname = "KernelCheck::kexpr_binder_struct_eq" →
        ∀ (k : Nat) (Ta Ba Tb Bb : KExpr) (ℓa ℓb : KLevel)
          (pta pba pla ptb pbb plb : SourceValue F),
          args = [pta, pba, pla, ptb, pbb, plb] →
          Tm κ d Γ h k Ta pta → Tm κ d Γ h (k + 1) Ba pba → RepKLevel h ℓa pla →
          Tm κ d Γ h k Tb ptb → Tm κ d Γ h (k + 1) Bb pbb → RepKLevel h ℓb plb →
          ExprSemEq Ta Tb ∧ ExprSemEq Ba Bb ∧ (bmeta ℓa).pw = (bmeta ℓb).pw)) :=
  ObsFn.strong_induction (world := W)
    (fun fname args h r h' cs => r = .field 1 →
      ((fname = "KernelCheck::kexpr_struct_eq" →
        ∀ (k : Nat) (Ea Eb : KExpr) (pa pb : SourceValue F),
          args = [pa, pb] → Tm κ d Γ h k Ea pa → Tm κ d Γ h k Eb pb → ExprSemEq Ea Eb) ∧
       (fname = "KernelCheck::kexpr_binder_struct_eq" →
        ∀ (k : Nat) (Ta Ba Tb Bb : KExpr) (ℓa ℓb : KLevel)
          (pta pba pla ptb pbb plb : SourceValue F),
          args = [pta, pba, pla, ptb, pbb, plb] →
          Tm κ d Γ h k Ta pta → Tm κ d Γ h (k + 1) Ba pba → RepKLevel h ℓa pla →
          Tm κ d Γ h k Tb ptb → Tm κ d Γ h (k + 1) Bb pbb → RepKLevel h ℓb plb →
          ExprSemEq Ta Tb ∧ ExprSemEq Ba Bb ∧ (bmeta ℓa).pw = (bmeta ℓb).pw)))
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
            · exact .bvar _
            · omega
          · rcases hbb_c with ⟨hlt, _⟩ | ⟨_, _, rfl⟩
            · omega
            · exact .fvar (ExprSemEq.refl _)
        · exact absurd (Value.field.inj he79) one_ne_zero
        · exact absurd (Value.field.inj he86) one_ne_zero
        · obtain ⟨ua, rfl, la, hla, hua⟩ := ha.sort_of_load ld12
          obtain ⟨ub, rfl, lb, hlb, hub⟩ := hb.sort_of_load ld112
          obtain ⟨hlv, _⟩ := KernelLevels.levelStructEq_refines hla hlb ev130.erase
          have hlab : la = lb := by
            by_cases hbeq : (la == lb) = true
            · exact beq_iff_eq.mp hbeq
            · simp [hbeq] at hlv
          subst hlab
          exact .sort (hua.trans hub.symm)
        · exact absurd (Value.field.inj he152) one_ne_zero
        · obtain ⟨aa, usa, rfl, hra, lsa, hrlsa, husa⟩ := ha.const_of_load ld12
          obtain ⟨ab, usb, rfl, hrb, lsb, hrlsb, husb⟩ := hb.const_of_load ld183
          obtain ⟨haddr, rfl⟩ := Lib.address_eq_spec ev215 hra hrb
          have haeq : aa = ab := by
            by_cases hab : aa = ab
            · exact hab
            · rw [ite_eq_right hab] at haddr
              exact absurd (Value.field.inj haddr) one_ne_zero
          subst haeq
          obtain ⟨hlseq, _⟩ := level_list_struct_eq_one hrlsa hrlsb ev241
          subst hlseq
          exact .const (LvEqList.trans husa (LvEqList.symm husb))
        · exact absurd (Value.field.inj he263) one_ne_zero
        · exact absurd (Value.field.inj he270) one_ne_zero
        · obtain ⟨Efa, Eaa, rfl, hfa, haa⟩ := ha.app_of_load ld12
          obtain ⟨Efb, Eab, rfl, hfb, hab⟩ := hb.app_of_load ld301
          subst hc376
          have e1 := ObsFn.heap_extends ev333
          exact .app
            ((ih _ _ _ _ _ _ (by native_lt_calls) ev333 rfl).1 rfl k Efa Efb x_fa x_fb rfl hfa hfb)
            ((ih _ _ _ _ _ _ (by native_lt_calls) ev359 rfl).1 rfl k Eaa Eab x_aa x_ab rfl
              (haa.mono e1) (hab.mono e1))
        · exact absurd (Value.field.inj he381) one_ne_zero
        · exact absurd (Value.field.inj he388) one_ne_zero
        · obtain ⟨Ta, Ba, ℓa, rfl, hta, hba, hla⟩ := ha.lam_of_load ld12
          obtain ⟨Tb, Bb, ℓb, rfl, htb, hbb, hlb⟩ := hb.lam_of_load ld424
          subst hc501
          obtain ⟨ht, hb', hpw⟩ := (ih _ _ _ _ _ _ (by native_lt_calls) ev452 rfl).2 rfl k
            Ta Ba Tb Bb ℓa ℓb x_ta x_ba x_la x_tb x_bb x_lb rfl hta hba hla htb hbb hlb
          exact .lam hpw ht hb'
        · exact absurd (Value.field.inj he506) one_ne_zero
        · obtain ⟨Ta, Ba, ℓa, rfl, hta, hba, hla⟩ := ha.forallE_of_load ld12
          obtain ⟨Tb, Bb, ℓb, rfl, htb, hbb, hlb⟩ := hb.forallE_of_load ld542
          subst hc619
          obtain ⟨ht, hb', hpw⟩ := (ih _ _ _ _ _ _ (by native_lt_calls) ev570 rfl).2 rfl k
            Ta Ba Tb Bb ℓa ℓb x_da x_xa x_la x_db x_xb x_lb rfl hta hba hla htb hbb hlb
          exact .forallE hpw ht hb'
        · exact absurd (Value.field.inj he624) one_ne_zero
        · obtain ⟨Ta, Va, Ba, rfl, _, hva, hba⟩ := ha.letE_of_load ld12
          obtain ⟨Tb, Vb, Bb, rfl, _, hvb, hbb⟩ := hb.letE_of_load ld660
          subst hc775
          have e1 := ObsFn.heap_extends ev697
          have e2 := ObsFn.heap_extends ev732
          have hveq := (ih _ _ _ _ _ _ (by native_lt_calls) ev732 rfl).1 rfl k Va Vb x_va x_vb rfl
            (hva.mono e1) (hvb.mono e1)
          have hbeq := (ih _ _ _ _ _ _ (by native_lt_calls) ev758 rfl).1 rfl (k + 1) Ba Bb x_ba x_bb
            rfl (hba.mono (e1.trans e2)) (hbb.mono (e1.trans e2))
          exact hveq.instantiate1Lift hbeq 0
        · exact absurd (Value.field.inj he780) one_ne_zero
        · exact absurd (Value.field.inj he787) one_ne_zero
        · exact absurd (Value.field.inj he794) one_ne_zero
        · subst hc855
          rcases Obs.«KernelLevels::literal_eq».obs ev838 with
            ⟨x_na, x_nb, cs46, hv15, hv36, ev48, _⟩ |
            ⟨_, _, _, he70, _, _⟩ |
            ⟨x_sa, x_sb, cs109, _, hv78, hv99, ev111, _⟩ |
            ⟨_, _, _, _, he133, _, _⟩
          · rcases ha.lit_of_load ld12 with ⟨lp_a, limbs_a, hva, rla, _, rfl⟩ | ⟨_, _, _, hva, _, _, _⟩
            · rw [hv15] at hva; injection hva with _ _ hxs; injection hxs with hxa; subst hxa
              rcases hb.lit_of_load ld820 with ⟨lp_b, limbs_b, hvb, rlb, _, rfl⟩ | ⟨_, _, _, hvb, _, _, _⟩
              · rw [hv36] at hvb; injection hvb with _ _ hys; injection hys with hxb; subst hxb
                rw [klimbs_eq_one_tm _ _ _ _ _ _ ev48 rfl rfl limbs_a limbs_b x_na x_nb rfl rla rlb]
                exact .lit _
              · rw [hv36] at hvb; injection hvb with _ hc; exact absurd hc (by decide)
            · rw [hv15] at hva; injection hva with _ hc; exact absurd hc (by decide)
          · exact absurd (Value.field.inj he70) one_ne_zero
          · rcases ha.lit_of_load ld12 with ⟨_, _, hva, _, _, _⟩ | ⟨bp_a, bytes_a, sa, hva, rba, hsa, rfl⟩
            · rw [hv78] at hva; injection hva with _ hc; exact absurd hc (by decide)
            · rw [hv78] at hva; injection hva with _ _ hxs; injection hxs with hxa; subst hxa
              rcases hb.lit_of_load ld820 with ⟨_, _, hvb, _, _, _⟩ | ⟨bp_b, bytes_b, sb, hvb, rbb, hsb, rfl⟩
              · rw [hv99] at hvb; injection hvb with _ hc; exact absurd hc (by decide)
              · rw [hv99] at hvb; injection hvb with _ _ hys; injection hys with hxb; subst hxb
                have hbytes := bytestream_eq_one_tm _ _ _ _ _ _ ev111 rfl rfl bytes_a bytes_b x_sa x_sb
                  rfl rba rbb
                subst hbytes
                rw [Option.some.inj (hsa.symm.trans hsb)]
                exact .lit _
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
          exact .proj
            ((ih _ _ _ _ _ _ (by native_lt_calls) ev982 rfl).1 rfl k Ea₁ Eb₁ x_ea x_eb rfl hEa₁ hEb₁)
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
          have hteq := (ih _ _ _ _ _ _ (by native_lt_calls) ev50 rfl).1 rfl k Ta Tb pta ptb rfl
            (hta.mono e1) (htb.mono e1)
          have hbeq := (ih _ _ _ _ _ _ (by native_lt_calls) ev76 rfl).1 rfl (k + 1) Ba Bb pba pbb rfl
            (hba.mono (e1.trans e2)) (hbb.mono (e1.trans e2))
          exact ⟨hteq, hbeq, hpw⟩
        · exact absurd (Value.field.inj he98) one_ne_zero
        · exact absurd (Value.field.inj he105) one_ne_zero)

/-- `KernelCheck::kexpr_struct_eq` returning `1` on two `Tm` heap terms certifies `ExprSemEq`. -/
theorem kexpr_struct_eq_tm_one {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {Ea Eb : KExpr} {pa pb : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : Tm κ d Γ h k Ea pa) (hb : Tm κ d Γ h k Eb pb)
    (ev : ObsFn W "KernelCheck::kexpr_struct_eq" [pa, pb] h (.field 1) h' cs) :
    ExprSemEq Ea Eb :=
  (kexpr_struct_eq_tm_aux _ _ _ _ _ _ ev rfl).1 rfl k Ea Eb pa pb rfl ha hb

/-! ## Shared `KernelCheck` telescope and parameter-level specs -/

theorem nat_eq_of_field_eq {a b : Nat} (ha : a < 549755813888) (hb : b < 549755813888)
    (heq : (.field (a : F) : SourceValue F) = .field (b : F)) : a = b := by
  have hf : (a : F) = (b : F) := Value.field.inj heq
  have hva : ((a : F)).val = a := ZMod.val_natCast_of_lt (Nat.lt_trans ha (by decide))
  have hvb : ((b : F)).val = b := ZMod.val_natCast_of_lt (Nat.lt_trans hb (by decide))
  have hv := congrArg ZMod.val hf
  omega

theorem succ_field_ne_zero {m : Nat} (hm : m + 1 < 549755813888) :
    (.field ((m + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
  intro h
  have h' : (.field ((m + 1 : Nat) : F) : SourceValue F) = .field ((0 : Nat) : F) := by
    simpa using h
  have := nat_eq_of_field_eq hm (by decide) h'
  omega

theorem evalBinOp_sub_succ (m : Nat) {v : SourceValue F}
    (op : evalBinOp .sub (.field ((m + 1 : Nat) : F) : SourceValue F) (.field 1) = .ok v) :
    v = .field (m : F) := by
  simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
    Except.ok.injEq] at op
  rw [← op]
  congr 1
  simp [Nat.cast_add]

theorem evalBinOp_add_one (m : Nat) {v : SourceValue F}
    (op : evalBinOp .add (.field (m : F) : SourceValue F) (.field 1) = .ok v) :
    v = .field ((m + 1 : Nat) : F) := by
  simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
    Except.ok.injEq] at op
  rw [← op]
  congr 1
  simp [Nat.cast_add]

/-- `KernelCheck::peel_n_foralls` on a `TmExact` expression strips `n` leading `∀`-binders. -/
theorem peel_n_foralls_exact_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {E : KExpr} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 549755813888 →
      TmExact κ d Γ h k E pe →
      ObsFn W "KernelCheck::peel_n_foralls" [pe, .field (n : F)] h r h' cs →
      h' = h ∧ ∃ bs body,
        E.stripPis n = some (bs, body) ∧ bs.length = n ∧ TmExact κ d Γ h (k + n) body r
  | 0, k, E, pe, r, h, h', cs, _, hE, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨_, rfl, rfl, _⟩ | ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · exact ⟨rfl, [], E, rfl, rfl, by simpa using hE⟩
    · exact absurd rfl hne
  | m + 1, k, E, pe, r, h, h', cs, hlt, hE, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨hv, _, _, _⟩ | ⟨w42, x_body, w43, cs62, v66, _, ld34, op87, ev64, _⟩
    · exact absurd hv (succ_field_ne_zero hlt)
    · obtain ⟨T, B, ℓ, rfl, _, hb, _⟩ := hE.forallE_of_load ld34
      rw [evalBinOp_sub_succ m op87] at ev64
      obtain ⟨hh, bs, body, hstrip, hlen, hbody⟩ :=
        peel_n_foralls_exact_spec m (by omega) hb ev64
      refine ⟨hh, (T, bmeta ℓ) :: bs, body, ?_, by simp [hlen], ?_⟩
      · simp [Expr.stripPis, hstrip]
      · rw [show k + (m + 1) = k + 1 + m by omega]
        exact hbody

/-- `KernelCheck::peel_n_foralls` on a `Tm` expression strips `n` leading `∀`-binders. -/
theorem peel_n_foralls_tm_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {E : KExpr} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 549755813888 →
      Tm κ d Γ h k E pe →
      ObsFn W "KernelCheck::peel_n_foralls" [pe, .field (n : F)] h r h' cs →
      h' = h ∧ ∃ bs body,
        E.stripPis n = some (bs, body) ∧ bs.length = n ∧ Tm κ d Γ h (k + n) body r
  | 0, k, E, pe, r, h, h', cs, _, hE, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨_, rfl, rfl, _⟩ | ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · exact ⟨rfl, [], E, rfl, rfl, by simpa using hE⟩
    · exact absurd rfl hne
  | m + 1, k, E, pe, r, h, h', cs, hlt, hE, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨hv, _, _, _⟩ | ⟨w42, x_body, w43, cs62, v66, _, ld34, op87, ev64, _⟩
    · exact absurd hv (succ_field_ne_zero hlt)
    · obtain ⟨T, B, ℓ, rfl, _, hb, _⟩ := hE.forallE_of_load ld34
      rw [evalBinOp_sub_succ m op87] at ev64
      obtain ⟨hh, bs, body, hstrip, hlen, hbody⟩ :=
        peel_n_foralls_tm_spec m (by omega) hb ev64
      refine ⟨hh, (T, bmeta ℓ) :: bs, body, ?_, by simp [hlen], ?_⟩
      · simp [Expr.stripPis, hstrip]
      · rw [show k + (m + 1) = k + 1 + m by omega]
        exact hbody

/-- `KernelCheck::assert_lvls_are_params` on a `RepKLevelList` certifies that `us` is the parameter
list `[.param idx, …, .param (idx + count - 1)]`. -/
theorem assert_lvls_are_params_spec :
    ∀ (count idx : Nat) {us : List KLevel} {plvls r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      count + idx < 4294967296 →
      IxVM.Consistency.Bounded cs →
      RepKLevelList h us plvls →
      ObsFn W "KernelCheck::assert_lvls_are_params"
        [plvls, .field (count : F), .field (idx : F)] h r h' cs →
      us = (List.range count).map (fun i => Level.param (idx + i)) ∧ h' = h
  | 0, idx, us, plvls, r, h, h', cs, _, hbnd, hus, ev => by
    rcases Obs.«KernelCheck::assert_lvls_are_params».obs ev with
      ⟨v26, m29, cs37, _, ev39, heq54, _, rfl, hc59⟩ | ⟨_, _, _, _, _, _, _, _, hne, _, _, _, _, _, _, _, _, _⟩
    · subst hc59
      have hlen_lt : us.length < 549755813888 :=
        RomBound.bounded_length_lt hbnd List.mem_cons_self List.mem_cons_self hus
      obtain ⟨hv26, rfl⟩ := klevel_length ev39 hus
      rw [hv26] at heq54
      have heq54' : (.field (us.length : F) : SourceValue F) = .field ((0 : Nat) : F) := heq54
      have hlen0 := nat_eq_of_field_eq hlen_lt (by decide) heq54'
      exact ⟨List.eq_nil_of_length_eq_zero hlen0, rfl⟩
    · exact absurd rfl hne
  | m + 1, idx, us, plvls, r, h, h', cs, hlt, hbnd, hus, ev => by
    rcases Obs.«KernelCheck::assert_lvls_are_params».obs ev with
      ⟨_, _, _, hv, _, _, _, _, _⟩ |
      ⟨x_l, x_rest, x_i, v145, m146, cs156, v160, v161, _, ld75, ld104, heq144, op182, op197,
        ev158, _, rfl, hc203⟩
    · exact absurd hv (succ_field_ne_zero (by omega))
    · subst hc203
      have ld75' : loadValue h plvls =
          .ok (.construct KernelLevels.klevelListEnum "Cons" [x_l, x_rest]) := by
        rwa [Levels.klevelList_names]
      obtain ⟨u, rest, rfl, hu, hrest⟩ := RepList.cons_of_load hus ld75'
      obtain ⟨p, rfl, hx_i, hp⟩ := Levels.rep_param_of_load' hu ld104
      rw [hx_i] at heq144
      have hp_lt : p < 549755813888 := Nat.lt_trans hp (by decide)
      have hp_eq : p = idx := nat_eq_of_field_eq hp_lt (by omega) heq144
      subst hp_eq
      rw [evalBinOp_sub_succ m op182, evalBinOp_add_one p op197] at ev158
      have hbnd' := RomBound.bounded_mono hbnd (fun c hc => List.mem_cons_of_mem _ hc)
      obtain ⟨htl, hh⟩ := assert_lvls_are_params_spec m (p + 1) (by omega) hbnd' hrest ev158
      refine ⟨?_, hh⟩
      rw [htl, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Nat.add_zero, Function.comp_def]
      congr 1
      congr 1
      funext i
      congr 1
      exact Nat.add_right_comm p 1 i

end IxVM.Refinement.Decl
