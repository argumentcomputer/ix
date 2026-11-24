import IxVMRefinement.FamilyAlias.ProjFacts
import IxVMRefinement.FamilyAlias.Assembly
import IxVMRefinement.FamilyAlias.Clause
import IxVMRefinement.Decl.NativeEnv
import IxVMRefinement.Infer.Close
import IxCK.Kernel.Model.DeclIndRen
import IxCK.Kernel.Model.IndMembers
import IxCK.Kernel.Model.IndEtaLaw
import IxCK.Kernel.Model.IndUnitLaw
import IxCK.Kernel.Model.Inductives.TowerCons
import IxCK.Kernel.Model.StoreArNative
import IxCK.Kernel.Semantics.Inductives.DeclNativeRecLateSplitJ
import IxCK.Kernel.Rules.Inversion
import IxCK.Kernel.Verify.PropWhen
import IxCK.Kernel.Verify.Inductives.StructBody
import IxCK.Kernel.Verify.InstLevels

/-! # Preparation for modeled projection-table installation

Pure definitions and structural lemmas consumed by `FamilyAlias/ProjTableInstall.lean`:

* **Pure projection constants** (`chainAxiom`, `memberProjConsts`): for each eligible
  1-constructor, 0-index, never-zero-sort member of a modeled block, its `nF` chain-graph axioms
  at `projChainKey T j` and its `.projInfo` table at `projTableName T` (`off := 2`).
* **Body existence and well-formedness** (`structProjBodies_exists_wf`, `ctorTeleOk_of_stripPis_ret`).
* **Type & constructor binder zero-ness** (`tyA_T_constsResolve_env`, `tyA_T_renameConsts_eq`,
  `type_binders_pw_never`, `ctor_binders_pw_never`).
* **No-projection-slot bookkeeping** (`noProjEnv_famStep`, `noProjAt_structProjBodies_ne`,
  `noProjIn_of_noProjAt_list`).
* **Leaf alignment across the family step** (`ModelExt.acval_eq_of_isSome`,
  `envModelM_aliasGroup`, `declIndRenJ_acval`, `denoteMeta_famStep_eq_renameConsts`).
-/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open IxVM.Refinement.Core (KExpr KKey KLevel)
open IxVM.Refinement.Decl (ExprSemEq)
open Ix.Kernel (Env Expr Key Level LevelParam ConstantInfo ConstantVal RecRule IndCaps
  ProjTable ProjEntry BinderMeta PropWhen EnvExt EnvWF SetTheory auxKey projTableName projChainKey)
open Ix.Kernel.Semantics (AnnotTerm Judgements DeclIndRenRunJ IndMembersRunJ ProvisionRecsRunJ
  IndRecsFoldRenRunJ IotaRuleRenRunJ IotaRulesRenRunJ MemberValRunJ renameJ
  acvalWith acvalWith_ne acvalWith_self)
open Ix.Kernel.Verify (BlockInstalledTT)
open Ix.Kernel.Model (EnvModel EnvModelM ModelExt BlockAcvalInstalled
  NoProjEnv NoProjHead noProjEnv_of_fresh denoteMeta)
open IxVM.Refinement.Decl.FamilyAlias (AliasGroup AliasEnv famJ FamilyAdvice FamilyCheckFacts
  MemberFacts MembersFacts iotaKey)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000

/-! ## Section 1: Pure projection constants -/

/-- Chain-graph axiom installed at `projChainKey T j` for field `j` of a modeled structure `T`. -/
def chainAxiom (T : KKey) (j : Nat) : ConstantInfo .anon :=
  .axiomInfo ⟨projChainKey T j, [0], .sort (.succ (.param 0))⟩

/-- Constants installed for one eligible modeled structure table `tbl`: the projection table
consed on top of its `tbl.numFields` chain axioms (so the chain axioms are installed first). -/
def memberProjConsts (tbl : ProjTable .anon) : List (ConstantInfo .anon) :=
  .projInfo tbl :: ((List.range tbl.numFields).map (chainAxiom tbl.structName))

theorem chainAxiom_name (T : KKey) (j : Nat) :
    (chainAxiom T j).name = projChainKey T j := rfl

theorem projInfo_name (tbl : ProjTable .anon) :
    (ConstantInfo.projInfo tbl).name = projTableName tbl.structName := rfl

theorem projChainKey_ne_projTableName (T₁ T₂ : KKey) (j : Nat) :
    projChainKey T₁ j ≠ projTableName T₂ := by
  intro h; unfold projChainKey projTableName auxKey at h; cases h

theorem projChainKey_inj {T₁ T₂ : KKey} {j₁ j₂ : Nat}
    (h : projChainKey T₁ j₁ = projChainKey T₂ j₂) : T₁ = T₂ ∧ j₁ = j₂ := by
  unfold projChainKey projTableName auxKey at h
  injection h with h1 h2
  injection h1 with hT _
  injection h2 with hj
  exact ⟨hT, hj⟩

theorem projTableName_inj {T₁ T₂ : KKey} (h : projTableName T₁ = projTableName T₂) : T₁ = T₂ := by
  unfold projTableName auxKey at h; injection h

theorem projChainKey_ne_model (T k : KKey) (j : Nat) :
    projChainKey T j ≠ auxKey k .model := by
  intro h; unfold projChainKey projTableName auxKey at h; cases h

theorem projChainKey_ne_iota (T k : KKey) (j j' : Nat) :
    projChainKey T j ≠ iotaKey k j' := by
  intro h; unfold projChainKey projTableName iotaKey auxKey at h; cases h

theorem projTableName_ne_model (T k : KKey) :
    projTableName T ≠ auxKey k .model := by
  intro h; unfold projTableName auxKey at h; cases h

theorem projTableName_ne_iota (T k : KKey) (j : Nat) :
    projTableName T ≠ iotaKey k j := by
  intro h; unfold projTableName iotaKey auxKey at h; cases h

theorem projChainKey_not_reserved (T : KKey) (j : Nat) :
    Ix.Kernel.reservedBasisNames.contains (projChainKey T j) = false := by
  unfold projChainKey projTableName
  exact Ix.Kernel.reservedBasisNames_contains_auxKey _ _

theorem projTableName_not_reserved (T : KKey) :
    Ix.Kernel.reservedBasisNames.contains (projTableName T) = false := by
  unfold projTableName
  exact Ix.Kernel.reservedBasisNames_contains_auxKey _ _

theorem projChainKey_base {T : KKey} (hT : Decl.isBaseKey T = true) (j : Nat) :
    (projChainKey T j).base = T := by
  show (Key.aux (Key.aux T .projTable) (.projFn j)).base = T
  simp only [Key.base]
  exact Decl.base_of_isBaseKey hT

theorem projTableName_base {T : KKey} (hT : Decl.isBaseKey T = true) :
    (projTableName T).base = T := by
  show (Key.aux T .projTable).base = T
  simp only [Key.base]
  exact Decl.base_of_isBaseKey hT

theorem memberProjConsts_names_aux (tbl : ProjTable .anon) :
    ∀ c ∈ memberProjConsts tbl,
      (c = .projInfo tbl ∧ c.name = projTableName tbl.structName) ∨
      ∃ j < tbl.numFields, c = chainAxiom tbl.structName j ∧
        c.name = projChainKey tbl.structName j := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc'
  · exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc'
    exact Or.inr ⟨j, List.mem_range.mp hj, rfl, rfl⟩

theorem memberProjConsts_nodup (tbl : ProjTable .anon) :
    ((memberProjConsts tbl).map (·.name)).Nodup := by
  unfold memberProjConsts
  rw [List.map_cons, List.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro hin
    obtain ⟨c, hc, hname⟩ := List.mem_map.mp hin
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
    exact projChainKey_ne_projTableName _ _ _ hname
  · rw [List.map_map]
    exact List.Nodup.map (fun _ _ h => (projChainKey_inj h).2) List.nodup_range

theorem memberProjConsts_disjoint {tbl₁ tbl₂ : ProjTable .anon}
    (hne : tbl₁.structName ≠ tbl₂.structName) :
    ∀ c₁ ∈ memberProjConsts tbl₁, ∀ c₂ ∈ memberProjConsts tbl₂, c₁.name ≠ c₂.name := by
  intro c₁ hc₁ c₂ hc₂ heq
  rcases memberProjConsts_names_aux tbl₁ c₁ hc₁ with ⟨-, h1⟩ | ⟨j₁, -, -, h1⟩ <;>
    rcases memberProjConsts_names_aux tbl₂ c₂ hc₂ with ⟨-, h2⟩ | ⟨j₂, -, -, h2⟩ <;>
    rw [h1, h2] at heq
  · exact hne (projTableName_inj heq)
  · exact projChainKey_ne_projTableName _ _ _ heq.symm
  · exact projChainKey_ne_projTableName _ _ _ heq
  · exact hne (projChainKey_inj heq).1

/-! ## Section 2: `structProjBodies` existence, well-formedness, and `ctorTeleOk` -/

theorem hasFvar_liftLooseBVars (n : Nat) :
    ∀ (e : KExpr) (c : Nat), (Expr.liftLooseBVars n c e).hasFvar = e.hasFvar := by
  intro e
  induction e with
  | bvar _ => intro _; simp only [Expr.liftLooseBVars]; split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app _ _ ih1 ih2 => intro c; simp [Expr.liftLooseBVars, Expr.hasFvar, ih1, ih2]
  | lam _ _ _ ih1 ih2 => intro c; simp [Expr.liftLooseBVars, Expr.hasFvar, ih1, ih2]
  | forallE _ _ _ ih1 ih2 => intro c; simp [Expr.liftLooseBVars, Expr.hasFvar, ih1, ih2]
  | letE _ _ _ _ ih1 ih2 ih3 => intro c; simp [Expr.liftLooseBVars, Expr.hasFvar, ih1, ih2, ih3]
  | proj _ _ _ ih => intro c; simp [Expr.liftLooseBVars, Expr.hasFvar, ih]

theorem hasFvar_instantiate1Lift {v : KExpr} (hv : v.hasFvar = false) :
    ∀ (e : KExpr) (d : Nat), e.hasFvar = false → (e.instantiate1Lift v d).hasFvar = false := by
  intro e
  induction e with
  | bvar _ =>
    intro d _
    simp only [Expr.instantiate1Lift]
    split
    · rw [hasFvar_liftLooseBVars]; exact hv
    · split <;> rfl
  | fvar _ _ _ => intro _ h; exact nomatch h
  | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app _ _ ih1 ih2 =>
    intro d h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1Lift, Expr.hasFvar, ih1 d h.1, ih2 d h.2]
  | lam _ _ _ ih1 ih2 =>
    intro d h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1Lift, Expr.hasFvar, ih1 d h.1, ih2 (d + 1) h.2]
  | forallE _ _ _ ih1 ih2 =>
    intro d h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1Lift, Expr.hasFvar, ih1 d h.1, ih2 (d + 1) h.2]
  | letE _ _ _ _ ih1 ih2 ih3 =>
    intro d h; simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1Lift, Expr.hasFvar, ih1 d h.1.1, ih2 d h.1.2, ih3 (d + 1) h.2]
  | proj _ _ _ ih =>
    intro d h; simp [Expr.instantiate1Lift, Expr.hasFvar, ih d h]

theorem allLevelParamsDefined_liftLooseBVars (lps : List LevelParam) (n : Nat) :
    ∀ (e : KExpr) (c : Nat),
      (Expr.liftLooseBVars n c e).allLevelParamsDefined lps = e.allLevelParamsDefined lps := by
  intro e
  induction e with
  | bvar _ => intro _; simp only [Expr.liftLooseBVars]; split <;> rfl
  | lit _ => intro _; rfl
  | _ => intro c; simp_all [Expr.liftLooseBVars, Expr.allLevelParamsDefined]

theorem allLevelParamsDefined_instantiate1Lift {lps : List LevelParam} {v : KExpr}
    (hv : v.allLevelParamsDefined lps = true) :
    ∀ (e : KExpr) (d : Nat), e.allLevelParamsDefined lps = true →
      (e.instantiate1Lift v d).allLevelParamsDefined lps = true := by
  intro e
  induction e with
  | bvar _ =>
    intro d _
    simp only [Expr.instantiate1Lift]
    split
    · rw [allLevelParamsDefined_liftLooseBVars]; exact hv
    · split <;> rfl
  | lit _ => intro _ _; rfl
  | _ => intro d h; simp_all [Expr.instantiate1Lift, Expr.allLevelParamsDefined]

theorem looseBVarsBounded_liftLooseBVars (n : Nat) :
    ∀ (e : KExpr) (c k : Nat),
      e.looseBVarsBounded k = true →
      (Expr.liftLooseBVars n c e).looseBVarsBounded (k + n) = true := by
  intro e
  induction e with
  | bvar i =>
    intro c k h
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
    simp only [Expr.liftLooseBVars]
    split <;> simp only [Expr.looseBVarsBounded, decide_eq_true_eq] <;> omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _ _; rfl
  | app _ _ ih1 ih2 =>
    intro c k h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Expr.liftLooseBVars, Expr.looseBVarsBounded, ih1 c k h.1, ih2 c k h.2]
  | lam _ _ _ ih1 ih2 =>
    intro c k h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    have h2 := ih2 (c + 1) (k + 1) h.2
    rw [show k + 1 + n = k + n + 1 from by omega] at h2
    simp [Expr.liftLooseBVars, Expr.looseBVarsBounded, ih1 c k h.1, h2]
  | forallE _ _ _ ih1 ih2 =>
    intro c k h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    have h2 := ih2 (c + 1) (k + 1) h.2
    rw [show k + 1 + n = k + n + 1 from by omega] at h2
    simp [Expr.liftLooseBVars, Expr.looseBVarsBounded, ih1 c k h.1, h2]
  | letE _ _ _ _ ih1 ih2 ih3 =>
    intro c k h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    have h3 := ih3 (c + 1) (k + 1) h.2
    rw [show k + 1 + n = k + n + 1 from by omega] at h3
    simp [Expr.liftLooseBVars, Expr.looseBVarsBounded, ih1 c k h.1.1, ih2 c k h.1.2, h3]
  | proj _ _ _ ih =>
    intro c k h; simp [Expr.liftLooseBVars, Expr.looseBVarsBounded, ih c k h]

theorem looseBVarsBounded_instantiate1Lift {v : KExpr} {m : Nat}
    (hv : v.looseBVarsBounded m = true) :
    ∀ (e : KExpr) (d k : Nat), m + d ≤ k →
      e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1Lift v d).looseBVarsBounded k = true := by
  intro e
  induction e with
  | bvar i =>
    intro d k hmd h
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
    simp only [Expr.instantiate1Lift]
    split
    · exact Ix.Kernel.Expr.looseBVarsBounded_mono hmd
        (looseBVarsBounded_liftLooseBVars d v 0 m hv)
    · split <;> simp only [Expr.looseBVarsBounded, decide_eq_true_eq] <;> omega
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _ _ _; rfl
  | app _ _ ih1 ih2 =>
    intro d k hmd h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Expr.instantiate1Lift, Expr.looseBVarsBounded, ih1 d k hmd h.1, ih2 d k hmd h.2]
  | lam _ _ _ ih1 ih2 =>
    intro d k hmd h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Expr.instantiate1Lift, Expr.looseBVarsBounded, ih1 d k hmd h.1,
      ih2 (d + 1) (k + 1) (by omega) h.2]
  | forallE _ _ _ ih1 ih2 =>
    intro d k hmd h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Expr.instantiate1Lift, Expr.looseBVarsBounded, ih1 d k hmd h.1,
      ih2 (d + 1) (k + 1) (by omega) h.2]
  | letE _ _ _ _ ih1 ih2 ih3 =>
    intro d k hmd h; simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Expr.instantiate1Lift, Expr.looseBVarsBounded, ih1 d k hmd h.1.1,
      ih2 d k hmd h.1.2, ih3 (d + 1) (k + 1) (by omega) h.2]
  | proj _ _ _ ih =>
    intro d k hmd h; simp [Expr.instantiate1Lift, Expr.looseBVarsBounded, ih d k hmd h]

theorem stripPis_instantiate1Lift (v : KExpr) :
    ∀ (k d : Nat) (e : KExpr), (e.stripPis k).isSome = true →
      ((e.instantiate1Lift v d).stripPis k).isSome = true
  | 0, _, _, _ => rfl
  | k + 1, d, e, h => by
    cases e with
    | forallE dom body bm =>
      simp only [Expr.stripPis, Option.isSome_map] at h
      simp only [Expr.instantiate1Lift, Expr.stripPis, Option.isSome_map]
      exact stripPis_instantiate1Lift v k (d + 1) body h
    | _ => simp [Expr.stripPis] at h

theorem instPisAtLift_exists_wf {env : Env .anon} {lps : List LevelParam} {m : Nat} :
    ∀ (as : List KExpr) (n : Nat) (e : KExpr),
      (∀ a ∈ as, a.hasFvar = false ∧ a.allLevelParamsDefined lps = true ∧
        a.constsResolve env = true ∧ a.looseBVarsBounded m = true) →
      (e.stripPis (as.length + n)).isSome = true →
      e.hasFvar = false → e.allLevelParamsDefined lps = true →
      e.constsResolve env = true → e.looseBVarsBounded m = true →
      ∃ r : KExpr, Expr.instPisAtLift as e = some r ∧
        (r.stripPis n).isSome = true ∧
        r.hasFvar = false ∧ r.allLevelParamsDefined lps = true ∧
        r.constsResolve env = true ∧ r.looseBVarsBounded m = true
  | [], n, e, _, hs, hf, hp, hr, hb =>
    ⟨e, rfl, by simpa using hs, hf, hp, hr, hb⟩
  | a :: as, n, e, ha, hs, hf, hp, hr, hb => by
    cases e with
    | forallE dom body bm =>
      simp only [List.length_cons, Nat.succ_add, Expr.stripPis, Option.isSome_map] at hs
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hp
      simp only [Expr.constsResolve, Bool.and_eq_true] at hr
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      obtain ⟨haf, hap, har, hab⟩ := ha a List.mem_cons_self
      exact instPisAtLift_exists_wf as n (body.instantiate1Lift a 0)
        (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (stripPis_instantiate1Lift a (as.length + n) 0 body hs)
        (hasFvar_instantiate1Lift haf body 0 hf.2)
        (allLevelParamsDefined_instantiate1Lift hap body 0 hp.1.2)
        (Ix.Kernel.Semantics.constsResolve_instantiate1Lift har body 0 hr.2)
        (looseBVarsBounded_instantiate1Lift hab body 0 m (by omega) hb.2)
    | _ => simp [List.length_cons, Nat.succ_add, Expr.stripPis] at hs

theorem structProjBodiesGo_exists_wf {env : Env .anon} {T : KKey} {lps : List LevelParam}
    {m : Nat} (hm : 0 < m) (hT : (env.find? T).isSome = true) :
    ∀ (k i : Nat) (r : KExpr),
      (r.stripPis k).isSome = true →
      r.hasFvar = false → r.allLevelParamsDefined lps = true →
      r.constsResolve env = true → r.looseBVarsBounded m = true →
      ∃ bs : List KExpr, Ix.Kernel.structProjBodiesGo T k i r = some bs ∧
        bs.length = k ∧
        ∀ b ∈ bs, b.hasFvar = false ∧ b.allLevelParamsDefined lps = true ∧
          b.constsResolve env = true ∧ b.looseBVarsBounded m = true
  | 0, _, _, _, _, _, _, _ => ⟨[], rfl, rfl, fun _ h => nomatch h⟩
  | k + 1, i, r, hs, hf, hp, hr, hb => by
    cases r with
    | forallE dom body bm =>
      simp only [Expr.stripPis, Option.isSome_map] at hs
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hp
      simp only [Expr.constsResolve, Bool.and_eq_true] at hr
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      have harg_f : (Ix.Kernel.structProjArgP T i).hasFvar = false := rfl
      have harg_p : (Ix.Kernel.structProjArgP T i).allLevelParamsDefined lps = true := rfl
      have harg_r : (Ix.Kernel.structProjArgP T i).constsResolve env = true := by
        simp [Ix.Kernel.structProjArgP, Expr.constsResolve, hT]
      have harg_b : (Ix.Kernel.structProjArgP T i).looseBVarsBounded m = true := by
        simp [Ix.Kernel.structProjArgP, Expr.looseBVarsBounded, hm]
      obtain ⟨bs, hbs, hlen, hwf⟩ := structProjBodiesGo_exists_wf hm hT k (i + 1)
        (body.instantiate1Lift (Ix.Kernel.structProjArgP T i) 0)
        (stripPis_instantiate1Lift _ k 0 body hs)
        (hasFvar_instantiate1Lift harg_f body 0 hf.2)
        (allLevelParamsDefined_instantiate1Lift harg_p body 0 hp.1.2)
        (Ix.Kernel.Semantics.constsResolve_instantiate1Lift harg_r body 0 hr.2)
        (looseBVarsBounded_instantiate1Lift harg_b body 0 m (by omega) hb.2)
      refine ⟨dom :: bs, by simp [Ix.Kernel.structProjBodiesGo, hbs], by simp [hlen], ?_⟩
      intro b hb'
      rcases List.mem_cons.mp hb' with rfl | hb''
      · exact ⟨hf.1, hp.1.1, hr.1, hb.1⟩
      · exact hwf b hb''
    | _ => simp [Expr.stripPis] at hs

/-- **`structProjBodies` succeeds and preserves well-formedness** whenever `cty` has `nP + nF`
outer `∀` binders and satisfies `ConstWF` in an environment storing `T`. -/
theorem structProjBodies_exists_wf {env : Env .anon} {T : KKey} {lps : List LevelParam}
    {nP nF : Nat} {cty : KExpr}
    (hT : (env.find? T).isSome = true)
    (hstrip : (cty.stripPis (nP + nF)).isSome = true)
    (hf : cty.hasFvar = false) (hp : cty.allLevelParamsDefined lps = true)
    (hr : cty.constsResolve env = true) (hb : cty.looseBVarsBounded 0 = true) :
    ∃ bodies : Array KExpr,
      Ix.Kernel.structProjBodies T nP nF cty = some bodies ∧
      bodies.size = nF ∧
      ∀ (i : Nat) (b : KExpr), bodies[i]? = some b →
        b.hasFvar = false ∧ b.allLevelParamsDefined lps = true ∧
        b.constsResolve env = true ∧ b.looseBVarsBounded (nP + 1) = true := by
  have hlenP : (Ix.Kernel.structProjPs (md := .anon) nP).length = nP := by
    simp [Ix.Kernel.structProjPs]
  have hps_wf : ∀ a ∈ Ix.Kernel.structProjPs (md := .anon) nP,
      a.hasFvar = false ∧ a.allLevelParamsDefined lps = true ∧
      a.constsResolve env = true ∧ a.looseBVarsBounded (nP + 1) = true := by
    intro a ha
    simp only [Ix.Kernel.structProjPs, List.mem_map, List.mem_range] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    refine ⟨rfl, rfl, rfl, ?_⟩
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
    omega
  obtain ⟨r, hr_eq, hr_strip, hr_f, hr_p, hr_r, hr_b⟩ :=
    instPisAtLift_exists_wf (Ix.Kernel.structProjPs nP) nF cty hps_wf
      (by rw [hlenP]; exact hstrip) hf hp hr
      (Ix.Kernel.Expr.looseBVarsBounded_mono (Nat.zero_le _) hb)
  obtain ⟨bs, hbs, hlen, hwf⟩ :=
    structProjBodiesGo_exists_wf (m := nP + 1) (Nat.succ_pos _) hT nF 0 r
      hr_strip hr_f hr_p hr_r hr_b
  refine ⟨bs.toArray, ?_, by simp [hlen], ?_⟩
  · unfold Ix.Kernel.structProjBodies
    simp [hr_eq, hbs]
  · intro i b hbi
    have hmem : b ∈ bs := by
      have : bs[i]? = some b := by simpa using hbi
      exact List.mem_of_getElem? this
    exact hwf b hmem

theorem getAppFn_mkAppN (f : KExpr) :
    ∀ (args : List KExpr), (Expr.mkAppN f args).getAppFn = f.getAppFn
  | [] => rfl
  | a :: as => by
    simp only [Expr.mkAppN]
    rw [getAppFn_mkAppN (.app f a) as]
    rfl

/-- `ctorTeleOk` from `stripPis (nP + nF)` ending in `mkAppN (.const T _) _`. -/
theorem ctorTeleOk_of_stripPis_ret {cty : KExpr} {nP nF : Nat}
    {bs : List (KExpr × BinderMeta)} {T : KKey} {us : List KLevel} {args : List KExpr}
    (hs : cty.stripPis (nP + nF) = some (bs, Expr.mkAppN (.const T us) args)) :
    Ix.Kernel.Expr.ctorTeleOk cty (nP + nF) = true :=
  Ix.Kernel.Expr.ctorTeleOk_of hs (by rw [getAppFn_mkAppN]; rfl)

/-! ## Section 3: Type and constructor binder zero-ness -/

theorem posOf_range_eq_prep (n : Nat) (e : KExpr) :
    Core.posOf (List.range n) e = e := by
  unfold Core.posOf Core.posLevels
  rw [List.length_range]
  exact Ix.Kernel.Expr.instantiateLevelParams_self (List.range n) e

theorem exprSemEq_constsResolve (env : Env .anon) :
    ∀ {e₁ e₂ : KExpr}, ExprSemEq e₁ e₂ → e₁.constsResolve env = e₂.constsResolve env := by
  intro e₁ e₂ h
  induction h with
  | bvar | sort | lit => rfl
  | fvar _ ih => exact ih
  | const => rfl
  | app _ _ ih1 ih2 => simp [Expr.constsResolve, ih1, ih2]
  | lam _ _ _ ih1 ih2 => simp [Expr.constsResolve, ih1, ih2]
  | forallE _ _ _ ih1 ih2 => simp [Expr.constsResolve, ih1, ih2]
  | letE _ _ _ ih1 ih2 ih3 => simp [Expr.constsResolve, ih1, ih2, ih3]
  | proj _ ih => simp [Expr.constsResolve, ih]

theorem stripPis_constsResolve (env : Env .anon) :
    ∀ (k : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripPis k = some (bs, rem) →
      (e.constsResolve env = true ↔
        (∀ bm ∈ bs, bm.1.constsResolve env = true) ∧ rem.constsResolve env = true)
  | 0, e, rem, bs, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | k + 1, e, rem, bs, h => by
    cases e with
    | forallE dom body bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', rem'⟩, hs, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (dom, bm) :: bs' = bs ∧ rem' = rem := by cases heq; exact ⟨rfl, rfl⟩
      have ih := stripPis_constsResolve env k hs
      simp only [Expr.constsResolve, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, ih]
      tauto
    | _ => simp [Expr.stripPis] at h

theorem renameConsts_eq_of_constsResolve {env : Env .anon} {g : KKey → KKey}
    (hg : ∀ k, (env.find? k).isSome = true → g k = k) :
    ∀ {e : KExpr}, e.constsResolve env = true → e.renameConsts g = e := by
  intro e
  induction e with
  | bvar _ | sort _ | lit _ => intro _; rfl
  | const n us =>
    intro h
    simp only [Expr.constsResolve] at h
    simp [Expr.renameConsts, hg n h]
  | fvar i ty ih =>
    intro h; simp only [Expr.constsResolve] at h
    simp [Expr.renameConsts, ih h]
  | app _ _ ih1 ih2 =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp [Expr.renameConsts, ih1 h.1, ih2 h.2]
  | lam _ _ _ ih1 ih2 =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp [Expr.renameConsts, ih1 h.1, ih2 h.2]
  | forallE _ _ _ ih1 ih2 =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp [Expr.renameConsts, ih1 h.1, ih2 h.2]
  | letE _ _ _ _ ih1 ih2 ih3 =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp [Expr.renameConsts, ih1 h.1.1, ih2 h.1.2, ih3 h.2]
  | proj _ _ _ ih =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp [Expr.renameConsts, ih h.2]

theorem constsResolve_instantiateLevelParams (env : Env .anon) (ks : List LevelParam)
    (us : List KLevel) :
    ∀ (e : KExpr), (e.instantiateLevelParams ks us).constsResolve env = e.constsResolve env := by
  intro e
  induction e <;> simp_all [Expr.instantiateLevelParams, Expr.constsResolve]

/-- From a field's `FieldProjFacts` (whose `cvProj` is stored in `env`), `tyA_T` resolves in `env`
and is therefore fixed by `g`. -/
theorem tyA_T_constsResolve_env {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {tModelKey cModelKey : KKey} {tyA_T ctyMPos fdom rawDom : KExpr}
    {nP bnl nF fidx : Nat} {bsT : List (KExpr × BinderMeta)} {structSort : KLevel}
    (hwf : EnvWF env)
    (hT_sort : tyA_T.stripPis nP = some (bsT, .sort structSort))
    (fp : FieldProjFacts t E env tModelKey cModelKey
      (Core.posOf (List.range bnl) tyA_T) ctyMPos nP bnl nF fidx fdom rawDom) :
    tyA_T.constsResolve env = true := by
  have hT_pos : Core.posOf (List.range bnl) tyA_T = tyA_T := posOf_range_eq_prep bnl tyA_T
  rw [hT_pos] at fp
  have hproj_res : (Core.posOf fp.cvProj.levelParams fp.cvProj.type).constsResolve env = true := by
    unfold Core.posOf
    rw [constsResolve_instantiateLevelParams]
    exact (hwf _ (Ix.Kernel.Semantics.Env.find?_mem fp.hfindProj)).2.2.1
  have hpbs_res : ∀ bm ∈ fp.pbsP, bm.1.constsResolve env = true :=
    ((stripPis_constsResolve env nP fp.hProj_strip).mp hproj_res).1
  have hbsT_eq : fp.tbsP = bsT := by
    have h := fp.hT_strip.symm.trans hT_sort
    exact (Prod.mk.inj (Option.some.inj h)).1
  have htbs_res : ∀ bm ∈ bsT, bm.1.constsResolve env = true := by
    rw [← hbsT_eq]
    have hgo : ∀ (l₁ l₂ : List (KExpr × BinderMeta)),
        List.Forall₂ ExprSemEq (l₁.map Prod.fst) (l₂.map Prod.fst) →
        (∀ x ∈ l₁, x.1.constsResolve env = true) →
        ∀ y ∈ l₂, y.1.constsResolve env = true := by
      intro l₁
      induction l₁ with
      | nil =>
        intro l₂ h _ y hy
        cases l₂ with
        | nil => exact nomatch hy
        | cons _ _ => exact nomatch h
      | cons a l₁ ih =>
        intro l₂ h h1 y hy
        cases l₂ with
        | nil => exact nomatch h
        | cons b l₂ =>
          cases h with
          | cons hab htl =>
            rcases List.mem_cons.mp hy with rfl | hy'
            · rw [← exprSemEq_constsResolve env hab]
              exact h1 a List.mem_cons_self
            · exact ih l₂ htl (fun x hx => h1 x (List.mem_cons_of_mem _ hx)) y hy'
    exact hgo fp.pbsP fp.tbsP fp.hProj_pdoms hpbs_res
  exact (stripPis_constsResolve env nP hT_sort).mpr ⟨htbs_res, rfl⟩

theorem tyA_T_renameConsts_eq {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Env .anon}
    {g : KKey → KKey} {tModelKey cModelKey : KKey} {tyA_T ctyMPos fdom rawDom : KExpr}
    {nP bnl nF fidx : Nat} {bsT : List (KExpr × BinderMeta)} {structSort : KLevel}
    (hwf : EnvWF env) (hg : ∀ k, (env.find? k).isSome = true → g k = k)
    (hT_sort : tyA_T.stripPis nP = some (bsT, .sort structSort))
    (fp : FieldProjFacts t E env tModelKey cModelKey
      (Core.posOf (List.range bnl) tyA_T) ctyMPos nP bnl nF fidx fdom rawDom) :
    tyA_T.renameConsts g = tyA_T :=
  renameConsts_eq_of_constsResolve hg (tyA_T_constsResolve_env hwf hT_sort fp)

theorem eval_pos_of_isNeverZero :
    ∀ {l : KLevel}, l.isNeverZero = true → ∀ φ, 0 < Level.eval φ l
  | .zero, h, _ => nomatch h
  | .param _, h, _ => nomatch h
  | .succ _, _, _ => Nat.succ_pos _
  | .max a b, h, φ => by
    simp only [Level.isNeverZero, Bool.or_eq_true] at h
    simp only [Level.eval]
    rcases h with ha | hb
    · exact Nat.lt_of_lt_of_le (eval_pos_of_isNeverZero ha φ) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (eval_pos_of_isNeverZero hb φ) (Nat.le_max_right _ _)
  | .imax a b, h, φ => by
    simp only [Level.isNeverZero] at h
    have hb := eval_pos_of_isNeverZero h φ
    simp only [Level.eval, Nat.ne_of_gt hb, ↓reduceIte]
    exact Nat.lt_of_lt_of_le hb (Nat.le_max_right _ _)

theorem zeronessOf_eq_never_of_pos {l : KLevel} (h : ∀ φ, 0 < Level.eval φ l) :
    Level.zeronessOf l = .never := by
  rw [Ix.Kernel.PropWhen.eq_iff_holds]
  intro φ
  rw [Ix.Kernel.PropWhen.zeronessOf_sound]
  have hne : Level.eval φ l ≠ 0 := Nat.ne_of_gt (h φ)
  simp [hne]

theorem substFn_getElem?_eq_aux (φ : LevelParam → Nat) :
    ∀ {ks : List LevelParam} {vs : List KLevel} {i : Nat} {p : LevelParam} {v : KLevel},
      ks.Nodup → ks[i]? = some p → vs[i]? = some v →
      Level.substFn φ ks vs p = Level.eval φ v
  | [], _, _, _, _, _, hk, _ => by simp at hk
  | k :: ks, [], _, _, _, _, _, hv => by simp at hv
  | k :: ks, v₀ :: vs, 0, p, v, _, hk, hv => by
    obtain rfl : k = p := by simpa using hk
    obtain rfl : v₀ = v := by simpa using hv
    simp [Level.substFn]
  | k :: ks, v₀ :: vs, i + 1, p, v, hnd, hk, hv => by
    rw [List.nodup_cons] at hnd
    have hp_mem : p ∈ ks := List.mem_of_getElem? (by simpa using hk)
    have hne : k ≠ p := fun e => hnd.1 (e ▸ hp_mem)
    simp only [Level.substFn, beq_iff_eq, hne, ↓reduceIte]
    exact substFn_getElem?_eq_aux φ hnd.2 (by simpa using hk) (by simpa using hv)

theorem substFn_of_not_mem_aux (φ : LevelParam → Nat) :
    ∀ {ks : List LevelParam} {vs : List KLevel} {p : LevelParam},
      p ∉ ks → Level.substFn φ ks vs p = φ p
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | k :: ks, _ :: vs, p, hp => by
    have hne : k ≠ p := fun e => hp (e ▸ List.mem_cons_self)
    have hp' : p ∉ ks := fun h => hp (List.mem_cons_of_mem _ h)
    simp only [Level.substFn, beq_iff_eq, hne, ↓reduceIte]
    exact substFn_of_not_mem_aux φ hp'

/-- `Level.substFn` along a permutation of `List.range n` is surjective on valuations. -/
theorem substFn_perm_surj {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    (φ : LevelParam → Nat) :
    ∃ φ₀ : LevelParam → Nat,
      Level.substFn φ₀ ps (Core.posLevels ps) = φ := by
  have hnd : ps.Nodup := hperm.nodup_iff.mpr List.nodup_range
  refine ⟨Level.substFn φ (List.range ps.length) (ps.map .param), ?_⟩
  funext p
  by_cases hp : p ∈ ps
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hp
    have hilt : i < ps.length := (List.getElem?_eq_some_iff.mp hi).1
    have hps_i : ps[i]'hilt = p := (List.getElem?_eq_some_iff.mp hi).2
    have h1 : Level.substFn (Level.substFn φ (List.range ps.length) (ps.map .param))
        ps (Core.posLevels ps) p =
        Level.eval (Level.substFn φ (List.range ps.length) (ps.map .param)) (.param i) := by
      have hidx : (Core.posLevels ps)[i]? = some (.param i) := by
        simp [Core.posLevels, hilt]
      exact substFn_getElem?_eq_aux _ hnd hi hidx
    rw [h1]
    simp only [Level.eval]
    have h2 : Level.substFn φ (List.range ps.length) (ps.map .param) i =
        Level.eval φ (.param p) := by
      have hr : (List.range ps.length)[i]? = some i := by simp [hilt]
      have hm : (ps.map Level.param)[i]? = some (.param p) := by
        simp [hilt, hps_i]
      exact substFn_getElem?_eq_aux _ List.nodup_range hr hm
    rw [h2]
    rfl
  · have h1 : Level.substFn (Level.substFn φ (List.range ps.length) (ps.map .param))
        ps (Core.posLevels ps) p =
        Level.substFn φ (List.range ps.length) (ps.map .param) p :=
      substFn_of_not_mem_aux _ hp
    have hp' : p ∉ List.range ps.length := fun h => hp (hperm.mem_iff.mpr h)
    rw [h1, substFn_of_not_mem_aux _ hp']

/-- `Level.substPW ps (posLevels ps) pw = .never` reflects to `pw = .never` for any permutation
`ps` of `List.range ps.length`. -/
theorem substPW_pos_eq_never_inv {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {pw : PropWhen} (h : Level.substPW ps (Core.posLevels ps) pw = .never) :
    pw = .never := by
  rw [Ix.Kernel.PropWhen.eq_iff_holds]
  intro φ
  obtain ⟨φ₀, hφ⟩ := substFn_perm_surj hperm φ
  have h1 := Ix.Kernel.Level.holds_substPW φ₀ ps (Core.posLevels ps) pw
  rw [h, hφ] at h1
  exact h1.symm

/-- `stripPis` commutes with `instantiateLevelParams`, mapping each binder's `pw` by `substPW`. -/
theorem stripPis_ilp_pw (ks : List LevelParam) (vs : List KLevel) :
    ∀ (k : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripPis k = some (bs, rem) →
      ∃ bs', (e.instantiateLevelParams ks vs).stripPis k =
          some (bs', rem.instantiateLevelParams ks vs) ∧
        bs'.map (·.2.pw) = bs.map (fun b => Level.substPW ks vs b.2.pw)
  | 0, e, rem, bs, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl⟩
  | k + 1, e, rem, bs, h => by
    cases e with
    | forallE dom body bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs₁, rem₁⟩, hs, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (dom, bm) :: bs₁ = bs ∧ rem₁ = rem := by cases heq; exact ⟨rfl, rfl⟩
      obtain ⟨bs', hs', hpw⟩ := stripPis_ilp_pw ks vs k hs
      refine ⟨(dom.instantiateLevelParams ks vs, { bm with pw := Level.substPW ks vs bm.pw }) :: bs',
        by simp [Expr.instantiateLevelParams, Expr.stripPis, hs'], by simp [hpw]⟩
    | _ => simp [Expr.stripPis] at h

theorem ilp_mkAppN (ks : List LevelParam) (vs : List KLevel) (f : KExpr) :
    ∀ (args : List KExpr),
      (Expr.mkAppN f args).instantiateLevelParams ks vs =
        Expr.mkAppN (f.instantiateLevelParams ks vs)
          (args.map fun a => a.instantiateLevelParams ks vs)
  | [] => rfl
  | a :: as => by
    simp only [Expr.mkAppN, List.map_cons]
    exact ilp_mkAppN ks vs (.app f a) as

/-- Any `∀`-telescope ending in `.sort u` that is `Infer`-typed has `pw = .never` on every binder. -/
theorem infer_stripPis_sort_pw_never {env : Env .anon} :
    ∀ (k d : Nat) {e t : KExpr} {bs : List (KExpr × BinderMeta)} {u : KLevel},
      e.stripPis k = some (bs, .sort u) →
      Ix.Kernel.Rules.Infer env .full d e t →
      (∀ bm ∈ bs, bm.2.pw = .never) ∧ ∃ v, t = .sort v ∧ ∀ φ, 0 < Level.eval φ v
  | 0, d, e, t, bs, u, hs, hinf => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have ht := Ix.Kernel.Rules.Infer.sort_inv hinf
    exact ⟨(fun _ h => nomatch h), ⟨.succ u, ht, fun _ => Nat.succ_pos _⟩⟩
  | k + 1, d, e, t, bs, u, hs, hinf => by
    cases e with
    | forallE dom body bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs', rem'⟩, hs', heq⟩ := hs
      obtain ⟨rfl, rfl⟩ : (dom, bm) :: bs' = bs ∧ rem' = .sort u := by
        cases heq; exact ⟨rfl, rfl⟩
      obtain ⟨s, u₁, bst, v, _, _, hinfB, hredB, hpw, ht⟩ :=
        Ix.Kernel.Rules.Infer.forallE_inv hinf
      obtain ⟨bs'', hs'', hpos⟩ :=
        Ix.Kernel.stripPis_instantiate1_full (v := .fvar d dom) k 0 hs'
      have hrem_eq : (Expr.sort u : KExpr).instantiate1 (.fvar d dom) (0 + k) = .sort u := rfl
      rw [hrem_eq] at hs''
      obtain ⟨hpw'', v', hv', hv'pos⟩ := infer_stripPis_sort_pw_never k (d + 1) hs'' hinfB
      rw [hv'] at hredB
      have hvv : v = v' := Ix.Kernel.Rules.Red.sort_eq hredB
      subst hvv
      have hbm_pw : bm.pw = .never := by
        rw [← hpw]
        exact zeronessOf_eq_never_of_pos hv'pos
      refine ⟨?_, ⟨.imax u₁ v, ht, fun φ => ?_⟩⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hbm_pw
        · obtain ⟨idx, hidx⟩ := List.getElem?_of_mem hx'
          exact hpw'' (x.1.instantiate1 (.fvar d dom) (0 + idx), x.2)
            (List.mem_of_getElem? (hpos idx x hidx))
      · simp only [Level.eval, Nat.ne_of_gt (hv'pos φ), ↓reduceIte]
        exact Nat.lt_of_lt_of_le (hv'pos φ) (Nat.le_max_right _ _)
    | _ => simp [Expr.stripPis] at hs

theorem exprLvEq_stripPis :
    ∀ (k : Nat) {e₁ e₂ rem₁ : KExpr} {bs₁ : List (KExpr × BinderMeta)},
      Core.ExprLvEq e₁ e₂ → e₁.stripPis k = some (bs₁, rem₁) →
      ∃ bs₂ rem₂, e₂.stripPis k = some (bs₂, rem₂) ∧ Core.ExprLvEq rem₁ rem₂
  | 0, e₁, e₂, rem₁, bs₁, heq, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨[], e₂, rfl, heq⟩
  | k + 1, e₁, e₂, rem₁, bs₁, heq, hs => by
    cases heq with
    | @forallE t₁ t₂ b₁ b₂ m hd hb =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs₁', rem₁'⟩, hs', hmk⟩ := hs
      obtain ⟨-, rfl⟩ := Prod.mk.inj hmk
      obtain ⟨bs₂', rem₂, hs₂, hrem⟩ := exprLvEq_stripPis k hb hs'
      exact ⟨(t₂, m) :: bs₂', rem₂, by simp [Expr.stripPis, hs₂], hrem⟩
    | _ => simp [Expr.stripPis] at hs

theorem mkAppN_append_singleton (f : KExpr) :
    ∀ (xs : List KExpr) (a : KExpr),
      Expr.mkAppN f (xs ++ [a]) = .app (Expr.mkAppN f xs) a
  | [], _ => rfl
  | x :: xs, a => mkAppN_append_singleton (.app f x) xs a

theorem infer_mkAppN_const_sort {env : Env .anon} {d nP : Nat} {cTM : KKey}
    {us : List KLevel} {cvTM : ConstantVal .anon} {mvalTM : KExpr}
    {hintTM : Ix.Kernel.ReducibilityHint} {bsTM : List (KExpr × BinderMeta)} {u : KLevel}
    (hfind : env.find? cTM = some (.defnInfo cvTM mvalTM hintTM))
    (hus : us.length = cvTM.levelParams.length)
    (hstrip : (cvTM.type.instantiateLevelParams cvTM.levelParams us).stripPis nP =
      some (bsTM, .sort u)) :
    ∀ (args : List KExpr) {t : KExpr},
      args.length ≤ nP →
      Ix.Kernel.Rules.Infer env .full d (Expr.mkAppN (.const cTM us) args) t →
      ∃ bs', t.stripPis (nP - args.length) = some (bs', .sort u) := by
  intro args
  induction args using List.reverseRecOn with
  | nil =>
    intro t _ hinf
    obtain ⟨ci, hf, -, -, rfl⟩ := Ix.Kernel.Rules.Infer.const_inv hinf
    rw [hfind] at hf
    obtain rfl := Option.some.inj hf
    exact ⟨bsTM, by simpa [ConstantInfo.toConstantVal] using hstrip⟩
  | append_singleton xs a ih =>
    intro t hle hinf
    rw [mkAppN_append_singleton] at hinf
    obtain ⟨tf, dom, body, mb, _, hinfF, hredF, _, _, rfl⟩ := Ix.Kernel.Rules.Infer.app_inv hinf
    have hlt : xs.length < nP := by simp at hle; omega
    obtain ⟨bs', hst⟩ := ih (Nat.le_of_lt hlt) hinfF
    have hrem : nP - xs.length = (nP - (xs.length + 1)) + 1 := by omega
    rw [hrem] at hst
    cases tf with
    | forallE dom₀ body₀ mb₀ =>
      have hEq : Expr.forallE dom body mb = Expr.forallE dom₀ body₀ mb₀ :=
        Ix.Kernel.Rules.Red.rigid hredF rfl
      obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj hEq
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs'', rem''⟩, hst', hpair⟩ := hst
      obtain ⟨-, rfl⟩ := Prod.mk.inj hpair
      obtain ⟨bs''', hst''', -⟩ := Ix.Kernel.stripPis_instantiate1_full (v := a) _ 0 hst'
      refine ⟨bs''', ?_⟩
      simpa [List.length_append] using hst'''
    | _ => simp [Expr.stripPis] at hst

theorem instantiate1_mkAppN (f : KExpr) (v : KExpr) (c : Nat) :
    ∀ (args : List KExpr),
      (Expr.mkAppN f args).instantiate1 v c =
        Expr.mkAppN (f.instantiate1 v c) (args.map fun a => a.instantiate1 v c)
  | [] => rfl
  | a :: as => by
    simp only [Expr.mkAppN, List.map_cons]
    exact instantiate1_mkAppN (.app f a) v c as

/-- Any `∀`-telescope ending in `mkAppN (.const cTM us) args` (with `args.length = nP`)
that is `Infer`-typed in `env` has `pw = .never` on every binder whenever `cTM`'s result sort is
strictly positive at every valuation. -/
theorem infer_stripPis_ctor_pw_never {env : Env .anon} {nP : Nat} {cTM : KKey}
    {us : List KLevel} {cvTM : ConstantVal .anon} {mvalTM : KExpr}
    {hintTM : Ix.Kernel.ReducibilityHint} {bsTM : List (KExpr × BinderMeta)} {u : KLevel}
    (hfind : env.find? cTM = some (.defnInfo cvTM mvalTM hintTM))
    (hus : us.length = cvTM.levelParams.length)
    (hstrip : (cvTM.type.instantiateLevelParams cvTM.levelParams us).stripPis nP =
      some (bsTM, .sort u))
    (hupos : ∀ φ, 0 < Level.eval φ u) :
    ∀ (k d : Nat) {e t : KExpr} {bs : List (KExpr × BinderMeta)} {args : List KExpr},
      args.length = nP →
      e.stripPis k = some (bs, Expr.mkAppN (.const cTM us) args) →
      Ix.Kernel.Rules.Infer env .full d e t →
      (∀ bm ∈ bs, bm.2.pw = .never) ∧ ∃ v, t = .sort v ∧ ∀ φ, 0 < Level.eval φ v
  | 0, d, e, t, bs, args, hlen, hs, hinf => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨bs', hst⟩ := infer_mkAppN_const_sort hfind hus hstrip args (by omega) hinf
    rw [hlen, Nat.sub_self] at hst
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    exact ⟨(fun _ h => nomatch h), ⟨u, hst.2, hupos⟩⟩
  | k + 1, d, e, t, bs, args, hlen, hs, hinf => by
    cases e with
    | forallE dom body bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs', rem'⟩, hs', heq⟩ := hs
      obtain ⟨rfl, rfl⟩ : (dom, bm) :: bs' = bs ∧ rem' = Expr.mkAppN (.const cTM us) args := by
        cases heq; exact ⟨rfl, rfl⟩
      obtain ⟨s, u₁, bst, v, _, _, hinfB, hredB, hpw, ht⟩ :=
        Ix.Kernel.Rules.Infer.forallE_inv hinf
      obtain ⟨bs'', hs'', hpos⟩ :=
        Ix.Kernel.stripPis_instantiate1_full (v := .fvar d dom) k 0 hs'
      rw [instantiate1_mkAppN] at hs''
      have hconst_eq : (Expr.const cTM us : KExpr).instantiate1 (.fvar d dom) (0 + k) =
          .const cTM us := rfl
      rw [hconst_eq] at hs''
      obtain ⟨hpw'', v', hv', hv'pos⟩ :=
        infer_stripPis_ctor_pw_never hfind hus hstrip hupos k (d + 1)
          (by simp [hlen]) hs'' hinfB
      rw [hv'] at hredB
      have hvv : v = v' := Ix.Kernel.Rules.Red.sort_eq hredB
      subst hvv
      have hbm_pw : bm.pw = .never := by
        rw [← hpw]
        exact zeronessOf_eq_never_of_pos hv'pos
      refine ⟨?_, ⟨.imax u₁ v, ht, fun φ => ?_⟩⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hbm_pw
        · obtain ⟨idx, hidx⟩ := List.getElem?_of_mem hx'
          exact hpw'' (x.1.instantiate1 (.fvar d dom) (0 + idx), x.2)
            (List.mem_of_getElem? (hpos idx x hidx))
      · simp only [Level.eval, Nat.ne_of_gt (hv'pos φ), ↓reduceIte]
        exact Nat.lt_of_lt_of_le (hv'pos φ) (Nat.le_max_right _ _)
    | _ => simp [Expr.stripPis] at hs

theorem stripPis_renameConsts (g : KKey → KKey) :
    ∀ (k : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripPis k = some (bs, rem) →
      (e.renameConsts g).stripPis k =
        some (bs.map fun p => (p.1.renameConsts g, p.2), rem.renameConsts g)
  | 0, e, rem, bs, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | k + 1, e, rem, bs, h => by
    cases e with
    | forallE dom body bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', rem'⟩, hs, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (dom, bm) :: bs' = bs ∧ rem' = rem := by cases heq; exact ⟨rfl, rfl⟩
      simp only [Expr.renameConsts, Expr.stripPis, stripPis_renameConsts g k hs, Option.map_some]
      rfl
    | _ => simp [Expr.stripPis] at h

theorem renameConsts_mkAppN (g : KKey → KKey) (f : KExpr) :
    ∀ (args : List KExpr),
      (Expr.mkAppN f args).renameConsts g =
        Expr.mkAppN (f.renameConsts g) (args.map (Expr.renameConsts g))
  | [] => rfl
  | a :: as => by
    simp only [Expr.mkAppN, List.map_cons]
    exact renameConsts_mkAppN g (.app f a) as

/-- Every binder of `tyA_T` carries `pw = .never` (from `MemberFacts.modelTyped`). -/
theorem type_binders_pw_never {env : Env .anon} {g : KKey → KKey} {ciT : ConstantInfo .anon}
    {tyA_T : KExpr} {nP : Nat} {bsT : List (KExpr × BinderMeta)} {structSort : KLevel}
    (hmfT : MemberFacts env g ciT tyA_T)
    (hrenT : tyA_T.renameConsts g = tyA_T)
    (hT_sort : tyA_T.stripPis nP = some (bsT, .sort structSort)) :
    ∀ bm ∈ bsT, bm.2.pw = .never := by
  obtain ⟨stype, u, ⟨ps, hperm, hinf⟩, -⟩ := hmfT.modelTyped
  rw [hrenT] at hinf
  obtain ⟨bs', hs', hpw_map⟩ := stripPis_ilp_pw ps (Core.posLevels ps) nP hT_sort
  obtain ⟨hpw', -⟩ := infer_stripPis_sort_pw_never nP 0 hs' hinf
  intro bm hbm
  have hmem : Level.substPW ps (Core.posLevels ps) bm.2.pw ∈ bs'.map (·.2.pw) := by
    rw [hpw_map]
    exact List.mem_map_of_mem (f := fun b : KExpr × BinderMeta =>
      Level.substPW ps (Core.posLevels ps) b.2.pw) hbm
  obtain ⟨bm', hbm', heq⟩ := List.mem_map.mp hmem
  exact substPW_pos_eq_never_inv hperm (heq.symm.trans (hpw' bm' hbm'))

/-- Every binder of `tyA_C` carries `pw = .never = Level.zeronessOf structSort` (from
`MemberFacts.modelTyped` on `ciC`, `MemberFacts.model` on `ciT`, and `structSort.isNeverZero`). -/
theorem ctor_binders_pw_never {env : Env .anon} {g : KKey → KKey}
    {ciT ciC : ConstantInfo .anon} {tyA_T tyA_C : KExpr}
    {nP bnl nF : Nat} {bsT bsC : List (KExpr × BinderMeta)} {structSort : KLevel}
    {args : List KExpr}
    (hwf : EnvWF env)
    (hmfT : MemberFacts env g ciT tyA_T)
    (hmfC : MemberFacts env g ciC tyA_C)
    (hlpsT : ciT.toConstantVal.levelParams = List.range bnl)
    (hrenT : tyA_T.renameConsts g = tyA_T)
    (hT_sort : tyA_T.stripPis nP = some (bsT, .sort structSort))
    (hT_sort_nz : structSort.isNeverZero = true)
    (hargs_len : args.length = nP)
    (hC_ret : tyA_C.stripPis (nP + nF) =
      some (bsC, Expr.mkAppN (.const ciT.name ((List.range bnl).map .param)) args)) :
    ∀ bm ∈ bsC, bm.2.pw = Level.zeronessOf structSort := by
  have hzero : Level.zeronessOf structSort = .never :=
    zeronessOf_eq_never_of_pos (eval_pos_of_isNeverZero hT_sort_nz)
  rw [hzero]
  obtain ⟨cvTM, mvalTM, hintTM, hfindTM, hpermTM, hlvTM⟩ := hmfT.model
  rw [hlpsT, List.length_range] at hpermTM
  rw [hlpsT, hrenT, posOf_range_eq_prep] at hlvTM
  have hlenTM : cvTM.levelParams.length = bnl := by
    have := hpermTM.length_eq; rwa [List.length_range] at this
  have hTM_def : cvTM.type.allLevelParamsDefined cvTM.levelParams = true :=
    (hwf _ (Ix.Kernel.Semantics.Env.find?_mem hfindTM)).2.1
  obtain ⟨bsTM₀, remTM₀, hstripTM₀, hremEq⟩ := exprLvEq_stripPis nP hlvTM hT_sort
  cases hremEq with
  | sort huEq =>
    rename_i uTM
    have huTM_pos : ∀ φ, 0 < Level.eval φ uTM := fun φ => by
      rw [← huEq φ]
      exact eval_pos_of_isNeverZero hT_sort_nz φ
    obtain ⟨stype, u, ⟨ps, hperm, hinf⟩, -⟩ := hmfC.modelTyped
    have hC_ren : (tyA_C.renameConsts g).stripPis (nP + nF) =
        some (bsC.map (fun p => (p.1.renameConsts g, p.2)),
          Expr.mkAppN (.const (g ciT.name) ((List.range bnl).map .param))
            (args.map (Expr.renameConsts g))) := by
      have h1 := stripPis_renameConsts g (nP + nF) hC_ret
      rwa [renameConsts_mkAppN] at h1
    obtain ⟨bs', hs', hpw_map⟩ := stripPis_ilp_pw ps (Core.posLevels ps) (nP + nF) hC_ren
    rw [ilp_mkAppN] at hs'
    let us' : List KLevel := ((List.range bnl).map .param).map (Level.subst ps (Core.posLevels ps))
    have hus'_len : us'.length = cvTM.levelParams.length := by simp [us', hlenTM]
    have hinst_eq :
        (Core.posOf cvTM.levelParams cvTM.type).instantiateLevelParams (List.range bnl) us' =
          cvTM.type.instantiateLevelParams cvTM.levelParams us' := by
      have hlenUs' : us'.length = bnl := by simp [us']
      rw [← hlenUs']
      exact IxVM.Refinement.Core.InferAux.posOf_instantiateLevelParams
        (hpermTM.nodup_iff.mpr List.nodup_range) hus'_len hTM_def
    obtain ⟨bsTM', hsTM', -⟩ := stripPis_ilp_pw (List.range bnl) us' nP hstripTM₀
    rw [hinst_eq] at hsTM'
    have huTM'_pos : ∀ φ, 0 < Level.eval φ (Level.subst (List.range bnl) us' uTM) := fun φ => by
      rw [Ix.Kernel.Level.eval_subst]
      exact huTM_pos _
    have hconst_ilp : (Expr.const (g ciT.name) ((List.range bnl).map .param) : KExpr).instantiateLevelParams
        ps (Core.posLevels ps) = .const (g ciT.name) us' := rfl
    rw [hconst_ilp] at hs'
    obtain ⟨hpw', -⟩ := infer_stripPis_ctor_pw_never hfindTM hus'_len hsTM' huTM'_pos (nP + nF) 0
      (by simp [hargs_len]) hs' hinf
    intro bm hbm
    have hmem : Level.substPW ps (Core.posLevels ps) bm.2.pw ∈ bs'.map (·.2.pw) := by
      rw [hpw_map]
      simp only [List.map_map]
      exact List.mem_map_of_mem (f := fun b : KExpr × BinderMeta =>
        Level.substPW ps (Core.posLevels ps) b.2.pw) hbm
    obtain ⟨bm', hbm', heq⟩ := List.mem_map.mp hmem
    exact substPW_pos_eq_never_inv hperm (heq.symm.trans (hpw' bm' hbm'))

/-! ## Section 4: `NoProjEnv` across aliases, the family block, and earlier tables -/

theorem noProjAt_instantiateLevelParams (T : KKey) (i : Nat) (ks : List LevelParam)
    (us : List KLevel) :
    ∀ {e : KExpr}, Expr.NoProjAt T i (e.instantiateLevelParams ks us) ↔ Expr.NoProjAt T i e := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => simp [Expr.instantiateLevelParams]
  | fvar _ _ ih => simp [Expr.instantiateLevelParams, ih]
  | app _ _ ih1 ih2 => simp [Expr.instantiateLevelParams, ih1, ih2]
  | lam _ _ _ ih1 ih2 => simp [Expr.instantiateLevelParams, ih1, ih2]
  | forallE _ _ _ ih1 ih2 => simp [Expr.instantiateLevelParams, ih1, ih2]
  | letE _ _ _ _ ih1 ih2 ih3 => simp [Expr.instantiateLevelParams, ih1, ih2, ih3]
  | proj s j e ih => simp [Expr.instantiateLevelParams, ih]

theorem noProjAt_renameConsts (T : KKey) (i : Nat) (f : KKey → KKey) :
    ∀ {e : KExpr}, Expr.NoProjAt T i (e.renameConsts f) ↔ Expr.NoProjAt T i e := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => simp [Expr.renameConsts]
  | fvar _ _ ih => simp [Expr.renameConsts, ih]
  | app _ _ ih1 ih2 => simp [Expr.renameConsts, ih1, ih2]
  | lam _ _ _ ih1 ih2 => simp [Expr.renameConsts, ih1, ih2]
  | forallE _ _ _ ih1 ih2 => simp [Expr.renameConsts, ih1, ih2]
  | letE _ _ _ _ ih1 ih2 ih3 => simp [Expr.renameConsts, ih1, ih2, ih3]
  | proj s j e ih => simp [Expr.renameConsts, ih]

theorem noProjAt_of_famJ_infer {env : Env .anon} {h : KKey → KKey} {T : KKey} {i : Nat}
    {e t : KExpr} (hfv : e.hasFvar = false) (hslot : env.findProj? T i = none)
    (hinf : (famJ h).infer env 0 e t) : Expr.NoProjAt T i e := by
  obtain ⟨-, -, ps, -, hInf⟩ := hinf
  have hfv2 : (Core.posOf ps (e.renameConsts h)).hasFvar = false := by
    unfold Core.posOf
    rw [Expr.hasFvar_instantiateLevelParams, Ix.Kernel.hasFvar_renameConsts]
    exact hfv
  have hps := Ix.Kernel.Model.infer_projSlots hInf rfl (Expr.FvarTysOk.of_not_hasFvar _ hfv2)
  have hnp := Ix.Kernel.Expr.ProjSlotsOk.noProjAt hslot _ hps
  unfold Core.posOf at hnp
  exact (noProjAt_renameConsts T i h).mp ((noProjAt_instantiateLevelParams T i _ _).mp hnp)

theorem noProjAt_of_renameJ_famJ {env : Env .anon} {f h : KKey → KKey} {T : KKey} {i : Nat}
    {e t : KExpr} (hfv : e.hasFvar = false) (hslot : env.findProj? T i = none)
    (hinf : (renameJ f (famJ h)).infer env 0 e t) : Expr.NoProjAt T i e := by
  rcases hinf with hi | ⟨-, hi⟩
  · exact noProjAt_of_famJ_infer hfv hslot hi
  · exact (noProjAt_renameConsts T i f).mp
      (noProjAt_of_famJ_infer (by rw [Ix.Kernel.hasFvar_renameConsts]; exact hfv) hslot hi)

theorem findProj?_none_of_table_none {env : Env .anon} {T : KKey} (i : Nat)
    (h : env.find? (projTableName T) = none) : env.findProj? T i = none := by
  unfold Env.findProj?
  rw [h]

theorem noProjEnv_aliasGroup {env : Env .anon} {h : KKey → KKey} {as : List (ConstantInfo .anon)}
    {T : KKey} (hBase : Decl.isBaseKey T = true) (hT : env.find? T = none)
    (hTbl : env.find? (projTableName T) = none) (i : Nat)
    (hg : AliasGroup env h as) (hnp : NoProjEnv env T i) :
    NoProjEnv ⟨as ++ env.consts⟩ T i ∧
      (⟨as ++ env.consts⟩ : Env .anon).find? T = none ∧
      (⟨as ++ env.consts⟩ : Env .anon).find? (projTableName T) = none := by
  induction hg with
  | nil _ => exact ⟨hnp, hT, hTbl⟩
  | @cons h₀ h' as' n d lps ty tgt ci hg' _ hfresh hnpt hsrc _ _ _ htr _ _ _ _ ih =>
    obtain ⟨hnp', hT', hTbl'⟩ := ih
    have hneT : auxKey n d ≠ T := Decl.FamilyAlias.auxKey_ne_of_isBaseKey hBase
    have hneTbl : auxKey n d ≠ projTableName T := hnpt T
    refine ⟨NoProjEnv.cons hnp' ?_, ?_, ?_⟩
    · exact
        { type := Ix.Kernel.Expr.noProjAt_of_constsResolve hT' ty htr
          defn := fun _ v _ heq => by
            obtain ⟨-, rfl, -⟩ := ConstantInfo.defnInfo.inj heq
            simp
          rule := fun _ _ _ _ heq => nomatch heq
          table := fun _ heq => nomatch heq }
    · rw [List.cons_append, Ix.Kernel.EnvExt.find?_cons_ne (env := ⟨as' ++ env.consts⟩)
            (c := .defnInfo ⟨auxKey n d, lps, ty⟩ (.const tgt (lps.map .param)) .abbrev) hneT]
      exact hT'
    · rw [List.cons_append, Ix.Kernel.EnvExt.find?_cons_ne (env := ⟨as' ++ env.consts⟩)
            (c := .defnInfo ⟨auxKey n d, lps, ty⟩ (.const tgt (lps.map .param)) .abbrev) hneTbl]
      exact hTbl'

theorem noProjAt_memberValRunJ {env : Env .anon} {h : KKey → KKey} {bn : List KKey}
    {cv cvA : ConstantVal .anon} {T : KKey} {i : Nat}
    (hslot : env.findProj? T i = none)
    (hmv : MemberValRunJ (renameJ (fun n => if bn.contains n then auxKey n .model else n)
      (famJ h)) env bn cv cvA) :
    Expr.NoProjAt T i cvA.type := by
  obtain ⟨type', hcv, rfl, -⟩ := hmv
  obtain ⟨-, -, -, -, hlb, hfv, hann, -, -, stype, u, hinf, -⟩ := hcv
  have hann' : (famJ h).annot env 0 cv.type type' := hann
  obtain ⟨hfv', -⟩ := (Decl.FamilyAlias.judgeFrames_famJ h env).annot_syntax hann' hfv hlb
  exact noProjAt_of_renameJ_famJ hfv' hslot hinf

theorem noProjEnv_indMembersRunJ {h : KKey → KKey} {bn : List KKey} {T : KKey} {i : Nat} :
    ∀ {env' : Env .anon} {ms : List (ConstantInfo .anon)} {envM : Env .anon},
      IndMembersRunJ (renameJ (fun n => if bn.contains n then auxKey n .model else n)
        (famJ h)) bn {} env' ms envM →
      (∀ ci ∈ ms, Decl.isBaseKey ci.name = true) →
      env'.find? (projTableName T) = none →
      NoProjEnv env' T i →
      NoProjEnv envM T i ∧ envM.find? (projTableName T) = none
  | env', [], envM, hrun, _, hTbl, hnp => by
    have e : envM = env' := hrun; subst e; exact ⟨hnp, hTbl⟩
  | env', ci :: rest, envM, hrun, hbase, hTbl, hnp => by
    obtain ⟨cvA, hmv, hrest⟩ := hrun
    have hciB : Decl.isBaseKey ci.name = true := hbase ci List.mem_cons_self
    have hcvB : Decl.isBaseKey cvA.name = true := by
      obtain ⟨_, _, rfl, -⟩ := hmv; exact hciB
    have hneTbl : cvA.name ≠ projTableName T := fun heq =>
      Decl.FamilyAlias.auxKey_ne_of_isBaseKey hcvB heq.symm
    have hnp_ty : Expr.NoProjAt T i cvA.type :=
      noProjAt_memberValRunJ (findProj?_none_of_table_none i hTbl) hmv
    have hrestB : ∀ c ∈ rest, Decl.isBaseKey c.name = true :=
      fun c hc => hbase c (List.mem_cons_of_mem _ hc)
    cases ci with
    | indInfo _ _ =>
      have hnp' : NoProjEnv ⟨.indInfo cvA {} :: env'.consts⟩ T i :=
        NoProjEnv.cons hnp (NoProjHead.ofType hnp_ty (fun _ _ _ h => nomatch h)
          (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h))
      have hTbl' : (⟨.indInfo cvA {} :: env'.consts⟩ : Env .anon).find? (projTableName T) = none := by
        rw [Ix.Kernel.EnvExt.find?_cons_ne (c := .indInfo cvA {}) hneTbl]; exact hTbl
      exact noProjEnv_indMembersRunJ hrest hrestB hTbl' hnp'
    | ctorInfo _ nP nF =>
      have hnp' : NoProjEnv ⟨.ctorInfo cvA nP nF :: env'.consts⟩ T i :=
        NoProjEnv.cons hnp (NoProjHead.ofType hnp_ty (fun _ _ _ h => nomatch h)
          (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h))
      have hTbl' : (⟨.ctorInfo cvA nP nF :: env'.consts⟩ : Env .anon).find? (projTableName T) = none := by
        rw [Ix.Kernel.EnvExt.find?_cons_ne (c := .ctorInfo cvA nP nF) hneTbl]; exact hTbl
      exact noProjEnv_indMembersRunJ hrest hrestB hTbl' hnp'
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | recInfo _ _ _ _ | projInfo _ =>
      exact hrest.elim

theorem noProjAt_provisionRecsRunJ {h : KKey → KKey} {bn : List KKey} {T : KKey} {i : Nat} :
    ∀ {envAcc : Env .anon} {recs : List (ConstantInfo .anon)} {envSelf : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      ProvisionRecsRunJ (renameJ (fun n => if bn.contains n then auxKey n .model else n)
        (famJ h)) bn envAcc recs envSelf checked →
      (∀ ci ∈ recs, Decl.isBaseKey ci.name = true) →
      envAcc.find? (projTableName T) = none →
      envSelf.find? (projTableName T) = none ∧ ∀ c ∈ checked, Expr.NoProjAt T i c.1.type
  | envAcc, [], envSelf, checked, ⟨hs, hc⟩, _, hTbl => by
    subst hs; subst hc; exact ⟨hTbl, fun _ hm => nomatch hm⟩
  | envAcc, ci :: rest, envSelf, checked, ⟨cvA, mI, rP, rules, rest', _, hmv, hprov, hchk⟩,
      hbase, hTbl => by
    have hciB : Decl.isBaseKey ci.name = true := hbase ci List.mem_cons_self
    have hcvB : Decl.isBaseKey cvA.name = true := by
      obtain ⟨_, _, rfl, -⟩ := hmv; exact hciB
    have hneTbl : cvA.name ≠ projTableName T := fun heq =>
      Decl.FamilyAlias.auxKey_ne_of_isBaseKey hcvB heq.symm
    have hnp_ty : Expr.NoProjAt T i cvA.type :=
      noProjAt_memberValRunJ (findProj?_none_of_table_none i hTbl) hmv
    have hTbl' : (⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ : Env .anon).find? (projTableName T) = none := by
      rw [Ix.Kernel.EnvExt.find?_cons_ne (c := .recInfo cvA mI rP []) hneTbl]; exact hTbl
    obtain ⟨hTblS, hall⟩ := noProjAt_provisionRecsRunJ hprov
      (fun c hc => hbase c (List.mem_cons_of_mem _ hc)) hTbl'
    refine ⟨hTblS, ?_⟩
    subst hchk
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact hnp_ty
    · exact hall c hc'

theorem noProjAt_liftLooseBVars_iff (T : KKey) (i n : Nat) :
    ∀ (e : KExpr) (c : Nat), Expr.NoProjAt T i (Expr.liftLooseBVars n c e) ↔ Expr.NoProjAt T i e := by
  intro e
  induction e with
  | bvar _ => intro _; simp only [Expr.liftLooseBVars]; split <;> simp
  | fvar _ _ ih => intro c; simp [Expr.liftLooseBVars, ih]
  | sort _ | const _ _ | lit _ => intro _; simp [Expr.liftLooseBVars]
  | app _ _ ih1 ih2 => intro c; simp [Expr.liftLooseBVars, ih1, ih2]
  | lam _ _ _ ih1 ih2 => intro c; simp [Expr.liftLooseBVars, ih1, ih2]
  | forallE _ _ _ ih1 ih2 => intro c; simp [Expr.liftLooseBVars, ih1, ih2]
  | letE _ _ _ _ ih1 ih2 ih3 => intro c; simp [Expr.liftLooseBVars, ih1, ih2, ih3]
  | proj s j e ih => intro c; simp [Expr.liftLooseBVars, ih]

theorem noProjAt_stripPis_rem (T : KKey) (i : Nat) :
    ∀ (k : Nat) {e rem : KExpr} {bs : List (KExpr × BinderMeta)},
      e.stripPis k = some (bs, rem) → Expr.NoProjAt T i e → Expr.NoProjAt T i rem
  | 0, e, rem, bs, hs, hnp => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs; exact hnp
  | k + 1, e, rem, bs, hs, hnp => by
    cases e with
    | forallE dom body bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs', rem'⟩, hs', hmk⟩ := hs
      obtain ⟨-, rfl⟩ := Prod.mk.inj hmk
      simp only [Ix.Kernel.Expr.noProjAt_forallE] at hnp
      exact noProjAt_stripPis_rem T i k hs' hnp.2
    | _ => simp [Expr.stripPis] at hs

theorem noProjAt_getAppArgs (T : KKey) (i : Nat) :
    ∀ {e : KExpr}, Expr.NoProjAt T i e → ∀ a ∈ e.getAppArgs, Expr.NoProjAt T i a
  | .app f a, hnp, x, hx => by
    simp only [Ix.Kernel.Expr.noProjAt_app] at hnp
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact noProjAt_getAppArgs T i hnp.1 x hx
    · exact hnp.2
  | .bvar _, _, _, hx | .fvar _ _, _, _, hx | .sort _, _, _, hx | .const _ _, _, _, hx
  | .lam _ _ _, _, _, hx | .forallE _ _ _, _, _, hx | .letE _ _ _ _, _, _, hx
  | .lit _, _, _, hx | .proj _ _ _, _, _, hx => by
    simp [Expr.getAppArgs] at hx

theorem noProjAt_iotaRuleRenRunJ {h f : KKey → KKey} {env' envSelf : Env .anon}
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP j : Nat}
    {r r' : RecRule .anon} {T : KKey} {i : Nat}
    (hslot : envSelf.findProj? T i = none) (hty : Expr.NoProjAt T i tyA)
    (hr : IotaRuleRenRunJ (famJ h) env' envSelf f cvName lps tyA mI rP j r r') :
    Expr.NoProjAt T i r'.rhs ∧
      ∀ lvls pins, r'.fire = .nested lvls pins → ∀ p ∈ pins, Expr.NoProjAt T i p := by
  obtain ⟨cvj, cnP, cnF, rhsA, -, -, hlb, hfv, hann, -, -, -, ⟨t', hinf⟩, fire, rfl, hbr⟩ := hr
  have hann' : (famJ h).annot envSelf 0 r.rhs rhsA := hann
  obtain ⟨hfv', -⟩ := (Decl.FamilyAlias.judgeFrames_famJ h envSelf).annot_syntax hann' hfv hlb
  refine ⟨noProjAt_of_renameJ_famJ hfv' hslot hinf, ?_⟩
  intro lvls pins hfire p hp
  have hfire' : fire = .nested lvls pins := hfire
  rcases hbr with ⟨-, hpl, -⟩ | ⟨-, lvls', pins', hfe, hthm⟩
  · rw [hpl] at hfire'; exact nomatch hfire'
  · rw [hfe] at hfire'
    injection hfire' with _ hpn
    subst hpn
    obtain ⟨-, -, -, pre, dom, body, bm, D, hstrip, -, hargs, -⟩ :=
      Ix.Kernel.nestedRuleShape_inv hthm.1
    have hdom_np : Expr.NoProjAt T i dom := by
      have h1 := noProjAt_stripPis_rem T i mI hstrip hty
      simp only [Ix.Kernel.Expr.noProjAt_forallE] at h1
      exact h1.1
    have hmem : Expr.liftLooseBVars (mI - rP) 0 p ∈ dom.getAppArgs := by
      rw [hargs]
      exact List.mem_append_left _ (List.mem_map_of_mem hp)
    have hlift_np : Expr.NoProjAt T i (Expr.liftLooseBVars (mI - rP) 0 p) :=
      noProjAt_getAppArgs T i hdom_np _ hmem
    exact (noProjAt_liftLooseBVars_iff T i (mI - rP) p 0).mp hlift_np

theorem noProjAt_iotaRulesRenRunJ {h f : KKey → KKey} {env' envSelf : Env .anon}
    {cvName : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat} {T : KKey} {i : Nat}
    (hslot : envSelf.findProj? T i = none) (hty : Expr.NoProjAt T i tyA) :
    ∀ {j : Nat} {rules rules' : List (RecRule .anon)},
      IotaRulesRenRunJ (famJ h) env' envSelf f cvName lps tyA mI rP j rules rules' →
      ∀ rl ∈ rules', Expr.NoProjAt T i rl.rhs ∧
        ∀ lvls pins, rl.fire = .nested lvls pins → ∀ p ∈ pins, Expr.NoProjAt T i p
  | _, [], rules', hout => by
    have e : rules' = [] := hout; rw [e]; intro _ h; exact nomatch h
  | _, r :: rest, out, ⟨r', rest', hr, hrest, hout⟩ => by
    rw [hout]
    intro rl hrl
    rcases List.mem_cons.mp hrl with rfl | hrl'
    · exact noProjAt_iotaRuleRenRunJ hslot hty hr
    · exact noProjAt_iotaRulesRenRunJ hslot hty hrest rl hrl'

theorem noProjEnv_indRecsFoldRenRunJ {h : KKey → KKey} {bn : List KKey}
    {envBase envSelf : Env .anon} {T : KKey} {i : Nat}
    (hslot : envSelf.findProj? T i = none) :
    ∀ {acc : Env .anon} {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))}
      {out : Env .anon},
      IndRecsFoldRenRunJ (famJ h) bn envBase envSelf acc checked out →
      (∀ c ∈ checked, Expr.NoProjAt T i c.1.type) →
      NoProjEnv acc T i → NoProjEnv out T i
  | acc, [], out, hout, _, hnp => by
    have e : out = acc := hout; rw [e]; exact hnp
  | acc, c :: rest, out, ⟨rules', hrules, hrest⟩, hty, hnp => by
    have hc := hty c List.mem_cons_self
    have hnp' : NoProjEnv ⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ T i :=
      NoProjEnv.cons hnp
        { type := hc
          defn := fun _ _ _ heq => nomatch heq
          rule := fun _ _ _ _ heq rl hrl => by
            injection heq with _ _ _ hr
            subst hr
            exact noProjAt_iotaRulesRenRunJ hslot hc hrules rl hrl
          table := fun _ heq => nomatch heq }
    exact noProjEnv_indRecsFoldRenRunJ hslot hrest
      (fun c' hc' => hty c' (List.mem_cons_of_mem _ hc')) hnp'

/-- **`NoProjEnv env₂ T i` across the entire family step** for any base key `T` fresh in `env`
whose table name is fresh in `env`. -/
theorem noProjEnv_famStep {env env₂ : Env .anon} {h : KKey → KKey}
    {as blk : List (ConstantInfo .anon)} {T : KKey}
    (hwf : EnvWF env) (hBase : Decl.isBaseKey T = true)
    (hT : env.find? T = none) (hTbl : env.find? (projTableName T) = none)
    (hblkBase : ∀ ci ∈ blk, Decl.isBaseKey ci.name = true)
    (hg : AliasGroup env h as)
    (hd : DeclIndRenRunJ (famJ h) ⟨as ++ env.consts⟩ blk env₂) (i : Nat) :
    NoProjEnv env₂ T i := by
  have hnp₀ : NoProjEnv env T i := noProjEnv_of_fresh hwf hT i
  obtain ⟨hnpA, -, hTblA⟩ := noProjEnv_aliasGroup hBase hT hTbl i hg hnp₀
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := hd
  obtain ⟨hnpM, hTblM⟩ := noProjEnv_indMembersRunJ hmem
    (fun ci hci => hblkBase ci (List.mem_filter.mp hci).1) hTblA hnpA
  rcases hrecs with ⟨-, rfl⟩ | ⟨-, -, envSelf, checked, hprov, hfold⟩
  · exact hnpM
  · obtain ⟨hTblS, htyChk⟩ := noProjAt_provisionRecsRunJ hprov
      (fun ci hci => hblkBase ci (List.mem_filter.mp hci).1) hTblM
    exact noProjEnv_indRecsFoldRenRunJ (findProj?_none_of_table_none i hTblS) hfold htyChk hnpM

theorem noProjAt_instantiate1Lift {T : KKey} {i : Nat} {v : KExpr} (hv : Expr.NoProjAt T i v) :
    ∀ (e : KExpr) (d : Nat), Expr.NoProjAt T i e → Expr.NoProjAt T i (e.instantiate1Lift v d) := by
  intro e
  induction e with
  | bvar _ =>
    intro d _
    simp only [Expr.instantiate1Lift]
    split
    · exact (noProjAt_liftLooseBVars_iff T i d v 0).mpr hv
    · split <;> simp
  | fvar _ _ _ => intro _ h; exact h
  | sort _ | const _ _ | lit _ => intro _ _; simp [Expr.instantiate1Lift]
  | app _ _ ih1 ih2 =>
    intro d h; simp only [Ix.Kernel.Expr.noProjAt_app] at h
    simp [Expr.instantiate1Lift, ih1 d h.1, ih2 d h.2]
  | lam _ _ _ ih1 ih2 =>
    intro d h; simp only [Ix.Kernel.Expr.noProjAt_lam] at h
    simp [Expr.instantiate1Lift, ih1 d h.1, ih2 (d + 1) h.2]
  | forallE _ _ _ ih1 ih2 =>
    intro d h; simp only [Ix.Kernel.Expr.noProjAt_forallE] at h
    simp [Expr.instantiate1Lift, ih1 d h.1, ih2 (d + 1) h.2]
  | letE _ _ _ _ ih1 ih2 ih3 =>
    intro d h; simp only [Ix.Kernel.Expr.noProjAt_letE] at h
    simp [Expr.instantiate1Lift, ih1 d h.1, ih2 d h.2.1, ih3 (d + 1) h.2.2]
  | proj s j e ih =>
    intro d h; simp only [Ix.Kernel.Expr.noProjAt_proj] at h
    simp [Expr.instantiate1Lift, h.1, ih d h.2]

theorem noProjAt_instPisAtLift {T : KKey} {i : Nat} {as : List KExpr}
    (ha : ∀ a ∈ as, Expr.NoProjAt T i a) :
    ∀ {e r : KExpr}, Expr.NoProjAt T i e → Expr.instPisAtLift as e = some r → Expr.NoProjAt T i r := by
  induction as with
  | nil =>
    intro e r he h; simp only [Expr.instPisAtLift, Option.some.injEq] at h; subst h; exact he
  | cons a as ih =>
    intro e r he h
    cases e with
    | forallE _ body _ =>
      simp only [Expr.instPisAtLift] at h
      simp only [Ix.Kernel.Expr.noProjAt_forallE] at he
      exact ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (noProjAt_instantiate1Lift (ha a List.mem_cons_self) body 0 he.2) h
    | _ => exact nomatch h

theorem noProjAt_structProjBodiesGo_ne {T T' : KKey} (hne : T' ≠ T) (i : Nat) :
    ∀ (k idx : Nat) (r : KExpr) (bs : List KExpr),
      Expr.NoProjAt T i r → Ix.Kernel.structProjBodiesGo T' k idx r = some bs →
      ∀ b ∈ bs, Expr.NoProjAt T i b
  | 0, _, _, bs, _, h, b, hb => by
    simp only [Ix.Kernel.structProjBodiesGo, Option.some.injEq] at h; subst h; exact nomatch hb
  | k + 1, idx, r, bs, hr, h, b, hb => by
    cases r with
    | forallE dom body _ =>
      simp only [Ix.Kernel.structProjBodiesGo, Option.map_eq_some_iff] at h
      obtain ⟨bs', hbs', rfl⟩ := h
      simp only [Ix.Kernel.Expr.noProjAt_forallE] at hr
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hr.1
      · have harg : Expr.NoProjAt T i (Ix.Kernel.structProjArgP T' idx) := by
          simp [Ix.Kernel.structProjArgP, hne]
        exact noProjAt_structProjBodiesGo_ne hne i k (idx + 1) _ bs'
          (noProjAt_instantiate1Lift harg body 0 hr.2) hbs' b hb'
    | _ => exact nomatch h

/-- `structProjBodies T' nP' nF' cty` introduces only `.proj T'`, preserving `NoProjAt T i`
whenever `T' ≠ T`. -/
theorem noProjAt_structProjBodies_ne {T T' : KKey} (hne : T' ≠ T) {nP' nF' i : Nat}
    {cty : KExpr} {bodies : Array KExpr}
    (hcty : Expr.NoProjAt T i cty)
    (hb : Ix.Kernel.structProjBodies T' nP' nF' cty = some bodies) :
    ∀ b ∈ bodies, Expr.NoProjAt T i b := by
  unfold Ix.Kernel.structProjBodies at hb
  split at hb
  · next r hr =>
    obtain ⟨bs, hbs, rfl⟩ := Option.map_eq_some_iff.mp hb
    have hr' := noProjAt_instPisAtLift (as := Ix.Kernel.structProjPs nP') (fun a ha => by
      simp only [Ix.Kernel.structProjPs, List.mem_map] at ha
      obtain ⟨_, -, rfl⟩ := ha; simp) hcty hr
    intro b hbm
    exact noProjAt_structProjBodiesGo_ne hne i nF' 0 r bs hr' hbs b (by simpa using hbm)
  · exact nomatch hb

theorem noProjIn_of_noProjAt_list {bad : List KKey} :
    ∀ {e : KExpr}, (∀ k ∈ bad, ∀ i, Expr.NoProjAt k i e) → Decl.NoProjIn bad e = true := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _; rfl
  | fvar _ _ ih =>
    intro h; exact ih (fun k hk i => by simpa using h k hk i)
  | app _ _ ih1 ih2 =>
    intro h
    simp only [Decl.NoProjIn, Bool.and_eq_true]
    exact ⟨ih1 (fun k hk i => (Ix.Kernel.Expr.noProjAt_app.mp (h k hk i)).1),
      ih2 (fun k hk i => (Ix.Kernel.Expr.noProjAt_app.mp (h k hk i)).2)⟩
  | lam _ _ _ ih1 ih2 =>
    intro h
    simp only [Decl.NoProjIn, Bool.and_eq_true]
    exact ⟨ih1 (fun k hk i => (Ix.Kernel.Expr.noProjAt_lam.mp (h k hk i)).1),
      ih2 (fun k hk i => (Ix.Kernel.Expr.noProjAt_lam.mp (h k hk i)).2)⟩
  | forallE _ _ _ ih1 ih2 =>
    intro h
    simp only [Decl.NoProjIn, Bool.and_eq_true]
    exact ⟨ih1 (fun k hk i => (Ix.Kernel.Expr.noProjAt_forallE.mp (h k hk i)).1),
      ih2 (fun k hk i => (Ix.Kernel.Expr.noProjAt_forallE.mp (h k hk i)).2)⟩
  | letE _ _ _ _ ih1 ih2 ih3 =>
    intro h
    simp only [Decl.NoProjIn, Bool.and_eq_true]
    exact ⟨⟨ih1 (fun k hk i => (Ix.Kernel.Expr.noProjAt_letE.mp (h k hk i)).1),
      ih2 (fun k hk i => (Ix.Kernel.Expr.noProjAt_letE.mp (h k hk i)).2.1)⟩,
      ih3 (fun k hk i => (Ix.Kernel.Expr.noProjAt_letE.mp (h k hk i)).2.2)⟩
  | proj s j e ih =>
    intro h
    simp only [Decl.NoProjIn, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ih (fun k hk i => (Ix.Kernel.Expr.noProjAt_proj.mp (h k hk i)).2)⟩
    cases hmem : bad.contains s with
    | false => rfl
    | true =>
      have hs : s ∈ bad := by simpa using hmem
      exact ((Ix.Kernel.Expr.noProjAt_proj.mp (h s hs j)).1 ⟨rfl, rfl⟩).elim

/-! ## Section 5: Leaf alignment across aliases and `DeclIndRenRunJ` -/

theorem modelExt_isSome_mono {V : Type u} [SetTheory V] {μ : Ix.Kernel.CheckMode}
    {env₁ env₂ : Env .anon} {mp₁ : EnvModelM V μ env₁} {mp₂ : EnvModelM V μ env₂}
    (hext : ModelExt mp₁ mp₂) {k : KKey} (hk : (env₁.find? k).isSome = true) :
    (env₂.find? k).isSome = true := by
  induction hext with
  | refl => exact hk
  | @step env' mp' c₀ A mp₃ _ hfresh _ _ _ ih =>
    rw [Ix.Kernel.Env.find?_cons_of_isSome hfresh ih]
    exact ih
  | @swap env' env₃ mp' mp₃ _ hsome _ _ _ ih =>
    exact hsome k ih

theorem modelExt_acval_eq_of_isSome {V : Type u} [SetTheory V] {μ : Ix.Kernel.CheckMode}
    {env₁ env₂ : Env .anon} {mp₁ : EnvModelM V μ env₁} {mp₂ : EnvModelM V μ env₂}
    (hext : ModelExt mp₁ mp₂) {k : KKey} (hk : (env₁.find? k).isSome = true)
    (ψ : LevelParam → Nat) :
    mp₂.base2.acval k ψ = mp₁.base2.acval k ψ := by
  induction hext with
  | refl => rfl
  | @step env' mp' c₀ A mp₃ hprev hfresh _ _ hac ih =>
    have h1 : (env'.find? k).isSome = true := modelExt_isSome_mono hprev hk
    have hne : k ≠ c₀.name := fun heq => by
      rw [heq, hfresh] at h1; exact Bool.false_ne_true h1
    rw [hac, acvalWith_ne hne, ih]
  | @swap env' env₃ mp' mp₃ _ _ _ _ hac ih =>
    rw [hac, ih]

/-- Build `EnvModelM` across an `AliasGroup` while exposing exact `acval` equations on each alias
and `ModelExt` from `mp`. -/
theorem envModelM_aliasGroup {V : Type u} [SetTheory V] {env : Env .anon}
    {h : KKey → KKey} {as : List (ConstantInfo .anon)}
    (mp : EnvModelM V .verified env) (hE : Ix.Kernel.EtaFamiliesClosed env)
    (hg : AliasGroup env h as) :
    ∃ mp₁ : EnvModelM V .verified ⟨as ++ env.consts⟩,
      ModelExt mp mp₁ ∧
      Ix.Kernel.EtaFamiliesClosed ⟨as ++ env.consts⟩ ∧
      AliasEnv ⟨as ++ env.consts⟩ h ∧
      ∀ (k : KKey) (lps : List LevelParam) (ty : KExpr) (tgt : KKey)
        (hint : Ix.Kernel.ReducibilityHint) (ci : ConstantInfo .anon),
        (⟨as ++ env.consts⟩ : Env .anon).find? k =
          some (.defnInfo ⟨k, lps, ty⟩ (.const tgt (lps.map .param)) hint) →
        env.find? k = none →
        env.find? tgt = some ci →
        ∀ ψ, mp₁.base2.acval k ψ =
          mp.base2.acval tgt (Level.substFn ψ ci.toConstantVal.levelParams (lps.map .param)) := by
  induction hg with
  | nil hid =>
    refine ⟨mp, .refl, hE, fun k hk => absurd (hid k) hk, fun k _ _ _ _ _ hf hnone => ?_⟩
    simp only [List.nil_append] at hf
    rw [hnone] at hf; exact nomatch hf
  | @cons h₀ h' as' n d lps ty tgt ci hg' hperm hfresh hnpt hsrc hlps htf htp htr htb hty
      hk' hrest ih =>
    obtain ⟨mp', hext', hE', hA', hac'⟩ := ih
    obtain ⟨mp₂, hac₂, hext₂, hE₂, -⟩ := Decl.FamilyAlias.installAliasPos mp' hE' hperm hfresh hnpt
      hsrc hlps htf htp htr htb
      (fun ψ => Decl.FamilyAlias.aliasType_reads mp'.base2
        (Decl.FamilyAlias.renameOkPos_of_aliasEnv mp' hA') hperm hlps hty ψ)
    refine ⟨mp₂, hext'.trans hext₂, hE₂,
      Decl.FamilyAlias.aliasEnv_cons hA' hperm hfresh hsrc hlps hk' hrest, ?_⟩
    intro k lps' ty' tgt' hint' ci' hf hnone hsrc' ψ
    rw [List.cons_append, Ix.Kernel.Env.find?_cons (env := ⟨as' ++ env.consts⟩)] at hf
    split at hf
    · rename_i heqk
      obtain ⟨hcv, hval, -⟩ := ConstantInfo.defnInfo.inj (Option.some.inj hf)
      obtain ⟨rfl, rfl, rfl⟩ := ConstantVal.mk.inj hcv
      obtain ⟨rfl, -⟩ := Expr.const.inj hval
      have hci_eq : ci' = ci := by
        have h1 := hg'.find_prefix _ _ hsrc'
        rw [hsrc] at h1
        exact Option.some.inj h1.symm
      subst hci_eq
      have hsrc_some : (env.find? tgt).isSome = true := by rw [hsrc']; rfl
      rw [hac₂]
      change acvalWith mp'.base2.acval (auxKey n d) _ (auxKey n d) ψ = _
      rw [acvalWith_self, modelExt_acval_eq_of_isSome hext' hsrc_some]
    · rename_i hnek
      have hne : k ≠ auxKey n d := fun e => hnek e.symm
      rw [hac₂]
      change acvalWith mp'.base2.acval (auxKey n d) _ k ψ = _
      rw [acvalWith_ne hne]
      exact hac' k lps' ty' tgt' hint' ci' hf hnone hsrc' ψ

/-- Variant of `Ix.Kernel.Model.declIndRenJ` exposing `BlockAcvalInstalled` on the resulting
model `mp₂`. -/
theorem declIndRenJ_acval_anon {V : Type u} [SetTheory V] {μ : Ix.Kernel.CheckMode}
    {J : Judgements .anon}
    (hfr : ∀ e : Env .anon, Ix.Kernel.Model.JudgeFrames J e)
    (hJ : ∀ {e : Env .anon} (m : EnvModelM V μ e), Ix.Kernel.Model.JudgeSound J m.base2)
    {env env₂ : Env .anon} {block : List (ConstantInfo .anon)} (mp : EnvModelM V μ env)
    (hE : Ix.Kernel.EtaFamiliesClosed env)
    (h : DeclIndRenRunJ J env block env₂) :
    Ix.Kernel.EtaFamiliesClosed env₂ ∧
    ∃ mp₂ : EnvModelM V μ env₂,
      BlockAcvalInstalled (block.map (·.name)) env₂ mp₂.base2.acval ∧
      ModelExt mp mp₂ := by
  refine ⟨Ix.Kernel.Semantics.declIndEtaClosedRunJ hE h.shape, ?_⟩
  have hns := Ix.Kernel.Model.declIndRenRunJ_noModel h
  obtain ⟨hsplit, envM, hmem, hrecs⟩ := h
  have hbnAll : ∀ ci ∈ block, (block.map (·.name)).contains ci.name = true := fun ci hci => by
    have hmm : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
    simpa using hmm
  have hEC0 : Ix.Kernel.EtaFamiliesClosedO (block.map (·.name)) env :=
    fun T cvT caps hf hcape hres _ => hE T cvT caps hf hcape hres
  have hnostore : ∀ n, (block.map (·.name)).contains n = true →
      ∀ ci : ConstantInfo .anon, env.find? n = some ci → False := by
    intro n hn ci hf
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · rw [Ix.Kernel.Semantics.indMembersRun_fresh _ hmem ci₀ hci₀] at hf
      exact nomatch hf
    · have hup := Ix.Kernel.Semantics.indMembersRun_mono _ hmem _ _ hf
      rw [Ix.Kernel.Semantics.indRecsRun_fresh (Ix.Kernel.Semantics.indRecsRenRunJ_shape hrecs) ci₀ hci₀] at hup
      exact nomatch hup
  have hI0 : BlockInstalledTT (block.map (·.name)) env mp.base2.cvalE :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hIA0 : BlockAcvalInstalled (block.map (·.name)) env mp.base2.acval :=
    fun n hn ci hf => absurd (hnostore n hn ci hf) (fun h => h)
  have hBP0 : Ix.Kernel.BlockEtaPinned μ (block.map (·.name)) env :=
    fun n cvS capsS hnb hf _ => absurd (hnostore n hnb _ hf) (fun h => h)
  obtain ⟨mp₁, hI₁, hIA₁, hEC₁, hBP₁, hext₁⟩ :=
    Ix.Kernel.Model.indMembersPM Ix.Kernel.Model.memberEtaLaw Ix.Kernel.Model.memberUnitLaw
      (fun e => Ix.Kernel.Model.judgeFrames_renameJ (hfr e)) _ mp
      (fun ci hci => hbnAll ci (List.mem_filter.mp hci).1)
      (fun cv caps₂ _ => ⟨Ix.Kernel.Semantics.etaPins_empty,
        ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩⟩)
      hmem hI0 hIA0 hEC0 hBP0
  obtain ⟨mp₂, -, hIA₂, hext₂⟩ :=
    Ix.Kernel.Model.indRecsRen Ix.Kernel.Model.memberEtaLaw Ix.Kernel.Model.memberUnitLaw
      hfr hJ mp₁ hI₁ hIA₁
      (fun ci hci => hbnAll ci (List.mem_filter.mp hci).1)
      (fun n hn => by
        have hmm : n ∈ block.map (·.name) := by simpa using hn
        obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
        rw [hsplit] at hci₀
        rcases List.mem_append.mp hci₀ with hci₀ | hci₀
        · exact Or.inl (Ix.Kernel.Semantics.indMembersRun_stored _ hmem ci₀ hci₀)
        · exact Or.inr ⟨ci₀, hci₀, rfl⟩)
      hns hEC₁ hBP₁ hrecs
  exact ⟨mp₂, hIA₂, hext₁.trans hext₂⟩

/-- SubstFn composition for two level-parameter permutations:
`substFn (substFn φ k_lps us) tgt_lps (k_lps.map .param) p = substFn φ tgt_lps us p`
whenever `p ∈ tgt_lps`, `k_lps.Nodup`, `tgt_lps.Nodup`, and `k_lps.length = tgt_lps.length = us.length`. -/
theorem substFn_comp_param_map {φ : LevelParam → Nat}
    {k_lps tgt_lps : List LevelParam} {us : List KLevel}
    (hknd : k_lps.Nodup) (htnd : tgt_lps.Nodup)
    (hlen1 : tgt_lps.length = k_lps.length) (hlen2 : us.length = k_lps.length) :
    ∀ p ∈ tgt_lps,
      Level.substFn (Level.substFn φ k_lps us) tgt_lps (k_lps.map .param) p =
        Level.substFn φ tgt_lps us p := by
  intro p hp
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hp
  have hilt : i < tgt_lps.length := (List.getElem?_eq_some_iff.mp hi).1
  have hik : i < k_lps.length := by omega
  have hiu : i < us.length := by omega
  have h1 : Level.substFn (Level.substFn φ k_lps us) tgt_lps (k_lps.map .param) p =
      Level.eval (Level.substFn φ k_lps us) (.param (k_lps[i]'hik)) :=
    substFn_getElem?_eq_aux _ htnd hi (by simp [hik])
  rw [h1]
  simp only [Level.eval]
  have h2 : Level.substFn φ k_lps us (k_lps[i]'hik) = Level.eval φ (us[i]'hiu) :=
    substFn_getElem?_eq_aux _ hknd (List.getElem?_eq_getElem hik)
      (List.getElem?_eq_getElem hiu)
  have h3 : Level.substFn φ tgt_lps us p = Level.eval φ (us[i]'hiu) :=
    substFn_getElem?_eq_aux _ htnd hi (List.getElem?_eq_getElem hiu)
  rw [h2, h3]

theorem mentionsConst_instantiate1 {k : KKey} {v : KExpr}
    (hv : v.mentionsConst k = false) :
    ∀ (e : KExpr) (c : Nat), e.mentionsConst k = false →
      (e.instantiate1 v c).mentionsConst k = false := by
  intro e
  induction e with
  | bvar _ =>
    intro c _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | fvar _ _ ih =>
    intro c h; exact h
  | sort _ | lit _ => intro _ _; rfl
  | const n _ => intro _ h; exact h
  | app _ _ ih1 ih2 =>
    intro c h; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1, Expr.mentionsConst, ih1 c h.1, ih2 c h.2]
  | lam _ _ _ ih1 ih2 =>
    intro c h; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1, Expr.mentionsConst, ih1 c h.1, ih2 (c + 1) h.2]
  | forallE _ _ _ ih1 ih2 =>
    intro c h; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1, Expr.mentionsConst, ih1 c h.1, ih2 (c + 1) h.2]
  | letE _ _ _ _ ih1 ih2 ih3 =>
    intro c h; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1, Expr.mentionsConst, ih1 c h.1.1, ih2 c h.1.2, ih3 (c + 1) h.2]
  | proj _ _ _ ih =>
    intro c h; simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at h
    simp [Expr.instantiate1, Expr.mentionsConst, h.1, ih c h.2]

theorem renameConsts_instantiate1 (g : KKey → KKey) (v : KExpr) :
    ∀ (e : KExpr) (c : Nat),
      (e.instantiate1 v c).renameConsts g = (e.renameConsts g).instantiate1 (v.renameConsts g) c := by
  intro e
  induction e with
  | bvar _ =>
    intro c
    simp only [Expr.instantiate1, Expr.renameConsts]
    split
    · rfl
    · split <;> rfl
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app _ _ ih1 ih2 => intro c; simp [Expr.instantiate1, Expr.renameConsts, ih1, ih2]
  | lam _ _ _ ih1 ih2 => intro c; simp [Expr.instantiate1, Expr.renameConsts, ih1, ih2]
  | forallE _ _ _ ih1 ih2 => intro c; simp [Expr.instantiate1, Expr.renameConsts, ih1, ih2]
  | letE _ _ _ _ ih1 ih2 ih3 => intro c; simp [Expr.instantiate1, Expr.renameConsts, ih1, ih2, ih3]
  | proj _ _ _ ih => intro c; simp [Expr.instantiate1, Expr.renameConsts, ih]

theorem noProjAt_instantiate1_prop {T : KKey} {i : Nat} {v : KExpr} (hv : Expr.NoProjAt T i v) :
    ∀ (e : KExpr) (c : Nat), Expr.NoProjAt T i e → Expr.NoProjAt T i (e.instantiate1 v c) := by
  intro e
  induction e with
  | bvar _ =>
    intro c _; simp only [Expr.instantiate1]; split
    · exact hv
    · split <;> simp
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ h; exact h
  | app _ _ ih1 ih2 =>
    intro c h; simp only [Ix.Kernel.Expr.noProjAt_app] at h
    simp [Expr.instantiate1, ih1 c h.1, ih2 c h.2]
  | lam _ _ _ ih1 ih2 =>
    intro c h; simp only [Ix.Kernel.Expr.noProjAt_lam] at h
    simp [Expr.instantiate1, ih1 c h.1, ih2 (c + 1) h.2]
  | forallE _ _ _ ih1 ih2 =>
    intro c h; simp only [Ix.Kernel.Expr.noProjAt_forallE] at h
    simp [Expr.instantiate1, ih1 c h.1, ih2 (c + 1) h.2]
  | letE _ _ _ _ ih1 ih2 ih3 =>
    intro c h; simp only [Ix.Kernel.Expr.noProjAt_letE] at h
    simp [Expr.instantiate1, ih1 c h.1, ih2 c h.2.1, ih3 (c + 1) h.2.2]
  | proj s j e ih =>
    intro c h; simp only [Ix.Kernel.Expr.noProjAt_proj] at h
    simp [Expr.instantiate1, h.1, ih c h.2]

/-- **Core denotation alignment across the family step**: on any expression `e` mentioning only
prefix constants and block members (and no `.proj` at a block member), `denoteMeta` in
`(mp₂, env₂)` equals `denoteMeta` in `(mp, env)` on `e.renameConsts g`. -/
theorem denoteMeta_famStep_eq_renameConsts {V : Type u} [SetTheory V]
    {env env₂ : Env .anon} {g : KKey → KKey} {bn : List KKey}
    (mp : EnvModelM V .verified env) (mp₂ : EnvModelM V .verified env₂)
    (hext : ModelExt mp mp₂)
    (hextE : EnvExt env env₂)
    (hpre : ∀ k, (env.find? k).isSome = true → g k = k)
    (hblk_stored : ∀ k ∈ bn, (env₂.find? k).isSome = true)
    (hblk_map : ∀ k ∈ bn, ∀ ci₂, env₂.find? k = some ci₂ →
      ∃ ci_tgt, env.find? (g k) = some ci_tgt ∧
        ci₂.toConstantVal.levelParams.Nodup ∧
        ci_tgt.toConstantVal.levelParams.Nodup ∧
        ci_tgt.toConstantVal.levelParams.length = ci₂.toConstantVal.levelParams.length ∧
        ∀ ψ, mp₂.base2.acval k ψ =
          mp.base2.acval (g k) (Level.substFn ψ ci_tgt.toConstantVal.levelParams
            (ci₂.toConstantVal.levelParams.map .param)))
    (hproj_eq : ∀ s i, s ∉ bn → env₂.findProj? s i = env.findProj? s i)
    (hproj_chain : ∀ s i entry, s ∉ bn → env.findProj? s i = some entry →
      ¬ entry.off ≤ 1 → (env.find? (projChainKey s i)).isSome = true)
    (ψ : LevelParam → Nat)
    (d : Nat) (e : KExpr)
    (hres : (e.renameConsts g).constsResolve env = true)
    (hmen : ∀ k, e.mentionsConst k = true → (env.find? k).isSome = true ∨ k ∈ bn)
    (hnp : ∀ k ∈ bn, ∀ i, Expr.NoProjAt k i e) :
    denoteMeta mp₂.base2.acval env₂ ψ d e =
      denoteMeta mp.base2.acval env ψ d (e.renameConsts g) := by
  have hfind_eq : ∀ k, (env.find? k).isSome = true → env₂.find? k = env.find? k := fun k hk => by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
    rw [hextE.find hci, hci]
  match e with
  | .bvar _ | .fvar _ _ | .sort _ | .letE _ _ _ _ =>
    simp [Expr.renameConsts, denoteMeta]
  | .lit (.natVal n) =>
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at hres
    have hnat : Ix.Kernel.natLitSupported env₂ = Ix.Kernel.natLitSupported env := by
      simp only [Ix.Kernel.natLitSupported, hfind_eq _ hres.1.1, hfind_eq _ hres.1.2,
        hfind_eq _ hres.2]
    simp only [Expr.renameConsts, denoteMeta, hnat,
      modelExt_acval_eq_of_isSome hext hres.1.2,
      modelExt_acval_eq_of_isSome hext hres.2]
  | .lit (.strVal s) =>
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at hres
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hres
    have hstr : Ix.Kernel.strLitSupported env₂ = Ix.Kernel.strLitSupported env := by
      simp only [Ix.Kernel.strLitSupported, Ix.Kernel.natLitSupported,
        hfind_eq _ h1, hfind_eq _ h2, hfind_eq _ h3, hfind_eq _ h4, hfind_eq _ h5,
        hfind_eq _ h6, hfind_eq _ h7, hfind_eq _ h8, hfind_eq _ h9, hfind_eq _ h10]
    have hlpNil : Ix.Kernel.Verify.levelParamsAt env₂ Ix.Kernel.listNilName =
        Ix.Kernel.Verify.levelParamsAt env Ix.Kernel.listNilName := by
      simp only [Ix.Kernel.Verify.levelParamsAt, hfind_eq _ h7]
    have hlpCons : Ix.Kernel.Verify.levelParamsAt env₂ Ix.Kernel.listConsName =
        Ix.Kernel.Verify.levelParamsAt env Ix.Kernel.listConsName := by
      simp only [Ix.Kernel.Verify.levelParamsAt, hfind_eq _ h8]
    simp only [Expr.renameConsts, denoteMeta, hstr, hlpNil, hlpCons,
      modelExt_acval_eq_of_isSome hext h2,
      modelExt_acval_eq_of_isSome hext h3,
      modelExt_acval_eq_of_isSome hext h5,
      modelExt_acval_eq_of_isSome hext h7,
      modelExt_acval_eq_of_isSome hext h8,
      modelExt_acval_eq_of_isSome hext h9,
      modelExt_acval_eq_of_isSome hext h10]
  | .const k us =>
    have hk : (env.find? k).isSome = true ∨ k ∈ bn := hmen k (by simp [Expr.mentionsConst])
    simp only [Expr.renameConsts, denoteMeta]
    rcases hk with hpreK | hblkK
    · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hpreK
      rw [hpre k hpreK, hextE.find hci, hci]
      split
      · rw [modelExt_acval_eq_of_isSome hext hpreK]
      · rfl
    · obtain ⟨ci₂, hf₂⟩ := Option.isSome_iff_exists.mp (hblk_stored k hblkK)
      obtain ⟨ci_tgt, hftgt, hknd, htnd, hlen, hac⟩ := hblk_map k hblkK ci₂ hf₂
      simp only [hf₂, hftgt, hlen]
      split
      · rename_i hus
        congr 1
        rw [hac]
        exact mp.base2.acval_params (g k) ci_tgt hftgt _ _
          (substFn_comp_param_map hknd htnd hlen hus)
      · rfl
  | .app f a =>
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at hres
    have ihf := denoteMeta_famStep_eq_renameConsts mp mp₂ hext hextE hpre hblk_stored hblk_map
      hproj_eq hproj_chain ψ d f hres.1
      (fun k hk => hmen k (by simp [Expr.mentionsConst, hk]))
      (fun k hk i => (Ix.Kernel.Expr.noProjAt_app.mp (hnp k hk i)).1)
    have iha := denoteMeta_famStep_eq_renameConsts mp mp₂ hext hextE hpre hblk_stored hblk_map
      hproj_eq hproj_chain ψ d a hres.2
      (fun k hk => hmen k (by simp [Expr.mentionsConst, hk]))
      (fun k hk i => (Ix.Kernel.Expr.noProjAt_app.mp (hnp k hk i)).2)
    simp only [Expr.renameConsts, denoteMeta, ihf, iha]
  | .lam dom body bm =>
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at hres
    have ihd := denoteMeta_famStep_eq_renameConsts mp mp₂ hext hextE hpre hblk_stored hblk_map
      hproj_eq hproj_chain ψ d dom hres.1
      (fun k hk => hmen k (by simp [Expr.mentionsConst, hk]))
      (fun k hk i => (Ix.Kernel.Expr.noProjAt_lam.mp (hnp k hk i)).1)
    have hres_b : ((body.instantiate1 (.fvar d dom) 0).renameConsts g).constsResolve env = true := by
      rw [renameConsts_instantiate1]
      exact Expr.constsResolve_instantiate1 hres.1 0 hres.2
    have ihb := denoteMeta_famStep_eq_renameConsts mp mp₂ hext hextE hpre hblk_stored hblk_map
      hproj_eq hproj_chain ψ (d + 1) (body.instantiate1 (.fvar d dom) 0) hres_b
      (fun k hk => by
        by_contra hnot
        have hdom_f : dom.mentionsConst k = false := by
          cases h1 : dom.mentionsConst k with
          | false => rfl
          | true => exact (hnot (hmen k (by simp [Expr.mentionsConst, h1]))).elim
        have hbod_f : body.mentionsConst k = false := by
          cases h1 : body.mentionsConst k with
          | false => rfl
          | true => exact (hnot (hmen k (by simp [Expr.mentionsConst, h1]))).elim
        have hinst_f := mentionsConst_instantiate1 (k := k) (v := .fvar d dom) hdom_f body 0 hbod_f
        rw [hinst_f] at hk; exact Bool.false_ne_true hk)
      (fun k hk i => noProjAt_instantiate1_prop (T := k) (i := i)
        (v := .fvar d dom) (by simpa using (Ix.Kernel.Expr.noProjAt_lam.mp (hnp k hk i)).1)
        body 0 (Ix.Kernel.Expr.noProjAt_lam.mp (hnp k hk i)).2)
    simp only [Expr.renameConsts, denoteMeta, ihd]
    rw [ihb, renameConsts_instantiate1]
    rfl
  | .forallE dom body bm =>
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at hres
    have ihd := denoteMeta_famStep_eq_renameConsts mp mp₂ hext hextE hpre hblk_stored hblk_map
      hproj_eq hproj_chain ψ d dom hres.1
      (fun k hk => hmen k (by simp [Expr.mentionsConst, hk]))
      (fun k hk i => (Ix.Kernel.Expr.noProjAt_forallE.mp (hnp k hk i)).1)
    have hres_b : ((body.instantiate1 (.fvar d dom) 0).renameConsts g).constsResolve env = true := by
      rw [renameConsts_instantiate1]
      exact Expr.constsResolve_instantiate1 hres.1 0 hres.2
    have ihb := denoteMeta_famStep_eq_renameConsts mp mp₂ hext hextE hpre hblk_stored hblk_map
      hproj_eq hproj_chain ψ (d + 1) (body.instantiate1 (.fvar d dom) 0) hres_b
      (fun k hk => by
        by_contra hnot
        have hdom_f : dom.mentionsConst k = false := by
          cases h1 : dom.mentionsConst k with
          | false => rfl
          | true => exact (hnot (hmen k (by simp [Expr.mentionsConst, h1]))).elim
        have hbod_f : body.mentionsConst k = false := by
          cases h1 : body.mentionsConst k with
          | false => rfl
          | true => exact (hnot (hmen k (by simp [Expr.mentionsConst, h1]))).elim
        have hinst_f := mentionsConst_instantiate1 (k := k) (v := .fvar d dom) hdom_f body 0 hbod_f
        rw [hinst_f] at hk; exact Bool.false_ne_true hk)
      (fun k hk i => noProjAt_instantiate1_prop (T := k) (i := i)
        (v := .fvar d dom) (by simpa using (Ix.Kernel.Expr.noProjAt_forallE.mp (hnp k hk i)).1)
        body 0 (Ix.Kernel.Expr.noProjAt_forallE.mp (hnp k hk i)).2)
    simp only [Expr.renameConsts, denoteMeta, ihd]
    rw [ihb, renameConsts_instantiate1]
    rfl
  | .proj s j sub =>
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at hres
    have hs : s ∉ bn := fun hmem => (Ix.Kernel.Expr.noProjAt_proj.mp (hnp s hmem j)).1 ⟨rfl, rfl⟩
    have ihs := denoteMeta_famStep_eq_renameConsts mp mp₂ hext hextE hpre hblk_stored hblk_map
      hproj_eq hproj_chain ψ d sub hres.2
      (fun k hk => hmen k (by simp [Expr.mentionsConst, hk]))
      (fun k hk i => (Ix.Kernel.Expr.noProjAt_proj.mp (hnp k hk i)).2)
    simp only [Expr.renameConsts, denoteMeta, ihs, hproj_eq s j hs]
    cases hfp : env.findProj? s j with
    | none => rfl
    | some entry =>
      cases hsub : denoteMeta mp.base2.acval env ψ d (sub.renameConsts g) with
      | none => rfl
      | some ea =>
        simp only [Option.bind_some]
        unfold Ix.Kernel.Semantics.projNodeAV?
        split
        · rfl
        · rename_i hgt
          have hch := hproj_chain s j entry hs hfp hgt
          have hch₂ : (env₂.find? (projChainKey s j)).isSome = true :=
            modelExt_isSome_mono hext hch
          simp only [hch₂, hch, ↓reduceIte]
          exact congrArg some (congrArg (fun f => AnnotTerm.chain f ea)
            (funext fun n => modelExt_acval_eq_of_isSome hext hch (fun _ => n)))
termination_by Expr.sizeB e
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; done)
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB])

end IxVM.Refinement.Typing.FamilyAlias
