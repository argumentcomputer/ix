import IxVMRefinement.Decl.DeclSpecs
import IxVMRefinement.Assembly.RoleFacts
import IxC.Kernel.Semantics.Bridge.DeclRun
import IxC.Kernel.Verify.Rules.Bridge

/-! # Checked role declaration runs

The pure kernel's accepted value-declaration runs yield the rules-tier judgements used by the
shared declaration invariant. Type and value fronts can also be transported to a prefix related
by `ThmSim`; this states the lookup agreement needed when replaying an admitted role prefix.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel
open Ix.Kernel.Semantics
open Ix.Kernel.Model
open Ix.Kernel.Rules (Annot Red DefEq Infer)

universe u

/-- A checked constant front yields its rules-tier front in the same environment. -/
theorem constantValRun_rulesJ {fuel : Nat} {env : Env .anon}
    {cv : ConstantVal .anon} {ty : Core.KExpr}
    (h : ConstantValRun .verified fuel env cv ty) :
    ConstantValRunJ rulesJ env cv ty := by
  obtain ⟨hfresh, hres, hshape, hnd, hlbb, hnfv, hann, hdef, hresolve, stype, level, hi, hs⟩ := h
  exact ⟨hfresh, hres, hshape, hnd, hlbb, hnfv, Assembly.annotateCore_to_annot hann,
    hdef, hresolve, stype, level, Rules.inferTypeCore_bridge hi,
    Rules.whnf_bridge (Ix.Kernel.ensureSortCore_inv hs)⟩

/-- A checked value front yields its rules-tier front in the same environment. -/
theorem valueFrontRun_rulesJ {fuel : Nat} {env : Env .anon}
    {cv : ConstantVal .anon} {value ty value' : Core.KExpr}
    (h : ValueFrontRun .verified fuel env cv value ty value') :
    ValueFrontRunJ rulesJ env cv value ty value' := by
  obtain ⟨hlbb, hnfv, hann, hdef, hresolve, vtype, hi, hd⟩ := h
  exact ⟨hlbb, hnfv, Assembly.annotateCore_to_annot hann, hdef, hresolve,
    vtype, Rules.inferTypeCore_bridge hi, Rules.isDefEqCore_bridge hd⟩

/-- Checked type-front transport needs reference-prefix lookup agreement, target freshness,
and the target store invariant; it does not assume equality of the environments. -/
theorem constantValRun_rulesJ_of_thmSim {fuel : Nat} {reference target : Env .anon}
    {cv : ConstantVal .anon} {ty : Core.KExpr}
    (sim : Assembly.ThmSim reference target) (store : Ix.Kernel.Open.StoreInv target)
    (fresh : target.find? cv.name = none)
    (h : ConstantValRun .verified fuel reference cv ty) :
    ConstantValRunJ rulesJ target cv ty := by
  obtain ⟨_, hres, hshape, hnd, hlbb, hnfv, hann, hdef, _, stype, level, hi, hs⟩ := h
  have inferred := sim.infer (Rules.inferTypeCore_bridge hi)
  have closed := (annotate_syntax hann hnfv hlbb).1
  exact ⟨by rw [fresh]; rfl, hres, hshape, hnd, hlbb, hnfv,
    Assembly.annotateCore_to_annot hann, hdef, infer_constsResolve inferred store closed,
    stype, level, inferred, sim.red (Rules.whnf_bridge (Ix.Kernel.ensureSortCore_inv hs))⟩

/-- Checked value-front transport under the same lookup agreement. -/
theorem valueFrontRun_rulesJ_of_thmSim {fuel : Nat} {reference target : Env .anon}
    {cv : ConstantVal .anon} {value ty value' : Core.KExpr}
    (sim : Assembly.ThmSim reference target) (store : Ix.Kernel.Open.StoreInv target)
    (h : ValueFrontRun .verified fuel reference cv value ty value') :
    ValueFrontRunJ rulesJ target cv value ty value' := by
  obtain ⟨hlbb, hnfv, hann, hdef, _, vtype, hi, hd⟩ := h
  have inferred := sim.infer (Rules.inferTypeCore_bridge hi)
  have closed := (annotate_syntax hann hnfv hlbb).1
  exact ⟨hlbb, hnfv, Assembly.annotateCore_to_annot hann, hdef,
    infer_constsResolve inferred store closed, vtype, inferred,
    sim.defEq (Rules.isDefEqCore_bridge hd)⟩

private theorem divModCertsJ_rulesJ {fuel : Nat} {env : Env .anon}
    {name : Key .anon} {value : Core.KExpr}
    {statements : List (List Core.KExpr × Core.KExpr)} {proofs : List Core.KExpr}
    (h : DivModCertsJ (runJ .verified fuel) env name value statements proofs) :
    DivModCertsJ rulesJ env name value statements proofs := by
  induction h with
  | nil => exact .nil
  | cons guard hann hinf hdef _ ih =>
    exact .cons guard (Assembly.annotateCore_to_annot hann)
      (Rules.inferTypeCore_bridge hinf) (Rules.isDefEqCore_bridge hdef) ih

/-- The accepted definition run, including structural and well-founded Nat obligations,
is a rules-tier declaration run. -/
theorem declDefnRun_rulesJ {fuel : Nat} {env env₂ : Env .anon}
    {cv : ConstantVal .anon} {value : Core.KExpr} {hint : ReducibilityHint}
    (h : DeclDefnRun .verified fuel env cv value hint env₂) :
    DeclDefnRunJ rulesJ env cv value hint env₂ := by
  obtain ⟨ty, value', hcv, hv, henv, hnat, hdiv⟩ := h
  refine ⟨ty, value', constantValRun_rulesJ hcv, valueFrontRun_rulesJ hv, henv, ?_, ?_⟩
  · intro hn
    obtain ⟨hguard, hdeps, heqns⟩ := hnat hn
    exact ⟨hguard, hdeps, fun eq heq => Rules.isDefEqCore_bridge (heqns eq heq)⟩
  · intro hd
    obtain ⟨hguard, proofs, hpguard, hchecks⟩ := hdiv hd
    exact ⟨hguard, proofs, hpguard, divModCertsJ_rulesJ (divModCertsJ_of_run hchecks)⟩

/-- The accepted opaque run is a rules-tier declaration run. -/
theorem declOpaqueRun_rulesJ {fuel : Nat} {env env₂ : Env .anon}
    {cv : ConstantVal .anon} {value : Core.KExpr}
    (h : DeclOpaqueRun .verified fuel env cv value env₂) :
    DeclOpaqueRunJ rulesJ env cv value env₂ := by
  obtain ⟨ty, value', hcv, hv, henv⟩ := h
  exact ⟨ty, value', constantValRun_rulesJ hcv, valueFrontRun_rulesJ hv, henv⟩

/-- The accepted axiom run keeps its standard-axiom and inert-name checks. -/
theorem declAxiomRun_rulesJ {fuel : Nat} {env env₂ : Env .anon}
    {cv : ConstantVal .anon}
    (h : DeclAxiomRun .verified fuel env cv env₂) :
    DeclAxiomRunJ rulesJ env cv env₂ := by
  rcases h with hquot | ⟨ty, hcv, hrest⟩
  · exact Or.inl hquot
  · exact Or.inr ⟨ty, constantValRun_rulesJ hcv, hrest⟩

/-- An accepted definition advances the full invariant when paired with its structural install. -/
theorem checkedDefn_fullInv {fuel : Nat} {ev : Evidences .anon} {env env₂ : Env .anon}
    {cv : ConstantVal .anon} {value : Core.KExpr} {hint : ReducibilityHint}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev env
      (.defnDecl cv value hint) = .ok env₂)
    (installed : CleanInstallStep env (.defnDecl cv value hint) env₂) :
    ∀ (V : Type u) [SetTheory V], FullDeclInv V env → FullDeclInv V env₂ :=
  FullDeclInv.step_of_foldInv_clean installed
    (foldInv_step_defn (declDefnRun_rulesJ (declDefnRun_of checked)))

/-- An accepted opaque advances the full invariant when paired with its structural install. -/
theorem checkedOpaque_fullInv {fuel : Nat} {ev : Evidences .anon} {env env₂ : Env .anon}
    {cv : ConstantVal .anon} {value : Core.KExpr}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev env
      (.opaqueDecl cv value) = .ok env₂)
    (installed : CleanInstallStep env (.opaqueDecl cv value) env₂) :
    ∀ (V : Type u) [SetTheory V], FullDeclInv V env → FullDeclInv V env₂ :=
  FullDeclInv.step_of_foldInv_clean installed
    (foldInv_step_opaque (declOpaqueRun_rulesJ (declOpaqueRun_of checked)))

/-- An accepted standard or inert axiom advances the full invariant. -/
theorem checkedAxiom_fullInv {fuel : Nat} {ev : Evidences .anon} {env env₂ : Env .anon}
    {cv : ConstantVal .anon}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev env
      (.axiomDecl cv) = .ok env₂)
    (installed : CleanInstallStep env (.axiomDecl cv) env₂) :
    ∀ (V : Type u) [SetTheory V], FullDeclInv V env → FullDeclInv V env₂ :=
  FullDeclInv.step_of_foldInv_clean installed
    (foldInv_step_axiom (declAxiomRun_rulesJ (declAxiomRun_of checked)))

end IxVM.Refinement.Decl
