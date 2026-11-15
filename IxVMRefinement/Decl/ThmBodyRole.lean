import IxVMRefinement.Decl.ThmBodyDecl
import IxVMRefinement.Decl.DeclRoleStep

/-! # Annotated role stores from accepted reference checks

Each value declaration advances a typed store whose theorem bodies are the actual checked
annotations, while retaining agreement with the reference prefix for subsequent checks.
-/

namespace IxVM.Refinement.Decl.ThmBodyView.Agrees

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe u

variable {source target : Env .anon} (h : Agrees source target)

include h

/-- Accepted definitions retain their exact annotated value and reducibility hint. -/
theorem checkedDefn_step {fuel : Nat} {ev : Evidences .anon} {referenceOut : Env .anon}
    {cv : ConstantVal .anon} {value : Expr .anon} {hint : ReducibilityHint}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev source
      (.defnDecl cv value hint) = .ok referenceOut) :
    ∃ targetOut, Agrees referenceOut targetOut ∧
      IxVM.Consistency.InstallStep target (.defnDecl cv value hint) targetOut ∧
      DeclDefnRunJ rulesJ target cv value hint targetOut ∧
      ∀ (V : Type u) [SetTheory V], FoldInv V target → FoldInv V targetOut := by
  obtain ⟨targetOut, agreement, run⟩ := h.declDefnRun (declDefnRun_of checked)
  have rules := declDefnRun_rulesJ run
  refine ⟨targetOut, agreement, ?_, rules, foldInv_step_defn rules⟩
  apply installStep_glue_defn rules
  obtain ⟨ty, value', hcv, hv, rfl, _, _⟩ := run
  obtain ⟨_, _, _, _, htb, htf, hat, _, _, _⟩ := hcv
  obtain ⟨hvb, hvf, hav, _, _, _⟩ := hv
  exact ⟨_, Env.find?_cons_self _ _, ⟨⟨rfl, rfl, annotateCore_to_annotates hat htf htb⟩,
    annotateCore_to_annotates hav hvf hvb, rfl⟩⟩

/-- Accepted opaque declarations keep their checked witness while installing the signature. -/
theorem checkedOpaque_step {fuel : Nat} {ev : Evidences .anon} {referenceOut : Env .anon}
    {cv : ConstantVal .anon} {value : Expr .anon}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev source
      (.opaqueDecl cv value) = .ok referenceOut) :
    ∃ targetOut, Agrees referenceOut targetOut ∧
      IxVM.Consistency.InstallStep target (.opaqueDecl cv value) targetOut ∧
      DeclOpaqueRunJ rulesJ target cv value targetOut ∧
      ∀ (V : Type u) [SetTheory V], FoldInv V target → FoldInv V targetOut := by
  obtain ⟨targetOut, agreement, run⟩ := h.declOpaqueRun (declOpaqueRun_of checked)
  have rules := declOpaqueRun_rulesJ run
  refine ⟨targetOut, agreement, ?_, rules, foldInv_step_opaque rules⟩
  apply installStep_glue_opaque rules
  obtain ⟨ty, _, hcv, _, rfl⟩ := run
  obtain ⟨_, _, _, _, htb, htf, hat, _, _, _⟩ := hcv
  exact ⟨_, Env.find?_cons_self _ _, ⟨⟨rfl, rfl, annotateCore_to_annotates hat htf htb⟩, trivial⟩⟩

/-- Standard axioms and inert declarations follow the reference branch exactly. -/
theorem checkedAxiom_step {fuel : Nat} {ev : Evidences .anon} {referenceOut : Env .anon}
    {cv : ConstantVal .anon}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev source
      (.axiomDecl cv) = .ok referenceOut) :
    ∃ targetOut, Agrees referenceOut targetOut ∧
      IxVM.Consistency.InstallStep target (.axiomDecl cv) targetOut ∧
      DeclAxiomRunJ rulesJ target cv targetOut ∧
      ∀ (V : Type u) [SetTheory V], FoldInv V target → FoldInv V targetOut := by
  obtain ⟨targetOut, agreement, run⟩ := h.declAxiomRun (declAxiomRun_of checked)
  have rules := declAxiomRun_rulesJ run
  refine ⟨targetOut, agreement, ?_, rules, foldInv_step_axiom rules⟩
  apply installStep_glue_axiom rules
  intro changed
  rcases run with ⟨_, same⟩ | ⟨ty, hcv, rest⟩
  · exact (changed same).elim
  · rcases rest with ⟨_, rfl⟩ | ⟨_, _, _, _, same⟩
    · obtain ⟨_, _, _, _, htb, htf, hat, _, _, _⟩ := hcv
      exact ⟨_, Env.find?_cons_self _ _, ⟨⟨rfl, rfl, annotateCore_to_annotates hat htf htb⟩, trivial⟩⟩
    · exact (changed same).elim

/-- An accepted theorem stores the checked annotated value and preserves the opaque checker view. -/
theorem checkedThm_step {fuel : Nat} {ev : Evidences .anon} {referenceOut : Env .anon}
    {cv : ConstantVal .anon} {value : Expr .anon}
    (checked : checkDecl .verified (fueledOps .verified fuel) ev source
      (.thmDecl cv value) = .ok referenceOut) :
    ∃ targetOut, Agrees referenceOut targetOut ∧
      IxVM.Consistency.InstallStep target (.thmDecl cv value) targetOut ∧
      DeclThmRunJ rulesJ target cv value targetOut ∧
      ∀ (V : Type u) [SetTheory V], FoldInv V target → FoldInv V targetOut := by
  obtain ⟨ty, value', hcv, hprop, hv, rfl⟩ := declThmRun_of checked
  obtain ⟨stype, level, hi, hs, hz⟩ := hprop
  have targetCV := h.constantValRun hcv
  have targetValue := h.valueFrontRun hv
  have targetInfer : Ix.Kernel.inferTypeCore .verified target fuel 0 ty = .ok stype := by
    simpa only [h.inferTypeCore] using hi
  have targetSort : Ix.Kernel.ensureSortCore .verified target fuel 0 stype = .ok level := by
    simpa only [h.ensureSortCore] using hs
  have rules : DeclThmRunJ rulesJ target cv value
      ⟨.thmInfo ⟨cv.name, cv.levelParams, ty⟩ value' :: target.consts⟩ :=
    ⟨ty, value', constantValRun_rulesJ targetCV,
      ⟨stype, level, (verifiedRunMap fuel).infer targetInfer,
        (verifiedRunMap fuel).sort targetSort, (verifiedRunMap fuel).isZero hz⟩,
      valueFrontRun_rulesJ targetValue, rfl⟩
  refine ⟨_, h.consThm _ _ _, ?_, rules, foldInv_step_thm rules⟩
  apply installStep_glue_thm rules
  obtain ⟨_, _, _, _, htb, htf, hat, _, _, _⟩ := targetCV
  obtain ⟨hvb, hvf, hav, _, _, _⟩ := targetValue
  exact ⟨_, Env.find?_cons_self _ _, ⟨⟨rfl, rfl, annotateCore_to_annotates hat htf htb⟩,
    annotateCore_to_annotates hav hvf hvb⟩⟩

end IxVM.Refinement.Decl.ThmBodyView.Agrees
