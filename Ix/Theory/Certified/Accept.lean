/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Ordinary.Admission

/-!
# Closed acceptance of the certified profile

Acceptance checks the exact primitive declarations, a dependency-ordered list
of safe definitions and modeled ordinary blocks, the original proof and proposition readings,
and both typing certificates. It constructs its dependency model and starts
from the empty context. This is an abstract Ix-syntax acceptance result;
serialized bytes, Ix.Kernel execution, claims, and proving backends need their own
refinement theorems.
-/

namespace Ix.Theory.Certified

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

structure ProofInput (β : Type u) where
  store : Store β
  universes : Nat
  proof : VExpr β
  proposition : VExpr β

structure ProofWitness (β : Type u) where
  declarations : List (DeclarationWitness β)
  proofAnnotations : AnnotationTree
  propositionAnnotations : AnnotationTree
  proofWitness : TypingWitness β
  propositionWitness : TypingWitness β

structure CheckedProof (signature : PrimitiveSignature β) (input : ProofInput β) where
  environment : AdmittedEnvironment.{u,v} signature input.store
  proof : Reading input.universes 0 input.proof
  proposition : Reading input.universes 0 input.proposition
  proofReferences : proof.val.ReferencesIn environment.entries
  propositionReferences : proposition.val.ReferencesIn environment.entries
  typing : TypingClaim.{u,v} environment.entries [] proof.val proposition.val
  isProp : TypingClaim.{u,v} environment.entries [] proposition.val (.sort .zero)

def checkProofCertified (fuel : Nat) (signature : PrimitiveSignature β)
    (input : ProofInput β) (witness : ProofWitness β) :
    Option (CheckedProof.{u,v} signature input) := do
  let initial ← initialize? signature input.store
  let declarations ← admitDeclarations? fuel initial witness.declarations
  let proof ← readAnnotations? input.universes 0 input.proof witness.proofAnnotations
  let proposition ← readAnnotations? input.universes 0 input.proposition witness.propositionAnnotations
  if he : proof.val.ReferencesIn declarations.val.entries then
    if hP : proposition.val.ReferencesIn declarations.val.entries then do
      let hp ← verifyType.{u,v} fuel input.universes declarations.val.entries []
        proposition.val (.sort .zero) witness.propositionWitness
      let ht ← verifyType.{u,v} fuel input.universes declarations.val.entries []
        proof.val proposition.val witness.proofWitness
      return ⟨declarations.val, proof, proposition, he, hP, ht.down, hp.down⟩
    else none
  else none

def acceptsCertified (fuel : Nat) (signature : PrimitiveSignature β)
    (input : ProofInput β) (witness : ProofWitness β) : Bool :=
  (checkProofCertified.{u,v} fuel signature input witness).isSome

/-- Acceptance constructs the model; it does not ask the caller to supply a
realization of unchecked declarations, annotations, or a nonempty context. -/
theorem accepted_has_model {fuel : Nat} {signature : PrimitiveSignature β}
    {input : ProofInput β} {witness : ProofWitness β}
    (h : acceptsCertified.{u,v} fuel signature input witness = true)
    (V : Type v) [SetTheory V] (levels : List Nat) (env : Nat → V) :
    ∃ result : CheckedProof.{u,v} signature input,
      checkProofCertified fuel signature input witness = some result ∧
      ∃ constants : Assignment β V, signature.Compatible result.environment.entries constants ∧
        WellDenoted constants levels env result.proof.val ∧
        WellDenoted constants levels env result.proposition.val ∧
        interp constants levels env result.proof.val ∈ˢ
          interp constants levels env result.proposition.val := by
  unfold acceptsCertified at h
  cases hc : checkProofCertified.{u,v} fuel signature input witness with
  | none => simp [hc] at h
  | some result =>
    obtain ⟨constants, hM⟩ := result.environment.model V
    exact ⟨result, rfl, constants, hM,
      result.typing V constants hM.realizes levels env (Context.valid_nil constants levels env)⟩

/-- The accepted proposition is inhabited in every compatible interpretation
of the checked dependency interface, not only in the model chosen above. -/
theorem accepted_proof_sound {fuel : Nat} {signature : PrimitiveSignature β}
    {input : ProofInput β} {witness : ProofWitness β}
    (h : acceptsCertified.{u,v} fuel signature input witness = true) :
    ∃ result : CheckedProof.{u,v} signature input,
      checkProofCertified fuel signature input witness = some result ∧
      ∀ (V : Type v) [SetTheory V] (constants : Assignment β V),
        signature.Compatible result.environment.entries constants → ∀ levels env,
          interp constants levels env result.proof.val ∈ˢ
            interp constants levels env result.proposition.val := by
  unfold acceptsCertified at h
  cases hc : checkProofCertified.{u,v} fuel signature input witness with
  | none => simp [hc] at h
  | some result =>
    refine ⟨result, rfl, ?_⟩
    intro V _ constants hM levels env
    exact (result.typing V constants hM.realizes levels env
      (Context.valid_nil constants levels env)).2.2

theorem no_proof_of_False {fuel : Nat} {signature : PrimitiveSignature β}
    {input : ProofInput β} {witness : ProofWitness β}
    (V : Type v) [SetTheory V]
    (hFalse : input.proposition = signature.falseExpr)
    (h : acceptsCertified.{u,v} fuel signature input witness = true) : False := by
  obtain ⟨result, _, constants, hM, _, _, hmem⟩ :=
    accepted_has_model h V [] (fun _ => empty)
  have herase : result.proposition.val.erase = .const signature.falseType [] :=
    result.proposition.property.1.trans hFalse
  have he := AExpr.eq_const_of_erase_eq herase
  rw [he] at hmem
  simp only [interp, List.map_nil, hM.falseValue] at hmem
  exact not_mem_empty _ hmem

/-- A source-level empty proposition can also be reached through certified
definitions or conversions. Its semantic emptiness contradicts acceptance. -/
theorem no_proof_of_empty {fuel : Nat} {signature : PrimitiveSignature β}
    {input : ProofInput β} {witness : ProofWitness β}
    (V : Type v) [SetTheory V]
    (hempty : ∀ result : CheckedProof.{u,v} signature input,
      checkProofCertified fuel signature input witness = some result →
      ∀ constants : Assignment β V, signature.Compatible result.environment.entries constants →
        interp constants [] (fun _ => empty) result.proposition.val = empty)
    (h : acceptsCertified.{u,v} fuel signature input witness = true) : False := by
  obtain ⟨result, hc, constants, hM, _, _, hmem⟩ :=
    accepted_has_model h V [] (fun _ => empty)
  rw [hempty result hc constants hM] at hmem
  exact not_mem_empty _ hmem

end Ix.Theory.Certified
