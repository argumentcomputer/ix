/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Ordinary.Admission

/-! Certification of requested declarations, including data declarations.
Logical proof acceptance additionally checks the requested proposition is in
Prop. A declaration certificate constructs a compatible model for every
requested type, body and admitted computation rule. -/

namespace Ix.Theory.Certified

open Model Model.SetTheory

universe u v
variable {β : Type u} [DecidableEq β]

structure CheckedStore (signature : PrimitiveSignature β) (store : Store β)
    (targets : List (ConstRef β)) where
  environment : AdmittedEnvironment.{u,v} signature store
  targetsPresent : ∀ r ∈ targets, (environment.entries r).isSome = true

def checkStoreCertified (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (targets : List (ConstRef β)) (witness : List (DeclarationWitness β)) :
    Option (CheckedStore.{u,v} signature store targets) := do
  let initial ← initialize? signature store
  let admitted ← admitDeclarations? fuel initial witness
  if h : targets.all (fun r => (admitted.val.entries r).isSome) = true then
    return ⟨admitted.val, List.all_eq_true.mp h⟩
  else none

def acceptsStoreCertified (fuel : Nat) (signature : PrimitiveSignature β) (store : Store β)
    (targets : List (ConstRef β)) (witness : List (DeclarationWitness β)) : Bool :=
  (checkStoreCertified.{u,v} fuel signature store targets witness).isSome

/-- Successful admission constructs one compatible model for the entire
requested interface, at every permitted universe instance. -/
theorem accepted_store_has_model {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {targets : List (ConstRef β)} {witness : List (DeclarationWitness β)}
    (h : acceptsStoreCertified.{u,v} fuel signature store targets witness = true)
    (V : Type v) [SetTheory V] :
    ∃ result : CheckedStore.{u,v} signature store targets,
      checkStoreCertified fuel signature store targets witness = some result ∧
      ∃ constants : Assignment β V,
        signature.Compatible result.environment.entries constants ∧
        ∀ r ∈ targets, ∃ entry, result.environment.entries r = some entry ∧
          EntrySource signature store r entry ∧
          ∀ levels, levels.length = entry.universes → ∀ env : Nat → V,
            WellDenoted constants levels env entry.type ∧
            constants r levels ∈ˢ interp constants levels env entry.type := by
  unfold acceptsStoreCertified at h
  cases hc : checkStoreCertified.{u,v} fuel signature store targets witness with
  | none => simp [hc] at h
  | some result =>
    obtain ⟨constants, hM⟩ := result.environment.model V
    refine ⟨result, rfl, constants, hM, ?_⟩
    intro r hr
    have present := result.targetsPresent r hr
    cases he : result.environment.entries r with
    | none => simp [he] at present
    | some entry =>
      refine ⟨entry, rfl, result.environment.source r entry he, ?_⟩
      intro levels hl env
      exact ⟨hM.realizes.typeValid r entry he levels hl env,
        hM.realizes.member r entry he levels hl env⟩

end Ix.Theory.Certified
