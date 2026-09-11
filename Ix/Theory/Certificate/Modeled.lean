/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Quotient
import Ix.Theory.Certified.Modeled.Admission

/-! Untrusted construction of exact model-companion certificates. Model
declarations are ordinary earlier checked declarations. This builder derives
all source headers and rule statements from the store, reads annotations in
the mapped model environment, and searches for conversion or a supplied
propositional proof. Its output must pass public declaration admission.
-/

namespace Ix.Theory.Certificate.Modeled

open Model Certified Certified.Modeled

universe u
variable {β : Type u} [DecidableEq β] [Hints β]

structure ProofHint (β : Type u) where
  equality : ConstRef β
  reflexivity : ConstRef β
  recursor : ConstRef β
  proof : VExpr β

/-- A finite untrusted package selects earlier model declarations and optional
equation proofs. The store remains the source of every original statement. -/
structure Candidate (β : Type u) where
  source : β
  recursors : List (ConstRef β)
  models : List (ConstRef β)
  proofs : List (ConstRef β × List (Option (ProofHint β))) := []

def Candidate.hint (candidate : Candidate β) (ref : ConstRef β) (index : Nat) : Option (ProofHint β) := do
  let (_, proofs) ← candidate.proofs.find? (fun pair => pair.1 == ref)
  (proofs[index]?).join

def Candidate.proofReferences (candidate : Candidate β) : List (ConstRef β) :=
  candidate.proofs.flatMap fun (_, proofs) => proofs.flatMap fun proof =>
    match proof with
    | none => []
    | some proof => [proof.equality, proof.reflexivity, proof.recursor] ++ proof.proof.refs

def target (pairs : List (ConstRef β × ConstRef β)) (ref : ConstRef β) : ConstRef β :=
  ((pairs.find? (fun pair => pair.1 == ref)).map (·.2)).getD ref

def readMapped? (fuel n : Nat) (entries : Environment β)
    (mapping : ConstRef β → ConstRef β) (raw : VExpr β) : Option (AExpr β) := do
  let inferred ← inferSource? fuel n entries [] (raw.mapRefs mapping)
  let annotated ← readAnnotations? n 0 raw (annotations inferred.expression)
  if annotated.val.mapRefs mapping = inferred.expression then some annotated.val else none

def rule? (fuel : Nat) (entries : Environment β) (mapping : ConstRef β → ConstRef β)
    (raw : RawRule β) (hint : Option (ProofHint β)) :
    Option (Signature.Rule β × EquationWitness β) := do
  let type ← readMapped? fuel raw.universes entries mapping raw.type
  let lhs ← readMapped? fuel raw.universes entries mapping raw.lhs
  let rhs ← readMapped? fuel raw.universes entries mapping raw.rhs
  let rule : Signature.Rule β := ⟨raw.universes, type, lhs, rhs⟩
  let mapped : Signature.Rule β := ⟨raw.universes, type.mapRefs mapping, lhs.mapRefs mapping, rhs.mapRefs mapping⟩
  let formation ← Quotient.ruleWitness? fuel entries mapped
  match hint with
  | none => do
    let proof ← conversion? fuel raw.universes entries [] mapped.lhs mapped.rhs
    return (rule, ⟨formation, .conversion proof⟩)
  | some hint => do
    let inferred ← inferSource? fuel raw.universes entries [] hint.proof
    let expected := Basis.Equality.applied hint.equality formation.level mapped.type mapped.lhs mapped.rhs
    let proof ← castWith? fuel raw.universes entries [] inferred expected
    return (rule, ⟨formation, .propositional hint.equality hint.reflexivity hint.recursor inferred.expression proof⟩)

def companion? (fuel : Nat) (entries : Environment β) (store : Store β)
    (pairs : List (ConstRef β × ConstRef β)) (ref model : ConstRef β)
    (hints : Nat → Option (ProofHint β)) : Option (Companion β × List (EquationWitness β)) := do
  let raw ← store.type ref
  let some universes := store.uvars ref | none
  let modelEntry ← entries model
  if modelEntry.universes != universes then none else do
    let reading ← readAnnotations? universes 0 raw (annotations modelEntry.type)
    if reading.val.mapRefs (target pairs) != modelEntry.type then none else do
      let rawRules ← sourceRules? store ref
      let rules ← rawRules.zipIdx.mapM fun (raw, index) => rule? fuel entries (target pairs) raw (hints index)
      return (⟨⟨ref, universes, reading.val⟩, model, rules.map (·.1)⟩, rules.map (·.2))

/-- Model targets are positional in the actual source layout. Duplicated
targets are allowed; their exact types and equations still undergo the same
check, which supplies semantic justification for auxiliary merging. -/
def witness? (fuel : Nat) (entries : Environment β) (store : Store β) (source : β)
    (recursors models : List (ConstRef β))
    (hints : ConstRef β → Nat → Option (ProofHint β) := fun _ _ => none) : Option (Witness β) := do
  let refs ← sourceRefs? store source recursors
  if refs.length != models.length then none else do
    let pairs := refs.zip models
    let checked ← pairs.mapM fun (ref, model) => companion? fuel entries store pairs ref model (hints ref)
    return ⟨source, recursors, checked.map (·.1), checked.map (·.2)⟩

def Candidate.witness? (candidate : Candidate β) (fuel : Nat) (entries : Environment β)
    (store : Store β) : Option (Witness β) :=
  Modeled.witness? fuel entries store candidate.source candidate.recursors candidate.models candidate.hint

end Ix.Theory.Certificate.Modeled
