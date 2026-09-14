/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Suggest
import Ix.Theory.Certified.Ordinary.Checked

/-! Untrusted witness construction for a proposed ordinary description. -/

namespace Ix.Theory.Certificate.Ordinary

open Model Certified Certified.Ordinary

universe u
variable {β : Type u} [DecidableEq β]
variable [Hints β]

def domains? (fuel n : Nat) (entries : Environment β) :
    Context β → List (AExpr β) → Option (List (DomainWitness β))
  | _, [] => some []
  | Γ, A :: rest => do
    let typed ← inferAnnotated? fuel n entries Γ A
    let .sort level := typed.type | none
    let tail ← domains? fuel n entries (Γ.push A) rest
    return ⟨level, typed.witness⟩ :: tail

def arguments? (fuel n : Nat) (entries : Environment β) (Γ : Context β) :
    List (AExpr β) → List (AExpr β) → Option (List (TypingWitness β))
  | [], [] => some []
  | A :: domains, a :: args => do
    let typed ← inferAnnotated? fuel n entries Γ a
    let witness ← castWith? fuel n entries Γ typed A
    let tail ← arguments? fuel n entries Γ (Telescope.inst a domains) args
    return witness :: tail
  | _, _ => none

def recursive? (fuel : Nat) (entries : Environment β) (shape : Shape β)
    (ctor : Constructor β) (field : RecursiveField β) : Option (RecursiveWitness β) := do
  let domains ← domains? fuel shape.universes entries (ctor.context shape) field.domains
  let indices ← arguments? fuel shape.universes entries
    (Telescope.context (ctor.context shape) field.domains)
    (Telescope.lift (ctor.fields.length + field.domains.length) shape.indices) field.indices
  return ⟨domains, indices⟩

def constructor? (fuel : Nat) (entries : Environment β) (shape : Shape β)
    (ctor : Constructor β) : Option (ConstructorWitness β) := do
  let fields ← domains? fuel shape.universes entries shape.parameterContext ctor.fields
  let indices ← arguments? fuel shape.universes entries (ctor.context shape)
    (Telescope.lift ctor.fields.length shape.indices) ctor.indices
  let recursive ← ctor.recursive.mapM (recursive? fuel entries shape ctor)
  return ⟨fields, indices, recursive⟩

def shape? (fuel : Nat) (entries : Environment β) (shape : Shape β) : Option (ShapeWitness β) := do
  let parameters ← domains? fuel shape.universes entries [] shape.parameters
  let indices ← domains? fuel shape.universes entries shape.parameterContext shape.indices
  let constructors ← shape.constructors.mapM (constructor? fuel entries shape)
  return ⟨shape, parameters, indices, constructors⟩

def type? (fuel n : Nat) (entries : Environment β) (type : AExpr β) : Option (Shape.TypeWitness β) := do
  let typed ← inferAnnotated? fuel n entries [] type
  let .sort level := typed.type | none
  return ⟨level, typed.witness⟩

def constructorTypes? (fuel : Nat) (entries : Environment β) (shape : Shape β) (source : β) :
    Option (List (Shape.TypeWitness β)) :=
  shape.constructors.mapM fun ctor => type? fuel shape.universes (shape.familyEnvironment entries source)
    (ctor.type shape source)

def recursorType? (fuel : Nat) (entries : Environment β) (shape : Shape β) (source : β)
    (mode : Inductive.ElimMode) : Option (Shape.TypeWitness β) :=
  type? fuel (mode.recUvars shape.universes) (shape.constructorEnvironment entries source) (shape.recursorType source mode)

def rule? (fuel : Nat) (entries : Environment β) (shape : Shape β) (source recursor : β)
    (mode : Inductive.ElimMode) (i : Nat) (ctor : Constructor β) : Option (RuleWitness β) := do
  let n := mode.recUvars shape.universes
  let type := shape.ruleType source mode i ctor
  let typed ← type? fuel n entries type
  let lhs ← inferAnnotated? fuel n entries [] (shape.ruleLhs source recursor mode i ctor)
  let lh ← castWith? fuel n entries [] lhs type
  let rhs ← inferAnnotated? fuel n entries [] (shape.ruleRhs source recursor mode i ctor)
  let rh ← castWith? fuel n entries [] rhs type
  return ⟨typed.level, typed.witness, lh, rh⟩

def rules? (fuel : Nat) (entries : Environment β) (shape : Shape β) (source recursor : β)
    (mode : Inductive.ElimMode) : Option (List (RuleWitness β)) :=
  shape.constructors.zipIdx.mapM fun (ctor, i) => rule? fuel
    (shape.recursorEnvironment entries source recursor mode) shape source recursor mode i ctor

def block? (fuel : Nat) (entries : Environment β) (shape : Shape β) (source recursor : β)
    (mode : Inductive.ElimMode) : Option (BlockWitness β) := do
  let sw ← shape? fuel entries shape
  let ct ← constructorTypes? fuel entries shape source
  let rt ← recursorType? fuel entries shape source mode
  let rs ← rules? fuel entries shape source recursor mode
  return ⟨source, recursor, sw, mode, ct, rt, rs⟩

end Ix.Theory.Certificate.Ordinary
