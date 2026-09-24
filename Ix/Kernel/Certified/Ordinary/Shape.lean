/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Certified/Ordinary/Shape.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added;
K2: the input store and its exact-source facts are removed (comparing the
stored block with the generated one is the caller's check) and the recursor is
member 1 of the family's block; `CheckedShape` drops `exactSource`, and
`checkShape`, `checkConstructors`, and `checkRecursive` infer with
`Ix.Kernel.Infer` instead of validating witnesses.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Certified.Telescope
import Ix.Kernel.Model.Support
import Ix.Kernel.Const

/-!
An executable producer for the ordinary container shape class. All ordinary
fields precede recursive fields. A recursive field is a dependent function
over checked external domains returning this family with the same parameters
and checked indices. Its domains and indices cannot depend on other recursive
fields. Exact source comparison, formation, and universe bounds are checked
here; publishing recursor equations requires the later realization producer.
-/

namespace Ix.Kernel.Certified.Ordinary

open Model

universe u v

structure RecursiveField (β : Type u) where
  domains : List (AExpr β)
  indices : List (AExpr β)
deriving DecidableEq

structure Constructor (β : Type u) where
  fields : List (AExpr β)
  recursive : List (RecursiveField β)
  indices : List (AExpr β)
deriving DecidableEq

structure Shape (β : Type u) where
  universes : Nat
  parameters : List (AExpr β)
  indices : List (AExpr β)
  level : VLevel
  constructors : List (Constructor β)
deriving DecidableEq

variable {β : Type u}

def parameterVars (offset : Nat) : Nat → List (AExpr β)
  | 0 => []
  | n + 1 => .bvar (offset + n) :: parameterVars offset n

@[simp] theorem erase_parameterVars (offset count : Nat) :
    (parameterVars (β := β) offset count).map AExpr.erase = VExpr.bvarRevRange offset count := by
  induction count <;> simp_all [parameterVars, VExpr.bvarRevRange, AExpr.erase]

def Shape.familyApp (shape : Shape β) (source : β) (offset : Nat)
    (indices : List (AExpr β)) : AExpr β :=
  .appN (.const (.member source 0) (VLevel.params shape.universes))
    (parameterVars offset shape.parameters.length ++ indices)

def Shape.type (shape : Shape β) : AExpr β :=
  .forallN .never (shape.parameters ++ shape.indices) (.sort shape.level)

def RecursiveField.type (field : RecursiveField β) (shape : Shape β)
    (source : β) (ordinaryFields : Nat) : AExpr β :=
  .forallN (zeroCondition shape.level) field.domains
    (shape.familyApp source (ordinaryFields + field.domains.length) field.indices)

def recursiveTypesFrom (shape : Shape β) (source : β) (ordinaryFields : Nat)
    (fields : List (RecursiveField β)) (offset : Nat) : List (AExpr β) :=
  (fields.zipIdx offset).map fun (field, previous) =>
    (field.type shape source ordinaryFields).liftN previous

def Constructor.recursiveTypes (ctor : Constructor β) (shape : Shape β) (source : β) : List (AExpr β) :=
  recursiveTypesFrom shape source ctor.fields.length ctor.recursive 0

def Constructor.type (ctor : Constructor β) (shape : Shape β) (source : β) : AExpr β :=
  .forallN (zeroCondition shape.level) shape.parameters <|
    .forallN (zeroCondition shape.level) ctor.fields <|
      .forallN (zeroCondition shape.level) (ctor.recursiveTypes shape source) <|
        shape.familyApp source (ctor.fields.length + ctor.recursive.length)
          (ctor.indices.map (AExpr.liftN ctor.recursive.length ·))

def Constructor.source (ctor : Constructor β) (shape : Shape β) (source : β) : Ctor β :=
  ⟨shape.universes, shape.parameters.length, ctor.fields.length + ctor.recursive.length,
    (ctor.type shape source).erase, .safe⟩

def Shape.source (shape : Shape β) (source : β) : Const β :=
  .induct shape.universes shape.parameters.length shape.indices.length shape.type.erase
    (shape.constructors.map (Constructor.source · shape source)) .safe

def Shape.references (shape : Shape β) (source : β) : List (ConstRef β) :=
  .member source 0 :: (List.range shape.constructors.length).map (.ctor source 0 ·)

def Shape.parameterContext (shape : Shape β) : Context β := Telescope.context [] shape.parameters

def Constructor.context (ctor : Constructor β) (shape : Shape β) : Context β :=
  Telescope.context shape.parameterContext ctor.fields

def RecursiveEvidence (entries : Environment β) (shape : Shape β) (ctor : Constructor β)
    (field : RecursiveField β) : Prop :=
  (∀ e ∈ field.domains ++ field.indices, e.ReferencesIn entries) ∧
  Telescope.Formed.{u,v} entries (ctor.context shape) field.domains ∧
  TelescopeBound.{u,v} entries (ctor.context shape) field.domains (some shape.level) ∧
  ArgumentsFit.{u,v} entries (Telescope.context (ctor.context shape) field.domains)
    (Telescope.lift (ctor.fields.length + field.domains.length) shape.indices) field.indices

def ConstructorEvidence (entries : Environment β) (shape : Shape β) (ctor : Constructor β) : Prop :=
  (∀ e ∈ ctor.fields ++ ctor.indices, e.ReferencesIn entries) ∧
  Telescope.Formed.{u,v} entries shape.parameterContext ctor.fields ∧
  TelescopeBound.{u,v} entries shape.parameterContext ctor.fields (some shape.level) ∧
  ArgumentsFit.{u,v} entries (ctor.context shape)
    (Telescope.lift ctor.fields.length shape.indices) ctor.indices ∧
  ∀ field ∈ ctor.recursive, RecursiveEvidence.{u,v} entries shape ctor field

/-- This is checked shape/formation evidence, not an admitted environment or
a premise asserting that an inductive has a model. The exact comparison of the
generated declarations with the stored block is the caller's check. -/
structure CheckedShape (entries : Environment β) (source : β)
    (shape : Shape β) : Prop where
  fresh : ∀ r ∈ shape.references source, entries r = none
  references : ∀ e ∈ shape.parameters ++ shape.indices, e.ReferencesIn entries
  scope : shape.type.Scope shape.universes 0
  constructorScope : ∀ ctor ∈ shape.constructors, (ctor.type shape source).Scope shape.universes 0
  parameters : Telescope.Formed.{u,v} entries [] shape.parameters
  indices : Telescope.Formed.{u,v} entries shape.parameterContext shape.indices
  constructors : ∀ ctor ∈ shape.constructors, ConstructorEvidence.{u,v} entries shape ctor

variable [DecidableEq β]

def checkRecursive (fuel : Nat) (entries : Environment β) (shape : Shape β)
    (ctor : Constructor β) : (fields : List (RecursiveField β)) →
      Option (CheckedClaim.{u} (∀ field ∈ fields, RecursiveEvidence.{u,v} entries shape ctor field))
  | [] => some ⟨by simp⟩
  | field :: fields =>
    if hrefs : ∀ e ∈ field.domains ++ field.indices, e.ReferencesIn entries then do
      let domains ← checkTelescope.{u,v} fuel entries (some shape.level) (ctor.context shape) field.domains
      let indices ← checkArguments.{u,v} fuel entries
        (Telescope.context (ctor.context shape) field.domains)
        (Telescope.lift (ctor.fields.length + field.domains.length) shape.indices) field.indices
      let rest ← checkRecursive fuel entries shape ctor fields
      return ⟨by
        intro field' hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact ⟨hrefs, domains.down.1, domains.down.2, indices.down⟩
        · exact rest.down field' hf⟩
    else none

def checkConstructors (fuel : Nat) (entries : Environment β) (shape : Shape β) :
    (ctors : List (Constructor β)) →
      Option (CheckedClaim.{u} (∀ ctor ∈ ctors, ConstructorEvidence.{u,v} entries shape ctor))
  | [] => some ⟨by simp⟩
  | ctor :: ctors =>
    if hrefs : ∀ e ∈ ctor.fields ++ ctor.indices, e.ReferencesIn entries then do
      let fields ← checkTelescope.{u,v} fuel entries (some shape.level) shape.parameterContext ctor.fields
      let indices ← checkArguments.{u,v} fuel entries (ctor.context shape)
        (Telescope.lift ctor.fields.length shape.indices) ctor.indices
      let recursive ← checkRecursive fuel entries shape ctor ctor.recursive
      let rest ← checkConstructors fuel entries shape ctors
      return ⟨by
        intro ctor' hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨hrefs, fields.down.1, fields.down.2, indices.down, recursive.down⟩
        · exact rest.down ctor' hc⟩
    else none

def checkShape (fuel : Nat) (entries : Environment β) (source : β) (shape : Shape β) :
    Option (CheckedClaim.{u} (CheckedShape.{u,v} entries source shape)) :=
  if hfresh : ∀ r ∈ shape.references source, entries r = none then
    if hrefs : ∀ e ∈ shape.parameters ++ shape.indices, e.ReferencesIn entries then
      if hscope : shape.type.Scope shape.universes 0 then
        if hctors : ∀ ctor ∈ shape.constructors, (ctor.type shape source).Scope shape.universes 0 then do
          let parameters ← checkTelescope.{u,v} fuel entries none [] shape.parameters
          let indices ← checkTelescope.{u,v} fuel entries none shape.parameterContext shape.indices
          let constructors ← checkConstructors fuel entries shape shape.constructors
          return ⟨⟨hfresh, hrefs, hscope, hctors, parameters.down.1, indices.down.1, constructors.down⟩⟩
        else none
      else none
    else none
  else none

theorem checkShape_sound {fuel : Nat} {entries : Environment β} {source : β} {shape : Shape β}
    {result} (_ : checkShape.{u,v} fuel entries source shape = some result) :
    CheckedShape.{u,v} entries source shape := result.down

end Ix.Kernel.Certified.Ordinary
