/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Model.Annotated
import Ix.Theory.Store

/-!
# Primitive identity and the initial declaration policy

The profile admits ordinary safe definitions, theorems and opaque declarations
only with a checked body. Initialization excludes object-language axioms;
the separate standard admission branch realizes supported exact schemas. Empty-inductive
primitives are selected by exact references and complete declaration shapes.
This is the policy/reading layer; the semantic checker must validate each body
before publishing a declaration as accepted.
-/

namespace Ix.Theory.Certified

open Model

universe u
variable {β : Type u}

/-- The public configuration fixes these references. Diagnostic names and
semantic equality cannot select primitives or identify authenticated bytes. -/
structure PrimitiveSignature (β : Type u) where
  falseType : ConstRef β
  falseElim : ConstRef β
  distinct : falseType ≠ falseElim
  natType : Option (ConstRef β) := none

namespace PrimitiveSignature

def falseExpr (signature : PrimitiveSignature β) : VExpr β :=
  .const signature.falseType []

/-- `False.rec.{u} : (motive : False → Sort u) → (x : False) → motive x`. -/
def falseElimType (signature : PrimitiveSignature β) : VExpr β :=
  .forallE (.forallE signature.falseExpr (.sort (.param 0)))
    (.forallE signature.falseExpr (.app (.bvar 1) (.bvar 0)))

def falseDeclaration : Const β := .induct 0 0 0 (.sort .zero) [] .safe

def falseElimDeclaration (signature : PrimitiveSignature β) : Const β :=
  .recursor 1 0 0 1 0 signature.falseElimType [] false .safe

/-- A decidable match on the whole declaration, including rule and constructor
lists, safety, universe arity, and recursor counts. -/
def validate [DecidableEq β] (signature : PrimitiveSignature β) (store : Store β) : Bool :=
  store.lookup signature.falseType == some falseDeclaration &&
    store.lookup signature.falseElim == some signature.falseElimDeclaration

theorem validate_iff [DecidableEq β] (signature : PrimitiveSignature β) (store : Store β) :
    signature.validate store = true ↔
      store.lookup signature.falseType = some falseDeclaration ∧
      store.lookup signature.falseElim = some signature.falseElimDeclaration := by
  simp [validate]

def rename (mapping : AddressEquiv β γ) (signature : PrimitiveSignature β) :
    PrimitiveSignature γ where
  falseType := signature.falseType.rename mapping
  falseElim := signature.falseElim.rename mapping
  distinct := fun h => signature.distinct (ConstRef.rename_injective mapping h)
  natType := signature.natType.map (ConstRef.rename mapping)

@[simp] theorem falseExpr_rename (mapping : AddressEquiv β γ)
    (signature : PrimitiveSignature β) :
    (signature.rename mapping).falseExpr = signature.falseExpr.rename mapping := rfl

@[simp] theorem falseElimType_rename (mapping : AddressEquiv β γ)
    (signature : PrimitiveSignature β) :
    (signature.rename mapping).falseElimType = signature.falseElimType.rename mapping := rfl

/-- The fixed annotation of the eliminator's type. The motive space is always
a positive sort; the remaining binders follow the result universe parameter. -/
def falseElimReading (signature : PrimitiveSignature β) : AExpr β :=
  .forallE (.param 0)
    (.forallE .never (.const signature.falseType []) (.sort (.param 0)))
    (.forallE (.param 0) (.const signature.falseType []) (.app (.bvar 1) (.bvar 0)))

@[simp] theorem erase_falseElimReading (signature : PrimitiveSignature β) :
    signature.falseElimReading.erase = signature.falseElimType := rfl

theorem falseElimReading_scoped (signature : PrimitiveSignature β) :
    signature.falseElimReading.Scope 1 0 := by
  simp [falseElimReading, AExpr.Scope, PropWhen.WF, PropWhen.param, VLevel.WF]

end PrimitiveSignature

/-- Data retained only after the declaration-kind and structural checks.
The body has not yet passed the semantic type checker. -/
structure DefinitionReading (β : Type u) where
  universes : Nat
  kind : DefKind
  type : AExpr β
  body : AExpr β
  typeScope : type.Scope universes 0
  bodyScope : body.Scope universes 0

def DefinitionReading.erase (entry : DefinitionReading β) : Const β :=
  .defn entry.universes entry.kind entry.type.erase entry.body.erase .safe

/-- The definition-like declaration reading branch. Missing
opaque bodies, arbitrary axioms, unsafe declarations, and unmodeled primitive
kinds cannot acquire a successful reading through this function. -/
def readDefinition? (source : Const β) (typeTree bodyTree : AnnotationTree) :
    Option { entry : DefinitionReading β // entry.erase = source } :=
  match source with
  | .defn n kind type body .safe => do
    let type' ← readAnnotations? n 0 type typeTree
    let body' ← readAnnotations? n 0 body bodyTree
    return ⟨⟨n, kind, type'.val, body'.val, type'.property.2, body'.property.2⟩,
      by simp [DefinitionReading.erase, type'.property.1, body'.property.1]⟩
  | _ => none

theorem axiom_rejected (n : Nat) (type : VExpr β) (safety : Safety)
    (typeTree bodyTree : AnnotationTree) :
    readDefinition? (.axiom n type safety) typeTree bodyTree = none := rfl

theorem unsafe_definition_rejected (n : Nat) (kind : DefKind) (type body : VExpr β)
    (typeTree bodyTree : AnnotationTree) :
    readDefinition? (.defn n kind type body .unsafe) typeTree bodyTree = none := rfl

theorem partial_definition_rejected (n : Nat) (kind : DefKind) (type body : VExpr β)
    (typeTree bodyTree : AnnotationTree) :
    readDefinition? (.defn n kind type body .partial) typeTree bodyTree = none := rfl

end Ix.Theory.Certified
