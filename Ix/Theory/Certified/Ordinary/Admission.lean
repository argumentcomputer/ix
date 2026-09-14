/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certified.Standard.Admission
import Ix.Theory.Certified.Quotient.Admission
import Ix.Theory.Certified.Structure.Admission
import Ix.Theory.Certified.Natural.Admission
import Ix.Theory.Certified.Modeled.Admission

namespace Ix.Theory.Certified

open Model

universe u v
variable {β : Type u} [DecidableEq β]

/-- Publish the family, constructors, recursor, and its complete equations
atomically, after their formation and semantic realization have been produced. -/
def checkOrdinaryExtension? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) (witness : Ordinary.BlockWitness β) :
    Option (CheckedExtension.{u,v} signature store state) := do
  let checked ← Ordinary.checkBlock.{u,v} fuel state.entries store witness
  let shape := witness.shape.shape
  let entries := shape.publishedEnvironment state.entries witness.source witness.recursor witness.mode
  have extension : Extends.{u,v} signature state.entries entries := by
    constructor
    · intro r entry hr
      exact Ordinary.Shape.publishedEnvironment_old checked.down hr
    · intro V _ constants hM
      let constants' := shape.recursorAssignment constants witness.source witness.recursor witness.mode
      have hnew := Ordinary.Shape.publishedAssignment_realizes checked.down state.wf constants hM.realizes
      have hagree := Ordinary.Shape.publishedAssignment_agrees checked.down constants
      exact ⟨constants', hM.extend signature state.present hnew hagree, hagree⟩
  let result : CheckedInterface signature := {
    entries
    wf := Ordinary.Shape.publishedEnvironment_wf checked.down state.wf
    present := ⟨extension.lookup _ _ state.present.1, extension.lookup _ _ state.present.2⟩
  }
  return {
    result, extension
    source := by
      intro r entry hr
      dsimp only [result] at hr
      rcases Ordinary.publishedEntry_source checked.down hr with hold | hnew
      · exact Or.inl hold
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hnew))))
  }

def admitOrdinary? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) (witness : Ordinary.BlockWitness β) :
    Option { result : AdmittedEnvironment.{u,v} signature store //
      Extends.{u,v} signature state.entries result.entries } := do
  let checked ← checkOrdinaryExtension?.{u,v} fuel (store := store) state.interface witness
  return checked.admit state

/-- Untrusted declaration choices in dependency order. A signature stage is
never itself an element of this public admission list. -/
inductive DeclarationWitness (β : Type u) where
  | definition (witness : DefinitionWitness β)
  | ordinary (witness : Ordinary.BlockWitness β)
  | standard (witness : Standard.Witness β)
  | quotient (witness : Quotient.Witness β)
  | structure (witness : Structure.Witness β)
  | natural (witness : Ordinary.BlockWitness β)
  | modeled (witness : Modeled.Witness β)

def checkDeclarationExtension? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) : DeclarationWitness β →
      Option (CheckedExtension.{u,v} signature store state)
  | .definition witness => checkDefinitionExtension? fuel state witness
  | .ordinary witness => checkOrdinaryExtension? fuel state witness
  | .standard witness => checkStandardExtension? fuel state witness
  | .quotient witness => checkQuotientExtension? fuel state witness
  | .structure witness => checkStructureExtension? fuel state witness
  | .natural witness => checkNaturalExtension? fuel state witness
  | .modeled witness => checkModeledExtension? fuel state witness

def checkDeclarationExtensions? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : CheckedInterface signature) : List (DeclarationWitness β) →
      Option (CheckedExtension.{u,v} signature store state)
  | [] => some (CheckedExtension.refl state)
  | witness :: rest => do
    let step ← checkDeclarationExtension? fuel state witness
    let rest ← checkDeclarationExtensions? fuel step.result rest
    return step.trans rest

def admitDeclaration? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) : DeclarationWitness β →
      Option { result : AdmittedEnvironment.{u,v} signature store //
        Extends.{u,v} signature state.entries result.entries }
  | .definition witness => admitDefinition? fuel state witness
  | .ordinary witness => admitOrdinary? fuel state witness
  | .standard witness => admitStandard? fuel state witness
  | .quotient witness => admitQuotient? fuel state witness
  | .structure witness => admitStructure? fuel state witness
  | .natural witness => admitNatural? fuel state witness
  | .modeled witness => admitModeled? fuel state witness

def admitDeclarations? (fuel : Nat) {signature : PrimitiveSignature β} {store : Store β}
    (state : AdmittedEnvironment.{u,v} signature store) (witness : List (DeclarationWitness β)) :
    Option { result : AdmittedEnvironment.{u,v} signature store //
      Extends.{u,v} signature state.entries result.entries } := do
  let checked ← checkDeclarationExtensions?.{u,v} fuel (store := store) state.interface witness
  return checked.admit state

theorem admitOrdinary?_extends {fuel : Nat} {signature : PrimitiveSignature β} {store : Store β}
    {state : AdmittedEnvironment.{u,v} signature store} {witness : Ordinary.BlockWitness β} {result}
    (_ : admitOrdinary? fuel state witness = some result) :
    Extends.{u,v} signature state.entries result.val.entries := result.property

end Ix.Theory.Certified
