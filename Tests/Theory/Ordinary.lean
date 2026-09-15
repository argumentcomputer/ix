/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Theory.Certificate.Ordinary
import Ix.Theory.Certified.Ordinary.LargeElim
import Ix.Theory.Certified.Ordinary.RecursorSyntax
import Tests.Theory.RecursorGoldens

open Ix.Theory

/-! These exercise shape and evidence production. They do not claim closed
proof acceptance or VM coverage of inductives. -/

namespace Tests.Theory.Ordinary

open Model Certified Certified.Ordinary

private structure SourceFamily where
  type : VExpr Nat
  ctors : List (Ctor Nat)

def natSourceBlock : Nat := 10
def functionalSourceBlock : Nat := 50
def indexedSourceBlock : Nat := 60

private def natType : VExpr Nat := .const (.member natSourceBlock 0) []
private def natFamily : SourceFamily := ⟨.sort (.succ .zero), [
  ⟨0, 0, 0, natType, .safe⟩,
  ⟨0, 0, 1, .forallE natType natType, .safe⟩]⟩

private def functionalType : VExpr Nat := .const (.member functionalSourceBlock 0) []
private def functionalFamily : SourceFamily := ⟨.sort (.succ .zero), [
  ⟨0, 0, 1, .forallE (.forallE (.sort .zero) functionalType) functionalType, .safe⟩]⟩

private def indexedFamily : SourceFamily :=
  ⟨.forallE (.sort (.succ .zero)) (.sort (.succ .zero)), [
    ⟨0, 0, 0, .app (.const (.member indexedSourceBlock 0) []) (.sort .zero), .safe⟩]⟩

def noEntries : Environment Nat := fun _ => none

def singletonStore (source : Nat) (decl : Const Nat) : Store Nat where
  dom := [source]
  nodup := by simp
  blocks b := if b = source then some ⟨[decl]⟩ else none
  mem_dom b := by by_cases h : b = source <;> simp [h]

def checked (source : Nat) (decl : Const Nat) (shape : Shape Nat) : Bool :=
  match Certificate.Ordinary.shape? 100 noEntries shape with
  | none => false
  | some witness => (checkShape.{0,0} 100 noEntries (singletonStore source decl) source witness).isSome

def largeChecked (shape : Shape Nat) : Bool :=
  match Certificate.Ordinary.shape? 100 noEntries shape with
  | none => false
  | some witness => (checkLarge.{0,0} 100 noEntries witness).isSome

def natShape : Shape Nat :=
  ⟨0, [], [], .succ .zero, [⟨[], [], []⟩, ⟨[], [⟨[], []⟩], []⟩]⟩

#guard natShape.source natSourceBlock =
  .induct 0 0 0 natFamily.type natFamily.ctors .safe
#guard checked natSourceBlock (.induct 0 0 0 natFamily.type natFamily.ctors .safe) natShape
#guard largeChecked natShape

def functionalShape : Shape Nat :=
  ⟨0, [], [], .succ .zero, [⟨[], [⟨[.sort .zero], []⟩], []⟩]⟩

#guard functionalShape.source functionalSourceBlock =
  .induct 0 0 0 functionalFamily.type functionalFamily.ctors .safe
#guard checked functionalSourceBlock
  (.induct 0 0 0 functionalFamily.type functionalFamily.ctors .safe) functionalShape

def indexedShape : Shape Nat :=
  ⟨0, [], [.sort (.succ .zero)], .succ .zero, [⟨[], [], [.sort .zero]⟩]⟩

#guard indexedShape.source indexedSourceBlock =
  .induct 0 0 1 indexedFamily.type indexedFamily.ctors .safe
#guard checked indexedSourceBlock
  (.induct 0 0 1 indexedFamily.type indexedFamily.ctors .safe) indexedShape

def listShape : Shape Nat :=
  ⟨1, [.sort (.succ (.param 0))], [], .succ (.param 0),
    [⟨[], [], []⟩, ⟨[.bvar 0], [⟨[], []⟩], []⟩]⟩

def listType : VExpr Nat := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
def listDecl : Const Nat := .induct 1 1 0 listType [
  ⟨1, 1, 0, .forallE (.sort (.succ (.param 0))) (.app (.const (.member 70 0) [.param 0]) (.bvar 0)), .safe⟩,
  ⟨1, 1, 2, .forallE (.sort (.succ (.param 0))) <| .forallE (.bvar 0) <|
    .forallE (.app (.const (.member 70 0) [.param 0]) (.bvar 1))
      (.app (.const (.member 70 0) [.param 0]) (.bvar 2)), .safe⟩] .safe

#guard listShape.source 70 = listDecl
#guard checked 70 listDecl listShape
#guard largeChecked listShape

-- The branch domain depends on the constructor's ordinary field and a
-- parameter function: W (A : Type) (B : A → Type), node a (B a → W A B).
def wShape : Shape Nat :=
  ⟨0, [.sort (.succ .zero), .forallE .never (.bvar 0) (.sort (.succ .zero))], [], .succ .zero,
    [⟨[.bvar 1], [⟨[.app (.bvar 1) (.bvar 0)], []⟩], []⟩]⟩
#guard checked 71 (wShape.source 71) wShape
#guard largeChecked wShape

-- The second index depends on the first. Checking only a list of arities
-- would miss an ill-typed second argument.
def dependentIndices : Shape Nat :=
  ⟨0, [], [.sort .zero, .bvar 0], .succ .zero,
    [⟨[.sort .zero, .bvar 0], [], [.bvar 1, .bvar 0]⟩]⟩
#guard checked 72 (dependentIndices.source 72) dependentIndices

def wrongIndices : Shape Nat :=
  { dependentIndices with constructors := [⟨[.sort .zero, .bvar 0], [], [.bvar 1, .sort .zero]⟩] }
#guard !checked 72 (wrongIndices.source 72) wrongIndices

def tooLarge : Shape Nat := ⟨0, [], [], .succ .zero, [⟨[.sort (.succ .zero)], [], []⟩]⟩
#guard !checked 73 (tooLarge.source 73) tooLarge

-- A negative occurrence and a same-block recursive domain are rejected even
-- when the proposed descriptor exactly reproduces the source declaration.
def negative : Shape Nat :=
  ⟨0, [], [], .succ .zero, [⟨[.forallE .never (.const (.member 74 0) []) (.sort .zero)], [], []⟩]⟩
#guard !checked 74 (negative.source 74) negative
def recursiveDomain : Shape Nat :=
  ⟨0, [], [], .succ .zero, [⟨[], [⟨[.const (.member 75 0) []], []⟩], []⟩]⟩
#guard !checked 75 (recursiveDomain.source 75) recursiveDomain

def emptyProp : Shape Nat := ⟨0, [], [], .zero, []⟩
def singletonProp : Shape Nat := ⟨0, [.sort .zero], [], .zero, [⟨[.bvar 0], [], []⟩]⟩
def manyProp : Shape Nat := ⟨0, [], [], .zero, [⟨[], [], []⟩, ⟨[], [], []⟩]⟩
def dataProp : Shape Nat := ⟨0, [], [], .zero, [⟨[.sort .zero], [], []⟩]⟩

#guard checked 76 (emptyProp.source 76) emptyProp
#guard checked 77 (singletonProp.source 77) singletonProp
#guard checked 78 (manyProp.source 78) manyProp
#guard checked 79 (dataProp.source 79) dataProp
#guard largeChecked emptyProp
#guard largeChecked singletonProp
#guard !largeChecked manyProp
#guard !largeChecked dataProp

#guard !checked natSourceBlock (.induct 0 0 0 natFamily.type natFamily.ctors .unsafe) natShape
#guard !checked (natSourceBlock + 1) (.induct 0 0 0 natFamily.type natFamily.ctors .safe) natShape
#guard !checked natSourceBlock (.induct 1 0 0 natFamily.type natFamily.ctors .safe) natShape

def recursorSyntaxMatches (name : String) (shape : Shape Nat) (source recursor : Nat)
    (mode : Inductive.ElimMode) : Bool :=
  match recursorGoldens.find? (·.1 == name) with
  | none => false
  | some (_, expectedType, expectedRules) =>
    (shape.recursorType source mode).erase == expectedType &&
      (shape.constructors.zipIdx.map fun (ctor, i) =>
        ((shape.ruleRhs source recursor mode i ctor).erase,
          (shape.ruleType source mode i ctor).erase)) == expectedRules

#guard recursorSyntaxMatches "nat" natShape natSourceBlock 90 .large
#guard recursorSyntaxMatches "list" listShape 70 91 .large
#guard recursorSyntaxMatches "indexed" indexedShape indexedSourceBlock 92 .large
#guard recursorSyntaxMatches "functional" functionalShape functionalSourceBlock 93 .large
#guard recursorSyntaxMatches "w" wShape 71 94 .large
#guard recursorSyntaxMatches "dependentIndices" dependentIndices 72 95 .large
#guard recursorSyntaxMatches "manyProp" manyProp 78 96 .small
#guard recursorSyntaxMatches "singletonProp" singletonProp 77 97 .large

def pairedStore (source recursor : Nat) (h : source ≠ recursor) (decl rec : Const Nat) : Store Nat where
  dom := [source, recursor]
  nodup := by simp [h]
  blocks b := if b = source then some ⟨[decl]⟩ else if b = recursor then some ⟨[rec]⟩ else none
  mem_dom b := by by_cases hs : b = source <;> by_cases hr : b = recursor <;> simp [hs, hr, Ne.symm h]

def signaturesChecked (shape : Shape Nat) (source recursor : Nat) (mode : Inductive.ElimMode) : Bool := Id.run do
  if hne : source ≠ recursor then
    let store := pairedStore source recursor hne (shape.source source) (shape.recursorSource source recursor mode)
    let some sw := Certificate.Ordinary.shape? 500 noEntries shape | return false
    let some _ := checkShape.{0,0} 500 noEntries store source sw | return false
    let some _ := checkMode.{0,0} 500 noEntries sw mode | return false
    let some cws := Certificate.Ordinary.constructorTypes? 500 noEntries shape source | return false
    let some _ := shape.checkConstructorTypes.{0,0} 500 noEntries source shape.constructors cws | return false
    let some rw := Certificate.Ordinary.recursorType? 500 noEntries shape source mode | return false
    let some _ := shape.checkRecursorType.{0,0} 500 noEntries store source recursor mode rw | return false
    let some rules := Certificate.Ordinary.rules? 500 noEntries shape source recursor mode | return false
    return (shape.checkRules.{0,0} 500 (shape.recursorEnvironment noEntries source recursor mode)
      source recursor mode shape.constructors.zipIdx rules).isSome
  else return false

#guard signaturesChecked natShape natSourceBlock 90 .large
#guard signaturesChecked listShape 70 91 .large
#guard signaturesChecked indexedShape indexedSourceBlock 92 .large
#guard signaturesChecked functionalShape functionalSourceBlock 93 .large
#guard signaturesChecked wShape 71 94 .large
#guard signaturesChecked dependentIndices 72 95 .large
#guard signaturesChecked manyProp 78 96 .small
#guard signaturesChecked singletonProp 77 97 .large
#guard !signaturesChecked manyProp 78 96 .large

-- Formation of a signature alone publishes no equation.
def formedSignature : Environment Nat := fun r =>
  if r = .member 80 0 then some ⟨0, .sort (.succ .zero), none, [], []⟩ else none
#guard !(verifyConversion.{0,0} 10 0 formedSignature [] (.sort .zero) (.sort (.succ .zero))
  (.equation (.member 80 0) 0 [])).isSome

end Tests.Theory.Ordinary
