/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel

/-! # Standard axiom fixtures

`propext` and `Classical.choice` through the public entry point: each is
admitted at its exact type once the interfaces it is stated over (`Eq` and
`Iff`, `Nonempty`) are installed as ordinary blocks, and each can then be
used. Rejections cover an axiom declared before its interfaces and an `Iff`
whose eliminator is not the admitted one; an axiom that is not standard
declines. -/

open Ix.Kernel Ix.Kernel.Certified Ix.Kernel.Certified.Ordinary

namespace Tests.Ix.Kernel.Axioms

abbrev E := VExpr String

def eqDecl : Decl String :=
  ⟨"Eq", ⟨[Basis.Equality.shape.source "Eq", Basis.Equality.shape.recursorSource "Eq" .large]⟩⟩
def iffDecl : Decl String :=
  ⟨"Iff", ⟨[Basis.Iff.shape.source "Iff", Basis.Iff.shape.recursorSource "Iff" .large]⟩⟩
def iffSmall : Decl String :=
  ⟨"Iff", ⟨[Basis.Iff.shape.source "Iff", Basis.Iff.shape.recursorSource "Iff" .small]⟩⟩
def nonemptyDecl : Decl String :=
  ⟨"Nonempty", ⟨[Basis.Nonempty.shape.source "Nonempty", Basis.Nonempty.shape.recursorSource "Nonempty" .small]⟩⟩

def propextSpec : Standard.Spec String :=
  .propext (.member "Eq" 0) (.ctor "Eq" 0 0) (.member "Eq" 1) (.member "Iff" 0) (.ctor "Iff" 0 0) (.member "Iff" 1)
def choiceSpec : Standard.Spec String :=
  .choice (.member "Nonempty" 0) (.ctor "Nonempty" 0 0) (.member "Nonempty" 1)
def propextDecl : Decl String := ⟨"propext", ⟨[propextSpec.source]⟩⟩
def choiceDecl : Decl String := ⟨"Classical.choice", ⟨[choiceSpec.source]⟩⟩

def cfg : Config := {}
def run (decls : List (Decl String)) : Except Error (Env String) := check.{0,1} cfg decls
def accepts (decls : List (Decl String)) : Bool :=
  match run decls with | .ok _ => true | .error _ => false
def installs (decls : List (Decl String)) (n : Nat) : Bool :=
  match run decls with | .ok env => env.entries.length == n | .error _ => false
def rejects (decls : List (Decl String)) (reason : String) : Bool :=
  match run decls with | .error (.rejected r) => r == reason | _ => false
def declines (decls : List (Decl String)) (reason : String) : Bool :=
  match run decls with | .error (.declined r) => r == reason | _ => false

/-! ## Accepted -/

#guard accepts [eqDecl, iffDecl, propextDecl]
#guard accepts [nonemptyDecl, choiceDecl]
-- three entries per block, one per axiom
#guard installs [eqDecl, iffDecl, nonemptyDecl, propextDecl, choiceDecl] 11

/-- `theorem usePropext : ∀ P Q, Iff P Q → Eq Prop P Q := propext` -/
def usePropext : Decl String :=
  ⟨"usePropext", ⟨[.defn 0 .theorem propextSpec.type.erase (.const (.member "propext" 0) []) .safe]⟩⟩
#guard accepts [eqDecl, iffDecl, propextDecl, usePropext]
/-- `def pick.{u} : ∀ (α : Sort u), Nonempty α → α := Classical.choice` -/
def pick : Decl String :=
  ⟨"pick", ⟨[.defn 1 .definition choiceSpec.type.erase (.const (.member "Classical.choice" 0) [.param 0]) .safe]⟩⟩
#guard accepts [nonemptyDecl, choiceDecl, pick]

/-! ## Rejected and declined -/

#guard rejects [eqDecl, propextDecl] "the declaration references a constant that is not installed"
#guard rejects [choiceDecl] "the declaration references a constant that is not installed"
#guard rejects [eqDecl, iffSmall, propextDecl] "the axiom's prerequisites are not the admitted interfaces"
#guard rejects [eqDecl, iffDecl, propextDecl, propextDecl] "duplicate declaration address"
def axiomProp : Decl String := ⟨"ax", ⟨[.axiom 0 (.sort .zero) .safe]⟩⟩
#guard declines [axiomProp] "only the standard axioms and quotient soundness are supported"
def axiomUnsafe : Decl String := ⟨"ax", ⟨[.axiom 0 (.sort .zero) .unsafe]⟩⟩
#guard declines [axiomUnsafe] "only the standard axioms and quotient soundness are supported"

end Tests.Ix.Kernel.Axioms
