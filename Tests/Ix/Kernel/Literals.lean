/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel

/-! # Literal fixtures

Natural-number literals through the public entry point: the `Nat` block is
recognized by its shape and published with the `natural` fact; with the pin
, literals name that family, type at it, convert with the
constructors, and drive recursor iota. A literal naming an uninstalled family
is a missing reference; one naming a block that is not `Nat` is ill-typed. -/

open Ix.Kernel Ix.Kernel.Certified Ix.Kernel.Certified.Ordinary Ix.Kernel.Inductive

namespace Tests.Ix.Kernel.Literals

abbrev E := VExpr String

def natShape : Shape String := ⟨0, [], [], .succ .zero, [⟨[], [], []⟩, ⟨[], [⟨[], []⟩], []⟩]⟩
def natDecl : Decl String := ⟨"Nat", ⟨[natShape.source "Nat", natShape.recursorSource "Nat" .large]⟩⟩
def eqShape : Shape String := ⟨1, [.sort (.param 0), .bvar 0], [.bvar 1], .zero, [⟨[], [], [.bvar 0]⟩]⟩
def eqDecl : Decl String := ⟨"Eq", ⟨[eqShape.source "Eq", eqShape.recursorSource "Eq" .large]⟩⟩

def natRef : ConstRef String := .member "Nat" 0
def natC : E := .const natRef []
def zeroC : E := .const (.ctor "Nat" 0 0) []
def succC : E := .const (.ctor "Nat" 0 1) []
def natRec1 : E := .const (.member "Nat" 1) [.succ .zero]
def eqNat (a b : E) : E := .app (.app (.app (.const (.member "Eq" 0) [.succ .zero]) natC) a) b
def reflNat (a : E) : E := .app (.app (.const (.ctor "Eq" 0 0) [.succ .zero]) natC) a
def thm (name : String) (type body : E) : Decl String := ⟨name, ⟨[.defn 0 .theorem type body .safe]⟩⟩

def cfg : Config := {}
def run (decls : List (Decl String)) : Except Error (Env String) := check.{0,1} cfg decls
def accepts (decls : List (Decl String)) : Bool :=
  match run decls with | .ok _ => true | .error _ => false
def rejects (decls : List (Decl String)) (reason : String) : Bool :=
  match run decls with | .error (.rejected r) => r == reason | _ => false

/-- The family entry carries exactly the `natural` fact. -/
def natFacts : Nat :=
  match run [natDecl] with
  | .ok env => match env.toEnvironment (.member "Nat" 0) with
    | some entry => entry.facts.length
    | none => 99
  | .error _ => 98
#guard natFacts == 1

def three : Decl String := ⟨"three", ⟨[.defn 0 .definition natC (.natLit natRef 3) .safe]⟩⟩
/-- `3 = succ 2` and `0 = zero` by `Eq.refl`. -/
def threeSucc : Decl String := thm "threeSucc" (eqNat (.natLit natRef 3) (.app succC (.natLit natRef 2))) (reflNat (.natLit natRef 3))
def zeroZero : Decl String := thm "zeroZero" (eqNat (.natLit natRef 0) zeroC) (reflNat zeroC)
/-- `add` by recursion on the second argument; `add 2 2 = 4` reduces through iota on literal majors. -/
def addBody : E :=
  .lam natC (.lam natC
    (.app (.app (.app (.app natRec1 (.lam natC natC)) (.bvar 1))
      (.lam natC (.lam natC (.app succC (.bvar 0))))) (.bvar 0)))
def addDecl : Decl String :=
  ⟨"add", ⟨[.defn 0 .definition (.forallE natC (.forallE natC natC)) addBody .safe]⟩⟩
def addC : E := .const (.member "add" 0) []
def twoPlusTwo : Decl String :=
  thm "twoPlusTwo" (eqNat (.app (.app addC (.natLit natRef 2)) (.natLit natRef 2)) (.natLit natRef 4)) (reflNat (.natLit natRef 4))
def twoPlusTwoWrong : Decl String :=
  thm "twoPlusTwoWrong" (eqNat (.app (.app addC (.natLit natRef 2)) (.natLit natRef 2)) (.natLit natRef 5)) (reflNat (.natLit natRef 5))
def twoThree : Decl String := thm "twoThree" (eqNat (.natLit natRef 2) (.natLit natRef 3)) (reflNat (.natLit natRef 3))

#guard accepts [natDecl, three]
#guard accepts [natDecl, eqDecl, threeSucc, zeroZero]
#guard accepts [natDecl, eqDecl, addDecl, twoPlusTwo]
#guard rejects [natDecl, eqDecl, addDecl, twoPlusTwoWrong] "the body does not have the declared type"
#guard rejects [natDecl, eqDecl, twoThree] "the body does not have the declared type"

-- A literal naming a family that is not installed is a missing reference.
#guard rejects [three] "the declaration references a constant that is not installed"
-- A literal naming a family that is not the natural numbers is ill-typed.
def eqRef : ConstRef String := .member "Eq" 0
def threeEq : Decl String := ⟨"threeEq", ⟨[.defn 0 .definition natC (.natLit eqRef 3) .safe]⟩⟩
#guard rejects [natDecl, eqDecl, threeEq] "the body is ill-typed"

end Tests.Ix.Kernel.Literals
