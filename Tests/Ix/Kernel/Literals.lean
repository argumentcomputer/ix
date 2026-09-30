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

def declines (decls : List (Decl String)) (reason : String) : Bool :=
  match run decls with | .error (.declined r) => r == reason | _ => false

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
#guard declines [natDecl, eqDecl, addDecl, twoPlusTwoWrong]
  "body conversion: conversion search did not establish equality"
#guard declines [natDecl, eqDecl, twoThree]
  "body conversion: conversion search did not establish equality"

/-! ## Operations on literals

A definition whose defining equations check publishes its operation
(`ConstantFact.natOp`/`natTest`), and applications to literals then evaluate
directly: `1000000 + 2345678` would take millions of iota steps otherwise. -/

def factsOf (decls : List (Decl String)) (r : ConstRef String) : List (Model.ConstantFact String) :=
  match run decls with
  | .ok env => (env.toEnvironment r).elim [] (·.facts)
  | .error _ => []

def lit (n : Nat) : E := .natLit natRef n
def app2 (f a b : E) : E := .app (.app f a) b
def recNat (motive base step major : E) : E := .app (.app (.app (.app natRec1 motive) base) step) major

#guard factsOf [natDecl, addDecl] (.member "add" 0) == [.natOp .add]

def bigSum : Decl String := thm "bigSum" (eqNat (app2 addC (lit 1000000) (lit 2345678)) (lit 3345678))
  (reflNat (lit 3345678))
def bigSumWrong : Decl String := thm "bigSumWrong" (eqNat (app2 addC (lit 1000000) (lit 2345678))
  (lit 3345679)) (reflNat (lit 3345679))
#guard accepts [natDecl, eqDecl, addDecl, bigSum]
#guard declines [natDecl, eqDecl, addDecl, bigSumWrong]
  "body conversion: conversion search did not establish equality"

/-- Keeps its first argument: the step is not a successor, so nothing is published. -/
def keepDecl : Decl String := ⟨"keep", ⟨[.defn 0 .definition (.forallE natC (.forallE natC natC))
  (.lam natC (.lam natC (recNat (.lam natC natC) (.bvar 1) (.lam natC (.lam natC (.bvar 0))) (.bvar 0))))
  .safe]⟩⟩
#guard factsOf [natDecl, keepDecl] (.member "keep" 0) == []

/-- Multiplication by its recurrence over the certified `add`. -/
def mulDecl : Decl String := ⟨"mul", ⟨[.defn 0 .definition (.forallE natC (.forallE natC natC))
  (.lam natC (.lam natC (recNat (.lam natC natC) (lit 0)
    (.lam natC (.lam natC (app2 addC (.bvar 0) (.bvar 3)))) (.bvar 0)))) .safe]⟩⟩
def mulC : E := .const (.member "mul" 0) []
def bigProduct : Decl String := thm "bigProduct" (eqNat (app2 mulC (lit 1234) (lit 5678)) (lit 7006652))
  (reflNat (lit 7006652))
#guard factsOf [natDecl, addDecl, mulDecl] (.member "mul" 0) == [.natOp .mul]
#guard accepts [natDecl, eqDecl, addDecl, mulDecl, bigProduct]
/-- Multiplication's shape over `keep`, which is not addition: nothing is published. -/
def mulKeepDecl : Decl String := ⟨"mulKeep", ⟨[.defn 0 .definition (.forallE natC (.forallE natC natC))
  (.lam natC (.lam natC (recNat (.lam natC natC) (lit 0)
    (.lam natC (.lam natC (app2 (.const (.member "keep" 0) []) (.bvar 0) (.bvar 3)))) (.bvar 0)))) .safe]⟩⟩
#guard factsOf [natDecl, addDecl, keepDecl, mulKeepDecl] (.member "mulKeep" 0) == []

def boolShape : Shape String := ⟨0, [], [], .succ .zero, [⟨[], [], []⟩, ⟨[], [], []⟩]⟩
def boolDecl : Decl String := ⟨"Bool", ⟨[boolShape.source "Bool", boolShape.recursorSource "Bool" .large]⟩⟩
def boolC : E := .const (.member "Bool" 0) []
def falseC : E := .const (.ctor "Bool" 0 0) []
def trueC : E := .const (.ctor "Bool" 0 1) []
def eqBool (a b : E) : E := .app (.app (.app (.const (.member "Eq" 0) [.succ .zero]) boolC) a) b
def reflBool (a : E) : E := .app (.app (.const (.ctor "Eq" 0 0) [.succ .zero]) boolC) a

/-- `ble` by recursion on the first argument, generalized over the second. -/
def bleDecl : Decl String := ⟨"ble", ⟨[.defn 0 .definition (.forallE natC (.forallE natC boolC))
  (.lam natC (.lam natC (.app
    (recNat (.lam natC (.forallE natC boolC)) (.lam natC trueC)
      (.lam natC (.lam (.forallE natC boolC) (.lam natC
        (recNat (.lam natC boolC) falseC (.lam natC (.lam boolC (.app (.bvar 3) (.bvar 1)))) (.bvar 0)))))
      (.bvar 1))
    (.bvar 0)))) .safe]⟩⟩
def bleC : E := .const (.member "ble" 0) []
def bleTrue : Decl String := thm "bleTrue" (eqBool (app2 bleC (lit 300000) (lit 500000)) trueC) (reflBool trueC)
def bleFalse : Decl String := thm "bleFalse" (eqBool (app2 bleC (lit 500001) (lit 500000)) falseC) (reflBool falseC)
#guard factsOf [natDecl, boolDecl, bleDecl] (.member "ble" 0) ==
  [.natTest .ble (.ctor "Bool" 0 1) (.ctor "Bool" 0 0)]
#guard accepts [natDecl, boolDecl, eqDecl, bleDecl, bleTrue, bleFalse]

-- A literal naming a family that is not installed is a missing reference.
#guard rejects [three] "the declaration references a constant that is not installed"
-- A literal naming a family that is not the natural numbers is ill-typed.
def eqRef : ConstRef String := .member "Eq" 0
def threeEq : Decl String := ⟨"threeEq", ⟨[.defn 0 .definition natC (.natLit eqRef 3) .safe]⟩⟩
#guard rejects [natDecl, eqDecl, threeEq] "body: literal family is not the admitted natural numbers"

end Tests.Ix.Kernel.Literals
