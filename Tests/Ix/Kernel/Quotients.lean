/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel

/-! # Quotient fixtures

The quotient primitives through the public entry point: after `Eq`, the
former, the constructor, the lift, and the eliminator are declared one by one
in Lean's own layout, and the soundness axiom follows. The lift's computation
rule takes `Quot.lift f h (Quot.mk a)` to `f a`, so the reflexivity proof of
that equation checks; the eliminator types at a constructor application.
Rejections cover a primitive declared before what it refers to, a duplicate
address, and a soundness axiom over an equality that is not the admitted one;
a former that is not the primitive one and an axiom other than soundness
decline. -/

open Ix.Kernel Ix.Kernel.Certified Ix.Kernel.Certified.Ordinary

namespace Tests.Ix.Kernel.Quotients

abbrev E := VExpr String

def eqShape : Shape String := ⟨1, [.sort (.param 0), .bvar 0], [.bvar 1], .zero, [⟨[], [], [.bvar 0]⟩]⟩
def eqDecl : Decl String := ⟨"Eq", ⟨[eqShape.source "Eq", eqShape.recursorSource "Eq" .large]⟩⟩
def natShape : Shape String := ⟨0, [], [], .succ .zero, [⟨[], [], []⟩, ⟨[], [⟨[], []⟩], []⟩]⟩
def natDecl : Decl String := ⟨"Nat", ⟨[natShape.source "Nat", natShape.recursorSource "Nat" .large]⟩⟩

def refs : Quotient.Refs String :=
  ⟨.member "Eq" 0, .member "Quot" 0, .member "Quot.mk" 0, .member "Quot.lift" 0, .member "Quot.ind" 0⟩

def quotDecl : Decl String := ⟨"Quot", ⟨[Quotient.Refs.source refs .type]⟩⟩
def mkDecl : Decl String := ⟨"Quot.mk", ⟨[Quotient.Refs.source refs .ctor]⟩⟩
def liftDecl : Decl String := ⟨"Quot.lift", ⟨[Quotient.Refs.source refs .lift]⟩⟩
def indDecl : Decl String := ⟨"Quot.ind", ⟨[Quotient.Refs.source refs .ind]⟩⟩
def soundDecl : Decl String := ⟨"Quot.sound", ⟨[Quotient.Refs.soundSource refs]⟩⟩

def primitives : List (Decl String) := [eqDecl, quotDecl, mkDecl, liftDecl, indDecl, soundDecl]

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

#guard accepts [eqDecl, quotDecl]
#guard accepts [eqDecl, quotDecl, mkDecl]
#guard accepts [eqDecl, quotDecl, liftDecl]
#guard accepts primitives
-- the equality block's three entries and the five primitives
#guard installs primitives 8

/-- The binders of the lift's rule: `A R B f h a`. -/
def liftBinders : List E := (Quotient.liftRuleBinders refs).map fun b => b.erase
def eqC : E := .const (.member "Eq" 0) [.param 1]
def reflC : E := .const (.ctor "Eq" 0 0) [.param 1]
def liftC : E := .const refs.lift [.param 0, .param 1]
def mkC : E := .const refs.ctor [.param 0]
def indC : E := .const refs.ind [.param 0]

/-- `theorem liftMk : ∀ A R B f h a, Eq B (Quot.lift A R B f h (Quot.mk A R a)) (f a) :=
fun A R B f h a => Eq.refl B (f a)` -/
def liftMk : Decl String :=
  ⟨"liftMk", ⟨[.defn 2 .theorem
    (.forallN liftBinders (.appN eqC [.bvar 3,
      .appN liftC [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1, .appN mkC [.bvar 5, .bvar 4, .bvar 0]],
      .app (.bvar 2) (.bvar 0)]))
    (.lamN liftBinders (.appN reflC [.bvar 3, .app (.bvar 2) (.bvar 0)])) .safe]⟩⟩
#guard accepts (primitives ++ [liftMk])

/-- The same equation with an extra point `b`, `f b` on the right: the rule
takes the left side to `f a`, which does not convert with `f b`. -/
def liftMkWrong : Decl String :=
  ⟨"liftMkWrong", ⟨[.defn 2 .theorem
    (.forallN (liftBinders ++ [.bvar 5]) (.appN eqC [.bvar 4,
      .appN liftC [.bvar 6, .bvar 5, .bvar 4, .bvar 3, .bvar 2, .appN mkC [.bvar 6, .bvar 5, .bvar 1]],
      .app (.bvar 3) (.bvar 0)]))
    (.lamN (liftBinders ++ [.bvar 5]) (.appN reflC [.bvar 4, .app (.bvar 3) (.bvar 1)])) .safe]⟩⟩
#guard rejects (primitives ++ [liftMkWrong]) "the body does not have the declared type"

/-- The binders of the eliminator's rule: `A R B h a`. -/
def indBinders : List E := (Quotient.indRuleBinders refs).map fun b => b.erase
/-- `theorem indMk : ∀ A R B h a, B (Quot.mk A R a) := fun A R B h a => Quot.ind A R B h (Quot.mk A R a)` -/
def indMk : Decl String :=
  ⟨"indMk", ⟨[.defn 1 .theorem
    (.forallN indBinders (.app (.bvar 2) (.appN mkC [.bvar 4, .bvar 3, .bvar 0])))
    (.lamN indBinders (.appN indC [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .appN mkC [.bvar 4, .bvar 3, .bvar 0]])) .safe]⟩⟩
#guard accepts (primitives ++ [indMk])

/-! ## Rejected and declined -/

#guard rejects [eqDecl, mkDecl] "the declaration references a constant that is not installed"
#guard rejects [eqDecl, quotDecl, indDecl] "the declaration references a constant that is not installed"
#guard rejects [eqDecl, quotDecl, quotDecl] "duplicate declaration address"

/-- Soundness over `Nat` in the equality's place: the former and the
constructor are the admitted ones, the equality is not. -/
def natRefs : Quotient.Refs String := { refs with eq := .member "Nat" 0 }
def soundNat : Decl String := ⟨"Quot.sound", ⟨[Quotient.Refs.soundSource natRefs]⟩⟩
#guard rejects [natDecl, eqDecl, quotDecl, mkDecl, soundNat]
  "the quotient soundness axiom's equality is not the admitted one"

def quotProp : Decl String := ⟨"Quot", ⟨[.quot .type 1 (.sort .zero)]⟩⟩
#guard declines [eqDecl, quotProp] "the quotient former is not the primitive one"
def axiomProp : Decl String := ⟨"ax", ⟨[.axiom 0 (.sort .zero) .safe]⟩⟩
#guard declines [axiomProp] "only the standard axioms and quotient soundness are supported"
def axiomSort : Decl String := ⟨"ax", ⟨[.axiom 1 (.sort (.param 0)) .safe]⟩⟩
#guard declines [axiomSort] "only the standard axioms and quotient soundness are supported"

end Tests.Ix.Kernel.Quotients
