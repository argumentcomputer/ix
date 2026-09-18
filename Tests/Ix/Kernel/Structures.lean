/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel

/-! # Structure fixtures

Structures through the public entry point: `Prod`, `And`, a dependent
subtype, and a proposition with a data field that stays an ordinary
inductive without projections. Projections are typed through the published
projection facts, reduce on constructor applications through the iota
rules, and constructor applications convert to their eta expansions. -/

open Ix.Kernel Ix.Kernel.Certified Ix.Kernel.Certified.Ordinary Ix.Kernel.Inductive

namespace Tests.Ix.Kernel.Structures

abbrev E := VExpr String
abbrev A := Ix.Kernel.Model.AExpr String

def prop : A := .sort .zero
def type0 : A := .sort (.succ .zero)

def block (source : String) (shape : Shape String) (mode : ElimMode) (k : Bool := false) :
    Decl String :=
  ⟨source, ⟨[shape.source source, shape.recursorSource source mode k]⟩⟩

/-- `Prod.{u,v} (α : Type u) (β : Type v) : Type (max u v)`, `mk (fst : α) (snd : β)` -/
def prodShape : Shape String :=
  ⟨2, [.sort (.succ (.param 0)), .sort (.succ (.param 1))], [], .max (.succ (.param 0)) (.succ (.param 1)),
    [⟨[.bvar 1, .bvar 1], [], []⟩]⟩
/-- `And (a b : Prop) : Prop`, `intro (left : a) (right : b)` -/
def andShape : Shape String := ⟨0, [prop, prop], [], .zero, [⟨[.bvar 1, .bvar 1], [], []⟩]⟩
/-- `Sub (α : Type) (p : α → Prop) : Type`, `mk (val : α) (property : p val)` -/
def subShape : Shape String :=
  ⟨0, [type0, .forallE .always (.bvar 0) prop], [], .succ .zero,
    [⟨[.bvar 1, .app (.bvar 1) (.bvar 0)], [], []⟩]⟩
/-- `Ex (α : Type) (p : α → Prop) : Prop`, `intro (w : α) (h : p w)`: a proposition
with a data field, so no projections. -/
def exShape : Shape String :=
  ⟨0, [type0, .forallE .always (.bvar 0) prop], [], .zero,
    [⟨[.bvar 1, .app (.bvar 1) (.bvar 0)], [], []⟩]⟩
/-- `Eq.{u} {α : Sort u} (a : α) : α → Prop`, `refl` -/
def eqShape : Shape String :=
  ⟨1, [.sort (.param 0), .bvar 0], [.bvar 1], .zero, [⟨[], [], [.bvar 0]⟩]⟩

def prodDecl : Decl String := block "Prod" prodShape .large
def andDecl : Decl String := block "And" andShape .large
def subDecl : Decl String := block "Sub" subShape .large
def exDecl : Decl String := block "Ex" exShape .small
def eqDecl : Decl String := block "Eq" eqShape .large

def accepted : List (Decl String) := [prodDecl, andDecl, subDecl, exDecl, eqDecl]

/-! ## Harness -/

def run (decls : List (Decl String)) : Except Error (Env String) := check.{0,1} {} decls

def accepts (decls : List (Decl String)) : Bool :=
  match run decls with | .ok _ => true | .error _ => false

def rejects (decls : List (Decl String)) (reason : String) : Bool :=
  match run decls with | .error (.rejected r) => r == reason | _ => false

/-- The number of facts on the family entry: a structure publishes the
arities and one projection fact per field. -/
def familyFacts (decls : List (Decl String)) (source : String) : Nat :=
  match run decls with
  | .ok env =>
    match env.toEnvironment (.member source 0) with
    | some entry => entry.facts.length
    | none => 0
  | .error _ => 0

#guard accepts accepted
-- the arities and one projection fact per field; Ex stays ordinary: no facts.
#guard familyFacts accepted "Prod" == 3
#guard familyFacts accepted "And" == 3
#guard familyFacts accepted "Sub" == 3
#guard familyFacts accepted "Ex" == 0

/-! ## Projections -/

def natT : E := type0.erase
def prodC (a b : E) : E := .app (.app (.const (.member "Prod" 0) [.zero, .zero]) a) b
def mkC (a b x y : E) : E := .app (.app (.app (.app (.const (.ctor "Prod" 0 0) [.zero, .zero]) a) b) x) y
def proj (source : String) (i : Nat) (x : E) : E := .proj (.member source 0) i x

/-- `fst : ∀ (α β : Type), Prod α β → α := fun α β x => x.1` -/
def fstDecl : Decl String :=
  ⟨"fst", ⟨[.defn 0 .definition
    (.forallE natT (.forallE natT (.forallE (prodC (.bvar 1) (.bvar 0)) (.bvar 2))))
    (.lam natT (.lam natT (.lam (prodC (.bvar 1) (.bvar 0)) (proj "Prod" 0 (.bvar 0))))) .safe]⟩⟩
/-- `snd : ∀ (α β : Type), Prod α β → β := fun α β x => x.2` -/
def sndDecl : Decl String :=
  ⟨"snd", ⟨[.defn 0 .definition
    (.forallE natT (.forallE natT (.forallE (prodC (.bvar 1) (.bvar 0)) (.bvar 1))))
    (.lam natT (.lam natT (.lam (prodC (.bvar 1) (.bvar 0)) (proj "Prod" 1 (.bvar 0))))) .safe]⟩⟩
/-- `andLeft : ∀ (a b : Prop) (h : And a b), a := fun a b h => h.1` -/
def andC (a b : E) : E := .app (.app (.const (.member "And" 0) []) a) b
def andLeft : Decl String :=
  ⟨"andLeft", ⟨[.defn 0 .theorem
    (.forallE (.sort .zero) (.forallE (.sort .zero) (.forallE (andC (.bvar 1) (.bvar 0)) (.bvar 2))))
    (.lam (.sort .zero) (.lam (.sort .zero) (.lam (andC (.bvar 1) (.bvar 0)) (proj "And" 0 (.bvar 0))))) .safe]⟩⟩
/-- `property : ∀ (α : Type) (p : α → Prop) (x : Sub α p), p x.1 := fun α p x => x.2` -/
def subC (a p : E) : E := .app (.app (.const (.member "Sub" 0) []) a) p
def propertyDecl : Decl String :=
  ⟨"property", ⟨[.defn 0 .theorem
    (.forallE natT (.forallE (.forallE (.bvar 0) (.sort .zero))
      (.forallE (subC (.bvar 1) (.bvar 0)) (.app (.bvar 1) (proj "Sub" 0 (.bvar 0))))))
    (.lam natT (.lam (.forallE (.bvar 0) (.sort .zero))
      (.lam (subC (.bvar 1) (.bvar 0)) (proj "Sub" 1 (.bvar 0))))) .safe]⟩⟩

#guard accepts (accepted ++ [fstDecl, sndDecl, andLeft, propertyDecl])

/-- A projection out of `Ex`, which has none. -/
def exC (a p : E) : E := .app (.app (.const (.member "Ex" 0) []) a) p
def exProj : Decl String :=
  ⟨"exProj", ⟨[.defn 0 .definition
    (.forallE natT (.forallE (.forallE (.bvar 0) (.sort .zero)) (.forallE (exC (.bvar 1) (.bvar 0)) (.bvar 2))))
    (.lam natT (.lam (.forallE (.bvar 0) (.sort .zero)) (.lam (exC (.bvar 1) (.bvar 0)) (proj "Ex" 0 (.bvar 0))))) .safe]⟩⟩
#guard rejects (accepted ++ [exProj]) "the body is ill-typed"

/-- A projection index past the fields. -/
def badIndex : Decl String :=
  ⟨"badIndex", ⟨[.defn 0 .definition
    (.forallE natT (.forallE natT (.forallE (prodC (.bvar 1) (.bvar 0)) (.bvar 2))))
    (.lam natT (.lam natT (.lam (prodC (.bvar 1) (.bvar 0)) (proj "Prod" 2 (.bvar 0))))) .safe]⟩⟩
#guard rejects (accepted ++ [badIndex]) "the body is ill-typed"

/-! ## Iota and eta -/

def eqC (t a b : E) : E := .app (.app (.app (.const (.member "Eq" 0) [.succ .zero]) t) a) b
def reflC (t a : E) : E := .app (.app (.const (.ctor "Eq" 0 0) [.succ .zero]) t) a

/-- `fstMk : ∀ (α β : Type) (a : α) (b : β), Eq α (Prod.mk α β a b).1 a := fun α β a b => Eq.refl α a` -/
def fstMk : Decl String :=
  ⟨"fstMk", ⟨[.defn 0 .theorem
    (.forallE natT (.forallE natT (.forallE (.bvar 1) (.forallE (.bvar 1)
      (eqC (.bvar 3) (proj "Prod" 0 (mkC (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))) (.bvar 1))))))
    (.lam natT (.lam natT (.lam (.bvar 1) (.lam (.bvar 1) (reflC (.bvar 3) (.bvar 1)))))) .safe]⟩⟩
/-- `etaProd : ∀ (α β : Type) (x : Prod α β), Eq (Prod α β) x (Prod.mk α β x.1 x.2) := fun α β x => Eq.refl _ x` -/
def etaProd : Decl String :=
  ⟨"etaProd", ⟨[.defn 0 .theorem
    (.forallE natT (.forallE natT (.forallE (prodC (.bvar 1) (.bvar 0))
      (eqC (prodC (.bvar 2) (.bvar 1)) (.bvar 0)
        (mkC (.bvar 2) (.bvar 1) (proj "Prod" 0 (.bvar 0)) (proj "Prod" 1 (.bvar 0)))))))
    (.lam natT (.lam natT (.lam (prodC (.bvar 1) (.bvar 0)) (reflC (prodC (.bvar 2) (.bvar 1)) (.bvar 0))))) .safe]⟩⟩
/-- The wrong value: `(Prod.mk α α a a').1` is `a`, not `a'`. -/
def fstMkWrong : Decl String :=
  ⟨"fstMkWrong", ⟨[.defn 0 .theorem
    (.forallE natT (.forallE (.bvar 0) (.forallE (.bvar 1)
      (eqC (.bvar 2) (proj "Prod" 0 (mkC (.bvar 2) (.bvar 2) (.bvar 1) (.bvar 0))) (.bvar 0)))))
    (.lam natT (.lam (.bvar 0) (.lam (.bvar 1) (reflC (.bvar 2) (.bvar 0))))) .safe]⟩⟩
#guard accepts (accepted ++ [fstMk, etaProd])
#guard rejects (accepted ++ [fstMkWrong]) "the body does not have the declared type"

end Tests.Ix.Kernel.Structures
