/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel

/-! # Inductive fixtures

Ordinary inductive blocks through the public entry point: `False`, `True`,
`And`, `Or`, `Nat`, `List`, and `Eq`, generated from their shapes, plus a
`Nat` block encoded by hand in Lean's own recursor layout, which must equal
the generated one. Rejections cover a non-positive occurrence, a universe
violation, a duplicate address, and large elimination from a two-constructor
proposition; a tampered recursor declines. -/

open Ix.Kernel Ix.Kernel.Certified Ix.Kernel.Certified.Ordinary Ix.Kernel.Inductive

namespace Tests.Ix.Kernel.Inductives

abbrev E := VExpr String
abbrev A := Ix.Kernel.Model.AExpr String

def prop : A := .sort .zero
def type0 : A := .sort (.succ .zero)
def sortU : A := .sort (.param 0)

/-- A block holding an inductive member and its recursor, generated from a shape. -/
def block (source : String) (shape : Shape String) (mode : ElimMode) (k : Bool := false) :
    Decl String :=
  ⟨source, ⟨[shape.source source, shape.recursorSource source mode k]⟩⟩

/-- `False : Prop` -/
def falseShape : Shape String := ⟨0, [], [], .zero, []⟩
/-- `True : Prop`, `intro` -/
def trueShape : Shape String := ⟨0, [], [], .zero, [⟨[], [], []⟩]⟩
/-- `And (a b : Prop) : Prop`, `intro (left : a) (right : b)` -/
def andShape : Shape String := ⟨0, [prop, prop], [], .zero, [⟨[.bvar 1, .bvar 1], [], []⟩]⟩
/-- `Or (a b : Prop) : Prop`, `inl (h : a)`, `inr (h : b)` -/
def orShape : Shape String := ⟨0, [prop, prop], [], .zero, [⟨[.bvar 1], [], []⟩, ⟨[.bvar 0], [], []⟩]⟩
/-- `Nat : Type`, `zero`, `succ (n : Nat)` -/
def natShape : Shape String := ⟨0, [], [], .succ .zero, [⟨[], [], []⟩, ⟨[], [⟨[], []⟩], []⟩]⟩
/-- `List.{u} (α : Type u) : Type u`, `nil`, `cons (head : α) (tail : List α)` -/
def listShape : Shape String :=
  ⟨1, [.sort (.succ (.param 0))], [], .succ (.param 0), [⟨[], [], []⟩, ⟨[.bvar 0], [⟨[], []⟩], []⟩]⟩
/-- `Eq.{u} {α : Sort u} (a : α) : α → Prop`, `refl : Eq α a a` -/
def eqShape : Shape String := ⟨1, [sortU, .bvar 0], [.bvar 1], .zero, [⟨[], [], [.bvar 0]⟩]⟩

def falseDecl : Decl String := block "False" falseShape .large
def trueDecl : Decl String := block "True" trueShape .large
def andDecl : Decl String := block "And" andShape .large
def orDecl : Decl String := block "Or" orShape .small
def natDecl : Decl String := block "Nat" natShape .large
def listDecl : Decl String := block "List" listShape .large
def eqDecl : Decl String := block "Eq" eqShape .large

def accepted : List (Decl String) := [falseDecl, trueDecl, andDecl, orDecl, natDecl, listDecl, eqDecl]

/-! ## `Nat` by hand, in Lean's recursor layout -/

def natC : E := .const (.member "Nat" 0) []
def zeroC : E := .const (.ctor "Nat" 0 0) []
def succC : E := .const (.ctor "Nat" 0 1) []
def natRecC : E := .const (.member "Nat" 1) [.param 0]

def natInduct : Const String :=
  .induct 0 0 0 (.sort (.succ .zero)) [⟨0, 0, 0, natC, .safe⟩, ⟨0, 0, 1, .forallE natC natC, .safe⟩] .safe

/-- `motive : Nat → Sort u` -/
def motiveT : E := .forallE natC (.sort (.param 0))
/-- `motive Nat.zero`, under `motive` -/
def zeroMinorT : E := .app (.bvar 0) zeroC
/-- `∀ (n : Nat), motive n → motive (Nat.succ n)`, under `motive`, `zeroMinor` -/
def succMinorT : E :=
  .forallE natC (.forallE (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app succC (.bvar 1))))
/-- `Nat.rec.{u} : ∀ (motive : Nat → Sort u), motive Nat.zero →
  (∀ (n : Nat), motive n → motive (Nat.succ n)) → ∀ (t : Nat), motive t` -/
def natRecT : E :=
  .forallE motiveT (.forallE zeroMinorT (.forallE succMinorT (.forallE natC (.app (.bvar 3) (.bvar 0)))))
/-- `fun motive zero succ => zero` -/
def zeroRule : E := .lam motiveT (.lam zeroMinorT (.lam succMinorT (.bvar 1)))
/-- `fun motive zero succ n => succ n (Nat.rec motive zero succ n)` -/
def succRule : E :=
  .lam motiveT (.lam zeroMinorT (.lam succMinorT (.lam natC
    (.app (.app (.bvar 1) (.bvar 0))
      (.app (.app (.app (.app natRecC (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0))))))
def natRecursor : Const String :=
  .recursor 1 0 0 1 2 natRecT [⟨0, zeroRule⟩, ⟨1, succRule⟩] false .safe

def natHand : Decl String := ⟨"Nat", ⟨[natInduct, natRecursor]⟩⟩

-- The generator reproduces Lean's layout exactly.
#guard natHand.block == natDecl.block

/-! ## Harness -/

def run (decls : List (Decl String)) : Except Error (Env String) := check.{0,1} {} decls

def accepts (decls : List (Decl String)) : Bool :=
  match run decls with | .ok _ => true | .error _ => false

def installs (decls : List (Decl String)) (n : Nat) : Bool :=
  match run decls with | .ok env => env.entries.length == n | .error _ => false

def rejects (decls : List (Decl String)) (reason : String) : Bool :=
  match run decls with | .error (.rejected r) => r == reason | _ => false

def declines (decls : List (Decl String)) (reason : String) : Bool :=
  match run decls with | .error (.declined r) => r == reason | _ => false

/-! ## Accepted -/

#guard accepts [falseDecl]
#guard accepts [trueDecl]
#guard accepts [andDecl]
#guard accepts [orDecl]
#guard accepts [natDecl]
#guard accepts [natHand]
#guard accepts [listDecl]
#guard accepts [eqDecl]
-- family, constructors, recursor per block: 2 + 3 + 3 + 4 + 4 + 4 + 3
#guard installs accepted 23

/-- Constants over the installed inductives: `Nat.succ Nat.zero : Nat`,
`List.nil.{0} Nat : List Nat`, and `Eq.refl.{1} Nat one : Eq Nat one one`. -/
def one : E := .app succC zeroC
def oneDecl : Decl String := ⟨"one", ⟨[.defn 0 .definition natC one .safe]⟩⟩
def natList : E := .app (.const (.member "List" 0) [.zero]) natC
def nilNat : Decl String :=
  ⟨"nilNat", ⟨[.defn 0 .definition natList (.app (.const (.ctor "List" 0 0) [.zero]) natC) .safe]⟩⟩
def oneC : E := .const (.member "one" 0) []
def eqOneOne : E := .app (.app (.app (.const (.member "Eq" 0) [.succ .zero]) natC) oneC) oneC
def reflOne : Decl String :=
  ⟨"reflOne", ⟨[.defn 0 .theorem eqOneOne
    (.app (.app (.const (.ctor "Eq" 0 0) [.succ .zero]) natC) oneC) .safe]⟩⟩
/-- `False.elim.{u} : ∀ (C : Sort u), False → C := fun C h => False.rec (fun _ => C) h` -/
def falseC : E := .const (.member "False" 0) []
def falseElim : Decl String :=
  ⟨"falseElim", ⟨[.defn 1 .definition
    (.forallE (.sort (.param 0)) (.forallE falseC (.bvar 1)))
    (.lam (.sort (.param 0)) (.lam falseC
      (.app (.app (.const (.member "False" 1) [.param 0]) (.lam falseC (.bvar 2))) (.bvar 0)))) .safe]⟩⟩

#guard accepts (accepted ++ [oneDecl, nilNat, reflOne, falseElim])

/-! ## Rejected and declined -/

/-- `Bad : Type` with `mk : (Bad → Nat) → Bad`: a negative occurrence. -/
def badShape : Shape String :=
  ⟨0, [], [], .succ .zero, [⟨[.forallE .never (.const (.member "Bad" 0) []) (.const (.member "Nat" 0) [])], [], []⟩]⟩
#guard rejects [natDecl, block "Bad" badShape .large] "the inductive block is ill-formed"

/-- `Big : Type` with `mk : Type → Big`: a field above the carrier's universe. -/
def bigShape : Shape String := ⟨0, [], [], .succ .zero, [⟨[type0], [], []⟩]⟩
#guard rejects [block "Big" bigShape .large] "the inductive block is ill-formed"

#guard rejects [natDecl, natDecl] "duplicate declaration address"

-- `Or` may not eliminate into `Type`.
#guard rejects [block "Or" orShape .large] "the inductive block is ill-formed"

/-- A tampered recursor: the `zero` rule returns the `succ` minor. -/
def tamperedRule : E := .lam motiveT (.lam zeroMinorT (.lam succMinorT (.bvar 0)))
def natTampered : Decl String :=
  ⟨"Nat", ⟨[natInduct, .recursor 1 0 0 1 2 natRecT [⟨0, tamperedRule⟩, ⟨1, succRule⟩] false .safe]⟩⟩
#guard declines [natTampered] "the block is not the generated ordinary block of its inductive"

-- A block whose recursor is unsafe.
#guard declines [⟨"Nat", ⟨[natInduct, .recursor 1 0 0 1 2 natRecT [⟨0, zeroRule⟩, ⟨1, succRule⟩] false .unsafe]⟩⟩]
  "unsafe inductive blocks are not supported"

/-- The public theorem applies at the model universe. -/
example (V : Type 1) [Ix.Kernel.Model.SetTheory V] {env : Env String}
    (h : run accepted = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  check_has_model V h

end Tests.Ix.Kernel.Inductives

namespace Tests.Ix.Kernel.Inductives

/-! ## Iota -/

def natRec1 : E := .const (.member "Nat" 1) [.succ .zero]
/-- `add : Nat → Nat → Nat := fun a b => Nat.rec.{1} (fun _ => Nat) a (fun _ ih => Nat.succ ih) b` -/
def addBody : E :=
  .lam natC (.lam natC
    (.app (.app (.app (.app natRec1 (.lam natC natC)) (.bvar 1))
      (.lam natC (.lam natC (.app succC (.bvar 0))))) (.bvar 0)))
def addDecl : Decl String :=
  ⟨"add", ⟨[.defn 0 .definition (.forallE natC (.forallE natC natC)) addBody .safe]⟩⟩
def two : E := .app succC (.app succC zeroC)
def twoDecl : Decl String := ⟨"two", ⟨[.defn 0 .definition natC two .safe]⟩⟩
def addC : E := .const (.member "add" 0) []
def twoC : E := .const (.member "two" 0) []
/-- `theorem addOneOne : Eq Nat (add one one) two := Eq.refl Nat two` -/
def eqNat (a b : E) : E := .app (.app (.app (.const (.member "Eq" 0) [.succ .zero]) natC) a) b
def reflNat (a : E) : E := .app (.app (.const (.ctor "Eq" 0 0) [.succ .zero]) natC) a
def addOneOne : Decl String :=
  ⟨"addOneOne", ⟨[.defn 0 .theorem (eqNat (.app (.app addC oneC) oneC) twoC) (reflNat twoC) .safe]⟩⟩
def addOneOneWrong : Decl String :=
  ⟨"addOneOneWrong", ⟨[.defn 0 .theorem (eqNat (.app (.app addC oneC) oneC) oneC) (reflNat oneC) .safe]⟩⟩

def arithmetic : List (Decl String) := accepted ++ [oneDecl, twoDecl, addDecl]

#guard accepts (arithmetic ++ [addOneOne])
#guard rejects (arithmetic ++ [addOneOneWrong]) "the body does not have the declared type"

end Tests.Ix.Kernel.Inductives

namespace Tests.Ix.Kernel.Inductives

/-! ## K-like reduction -/

def natC' : E := .const (.member "Nat" 0) []
def eqRec01 : E := .const (.member "Eq" 1) [.zero, .succ .zero]
def eqNat' (a b : E) : E := .app (.app (.app (.const (.member "Eq" 0) [.succ .zero]) natC') a) b
def eqProp (t a b : E) : E := .app (.app (.app (.const (.member "Eq" 0) [.zero]) t) a) b
def reflProp (t a : E) : E := .app (.app (.const (.ctor "Eq" 0 0) [.zero]) t) a
/-- `kSubst : ∀ (P : Nat → Prop) (a : Nat) (pa : P a) (h : Eq Nat a a),
  Eq (P a) (Eq.rec.{0,1} Nat a (fun x e => P x) pa a h) pa := fun P a pa h => Eq.refl (P a) pa`.
The major `h` is a variable, not `Eq.refl`; the recursor reduces because `h`
converts to `Eq.refl Nat a` by proof irrelevance. -/
def kSubst : Decl String :=
  ⟨"kSubst", ⟨[.defn 0 .theorem
    (.forallE (.forallE natC' (.sort .zero)) (.forallE natC' (.forallE (.app (.bvar 1) (.bvar 0))
      (.forallE (eqNat' (.bvar 1) (.bvar 1))
        (eqProp (.app (.bvar 3) (.bvar 2))
          (.app (.app (.app (.app (.app (.app eqRec01 natC') (.bvar 2))
            (.lam natC' (.lam (eqNat' (.bvar 3) (.bvar 0)) (.app (.bvar 5) (.bvar 1)))))
            (.bvar 1)) (.bvar 2)) (.bvar 0))
          (.bvar 1))))))
    (.lam (.forallE natC' (.sort .zero)) (.lam natC' (.lam (.app (.bvar 1) (.bvar 0))
      (.lam (eqNat' (.bvar 1) (.bvar 1)) (reflProp (.app (.bvar 3) (.bvar 2)) (.bvar 1)))))) .safe]⟩⟩

#guard accepts (accepted ++ [kSubst])

end Tests.Ix.Kernel.Inductives
