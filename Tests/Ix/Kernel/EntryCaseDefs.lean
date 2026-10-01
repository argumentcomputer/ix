/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Ix.Kernel.TutorialMeta

/-! # Lean sources of the certified entry's host cases

Ordinary Lean declarations that `kernel-entry-cases`
(`Tests.Ix.Kernel.EntryCases`) loads from this module's `.olean`, compiles
with Ix's compiler and submits, as canonical record bytes, to the certified
entry `Ix.Ixon.Admission.checkBytes`. Lean's kernel checked every
declaration here except `falseThm`, whose value is `True.intro` installed
unchecked (`TutorialMeta.bad_thm`): it is the one input of the wrong type.
-/

open Tests.Ix.Kernel.TutorialMeta

namespace Tests.Ix.Kernel.EntryCaseDefs

universe u

/-! ## Accepted -/

/-- A definition. -/
def twice {α : Sort u} (f : α → α) (a : α) : α := f (f a)

/-- A theorem, by δ through `twice` and `id`. -/
theorem twiceId {α : Sort u} (a : α) : twice id a = a := rfl

/-- An inductive with its recursor, and an ι-reduction through it. -/
inductive Color where
  | red
  | green
  | blue

noncomputable def Color.next (c : Color) : Color :=
  Color.rec (motive := fun _ => Color) .green .blue .red c

theorem Color.nextRed : Color.red.next = .green := rfl

/-- A structure, its projection function, and a projection reduction. -/
structure Point where
  x : Nat
  y : Nat

theorem Point.xMk : (Point.mk Nat.zero (Nat.succ Nat.zero)).x = Nat.zero := rfl

/-- The quotient's lift reduction. -/
theorem quotLiftMk (r : Nat → Nat → Prop) (f : Nat → Nat) (h : ∀ a b, r a b → f a = f b)
    (a : Nat) : Quot.lift f h (Quot.mk r a) = f a := rfl

/-- A `Nat` literal against its constructors. -/
theorem natLit : (2 : Nat) = Nat.succ (Nat.succ Nat.zero) := rfl

/-- A pinned `Nat` operation on literals. -/
theorem natAdd : (2 : Nat) + 3 = 5 := rfl

/-- A `String` literal against its `String.ofList` expansion. -/
theorem strLit : "ab" = String.ofList [Char.ofNat 97, Char.ofNat 98] := rfl

/-- A nested inductive (through `List`). -/
inductive Tree where
  | node : List Tree → Tree

/-- A container that is itself nested (through `List`). -/
inductive LNode (α : Type) where
  | node : List (LNode α) → LNode α
  | leaf : α → LNode α

/-- A block nested through a container that is itself nested. Ix's compiler
orders `LTree.rec`'s auxiliary motives canonically, as
`[List (LNode LTree), LNode LTree]`: the container family's instance before
its head, the order that made the in-process modeller emit `pack_0` twice
(cl-m1). -/
inductive LTree where
  | node : LNode LTree → LTree

/-- The shape of `Lean.Elab.InfoTree`: nested through a structure whose field
is nested through `Array` (`PersistentArray` → `PersistentArrayNode`). Its
auxiliary motives are compiled as `[Array ITree, Array (PNode ITree), PArr
ITree, List (PNode ITree), List ITree, PNode ITree]`, as `InfoTree`'s are. -/
inductive PNode (α : Type) where
  | node : Array (PNode α) → PNode α
  | leaf : Array α → PNode α

structure PArr (α : Type) where
  root : PNode α
  tail : Array α
  size : Nat

inductive ITree where
  | context : Nat → ITree → ITree
  | node : Nat → PArr ITree → ITree
  | hole : Nat → ITree

/-- The face of a `partial` definition: an opaque constant whose value is an
inhabitant of its type. The recursive body is the `partial` companion
`loop._unsafe_rec`. -/
partial def loop (n : Nat) : Nat := loop (n + 1)

/-- An equation between elements of a `Subtype` of a type in
`Sort (imax (u+2) (imax (v+1) v))`, the shape of `RatFunc.liftOn_def` (an
`irreducible_def` unfolding lemma). Lean elaborates `Subtype.{W}` and
`Eq.{max 1 W}`; Ix's compiler stores each level as its canonical form,
`Subtype.{imax (max (u+2) (v+1)) v}` and `Eq.{max (v+1) (imax (u+2) v)}`.
The `Subtype`'s type `Sort (max (imax (max (u+2) (v+1)) v) 1)` is the
`Eq`'s domain at every valuation, which nanoda's level comparison (the
official kernel's) does not establish (cl-m1). Con-leche's comparison
decides that case by Géran's sublevels since cl-level.
-/
theorem levelCanon.{w, x} {a b : {_f : (K : Type w) → (P : Sort x) → P // True}} (h : a = b) :
    a = b := h

/-! ## Refused -/

/-- An axiom other than the pinned standard ones. -/
axiom someAxiom (n : Nat) : n = n

-- `∀ (α : Sort w) (a : α), @Eq.{w+1} α a a`, by `Eq.refl.{w+1}`: an
-- equation at the wrong universe level, installed in Lean unchecked. No
-- valuation of `w` makes it well typed (cl-m1: a reject, not a level
-- comparison's decline; cl-level: still rejected by the complete comparison).
bad_decl .thmDecl {
  name := `Tests.Ix.Kernel.EntryCaseDefs.levelWrong
  levelParams := [`w]
  type := .forallE `α (.sort (.param `w))
    (.forallE `a (.bvar 0) (Lean.mkApp3 (.const ``Eq [.succ (.param `w)]) (.bvar 1) (.bvar 0) (.bvar 0))
      .default) .default
  value := .lam `α (.sort (.param `w))
    (.lam `a (.bvar 0) (Lean.mkApp2 (.const ``Eq.refl [.succ (.param `w)]) (.bvar 1) (.bvar 0)) .default)
    .default }

-- A theorem of `False`, installed in Lean unchecked.
bad_thm falseThm : False := unchecked True.intro

end Tests.Ix.Kernel.EntryCaseDefs
