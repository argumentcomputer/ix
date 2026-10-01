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

/-- The face of a `partial` definition: an opaque constant whose value is an
inhabitant of its type. The recursive body is the `partial` companion
`loop._unsafe_rec`. -/
partial def loop (n : Nat) : Nat := loop (n + 1)

/-! ## Refused -/

/-- An axiom other than the pinned standard ones. -/
axiom someAxiom (n : Nat) : n = n

-- A theorem of `False`, installed in Lean unchecked.
bad_thm falseThm : False := unchecked True.intro

end Tests.Ix.Kernel.EntryCaseDefs
