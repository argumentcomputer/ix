/-
Copyright (c) 2026 Argument Computer Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Ix contributors
-/
import Ix.Common

/-!
# TauCeti Rule-K rejection reduction

This is a dependency-free reducer model of the expensive shape in TauCeti's
`chebyshevWeightL2Isometry_apply` pair.  There, an equality proof transports a
bundled isometry between two propositionally equal, but not definitionally
equal, measure-indexed types.  Exposing the transported structure's function
field probes `Eq.rec` reduction:

1. Rule-K synthesis compares the major's equality type with `Eq.refl` and
   rejects it because the endpoints are not definitionally equal.
2. Normalizing the equality proof after that conclusive rejection is futile;
   the proof can be arbitrarily expensive without ever exposing `Eq.refl`.

`slowTypeEquality` makes that second step observably expensive while keeping
the fixture tiny.  The source is intentionally inconsistent (via one axiom),
just as a kernel unit test may contain arbitrary axioms; every declaration is
nevertheless well typed.
-/

namespace Tests.Ix.Kernel.TauCetiReduction

structure TinyIso (α β : Type) where
  toFun : α → β
  invFun : β → α
  leftInv : ∀ x, invFun (toFun x) = x
  rightInv : ∀ x, toFun (invFun x) = x

instance : CoeFun (TinyIso α β) (fun _ => α → β) := ⟨TinyIso.toFun⟩

def TinyIso.refl (α : Type) : TinyIso α α where
  toFun := id
  invFun := id
  leftInv := fun _ => rfl
  rightInv := fun _ => rfl

def TinyIso.trans (f : TinyIso α β) (g : TinyIso β γ) : TinyIso α γ where
  toFun := fun x => g (f x)
  invFun := fun x => f.invFun (g.invFun x)
  leftInv := fun x => by rw [g.leftInv, f.leftInv]
  rightInv := fun x => by rw [f.rightInv, g.rightInv]

/-- A stand-in for TauCeti's propositional equality of two measures. -/
axiom typeEquality : Nat = Bool

/-- Productive proof work hidden behind an opaque equality theorem. -/
theorem spinProof (n : Nat) (h : Nat = Bool) : Nat = Bool :=
  match n with
  | 0 => h
  | n + 1 => spinProof n h

theorem slowTypeEquality : Nat = Bool := spinProof 4096 typeEquality

/-- The minimal analogue of TauCeti's `castLpₗᵢ`: an `Eq.rec` whose result is
a bundled function in `Type`, rather than a proof in `Prop`. -/
noncomputable def castIso {α β : Type} (h : α = β) : TinyIso α β :=
  h.rec (motive := fun β _ => TinyIso α β) (TinyIso.refl α)

def downstream : TinyIso Bool Bool := TinyIso.refl Bool

noncomputable def composed : TinyIso Nat Bool :=
  (castIso slowTypeEquality).trans downstream

def TinyIso.symm (f : TinyIso α β) : TinyIso β α where
  toFun := f.invFun
  invFun := f.toFun
  leftInv := f.rightInv
  rightInv := f.leftInv

/-- Unfolding composition exposes the transported isometry's `toFun`
projection, reproducing the `Eq.rec`/failed-K probe from TauCeti. -/
theorem composedApply (x : Nat) :
    composed x = downstream (castIso slowTypeEquality x) := by
  rfl

/-- The inverse projection is the corresponding reducer shape from
TauCeti's `chebyshevWeightL2Isometry_symm_apply`. -/
theorem composedSymmApply (x : Bool) :
    composed.symm x = (castIso slowTypeEquality).symm (downstream.symm x) := by
  rfl

end Tests.Ix.Kernel.TauCetiReduction
