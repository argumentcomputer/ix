/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Infer

/-! # The annotation pass

Raw terms carry no binder regimes. `annotate` computes them bottom up: each
`lam`/`forallE` gets the zero condition of its inferred codomain sort, using
the certified `inferA` and `whnf` on the already annotated subterms. The pass
proves that its output erases to the exact supplied term (`annotate_erase`).
Its binder regimes are validated by `inferA` when the declaration is
checked; structural fidelity does not establish their semantic correctness.

Nested inference and normalization failures retain their causes. In
particular, running out of fuel below a binder remains exhaustion, and
unsuccessful conversion remains an unresolved search. -/

namespace Ix.Kernel

open Model Certified

universe u v

variable {β : Type u} [DecidableEq β]

/-- Compute binder annotations. -/
def annotate : Nat → (entries : Environment β) → (Γ : Context β) → VExpr β →
    Search (AExpr β)
  | 0, _, _, _ => .error .exhausted
  | fuel + 1, entries, Γ, e =>
    match e with
    | .bvar i => .ok (.bvar i)
    | .sort l => .ok (.sort l)
    | .const r ls => .ok (.const r ls)
    | .natLit r n => .ok (.natLit r n)
    | .app f a => do
      let f' ← annotate fuel entries Γ f
      let a' ← annotate fuel entries Γ a
      return .app f' a'
    | .proj r i x => do
      let x' ← annotate fuel entries Γ x
      return .proj r i x'
    | .lam D b => do
      let D' ← annotate fuel entries Γ D
      let Γ' := Γ.push D'
      let b' ← annotate fuel entries Γ' b
      let ⟨B, _⟩ ← inferA.{u,v} fuel entries Γ' b'
      let ⟨SB, hSB⟩ ← inferA.{u,v} fuel entries Γ' B
      let ⟨lB, _⟩ ← sortOf (whnf.{u,v} fuel entries Γ' SB) hSB
      return .lam (zeroCondition lB) D' b'
    | .forallE D B => do
      let D' ← annotate fuel entries Γ D
      let Γ' := Γ.push D'
      let B' ← annotate fuel entries Γ' B
      let ⟨SB, hSB⟩ ← inferA.{u,v} fuel entries Γ' B'
      let ⟨lB, _⟩ ← sortOf (whnf.{u,v} fuel entries Γ' SB) hSB
      return .forallE (zeroCondition lB) D' B'
    | .letE t v b => do
      let t' ← annotate fuel entries Γ t
      let v' ← annotate fuel entries Γ v
      let b' ← annotate fuel entries (Γ.push t') b
      return .letE t' v' b'

private theorem search_bind_eq_ok {α γ : Type u} {x : Search α} {f : α → Search γ} {b : γ}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Every successful annotation preserves the exact raw expression. This
does not assert scope or the validity of its binder conditions. -/
theorem annotate_erase {fuel : Nat} {entries : Environment β} {Γ : Context β}
    {raw : VExpr β} {a : AExpr β} (h : annotate.{u,v} fuel entries Γ raw = .ok a) :
    a.erase = raw := by
  induction fuel generalizing Γ raw a with
  | zero => cases h
  | succ fuel ih =>
    cases raw with
    | bvar _ | sort _ | const _ _ | natLit _ _ => cases h; rfl
    | app f x =>
      obtain ⟨f', hf, h⟩ := search_bind_eq_ok h
      obtain ⟨x', hx, h⟩ := search_bind_eq_ok h
      cases h
      simp only [AExpr.erase, ih hf, ih hx]
    | proj r i x =>
      obtain ⟨x', hx, h⟩ := search_bind_eq_ok h
      cases h
      simp only [AExpr.erase, ih hx]
    | lam D b =>
      obtain ⟨D', hD, h⟩ := search_bind_eq_ok h
      obtain ⟨b', hb, h⟩ := search_bind_eq_ok h
      obtain ⟨⟨B, _⟩, _, h⟩ := search_bind_eq_ok h
      obtain ⟨⟨SB, _⟩, _, h⟩ := search_bind_eq_ok h
      obtain ⟨⟨l, _⟩, _, h⟩ := search_bind_eq_ok h
      cases h
      simp only [AExpr.erase, ih hD, ih hb]
    | forallE D B =>
      obtain ⟨D', hD, h⟩ := search_bind_eq_ok h
      obtain ⟨B', hB, h⟩ := search_bind_eq_ok h
      obtain ⟨⟨SB, _⟩, _, h⟩ := search_bind_eq_ok h
      obtain ⟨⟨l, _⟩, _, h⟩ := search_bind_eq_ok h
      cases h
      simp only [AExpr.erase, ih hD, ih hB]
    | letE t v b =>
      obtain ⟨t', ht, h⟩ := search_bind_eq_ok h
      obtain ⟨v', hv, h⟩ := search_bind_eq_ok h
      obtain ⟨b', hb, h⟩ := search_bind_eq_ok h
      cases h
      simp only [AExpr.erase, ih ht, ih hv, ih hb]

/-- Package an exact annotation with its separately checked scope, reusing
the model's reading interface. Binder-condition scope is included in `hs`. -/
def annotationReading {fuel : Nat} {entries : Environment β} {Γ : Context β}
    {raw : VExpr β} {a : AExpr β} {universes depth : Nat}
    (h : annotate.{u,v} fuel entries Γ raw = .ok a) (hs : a.Scope universes depth) :
    Model.Reading universes depth raw := ⟨a, annotate_erase h, hs⟩

/-- Exact reading transfers the raw reference list without discarding
annotation-condition scope, which is a separate obligation. -/
theorem annotate_references {fuel : Nat} {entries : Environment β} {Γ : Context β}
    {raw : VExpr β} {a : AExpr β} (h : annotate.{u,v} fuel entries Γ raw = .ok a) :
    a.references = raw.refs := by
  rw [← annotate_erase h, AExpr.refs_erase]

theorem annotate_raw_scope {fuel : Nat} {entries : Environment β} {Γ : Context β}
    {raw : VExpr β} {a : AExpr β} {universes depth : Nat}
    (h : annotate.{u,v} fuel entries Γ raw = .ok a) (hs : a.Scope universes depth) :
    raw.LevelWF universes ∧ raw.ClosedN depth := by
  rw [← annotate_erase h]
  exact hs.erase

end Ix.Kernel
