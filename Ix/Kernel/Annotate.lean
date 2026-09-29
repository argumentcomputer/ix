/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Infer

/-! # The annotation pass

Raw terms carry no binder regimes. `annotate` computes them bottom up: each
`lam`/`forallE` gets the zero condition of its inferred codomain sort, using
the certified `inferA` and `whnf` on the already annotated subterms. The pass
itself proves nothing; its output is validated by `inferA` when the
declaration is checked, so a wrong annotation is rejected there, never
accepted. This is con-leche's arrangement: an unverified annotate pass and a
verified validator.

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
      let b' ← annotate fuel entries (Γ.push D') b
      let ⟨B, _⟩ ← inferA.{u,v} fuel entries (Γ.push D') b'
      let ⟨SB, hSB⟩ ← inferA.{u,v} fuel entries (Γ.push D') B
      let ⟨lB, _⟩ ← sortOf (whnf.{u,v} fuel entries (Γ.push D') SB) hSB
      return .lam (zeroCondition lB) D' b'
    | .forallE D B => do
      let D' ← annotate fuel entries Γ D
      let B' ← annotate fuel entries (Γ.push D') B
      let ⟨SB, hSB⟩ ← inferA.{u,v} fuel entries (Γ.push D') B'
      let ⟨lB, _⟩ ← sortOf (whnf.{u,v} fuel entries (Γ.push D') SB) hSB
      return .forallE (zeroCondition lB) D' B'
    | .letE t v b => do
      let t' ← annotate fuel entries Γ t
      let v' ← annotate fuel entries Γ v
      let b' ← annotate fuel entries (Γ.push t') b
      return .letE t' v' b'

end Ix.Kernel
