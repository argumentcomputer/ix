/-
Ported from Ix branch jcb/ix-kernel-consistency at ad60e5f6dd23655da79cf9898d2b6b3fefbe8658.
Source: Ix/Theory/Expr.lean
Transformations: `Ix.Theory` renamed to `Ix.Kernel` in module names, imports,
namespaces, qualified names, and documentation paths; this header added.
-/
/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Ref
import Ix.Kernel.VLevel

/-!
# Anonymous kernel expressions

`VExpr β` is the binder-name-free term syntax used by the Theory. Constants
refer to members of content-addressed blocks through `ConstRef β`; projections
and natural-number literals remain structural instead of being expanded by a
front-end translation.
-/

namespace Ix.Kernel

inductive VExpr (β : Type u) where
  | bvar (deBruijnIndex : Nat)
  | sort (u : VLevel)
  | const (ref : ConstRef β) (levels : List VLevel)
  | app (fn arg : VExpr β)
  | lam (binderType body : VExpr β)
  | forallE (binderType body : VExpr β)
  | proj (ref : ConstRef β) (index : Nat) (expr : VExpr β)
  | natLit (value : Nat)
deriving DecidableEq, Hashable

instance : Inhabited (VExpr β) := ⟨.sort .zero⟩

/-- Shift a de Bruijn index by `n` when it is at or above cutoff `k`. -/
def liftVar (n i : Nat) (k := 0) : Nat := if i < k then i else n + i

namespace VExpr

/-- Iterated application, with arguments ordered from left to right. -/
def appN (f : VExpr β) : List (VExpr β) → VExpr β
  | [] => f
  | a :: as => (f.app a).appN as

variable (n : Nat) in
/-- Insert `n` variables at cutoff `k`. -/
def liftN : VExpr β → (k : _ := 0) → VExpr β
  | .bvar i, k => .bvar (liftVar n i k)
  | .sort u, _ => .sort u
  | .const r us, _ => .const r us
  | .app fn arg, k => .app (fn.liftN k) (arg.liftN k)
  | .lam ty body, k => .lam (ty.liftN k) (body.liftN (k + 1))
  | .forallE ty body, k => .forallE (ty.liftN k) (body.liftN (k + 1))
  | .proj r i e, k => .proj r i (e.liftN k)
  | .natLit value, _ => .natLit value

abbrev lift (e : VExpr β) : VExpr β := liftN 1 e

/-- Every free de Bruijn index in the expression is below `k`. -/
def ClosedN : VExpr β → (k : _ := 0) → Prop
  | .bvar i, k => i < k
  | .sort .., _ | .const .., _ | .natLit .., _ => True
  | .app fn arg, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k + 1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k + 1)
  | .proj _ _ e, k => e.ClosedN k

abbrev Closed (e : VExpr β) : Prop := ClosedN e

variable (levels : List VLevel) in
/-- Instantiate the universe parameters in an expression. -/
def instL : VExpr β → VExpr β
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst levels)
  | .const r us => .const r (us.map (VLevel.inst levels))
  | .app fn arg => .app fn.instL arg.instL
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL
  | .proj r i e => .proj r i e.instL
  | .natLit value => .natLit value

/-- Replace interpreted constant occurrences by closed values, instantiated
at the occurrence's universe arguments. Projection annotations remain store
references; only expression-position constants are interpreted. -/
def substConst (interp : ConstRef β → Option (VExpr β)) :
    VExpr β → VExpr β
  | .bvar index => .bvar index
  | .sort level => .sort level
  | .const ref levels =>
      match interp ref with
      | some value => value.instL levels
      | none => .const ref levels
  | .app function argument =>
      .app (function.substConst interp) (argument.substConst interp)
  | .lam domain body =>
      .lam (domain.substConst interp) (body.substConst interp)
  | .forallE domain body =>
      .forallE (domain.substConst interp) (body.substConst interp)
  | .proj ref field expression =>
      .proj ref field (expression.substConst interp)
  | .natLit value => .natLit value

/-- All universe parameters in an expression are below `U`. -/
def LevelWF (U : Nat) : VExpr β → Prop
  | .bvar _ | .natLit _ => True
  | .sort l => l.WF U
  | .const _ levels => ∀ l ∈ levels, l.WF U
  | .app e₁ e₂ | .lam e₁ e₂ | .forallE e₁ e₂ => e₁.LevelWF U ∧ e₂.LevelWF U
  | .proj _ _ e => e.LevelWF U

/-- Instantiate de Bruijn index `k` in a single variable occurrence. -/
def instVar (i : Nat) (e : VExpr β) (k := 0) : VExpr β :=
  if i < k then .bvar i else if i = k then liftN k e else .bvar (i - 1)

/-- Instantiate de Bruijn index `k` throughout an expression. -/
def inst : VExpr β → VExpr β → (k : _ := 0) → VExpr β
  | .bvar i, e, k => instVar i e k
  | .sort u, _, _ => .sort u
  | .const r us, _, _ => .const r us
  | .app fn arg, e, k => .app (fn.inst e k) (arg.inst e k)
  | .lam ty body, e, k => .lam (ty.inst e k) (body.inst e (k + 1))
  | .forallE ty body, e, k => .forallE (ty.inst e k) (body.inst e (k + 1))
  | .proj r i p, e, k => .proj r i (p.inst e k)
  | .natLit value, _, _ => .natLit value

/-- Remove `n` variables at cutoff `k`, using `default` for missing terms. -/
def unliftN (e : VExpr β) (n k : Nat) : VExpr β :=
  match n with
  | 0 => e
  | n + 1 => unliftN (e.inst default k) n k

/-- Structural form of `Skips`. -/
def Skips' (n : Nat) : VExpr β → (k : _ := 0) → Prop
  | .bvar i, k => i < k + n → i < k
  | .sort .., _ | .const .., _ | .natLit .., _ => True
  | .app fn arg, k => fn.Skips' n k ∧ arg.Skips' n k
  | .lam ty body, k => ty.Skips' n k ∧ body.Skips' n (k + 1)
  | .forallE ty body, k => ty.Skips' n k ∧ body.Skips' n (k + 1)
  | .proj _ _ e, k => e.Skips' n k

/-- `[bvar (off+m-1), ..., bvar off]`. -/
def bvarRevRange (off : Nat) : Nat → List (VExpr β)
  | 0 => []
  | m + 1 => .bvar (off + m) :: bvarRevRange off m

/-- Iterated lambda; the binder list is outermost first. -/
def lamN : List (VExpr β) → VExpr β → VExpr β
  | [], e => e
  | A :: As, e => .lam A (lamN As e)

/-- Iterated pi; the binder list is outermost first. -/
def forallN : List (VExpr β) → VExpr β → VExpr β
  | [], e => e
  | A :: As, e => .forallE A (forallN As e)

/-- Insert `n` binders below a telescope at depth `k`. -/
def liftTelN (n : Nat) : List (VExpr β) → Nat → List (VExpr β)
  | [], _ => []
  | A :: As, k => A.liftN n k :: liftTelN n As (k + 1)

/-- The first `n` binder types of an iterated pi, outermost first. -/
def telN : Nat → VExpr β → List (VExpr β)
  | 0, _ => []
  | n + 1, .forallE A rest => A :: telN n rest
  | _ + 1, _ => []

/-- Strip up to `n` binders from an iterated pi. -/
def dropN : Nat → VExpr β → VExpr β
  | 0, e => e
  | n + 1, .forallE _ rest => dropN n rest
  | _ + 1, e => e

/-- The result after all leading pi binders. -/
def resultOf : VExpr β → VExpr β
  | .forallE _ rest => resultOf rest
  | e => e

/-- Collect application arguments, outermost first. -/
def appArgs : VExpr β → List (VExpr β) → List (VExpr β)
  | .app f a, acc => appArgs f (a :: acc)
  | _, acc => acc

/-- Remove every application node and return its head. -/
def appHead : VExpr β → VExpr β
  | .app f _ => appHead f
  | e => e

/-- Instantiate a term under each entry of a telescope. -/
def instTelN (a : VExpr β) : List (VExpr β) → Nat → List (VExpr β)
  | [], _ => []
  | A :: As, k => A.inst a k :: instTelN a As (k + 1)

/-- Consume an outermost-first argument list from a body. -/
def instRev : VExpr β → List (VExpr β) → VExpr β
  | C, [] => C
  | C, e :: es => instRev (C.inst e es.length) es

/-- Consume an outermost-first argument list above a fixed binder offset. -/
def instRevAt : VExpr β → List (VExpr β) → Nat → VExpr β
  | e, [], _ => e
  | e, a :: as, k => instRevAt (e.inst a (k + as.length)) as k

/-- Whether an expression mentions a particular constant reference. -/
def mentions [DecidableEq β] : VExpr β → ConstRef β → Bool
  | .bvar _, _ | .sort _, _ | .natLit _, _ => false
  | .const r _, target => decide (r = target)
  | .app e₁ e₂, target | .lam e₁ e₂, target | .forallE e₁ e₂, target =>
    e₁.mentions target || e₂.mentions target
  | .proj r _ e, target => decide (r = target) || e.mentions target

/-- All constant references occurring in an expression, including projection heads. -/
def refs : VExpr β → List (ConstRef β)
  | .bvar _ | .sort _ | .natLit _ => []
  | .const r _ => [r]
  | .app e₁ e₂ | .lam e₁ e₂ | .forallE e₁ e₂ => e₁.refs ++ e₂.refs
  | .proj r _ e => r :: e.refs

end VExpr

/-- A context embedding represented by skips and retained binders. -/
inductive Lift : Type where
  | refl
  | skip (tail : Lift)
  | cons (tail : Lift)

namespace Lift

@[simp] def skipN (l : Lift) : Nat → Lift
  | 0 => l
  | n + 1 => .skip (skipN l n)

@[simp] def consN (l : Lift) : Nat → Lift
  | 0 => l
  | n + 1 => .cons (consN l n)

@[simp] def comp (l₁ l₂ : Lift) : Lift :=
  match l₂, l₁ with
  | .refl, l₁ => l₁
  | .skip l₂, l₁ => .skip (l₁.comp l₂)
  | .cons l₂, .refl => .cons l₂
  | .cons l₂, .skip l₁ => .skip (l₁.comp l₂)
  | .cons l₂, .cons l₁ => .cons (l₁.comp l₂)

@[simp] def dom : Lift → Nat
  | .refl => 0
  | .skip l => l.dom
  | .cons l => l.dom + 1

@[simp] def size : Lift → Nat
  | .refl => 0
  | .skip l | .cons l => l.size + 1

@[simp] def depth : Lift → Nat
  | .refl => 0
  | .skip l => l.depth + 1
  | .cons l => l.depth

@[simp] protected def liftVar : Lift → Nat → Nat
  | .refl, n => n
  | .skip l, n => l.liftVar n + 1
  | .cons _, 0 => 0
  | .cons l, n + 1 => l.liftVar n + 1

@[simp] def diff : Lift → Lift → Lift
  | .refl, _ => .refl
  | l, .refl => l
  | .skip l₁, .skip l₂ | .cons l₁, .skip l₂ => diff l₁ l₂
  | .skip l₁, .cons l₂ => .skip (diff l₁ l₂)
  | .cons l₁, .cons l₂ => .cons (l₁.diff l₂)

end Lift

namespace VExpr

@[simp] def lift' : VExpr β → Lift → VExpr β
  | .bvar i, ρ => .bvar (ρ.liftVar i)
  | .sort u, _ => .sort u
  | .const r us, _ => .const r us
  | .app fn arg, ρ => .app (fn.lift' ρ) (arg.lift' ρ)
  | .lam ty body, ρ => .lam (ty.lift' ρ) (body.lift' ρ.cons)
  | .forallE ty body, ρ => .forallE (ty.lift' ρ) (body.lift' ρ.cons)
  | .proj r i e, ρ => .proj r i (e.lift' ρ)
  | .natLit value, _ => .natLit value

end VExpr
end Ix.Kernel
