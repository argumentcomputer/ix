/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Ingress.Reading

/-! # Layout retained for exact Ixon egress

Ingress expands sharing and table indexes and erases every Ixon v3 contract.
Those choices cannot be recovered from a raw kernel term. This layout keeps
only the choices needed to reconstruct that spelling; variable indexes and
projection field positions are rebuilt from the kernel payload. `rebuild`
alone is a layout operation. The checked writer separately validates that
its output reads as the complete supplied kernel term.
-/

namespace Ix.Kernel.Egress

/-- Convert a kernel index without silently narrowing it. -/
def word (n : Nat) : Option UInt64 :=
  let value := UInt64.ofNat n
  if value.toNat = n then some value else none

@[simp] theorem word_toNat (n : UInt64) : word n.toNat = some n := by
  simp [word]

theorem word_reading {n : Nat} {value : UInt64} (h : word n = some value) : value.toNat = n := by
  dsimp only [word] at h
  by_cases bound : (UInt64.ofNat n).toNat = n
  · simp only [ite_eq_left bound, Option.some.injEq] at h
    exact h ▸ bound
  · simp only [ite_eq_right bound] at h
    cases h

inductive ExprLayout where
  | var
  | sort (index : UInt64)
  | ref (index : UInt64) (universes : Array UInt64)
  | recur (index : UInt64) (universes : Array UInt64)
  | nat (index : UInt64)
  | app (function argument : ExprLayout)
  | lam (contract : Ixon.BinderContract) (type body : ExprLayout)
  | all (contract : Ixon.BinderContract) (result : Ixon.ValueContract) (type body : ExprLayout)
  | letE (contract : Ixon.LetContract) (type value body : ExprLayout)
  | prj (index : UInt64) (value : ExprLayout)
  | share (index : UInt64)
  | unsupported
  deriving Repr

def ExprLayout.ofExpr : Ixon.Expr → ExprLayout
  | .var _ => .var
  | .sort i => .sort i
  | .ref i us => .ref i us
  | .recur i us => .recur i us
  | .nat i => .nat i
  | .app f a => .app (ofExpr f) (ofExpr a)
  | .lam contract type body => .lam contract (ofExpr type) (ofExpr body)
  | .all contract result type body => .all contract result (ofExpr type) (ofExpr body)
  | .letE contract type value body => .letE contract (ofExpr type) (ofExpr value) (ofExpr body)
  | .prj i _ value => .prj i (ofExpr value)
  | .share i => .share i
  | .str _ => .unsupported

/-- Rebuild syntax with the retained table/sharing choices. Payload agreement
with those tables is established by the checked writer, not by this function. -/
def ExprLayout.rebuild : ExprLayout → VExpr Address → Option Ixon.Expr
  | .var, .bvar i => return .var (← word i)
  | .sort i, .sort _ => some (.sort i)
  | .ref i us, .const _ _ => some (.ref i us)
  | .recur i us, .const _ _ => some (.recur i us)
  | .nat i, .natLit _ _ => some (.nat i)
  | .app fl al, .app f a => return .app (← fl.rebuild f) (← al.rebuild a)
  | .lam contract tl bl, .lam type body =>
    return .lam contract (← tl.rebuild type) (← bl.rebuild body)
  | .all contract result tl bl, .forallE type body =>
    return .all contract result (← tl.rebuild type) (← bl.rebuild body)
  | .letE contract tl vl bl, .letE type value body =>
    return .letE contract (← tl.rebuild type) (← vl.rebuild value) (← bl.rebuild body)
  | .prj i vl, .proj _ field value => return .prj i (← word field) (← vl.rebuild value)
  | .share i, _ => some (.share i)
  | _, _ => none

/-- Rebuilding from an exact reading recovers the original expression,
including repeated table slots, sharing choices, and every contract. -/
theorem ExprLayout.rebuild_reading {ctx : Ingress.Context} {limit : Nat}
    {source : Ixon.Expr} {target : VExpr Address}
    (h : Ingress.ExprReads ctx limit source target) :
    (ofExpr source).rebuild target = some source := by
  induction h <;> simp_all [ofExpr, rebuild]

end Ix.Kernel.Egress
