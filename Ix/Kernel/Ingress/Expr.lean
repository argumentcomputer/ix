/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Ingress.Reading
import Ix.Kernel.Search

/-! # A proof-carrying Ixon expression reader

The fuel bounds expansion depth, including sharing edges. A forward/cyclic
sharing edge is malformed independently of fuel. Unsupported syntax and a
missing literal-family configuration decline. Successful output carries its
exact structural reading; the proof is erased during execution.
-/

namespace Ix.Kernel.Ingress

private def requireSome (value : Option α) (failure : SearchFailure) :
    Search { result : α // value = some result } :=
  match value with
  | none => .error failure
  | some result => .ok ⟨result, rfl⟩

/-- Read one expression with a decreasing bound on reachable sharing entries.
The usual initial bound is the source sharing table's size. -/
def readExprC (ctx : Context) : (fuel limit : Nat) → (input : Ixon.Expr) →
    Search { output : VExpr Address // ExprReads ctx limit input output }
  | 0, _, _ => .error .exhausted
  | fuel + 1, limit, input =>
    match input with
    | .var i => .ok ⟨.bvar i.toNat, .var⟩
    | .sort i => do
      let level ← requireSome (ctx.level i) (.malformed "universe table index is out of bounds")
      return ⟨.sort level.val, .sort level.property⟩
    | .ref i us => do
      let ref ← requireSome (ctx.external i) (.malformed "reference is missing or has invalid ownership")
      let levels ← requireSome (ctx.levels us.toList) (.malformed "universe argument index is out of bounds")
      return ⟨.const ref.val levels.val, .ref ref.property levels.property⟩
    | .recur i us => do
      let ref ← requireSome (ctx.recursive i) (.malformed "recursive reference is outside this block")
      let levels ← requireSome (ctx.levels us.toList) (.malformed "universe argument index is out of bounds")
      return ⟨.const ref.val levels.val, .recur ref.property levels.property⟩
    | .nat i => do
      let bytes ← requireSome (ctx.blob i) (.malformed "natural literal blob is missing")
      let family ← requireSome ctx.natFamily (.unsupported "natural literal family is not configured")
      return ⟨.natLit family.val (natural bytes.val), .nat bytes.property family.property⟩
    | .str _ => throw (.unsupported "string literals are not supported")
    | .app f a => do
      let f' ← readExprC ctx fuel limit f
      let a' ← readExprC ctx fuel limit a
      return ⟨.app f'.val a'.val, .app f'.property a'.property⟩
    | .lam .many type body => do
      let type' ← readExprC ctx fuel limit type
      let body' ← readExprC ctx fuel limit body
      return ⟨.lam type'.val body'.val, .lam type'.property body'.property⟩
    | .lam _ _ _ => throw (.unsupported "lambda usage mode is not many")
    | .all .many .shared type body => do
      let type' ← readExprC ctx fuel limit type
      let body' ← readExprC ctx fuel limit body
      return ⟨.forallE type'.val body'.val, .all type'.property body'.property⟩
    | .all _ _ _ _ => throw (.unsupported "forall mode is not many/shared")
    | .letE _ type value body => do
      let type' ← readExprC ctx fuel limit type
      let value' ← readExprC ctx fuel limit value
      let body' ← readExprC ctx fuel limit body
      return ⟨.letE type'.val value'.val body'.val,
        .letE type'.property value'.property body'.property⟩
    | .prj i field value => do
      let ref ← requireSome (ctx.external i) (.malformed "projection family is missing or has invalid ownership")
      let value' ← readExprC ctx fuel limit value
      return ⟨.proj ref.val field.toNat value'.val, .prj ref.property value'.property⟩
    | .share i => do
      if earlier : i.toNat < limit then
        let value ← requireSome ctx.source.sharing[i.toNat]? (.malformed "sharing index is out of bounds")
        let value' ← readExprC ctx fuel i.toNat value.val
        return ⟨value'.val, .share earlier value.property value'.property⟩
      else throw (.malformed "sharing reference is not to an earlier entry")

/-- Erase the reading evidence at the public expression boundary. -/
def readExpr (ctx : Context) (fuel : Nat) (input : Ixon.Expr) : Search (VExpr Address) :=
  (readExprC ctx fuel ctx.source.sharing.size input).map Subtype.val

theorem readExpr_reading {ctx : Context} {fuel : Nat} {input : Ixon.Expr}
    {output : VExpr Address} (h : readExpr ctx fuel input = .ok output) :
    ExprReads ctx ctx.source.sharing.size input output := by
  unfold readExpr at h
  cases hc : readExprC ctx fuel ctx.source.sharing.size input with
  | error failure => simp [hc, Except.map] at h
  | ok result =>
    simp [hc, Except.map] at h
    exact h ▸ result.property

/-- Successful reads at different fuel budgets describe the same expression. -/
theorem readExpr_agree {ctx : Context} {fuel₁ fuel₂ : Nat} {input : Ixon.Expr}
    {left right : VExpr Address}
    (h₁ : readExpr ctx fuel₁ input = .ok left) (h₂ : readExpr ctx fuel₂ input = .ok right) :
    left = right := (readExpr_reading h₁).deterministic (readExpr_reading h₂)

end Ix.Kernel.Ingress
