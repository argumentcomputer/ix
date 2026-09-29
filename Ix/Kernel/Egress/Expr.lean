/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Egress.Layout
import Ix.Kernel.Ingress.Expr

namespace Ix.Kernel.Egress

/-- Rebuild with a retained layout, then validate its complete reading.
In particular a shared/table leaf cannot conceal a changed kernel payload. -/
def writeExprC (ctx : Ingress.Context) (fuel limit : Nat) (layout : ExprLayout)
    (target : VExpr Address) : Search { source : Ixon.Expr // Ingress.ExprReads ctx limit source target } := do
  let some source := layout.rebuild target |
    throw (.malformed "expression does not fit its Ixon layout or an index exceeds UInt64")
  let reading ← Ingress.readExprC ctx fuel limit source
  if same : reading.val = target then
    return ⟨source, same ▸ reading.property⟩
  else throw (.malformed "Ixon layout resolves to a different kernel expression")

def writeExpr (ctx : Ingress.Context) (fuel : Nat) (layout : ExprLayout)
    (target : VExpr Address) : Search Ixon.Expr :=
  (writeExprC ctx fuel ctx.source.sharing.size layout target).map Subtype.val

theorem writeExpr_reading {ctx : Ingress.Context} {fuel : Nat} {layout : ExprLayout}
    {target : VExpr Address} {source : Ixon.Expr}
    (h : writeExpr ctx fuel layout target = .ok source) :
    Ingress.ExprReads ctx ctx.source.sharing.size source target := by
  obtain ⟨result, _, same⟩ := Except.map_eq_ok h
  exact same ▸ result.property

/-- A successful reader and the checked writer use the same depth bound. -/
theorem writeExpr_roundtrip {ctx : Ingress.Context} {fuel : Nat}
    {source : Ixon.Expr} {target : VExpr Address}
    (h : Ingress.readExpr ctx fuel source = .ok target) :
    writeExpr ctx fuel (ExprLayout.ofExpr source) target = .ok source := by
  have rebuilt := ExprLayout.rebuild_reading (Ingress.readExpr_reading h)
  unfold Ingress.readExpr at h
  obtain ⟨reading, success, same⟩ := Except.map_eq_ok h
  simp [writeExpr, writeExprC, rebuilt, success, bind, pure, Except.bind, Except.pure, Except.map, same]

end Ix.Kernel.Egress
