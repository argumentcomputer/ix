/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Level
import Ix.Kernel.Verify.Expr
import Ix.Theory.Expr

/-!
# Reading kernel expressions into the consistency model

References are resolved to explicit block/member/constructor coordinates.
The reader uses the expression tree, not cached hashes or scope annotations.
It preserves projections and natural literals, and expands a let by
capture-avoiding substitution. Free variables, unresolved references, and
string literals have no reading in this initial fragment.

The theorems below connect the production hash-equality fast path and intern
table to this reading. Their finite-support collision hypotheses are retained;
no global hash-injectivity assumption is introduced.
-/

namespace Ix.Kernel.Consistency

universe u
variable {β : Type u} {m : Mode}

/-- A structural reading into the new theory. The reference resolver will be
supplied by the declaration/store refinement; an unknown address fails. -/
def readExpr? (resolve : Address → Option (Theory.ConstRef β)) :
    KExpr m → Option (Theory.VExpr β)
  | .var index _ _ => some (.bvar index.toNat)
  | .fvar .. => none
  | .sort level _ => some (.sort (readLevel level))
  | .const id levels _ => do
      let ref ← resolve id.addr
      return .const ref (levels.toList.map readLevel)
  | .app fn arg _ => do
      return .app (← readExpr? resolve fn) (← readExpr? resolve arg)
  | .lam _ _ domain body _ => do
      return .lam (← readExpr? resolve domain) (← readExpr? resolve body)
  | .all _ _ domain body _ => do
      return .forallE (← readExpr? resolve domain) (← readExpr? resolve body)
  | .letE _ domain value body _ _ => do
      let _ ← readExpr? resolve domain
      let value ← readExpr? resolve value
      let body ← readExpr? resolve body
      return body.inst value
  | .prj id index value _ => do
      let ref ← resolve id.addr
      return .proj ref index.toNat (← readExpr? resolve value)
  | .nat value _ _ => some (.natLit value)
  | .str .. => none

/-- Hashing and display metadata do not change a smart-constructed sort. -/
@[simp] theorem readExpr?_mkSort
    (resolve : Address → Option (Theory.ConstRef β)) (u : KUniv m) :
    readExpr? resolve (KExpr.mkSort u) = some (.sort (readLevel u)) := rfl

/-- Kernel metadata erasure preserves the exact model syntax. -/
@[simp] theorem readExpr?_eraseMeta
    (resolve : Address → Option (Theory.ConstRef β)) (e : KExpr m) :
    readExpr? resolve e.eraseMeta = readExpr? resolve e := by
  induction e <;>
    simp_all [readExpr?, KExpr.eraseMeta, KId.eraseMeta,
      Array.toList_map, List.map_map, Function.comp_def]

/-- The production `BEq` fast path preserves the model reading when the
specific compared expressions have faithful addresses. -/
theorem beq_readExpr? {resolve : Address → Option (Theory.ConstRef β)}
    {left right : KExpr m} (faithful : left.AddrFaithful right)
    (equal : (left == right) = true) :
    readExpr? resolve left = readExpr? resolve right := by
  have erased := faithful (KExpr.beq_def left right ▸ equal)
  simpa only [readExpr?_eraseMeta] using
    congrArg (readExpr? resolve) erased

/-- The production intern table preserves the model reading of a candidate.
Collision-freedom is required only on the table support plus that candidate. -/
theorem internExpr_readExpr? {resolve : Address → Option (Theory.ConstRef β)}
    {table : InternTable m} {e : KExpr m} (coherent : table.WF)
    (faithful : KExpr.KeyCollisionFree fun v => table.ExprSupport v ∨ v = e) :
    readExpr? resolve (table.internExpr e).1 = readExpr? resolve e := by
  simpa only [readExpr?_eraseMeta] using
    congrArg (readExpr? resolve) (table.internExpr_eraseMeta coherent faithful)

end Ix.Kernel.Consistency
