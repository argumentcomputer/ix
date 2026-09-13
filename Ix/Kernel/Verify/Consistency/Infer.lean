/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Infer
import Ix.Kernel.Verify.Consistency.Judgment

/-!
# Production sort inference in the set-theory model

This theorem examines the actual uncached inference dispatcher and its intern
table update. The intern-table premises are its concrete key coherence and
collision freedom on the table support plus the newly constructed type.
No named-calculus typing or checker-soundness assumption is used.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v
variable {β : Type u} {m : Mode}

/-- Every successful execution of the production sort-inference branch
establishes the model typing postcondition for its actual returned type. -/
theorem inferUncached_sort_sound
    {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β}
    {inferRec : KExpr m → RecM m (KExpr m)} {inferOnly : Bool}
    {methods : Methods m} {before after : TcState m}
    {level : KUniv m} {info : ExprInfo m} {type : KExpr m}
    (coherent : before.env.intern.WF)
    (faithful : KExpr.KeyCollisionFree fun e =>
      before.env.intern.ExprSupport e ∨ e = KExpr.mkSort (KUniv.mkSucc level))
    (accepted : RecM.inferUncached inferRec inferOnly (.sort level info) methods before =
      .ok type after) :
    ModelTyping.{u,v} resolve entries context (.sort level info) type := by
  change EStateM.Result.ok
      (before.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).1
      { before with env := { before.env with intern :=
        (before.env.intern.internExpr (KExpr.mkSort (KUniv.mkSucc level))).2 } } =
    .ok type after at accepted
  cases accepted
  exact ModelTyping.internType coherent faithful (ModelTyping.sort level info)

end Ix.Kernel.Consistency
