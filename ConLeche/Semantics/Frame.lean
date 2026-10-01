module

public import ConLeche.Verify.InferLeaves

@[expose] public section

/-!
# `SetBase/Frame` — the opened binder's frame conditions

One theorem, `frame_open2`, re-based out of
`SetR/Interp/Steps/InferQ.lean` at THE SEPARATION's S2 (task #161).

It is the **two-edit sever**'s first edit.  `InferQ` is 2U-lane content
and the design review ruled the 2U lane goes to R whole; the graded
lane's `Steps/InferP` imported the whole of it for this one lemma.  The
lemma itself mentions no model at all — it is pure `Expr` scoping
arithmetic (`WScoped`, `looseBVarsBounded`, `LeavesBounded` under
`instantiate1`) — so it belongs BELOW both lanes and the edge dies.

The statement is verbatim, in its original namespace
(`ConLeche.SetR.Interp`), so every consumer sees the same name.
-/

namespace ConLeche.Semantics

open ConLeche (Expr Name)

/-- The frame conditions of an opened binder, *without* the context —
`frame_openR`'s first three components, which need no correspondence in
either currency. -/
theorem frame_open2 {d : Nat} {ty body : Expr}
    (hwty : Expr.WScoped d ty) (hbty : ty.looseBVarsBounded 0 = true)
    (hwb : Expr.WScoped d body)
    (hbb : body.looseBVarsBounded 1 = true)
    (hLty : Expr.LeavesBounded ty)
    (hLbody : Expr.LeavesBounded body) :
    Expr.WScoped (d + 1) (body.instantiate1 (.fvar d ty)) ∧
      (body.instantiate1 (.fvar d ty)).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (body.instantiate1 (.fvar d ty)) := by
  refine ⟨Expr.WScoped.instantiate1 hwty 0 hwb,
    ConLeche.looseBVarsBounded_instantiate1 body 0 hbb, fun l hl => ?_⟩
  rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
  · exact hLbody l h2
  · rw [Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hbty
    · exact hLty l h3

end ConLeche.Semantics
