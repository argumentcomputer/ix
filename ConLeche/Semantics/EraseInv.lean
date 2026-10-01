module

public import ConLeche.Kernel.StdAxioms

@[expose] public section

/-!
# `erasePw` head inversions (task #161, S1)

THE SEPARATION's shared base: the constant-head inversion of the
checker's erasure, lifted out of `SetR/Install/Axiom.lean` (design
census §3.3, edge 6).  It is **pure `Expr` syntax** — no `EnvS`, no
valuation, no relation — and both lanes invert through it: the
collapsed lane at the axiom install, the graded lane at
`Interp/ErasePwInv.lean`'s composite heads.

Statements verbatim from their old home; the namespace is unchanged.
-/

namespace ConLeche.Semantics

/-- `erasePw` fixes a constant (task #161 P5: `matchesPin` compares
through `Expr.erasePw`, so a pinned-shape inversion has to see through
that erasure).  Head inversion. -/
theorem erasePw_const_invS {e : Expr} {n : Name} {us : List Level}
    (h : e.erasePw = .const n us) : e = .const n us := by
  cases e <;> simp only [Expr.erasePw] at h <;> first
    | exact h
    | exact nomatch h


end ConLeche.Semantics
