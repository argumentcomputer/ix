module

public import ConLeche.Semantics.EraseInv
import ConLeche.Verify.Denote -- shake: keep (the `open ConLeche.Term` below; task #223)

public section

/-!
# The `erasePw` head inversions (task #161)

`ConstantVal.matchesPin` compares through `erasePw`.
`Install/Axiom.lean` has the constant-head inversion; the pinned
telescopes need the four remaining heads, and doing the erasure once
here keeps every consumer's chain one step per node.

These lemmas landed in `Interp/AxiomBitsP.lean` (ENDGAME A) and moved
here **verbatim** at ENDGAME D, when the reduce-operation pin's shape
lemma (`Interp/ReduceOps.lean`) needed them from *below* `HarvestP`
— which `AxiomBitsP` imports.  Nothing else changed.
-/

namespace ConLeche.Model
open ConLeche.Semantics

open ConLeche.Term ConLeche.Verify
open ConLeche (Expr Name Level BinderMeta)

/-- `erasePw` inversion at a `∀`: the head is a `∀`, and
its meta is exactly what the comparison forgives. -/
theorem erasePwNames_forallE_invS {e : Expr} {ty b : Expr}
    {m : BinderMeta}
    (h : e.erasePw = .forallE ty b m) :
    ∃ ty' b' m', e = .forallE ty' b' m' ∧
      ty'.erasePw = ty ∧ b'.erasePw = b := by
  cases e with
  | forallE ty' b' m' =>
    simp only [Expr.erasePw, Expr.forallE.injEq] at h
    exact ⟨ty', b', m', rfl, h.1, h.2.1⟩
  | _ => simp only [Expr.erasePw] at h; exact nomatch h

/-- `erasePw` inversion at a sort (the erasure fixes it). -/
theorem erasePwNames_sort_invS {e : Expr} {u : Level}
    (h : e.erasePw = .sort u) : e = .sort u := by
  cases e with
  | sort u' => simp only [Expr.erasePw] at h; rw [h]
  | _ => simp only [Expr.erasePw] at h; exact nomatch h

/-- `erasePw` inversion at an application. -/
theorem erasePwNames_app_invS {e : Expr} {f a : Expr}
    (h : e.erasePw = .app f a) :
    ∃ f' a', e = .app f' a' ∧ f'.erasePw = f ∧
      a'.erasePw = a := by
  cases e with
  | app f' a' =>
    simp only [Expr.erasePw, Expr.app.injEq] at h
    exact ⟨f', a', rfl, h.1, h.2⟩
  | _ => simp only [Expr.erasePw] at h; exact nomatch h

/-- `erasePw` inversion at a constant (`Install/Axiom.lean`'s head
inversion). -/
theorem erasePwNames_const_invS {e : Expr} {n : Name} {us : List Level}
    (h : e.erasePw = .const n us) : e = .const n us :=
  erasePw_const_invS h

/-- `erasePw` inversion at a bound variable. -/
theorem erasePwNames_bvar_invS {e : Expr} {i : Nat}
    (h : e.erasePw = .bvar i) : e = .bvar i := by
  cases e with
  | bvar i' => simp only [Expr.erasePw] at h; rw [h]
  | _ => simp only [Expr.erasePw] at h; exact nomatch h


end ConLeche.Model
