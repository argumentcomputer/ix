module

public import ConLeche.Verify.Rules.Defs
import ConLeche.Verify.Rules.RedBridge
import ConLeche.Verify.Rules.DefEqBridge
import ConLeche.Verify.Rules.InferBridge

public section

/-!
# The bridge, closed (task #305)

The five bridges at every fuel: one mutual fuel induction, the shape
of `checkSoundAtP5`'s (`Model/Rules/Recompose.lean`), with the zero cases
from `Defs` and the step from the three lane files.  Proved, and so
is everything it consumes: the branch carries no `sorry`.
-/

namespace ConLeche.Rules

variable {env : Env}

/-- **The bridge**: an accepting run of any of the five entry points
of the `.verified` pure knot, at any fuel, yields a derivation. -/
theorem bridge (env : Env) :
    ∀ fuel : Nat,
      WhnfCoreBridge env fuel ∧ WhnfBridge env fuel ∧ DefEqBridge env fuel ∧
        InferBridge env fuel ∧ InferIOBridge env fuel := by
  intro fuel
  induction fuel with
  | zero =>
    exact ⟨whnfCore_bridge_zero, whnf_bridge_zero, defeq_bridge_zero,
      infer_bridge_zero, inferIO_bridge_zero⟩
  | succ fuel ih =>
    obtain ⟨hwc, hw, hd, hi, hio⟩ := ih
    exact ⟨whnfCore_bridge_succ hwc hw hd hio, whnf_bridge_succ hwc hw,
      defeq_bridge_succ hwc hw hd hio, infer_bridge_succ hw hd hi hio,
      inferIO_bridge_succ hw hd hio⟩

theorem whnfCore_bridge {fuel d : Nat} {e e' : Expr}
    (h : whnfCore .verified env fuel d e = .ok e') : Red env d e e' :=
  (bridge env fuel).1 h

theorem whnf_bridge {fuel d : Nat} {e e' : Expr}
    (h : whnf .verified env fuel d e = .ok e') : Red env d e e' :=
  (bridge env fuel).2.1 h

theorem isDefEqCore_bridge {fuel d : Nat} {a b : Expr}
    (h : isDefEqCore .verified env fuel d a b = .ok true) : DefEq env d a b :=
  (bridge env fuel).2.2.1 h

theorem inferTypeCore_bridge {fuel d : Nat} {e t : Expr}
    (h : inferTypeCore .verified env fuel d e = .ok t) : Infer env .full d e t :=
  (bridge env fuel).2.2.2.1 h

theorem inferTypeCoreIO_bridge {fuel d : Nat} {e t : Expr}
    (h : inferTypeCoreIO .verified env fuel d e = .ok t) : Infer env .io d e t :=
  (bridge env fuel).2.2.2.2 h

end ConLeche.Rules
