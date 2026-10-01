module

public import ConLeche.Rules.Rel
import ConLeche.Kernel.TypeChecker
public import ConLeche.Kernel.CoreIO
import ConLeche.Verify.Knot
import ConLeche.Verify.InferLemmas

public section

/-!
# The bridge's statements: run ⇒ derivation (task #305)

One predicate per fueled entry point of the `.verified` pure knot: an
accepting run at `fuel` yields a derivation in the rules tier
(`ConLeche/Rules/Rel.lean`).  The relation has no mode index — it
describes the `.verified` checker — so the runs are stated at
`.verified` outright; the recomposition (`Model/Rules/Recompose.lean`)
cases on the mode under `hμ : μ.verifiedChecks = true`.

The five are closed by one mutual fuel induction (`Verify/Rules/Bridge.lean`),
whose step is the four `*_bridge_succ` theorems of the lane files
(`RedBridge`, `DefEqBridge`, `InferBridge`) over the shared certificate
bridges (`Certs`).  The zero cases are the checker's own zero-fuel
throws, proved here.

**Mechanical by construction** (ruling 2): every clause of every step
theorem inverts the run with the `Verify/*` inversion lemma of its
site and lands on one rule of `ConLeche/Rules/*` whose premises are
exactly the sub-runs the inversion hands back, each sub-run being at
`fuel` and bridged by an induction hypothesis.
-/

namespace ConLeche.Rules

variable {env : Env}

/-- `whnfCore` at `fuel` is bridged. -/
@[expose] def WhnfCoreBridge (env : Env) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr},
    whnfCore .verified env fuel d e = .ok e' → Red env d e e'

/-- `whnf` at `fuel` is bridged. -/
@[expose] def WhnfBridge (env : Env) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr},
    whnf .verified env fuel d e = .ok e' → Red env d e e'

/-- `isDefEqCore` at `fuel` is bridged. -/
@[expose] def DefEqBridge (env : Env) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr},
    isDefEqCore .verified env fuel d a b = .ok true → DefEq env d a b

/-- `inferTypeCore` at `fuel` is bridged, at the full grade. -/
@[expose] def InferBridge (env : Env) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr},
    inferTypeCore .verified env fuel d e = .ok t → Infer env .full d e t

/-- `inferTypeCoreIO` (the io leaf lane, the `InferClaimIO` subject) at
`fuel` is bridged, at the io grade. -/
@[expose] def InferIOBridge (env : Env) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr},
    inferTypeCoreIO .verified env fuel d e = .ok t → Infer env .io d e t

/-- The knot's io SLOT (`inferTypeIO`, what every internal inference
call site runs) is the io lane at `.verified` (`inferTypeIO_on`), so
its bridge is the lane's. -/
theorem inferTypeIO_bridge {fuel : Nat} (hio : InferIOBridge env fuel)
    {d : Nat} {e t : Expr}
    (h : inferTypeIO .verified env fuel d e = .ok t) : Infer env .io d e t :=
  hio (by rwa [inferTypeIO_on rfl] at h)

/-- `ensureSort` is a reduction to a sort. -/
theorem ensureSort_bridge {fuel : Nat} (hw : WhnfBridge env fuel)
    {d : Nat} {t : Expr} {u : Level}
    (h : ensureSortCore .verified env fuel d t = .ok u) :
    Red env d t (.sort u) :=
  hw (ensureSortCore_inv h)

/-! ## The zero cases: every entry point throws at fuel `0` -/

theorem whnfCore_bridge_zero : WhnfCoreBridge env 0 := by
  intro d e e' h
  rw [whnfCore_zero] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

theorem whnf_bridge_zero : WhnfBridge env 0 := by
  intro d e e' h
  rw [whnf_zero] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

theorem defeq_bridge_zero : DefEqBridge env 0 := by
  intro d a b h
  rw [isDefEqCore_zero] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

theorem infer_bridge_zero : InferBridge env 0 := by
  intro d e t h
  rw [inferTypeCore_zero] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

theorem inferIO_bridge_zero : InferIOBridge env 0 := by
  intro d e t h
  rw [inferTypeCoreIO_zero] at h
  simp [throw, throwThe, MonadExceptOf.throw] at h

end ConLeche.Rules
