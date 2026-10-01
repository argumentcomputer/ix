module

public import ConLeche.Verify.Cached.KnotC
public import ConLeche.Verify.BridgeDecl
import ConLeche.Cached.CheckerC

public section

/-!
# Cached checker: the per-declaration faithfulness kit (task #163)

Port of `ConLeche/Verify/SimS.lean` for the cached tier.  The cached core
simulation (`CSOK`/`SimC`, `ConLeche/Verify/Cached/SimC.lean`, knotted in
`ConLeche/Verify/Cached/KnotC.lean`) is stated for *arbitrary* initial
states, so extending the cache lifetime from one entry call to one
declaration needs no new state invariant: this file provides the shared
entry-point simulation lemmas (`opE_*_sim`, `opB_sim`, `opS_sim`) — a
successful shared-state operation run from any `CSOK` state preserves
the invariant and is reproduced by the pure fueled family, keeping the
final state facts instead of discarding them.

Two pieces of the interned kit are *not* restated here:

* `mkFEnv_push` (`ConLeche/Verify/SimS.lean`) is `Expr`-level — the index
  of a cons-extended environment is one insert, definitionally, with no
  reference to any state representation;
* `flushC_csok` (`ConLeche/Verify/Cached/SimC.lean`) is the `flushS_isok`
  mirror already proved with the invariant: after a flush the state
  satisfies `CSOK` for *any* environment, which is what makes the
  driver-directed flush at environment transitions sound.

Against `SimS` the systematic deletions of the tier carry through: no
arena, hence no `Ext` and no readback, and (since task #172 B3a) no
conversion into the cached representation either — the runners pass
their argument through, so both seams collapse to `RelC` facts and a
fabricated node is a plain `pure` (`pureC_eff`).  The `opE` result
relation therefore stays on `Expr` and is state-free.

The driver-level walks composing these along `checkDeclSF` are in
`ConLeche/Verify/Cached/BridgeCS*.lean`.
-/

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr

variable {mode : CheckMode}

/-! ## Shared entry points simulate the fueled families -/

/-- The result relation for the shared expression-valued entry points:
equal values, well-scoped at the call depth (the scopedness of
intermediate results feeds the later call sites of a walk).  State-free
— there is no arena for the relation to be relative to. -/
@[expose] def RelW (d : Nat) (v w : Expr) : Prop :=
  v = w ∧ Expr.WScoped d v

section Runners

variable {env : Env} {s₀ : CState}

/-- Generic unary shared-runner simulation: convert in, run the
simulated knot entry, convert back. -/
theorem opE_sim {pick : CoreFnsI → Nat → Expr → CheckCM Expr}
    {pf : FueledM Expr} {d : Nat} {e : Expr}
    (hsim : ∀ {s₁ : CState} {i : Expr}, CSOK mode env s₁ →
      RelC i e →
      SimC mode env s₁ (RelEC d)
        (pick (coreKnotI mode (mkFEnv env) checkFuel) d i) pf)
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (RelW d) (opE mode (mkFEnv env) pick d e) pf := by
  refine SimC.mono ?_ (hsim hs rfl)
  rintro v' v ⟨rfl, hw⟩
  exact ⟨rfl, hw⟩

/-- Shared `annotate` simulates the fueled family, from any invariant
state. -/
theorem opE_annotate_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelW d) (opE mode (mkFEnv env) (·.annotate) d e)
      ((fueledOpsM mode).annotate env d e) :=
  opE_sim (fun hs₁ hden =>
    (ssimC hμ env henv checkFuel).annotate hs₁ hden hw) hs

/-- Shared `inferType` simulates the fueled family. -/
theorem opE_infer_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelW d) (opE mode (mkFEnv env) (·.infer) d e)
      ((fueledOpsM mode).inferType env d e) :=
  opE_sim (fun hs₁ hden =>
    (ssimC hμ env henv checkFuel).infer hs₁ hden hw) hs

/-- Shared `whnf` simulates the fueled family. -/
theorem opE_whnf_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d e) :
    SimC mode env s₀ (RelW d) (opE mode (mkFEnv env) (·.whnf) d e)
      ((fueledOpsM mode).whnf env d e) :=
  opE_sim (fun hs₁ hden =>
    (ssimC hμ env henv checkFuel).whnf hs₁ hden hw) hs

/-- Shared `isDefEq` simulates the fueled family. -/
theorem opB_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {a b : Expr}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) :
    SimC mode env s₀ RelVC (opB mode (mkFEnv env) d a b)
      ((fueledOpsM mode).isDefEq env d a b) := by
  exact (ssimC hμ env henv checkFuel).defeq hs rfl
    rfl hwa hwb

/-- Shared `ensureSort` simulates the fueled family. -/
theorem opS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d e) :
    SimC mode env s₀ RelVC (opS mode (mkFEnv env) d e)
      ((fueledOpsM mode).ensureSort env d e) := by
  have h1 : SimC mode env s₀ RelVC (opS mode (mkFEnv env) d e)
      (ensureSort (fueledFns mode env) env d e) :=
    ensureSortC_sim (ssimC hμ env henv checkFuel) hs rfl hw
  refine SimC.wr h1 (fun u F h => ⟨F, ?_⟩)
  rw [ensureSort_atF, ensureSort_def] at h
  exact h

end Runners

end ConLeche.Cached
