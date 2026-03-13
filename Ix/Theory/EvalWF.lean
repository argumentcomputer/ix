/-
  Ix.Theory.EvalWF: Evaluation preserves well-formedness.

  If an expression is well-scoped (ClosedN) and its environment is well-formed (EnvWF),
  then eval_s produces a well-formed value (ValWF).
  Similarly, apply_s preserves well-formedness.
-/
import Ix.Theory.WF

namespace Ix.Theory

variable {L : Type}

-- Bind decomposition for Option.bind (used by eval_s equation lemmas)
private theorem option_bind_eq_some {x : Option α} {f : α → Option β} {b : β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp [Option.bind]

-- eval_s/apply_s equation lemmas (hold by rfl)
private theorem eval_s_zero : eval_s 0 e env = (none : Option (SVal L)) := rfl
private theorem eval_s_bvar : eval_s (n+1) (.bvar idx : SExpr L) env = env[idx]? := rfl
private theorem eval_s_sort : eval_s (n+1) (.sort u : SExpr L) env = some (.sort u) := rfl
private theorem eval_s_const' : eval_s (n+1) (.const c ls : SExpr L) env = some (.neutral (.const c ls) []) := rfl
private theorem eval_s_lit : eval_s (n+1) (.lit l : SExpr L) env = some (.lit l) := rfl
private theorem eval_s_proj : eval_s (n+1) (.proj t i s : SExpr L) env = (none : Option (SVal L)) := rfl
private theorem eval_s_app : eval_s (n+1) (.app fn arg : SExpr L) env =
    (eval_s n fn env).bind fun fv => (eval_s n arg env).bind fun av => apply_s n fv av := rfl
private theorem eval_s_lam : eval_s (n+1) (.lam dom body : SExpr L) env =
    (eval_s n dom env).bind fun dv => some (.lam dv body env) := rfl
private theorem eval_s_forallE : eval_s (n+1) (.forallE dom body : SExpr L) env =
    (eval_s n dom env).bind fun dv => some (.pi dv body env) := rfl
private theorem eval_s_letE : eval_s (n+1) (.letE ty val body : SExpr L) env =
    (eval_s n val env).bind fun vv => eval_s n body (vv :: env) := rfl
private theorem apply_s_zero : apply_s 0 fn arg = (none : Option (SVal L)) := rfl
private theorem apply_s_lam : apply_s (n+1) (.lam dom body fenv : SVal L) arg =
    eval_s n body (arg :: fenv) := rfl
private theorem apply_s_neutral : apply_s (n+1) (.neutral hd spine : SVal L) arg =
    some (.neutral hd (spine ++ [arg])) := rfl

private theorem eval_apply_preserves_wf_aux (fuel : Nat) :
    (∀ (e : SExpr L) (env : List (SVal L)) (d : Nat) (v : SVal L),
      eval_s fuel e env = some v →
      SExpr.ClosedN e env.length → EnvWF env d → ValWF v d) ∧
    (∀ (fn arg : SVal L) (d : Nat) (v : SVal L),
      apply_s fuel fn arg = some v →
      ValWF fn d → ValWF arg d → ValWF v d) := by
  induction fuel with
  | zero =>
    exact ⟨fun _ _ _ _ h => by rw [eval_s_zero] at h; exact absurd h nofun,
           fun _ _ _ _ h => by rw [apply_s_zero] at h; exact absurd h nofun⟩
  | succ n ih =>
    obtain ⟨ihe, iha⟩ := ih
    constructor
    · intro e env d v hev hcl henv
      cases e with
      | bvar idx =>
        rw [eval_s_bvar] at hev
        simp [SExpr.ClosedN] at hcl
        obtain ⟨w, heq, hwf⟩ := henv.getElem? hcl
        rw [heq] at hev; cases hev
        exact hwf
      | sort _ =>
        rw [eval_s_sort] at hev
        cases hev; exact .sort
      | const _ ls =>
        rw [eval_s_const'] at hev
        cases hev; exact .neutral .const .nil
      | lit _ =>
        rw [eval_s_lit] at hev
        cases hev; exact .lit
      | proj _ _ _ =>
        rw [eval_s_proj] at hev
        exact absurd hev nofun
      | app fn arg =>
        rw [eval_s_app] at hev
        simp only [option_bind_eq_some] at hev
        obtain ⟨fv, hfn, av, harg, happ⟩ := hev
        simp [SExpr.ClosedN] at hcl
        exact iha fv av d v happ
          (ihe fn env d fv hfn hcl.1 henv)
          (ihe arg env d av harg hcl.2 henv)
      | lam dom body =>
        rw [eval_s_lam] at hev
        simp only [option_bind_eq_some] at hev
        obtain ⟨dv, hdom, hret⟩ := hev
        cases hret
        simp [SExpr.ClosedN] at hcl
        exact .lam (ihe dom env d dv hdom hcl.1 henv) hcl.2 henv
      | forallE dom body =>
        rw [eval_s_forallE] at hev
        simp only [option_bind_eq_some] at hev
        obtain ⟨dv, hdom, hret⟩ := hev
        cases hret
        simp [SExpr.ClosedN] at hcl
        exact .pi (ihe dom env d dv hdom hcl.1 henv) hcl.2 henv
      | letE ty val body =>
        rw [eval_s_letE] at hev
        simp only [option_bind_eq_some] at hev
        obtain ⟨vv, hval, hbody⟩ := hev
        simp [SExpr.ClosedN] at hcl
        have hvv := ihe val env d vv hval hcl.2.1 henv
        exact ihe body (vv :: env) d v hbody hcl.2.2 (.cons hvv henv)
    · intro fn arg d v hap hfn harg
      cases fn with
      | lam _dom body fenv =>
        rw [apply_s_lam] at hap
        cases hfn with
        | lam hdom hcl henv =>
          exact ihe body (arg :: fenv) d v hap hcl (.cons harg henv)
      | neutral hd spine =>
        rw [apply_s_neutral] at hap
        cases hap
        cases hfn with
        | neutral hhd hsp =>
          exact .neutral hhd (hsp.snoc harg)
      | sort _ => exact absurd hap nofun
      | lit _ => exact absurd hap nofun
      | pi _ _ _ => exact absurd hap nofun

theorem eval_preserves_wf {fuel : Nat} {e : SExpr L} {env : List (SVal L)} {d : Nat} {v : SVal L}
    (h_eval : eval_s fuel e env = some v)
    (h_closed : SExpr.ClosedN e env.length)
    (h_env : EnvWF env d) : ValWF v d :=
  (eval_apply_preserves_wf_aux fuel).1 e env d v h_eval h_closed h_env

theorem apply_preserves_wf {fuel : Nat} {fn arg : SVal L} {d : Nat} {v : SVal L}
    (h_app : apply_s fuel fn arg = some v)
    (h_fn : ValWF fn d) (h_arg : ValWF arg d) : ValWF v d :=
  (eval_apply_preserves_wf_aux fuel).2 fn arg d v h_app h_fn h_arg

end Ix.Theory
