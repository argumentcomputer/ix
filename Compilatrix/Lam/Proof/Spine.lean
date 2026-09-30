import Compilatrix.Lam.Proof.Mono
import Compilatrix.Sem.SimUpTo

/-! # Lam on application spines

`Term.apps h args` evaluates the head, then each argument's slot (`argSlot`:
strict arguments evaluated, `name` ones suspended) and applies, left to
right (`eval_apps`); `Term.lams` evaluates to a closure. With the clock
monotonicity of each piece, for the erasure simulation (M2.2). -/

namespace Compilatrix.Lam

open Compilatrix.Sem (Result ClockMono)

variable (P : Program) (k : Nat) (ρ : Env)

/-- The slot an application node passes. -/
def argSlot : Term × Mode → Result Slot
  | (a, .strict) => (eval P k ρ a).bind fun v => .ok (.val v)
  | (a, .name) => .ok (.name ρ a)

/-- Apply a value to a spine's argument slots, left to right. -/
def applyArgs : Val → List (Term × Mode) → Result Val
  | f, [] => .ok f
  | f, a :: as => (argSlot P k ρ a).bind fun s => (apply P k f s).bind fun v => applyArgs v as

theorem applyArgs_nil (f : Val) : applyArgs P k ρ f [] = .ok f := rfl

theorem applyArgs_cons (f : Val) (a : Term × Mode) (as : List (Term × Mode)) :
    applyArgs P k ρ f (a :: as) =
      (argSlot P k ρ a).bind fun s => (apply P k f s).bind fun v => applyArgs P k ρ v as := rfl

theorem eval_app_slot (f a : Term) (m : Mode) :
    eval P k ρ (.app f a m) = (eval P k ρ f).bind fun fv => (argSlot P k ρ (a, m)).bind (apply P k fv) := by
  rw [eval_app]
  apply Sem.Result.bind_congr
  intro fv
  cases m with
  | strict => simp only [argSlot, Sem.Result.bind_assoc, Sem.Result.bind_ok]
  | name => rfl

theorem eval_apps : ∀ (h : Term) (args : List (Term × Mode)),
    eval P k ρ (Term.apps h args) = (eval P k ρ h).bind (applyArgs P k ρ · args)
  | h, [] => by simp [Term.apps, applyArgs, Sem.Result.bind_pure]
  | h, (a, m) :: args => by
    have e : Term.apps h ((a, m) :: args) = Term.apps (.app h a m) args := rfl
    rw [e, eval_apps, eval_app_slot, Sem.Result.bind_assoc]
    apply Sem.Result.bind_congr
    intro fv
    rw [Sem.Result.bind_assoc]
    rfl

theorem applyArgs_append (f : Val) :
    ∀ (as bs : List (Term × Mode)),
      applyArgs P k ρ f (as ++ bs) = (applyArgs P k ρ f as).bind (applyArgs P k ρ · bs)
  | [], bs => by simp [applyArgs]
  | a :: as, bs => by
    simp only [List.cons_append, applyArgs, Sem.Result.bind_assoc]
    apply Sem.Result.bind_congr
    intro s
    apply Sem.Result.bind_congr
    intro v
    exact applyArgs_append v as bs

theorem eval_lams_cons (m : Mode) (ms : List Mode) (b : Term) :
    eval P k ρ (Term.lams (m :: ms) b) = .ok (.clos ρ (Term.lams ms b)) := by
  simp only [Term.lams, List.foldr_cons]
  exact eval_lam P k ρ _ _ _

/-! ## Monotone pieces -/

theorem argSlot_mono (a : Term × Mode) : ClockMono fun k => argSlot P k ρ a := by
  obtain ⟨a, m⟩ := a
  cases m with
  | strict => exact (eval_mono P ρ a).bind fun _ => ClockMono.const _
  | name => exact ClockMono.const _

theorem applyArgs_mono : ∀ (f : Val) (as : List (Term × Mode)), ClockMono fun k => applyArgs P k ρ f as
  | _, [] => ClockMono.const _
  | f, a :: as =>
    (argSlot_mono P ρ a).bind fun s => (apply_mono P f s).bind fun v => applyArgs_mono v as

end Compilatrix.Lam
