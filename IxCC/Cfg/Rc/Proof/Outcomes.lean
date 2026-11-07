import IxCC.Cfg.Rc.Proof.Step
import IxCC.Cfg.Proof.Sim

/-! Concrete abstract-heap operations are successful or stuck; the resource
branch of the source trace interface is not discharged by assumption. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc

theorem action_outcome (ρ : Own.Env) (H : Own.Heap) (a : Action) :
    Own.Plain.evalAction ρ H a = .stuck ∨ ∃ H', Own.Plain.evalAction ρ H a = .ok H' := by
  cases a with
  | inc x n =>
    cases hx : ρ.get? x with
    | none => exact Or.inl (by simp [Own.Plain.evalAction, hx])
    | some v =>
      cases he : Own.Rc.inc H v n with
      | none => exact Or.inl (by simp [Own.Plain.evalAction, hx, he, Sem.Result.ofOption])
      | some H' => exact Or.inr ⟨H', by simp [Own.Plain.evalAction, hx, he, Sem.Result.ofOption]⟩
  | dec x =>
    cases hx : ρ.get? x with
    | none => exact Or.inl (by simp [Own.Plain.evalAction, hx])
    | some v =>
      cases he : Own.Rc.dropAll H [v] with
      | none => exact Or.inl (by simp [Own.Plain.evalAction, hx, he, Sem.Result.ofOption])
      | some H' => exact Or.inr ⟨H', by simp [Own.Plain.evalAction, hx, he, Sem.Result.ofOption]⟩

theorem rhs_outcome (T : Own.Tables) (ρ : Own.Env) (H : Own.Heap) (r : Fir.Rhs) :
    Own.Plain.evalRhs T ρ H r = .stuck ∨ ∃ p, Own.Plain.evalRhs T ρ H r = .ok p := by
  have outcomes := Cfg.Proof.evalRhs_cases .rc T ρ H (Own.immRhs r)
  cases r <;> simpa only [Own.Plain.evalRhs, Own.immRhs] using outcomes



end IxCC.Cfg.Rc
