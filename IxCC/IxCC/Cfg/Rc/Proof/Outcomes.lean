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

theorem resetMask_outcome (ρ : Own.Env) (H : Own.Heap) (x : Fir.Var) (ctor : Fir.CtorInfo)
    (mask : Nat) (uniq : Bool) :
    Own.Plain.evalResetMask ρ H x ctor mask uniq = .stuck ∨
      ∃ p, Own.Plain.evalResetMask ρ H x ctor mask uniq = .ok p := by
  unfold Own.Plain.evalResetMask
  split
  · exact Or.inl rfl
  · cases hx : ρ.get? x with
    | none => exact Or.inl rfl
    | some v =>
      cases v with
      | loc l =>
        simp only
        cases hc : H.cell? l with
        | none => exact Or.inl rfl
        | some cell =>
          cases cell with
          | dead => exact Or.inl rfl
          | live rc st b =>
            split
            · cases hr : Own.Rc.reuseCell H l (Own.Plain.resetShell ctor) with
              | none => exact Or.inl rfl
              | some p =>
                simp only
                cases hd : Own.Rc.dropAll p.2 _ with
                | none => exact Or.inl rfl
                | some H₂ => exact Or.inr ⟨(p.1, H₂), by simp [Sem.Result.ofOption]⟩
            · split
              · exact Or.inl rfl
              · cases hi : Own.Plain.incList H _ with
                | none => exact Or.inl rfl
                | some H₁ =>
                  simp only
                  cases hd : Own.Rc.dropAll H₁ [.loc l] with
                  | none => exact Or.inl rfl
                  | some H₂ => exact Or.inr ⟨(.erased, H₂), by simp [Sem.Result.ofOption]⟩
            · exact Or.inl rfl
      | lit _ | ctor0 _ | erased =>
        simp only
        split
        · exact Or.inl rfl
        · exact Or.inr ⟨(.erased, H), rfl⟩

theorem reuseVal_outcome (ρ : Own.Env) (H : Own.Heap) (sv : Own.RVal) (ctor : Fir.CtorInfo)
    (args : List Fir.Arg) (uniq : Bool) :
    Own.Plain.evalReuseVal ρ H sv ctor args uniq = .stuck ∨
      ∃ p, Own.Plain.evalReuseVal ρ H sv ctor args uniq = .ok p := by
  unfold Own.Plain.evalReuseVal
  cases ha : Own.evalArgs ρ args with
  | none => exact Or.inl rfl
  | some vs =>
    simp only
    split
    · cases sv with
      | loc l =>
        cases hr : Own.Rc.reuseCell H l { ctor, fields := vs } with
        | none => exact Or.inl (by simp [Sem.Result.ofOption, hr])
        | some p => exact Or.inr ⟨p, by simp [Sem.Result.ofOption, hr]⟩
      | erased =>
        cases uniq with
        | true => exact Or.inl rfl
        | false => exact Or.inr ⟨Own.Heap.alloc .rc H { ctor, fields := vs }, rfl⟩
      | lit _ | ctor0 _ => exact Or.inl rfl
    · exact Or.inl rfl

theorem dropVal_outcome (H : Own.Heap) (sv : Own.RVal) :
    Own.Plain.evalDropVal H sv = .stuck ∨ ∃ H', Own.Plain.evalDropVal H sv = .ok H' := by
  unfold Own.Plain.evalDropVal
  cases Own.Rc.dropAll H [sv] with
  | none => exact Or.inl (by simp [Sem.Result.ofOption])
  | some H' => exact Or.inr ⟨H', by simp [Sem.Result.ofOption]⟩



end IxCC.Cfg.Rc
