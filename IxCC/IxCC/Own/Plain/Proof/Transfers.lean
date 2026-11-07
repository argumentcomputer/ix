import IxCC.Own.Plain.Proof.Drops

/-! The actual canonical copies-then-drops schedule stutters at the source
clock and transfers owned arguments plus captured roots to its continuation. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

theorem evalActions_append (ρ : Own.Env) (H : Heap) (as bs : List Action) :
    evalActions ρ H (as ++ bs) =
      (evalActions ρ H as).bind fun H' => evalActions ρ H' bs := by
  induction as generalizing H with
  | nil => rfl
  | cons a as ih =>
    simp only [List.cons_append, evalActions]
    cases ha : evalAction ρ H a <;> simp [Result.bind, ih]

theorem transfer_sound (P : Program) (k : Nat) (ρ : Own.Env) (J : List JEntry)
    (H : Heap) (live captured : List Fir.Var) (args : List Fir.Arg) (c : Code)
    {external : Nat → Nat} {roots values : List RVal}
    (hr : EnvRoots ρ live roots) (hb : Balance H external roots)
    (ho : ArgsOwned ρ args roots) (ha : Own.evalArgs ρ args = some values) :
    ∃ H' kept,
      eval P k ρ J H (transfer live captured args c) = eval P k ρ J H' c ∧
      EnvRoots ρ (retained captured live) kept ∧ Balance H' external (values ++ kept) ∧
      (∀ v, v ∈ kept → v ∈ roots) ∧
      (∀ v, v ∈ values ++ kept → H.value? v = H'.value? v) ∧
      (∀ v, ExternalRoot external v → H.value? v = H'.value? v) := by
  obtain ⟨H₁, hcopy, hb₁, hv₁⟩ := copies_sound ρ H args hb ho ha
  obtain ⟨H₂, kept, hdrop, hk, hb₂, hsub, hv₂, he₂⟩ := drops_sound ρ H₁ captured live hr hb₁
  refine ⟨H₂, kept, ?_, hk, hb₂, hsub,
    fun v hm => (hv₁ v).trans (hv₂ v hm), fun v he => (hv₁ v).trans (he₂ v he)⟩
  unfold transfer
  rw [eval_actionPrefix, evalActions_append, hcopy]
  simp only [Result.bind_ok, hdrop]


end IxCC.Own.Plain
