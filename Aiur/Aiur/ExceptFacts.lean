import Mathlib.Data.List.Basic

namespace Aiur

theorem except_bind_ok {first : Except ε α} {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔ ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [bind, Except.bind]

theorem forIn_ok {action : α → Except ε Unit} {items : List α}
    (checked : (do for item in items do action item : Except ε Unit) = .ok ()) :
    ∀ item ∈ items, action item = .ok () := by
  induction items with
  | nil => simp
  | cons item items ih =>
      cases first : action item with
      | error error => simp [List.forIn_cons, first, bind, Except.bind] at checked
      | ok finished =>
          cases finished
          simp only [List.forIn_cons, first, bind, Except.bind, pure, Except.pure] at checked
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact first
          · exact ih checked value member

@[simp] theorem except_pure_ok {value result : α} :
    (pure value : Except ε α) = .ok result ↔ value = result := by simp [pure, Except.pure]

@[simp] theorem except_throw_eq (error : ε) : (throw error : Except ε α) = .error error := rfl

end Aiur
