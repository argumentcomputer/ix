import Init.Data.Range.Lemmas
import Init.Data.List.Monadic

namespace IxCC.Aiur.CounterAnalysis

def stepValue {α : Type} : ForInStep α → α
  | .done value | .yield value => value

theorem forIn_invariant {α β : Type} (items : List α) (initial : β) (body : α → β → Id (ForInStep β))
    (property : β → Prop) (start : property initial)
    (preserves : ∀ item ∈ items, ∀ state, property state → property (stepValue (body item state))) :
    property (forIn items initial body : Id β) := by
  induction items generalizing initial with
  | nil => exact start
  | cons item rest ih =>
    rw [List.forIn_cons]
    have next := preserves item (List.mem_cons_self) initial start
    cases outcome : body item initial with
    | done result => simpa only [outcome, bind, pure, stepValue] using next
    | «yield» result =>
      have next : property result := by simpa [outcome, stepValue] using next
      have later := ih result next (fun value member state valid => preserves value (List.mem_cons_of_mem _ member) state valid)
      simpa only [outcome, bind, pure] using later

theorem forIn_range_invariant {β : Type} (count : Nat) (initial : β) (body : Nat → β → Id (ForInStep β))
    (property : β → Prop) (start : property initial)
    (preserves : ∀ index, index < count → ∀ state, property state → property (stepValue (body index state))) :
    property (forIn [:count] initial body : Id β) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply forIn_invariant _ _ _ property start
  intro index member state valid
  apply preserves index ?_ state valid
  have inside := Std.Legacy.Range.mem_of_mem_range' member
  exact inside.2.1

end IxCC.Aiur.CounterAnalysis
