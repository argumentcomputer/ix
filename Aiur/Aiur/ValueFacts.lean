import Aiur.AST
import Mathlib.Data.List.Basic

namespace Aiur.Value

theorem map_congr (value : Value α) {f g : α → β}
    (agree : ∀ x ∈ value.flatten, f x = g x) : value.map f = value.map g := by
  cases value with
  | field x => simp only [Value.map, agree x (by simp [Value.flatten])]
  | ptr target x => simp only [Value.map, agree x (by simp [Value.flatten])]
  | tuple items | construct _ _ items =>
      simp only [Value.map, Value.tuple.injEq, Value.construct.injEq, true_and]
      apply List.map_congr_left
      intro value member
      apply map_congr value
      intro x inside
      exact agree x (by simpa only [Value.flatten, List.mem_flatMap] using ⟨value, member, inside⟩)
termination_by sizeOf value
decreasing_by
  all_goals
    simp_wf
    have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
    simp_all only [Value.tuple.sizeOf_spec, Value.construct.sizeOf_spec]
    omega

@[simp] theorem flatten_map (f : α → β) (value : Value α) :
    (value.map f).flatten = value.flatten.map f := by
  cases value with
  | field => simp [Value.map, Value.flatten]
  | ptr => simp [Value.map, Value.flatten]
  | tuple items | construct _ _ items =>
      simp only [Value.map, Value.flatten, List.flatMap_map, List.map_flatMap]
      apply List.flatMap_congr
      intro value member
      exact flatten_map f value
termination_by sizeOf value
decreasing_by
  all_goals
    simp_wf
    have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
    simp_all only [Value.tuple.sizeOf_spec, Value.construct.sizeOf_spec]
    omega

@[simp] theorem map_map (f : α → β) (g : β → γ) (value : Value α) :
    (value.map f).map g = value.map (g ∘ f) := by
  cases value with
  | field => simp [Value.map]
  | ptr => simp [Value.map]
  | tuple items | construct _ _ items =>
      simp only [Value.map, List.map_map, Value.tuple.injEq, Value.construct.injEq, true_and]
      apply List.map_congr_left
      intro value member
      exact map_map f g value
termination_by sizeOf value
decreasing_by
  all_goals
    simp_wf
    have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
    simp_all only [Value.tuple.sizeOf_spec, Value.construct.sizeOf_spec]
    omega

@[simp] theorem type_map (f : α → β) (value : Value α) :
    (value.map f).type = value.type := by
  cases value with
  | field => simp [Value.map, Value.type]
  | ptr => simp [Value.map, Value.type]
  | construct => simp [Value.map, Value.type]
  | tuple items =>
      simp only [Value.map, Value.type, List.map_map, Ty.tuple.injEq]
      apply List.map_congr_left
      intro value member
      exact type_map f value
termination_by sizeOf value
decreasing_by
  all_goals
    simp_wf
    have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
    simp_all only [Value.tuple.sizeOf_spec, Value.construct.sizeOf_spec]
    omega

end Aiur.Value
