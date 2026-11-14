import Aiur.Wire

namespace Aiur.WireValue

@[simp] theorem type_map (f : α → β) (value : WireValue α) :
    (value.map f).type = value.type := rfl

@[simp] theorem words_map (f : α → β) (value : WireValue α) :
    (value.map f).words = value.words.map f := rfl

@[simp] theorem map_map (f : α → β) (g : β → γ) (value : WireValue α) :
    (value.map f).map g = value.map (g ∘ f) := by
  cases value
  simp [map, List.map_map]

theorem map_congr (value : WireValue α) {f g : α → β}
    (agree : ∀ x ∈ value.words, f x = g x) : value.map f = value.map g := by
  exact congrArg (WireValue.mk value.type) (List.map_congr_left agree)

@[simp] theorem map_field (f : α → β) (value : α) :
    (field value).map f = field (f value) := rfl

@[simp] theorem map_ptr (f : α → β) (target : Ty) (address : α) :
    (ptr target address).map f = ptr target (f address) := rfl

@[simp] theorem map_tuple (f : α → β) (values : List (WireValue α)) :
    (tuple values).map f = tuple (values.map (map f)) := by
  simp [map, tuple, List.map_map, List.map_flatMap, List.flatMap_map]

end Aiur.WireValue
