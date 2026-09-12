module
public import Ix.MultiStark.Verify.Basic

/-! Small logical elimination lemmas for total error-returning algorithms.
These state no protocol assumptions and execute no native code. -/

public section

namespace MultiStark.Verify.Proofs

theorem bind_ok_iff {ε α β : Type} (first : Except ε α) (next : α → Except ε β) (value : β) :
    (first >>= next) = .ok value ↔ ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Bind.bind, Except.bind]

theorem mapError_ok_iff {ε δ α : Type} (mapError : ε → δ) (result : Except ε α) (value : α) :
    result.mapError mapError = .ok value ↔ result = .ok value := by
  cases result <;> simp [Except.mapError]

theorem map_ok_iff {ε α β : Type} (map : α → β) (result : Except ε α) (value : β) :
    map <$> result = .ok value ↔ ∃ original, result = .ok original ∧ map original = value := by
  cases result <;> simp [Functor.map, Except.map]

theorem pure_ok_iff {ε α : Type} (left right : α) :
    (pure left : Except ε α) = .ok right ↔ left = right := by
  change (Except.ok left : Except ε α) = .ok right ↔ left = right
  simp only [Except.ok.injEq]

theorem action_bind_ok_iff {ε σ α β : Type} (first : StateT σ (Except ε) α)
    (next : α → StateT σ (Except ε) β) (state final : σ) (value : β) :
    ((first >>= next).run state = .ok (value, final)) ↔
      ∃ intermediate middle, first.run state = .ok (intermediate, middle) ∧
        (next intermediate).run middle = .ok (value, final) := by
  change (first state >>= fun result => next result.1 result.2) = .ok (value, final) ↔ _
  rw [bind_ok_iff]
  constructor
  · rintro ⟨⟨intermediate, middle⟩, left, right⟩
    exact ⟨intermediate, middle, left, right⟩
  · rintro ⟨intermediate, middle, left, right⟩
    exact ⟨(intermediate, middle), left, right⟩

theorem action_pure_ok_iff {ε σ α : Type} (state final : σ) (left right : α) :
    ((pure left : StateT σ (Except ε) α).run state = .ok (right, final)) ↔
      left = right ∧ state = final := by
  change (Except.ok (left, state) : Except ε (α × σ)) = .ok (right, final) ↔ _
  simp only [Except.ok.injEq, Prod.mk.injEq]

theorem action_map_ok_iff {ε σ α β : Type} (map : α → β)
    (action : StateT σ (Except ε) α) (state final : σ) (value : β) :
    ((map <$> action).run state = .ok (value, final)) ↔
      ∃ original, action.run state = .ok (original, final) ∧ map original = value := by
  change ((fun result : α × σ => (map result.1, result.2)) <$> action state) =
    .ok (value, final) ↔ _
  rw [map_ok_iff]
  constructor
  · rintro ⟨⟨original, middle⟩, accepted, equal⟩
    cases (Prod.mk.inj equal).2
    exact ⟨original, accepted, (Prod.mk.inj equal).1⟩
  · rintro ⟨original, accepted, equal⟩
    exact ⟨(original, final), accepted, by simp only [equal]⟩

theorem unit_exists_iff (predicate : Unit → Prop) : (∃ value, predicate value) ↔ predicate () := by
  constructor
  · rintro ⟨⟨⟩, accepted⟩
    exact accepted
  · intro accepted
    exact ⟨(), accepted⟩

theorem ensure_ok_iff {ε : Type} (condition : Bool) (error : ε) :
    ensure condition error = .ok () ↔ condition = true := by
  cases condition <;> simp [ensure]

theorem listArray_exists_iff {α : Type} (predicate : List α → Prop) (values : Array α) :
    (∃ list, predicate list ∧ list.toArray = values) ↔ predicate values.toList := by
  constructor
  · rintro ⟨list, accepted, equal⟩
    cases equal
    simpa using accepted
  · intro accepted
    exact ⟨values.toList, accepted, by simp⟩

theorem action_throw_ok_iff {ε σ α : Type} (error : ε) (state final : σ) (value : α) :
    ((throw error : StateT σ (Except ε) α).run state = .ok (value, final)) ↔ False := by
  change (Except.error error : Except ε (α × σ)) = .ok (value, final) ↔ False
  simp

end MultiStark.Verify.Proofs
