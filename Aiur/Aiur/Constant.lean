import Aiur.Declarations
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2

namespace Aiur

set_option linter.unusedSimpArgs false

@[simp] theorem Value.type_mapAddress (encode : A → B) (value : Value F A) :
    (value.mapAddress encode).type = value.type := by
  cases value with
  | field | ptr | construct => simp [Value.mapAddress, Value.type]
  | tuple values =>
      simp only [Value.mapAddress, Value.type, List.map_map, Ty.tuple.injEq]
      apply List.map_congr_left
      intro value member
      exact Value.type_mapAddress encode value
termination_by sizeOf value
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹_ ∈ _›
  omega

@[simp] theorem Value.wellFormed_mapAddress (decls : Declarations) (encode : A → B)
    (value : Value F A) : (value.mapAddress encode).wellFormed decls = value.wellFormed decls := by
  cases value with
  | field | ptr => simp [Value.mapAddress, Value.wellFormed]
  | tuple values =>
      simp only [Value.mapAddress, Value.wellFormed, List.map_map]
      congr 1
      apply List.map_congr_left
      intro value member
      exact Value.wellFormed_mapAddress decls encode value
  | construct name ctor values =>
      simp only [Value.mapAddress, Value.wellFormed]
      cases decls.findConstructor? name ctor with
      | none => rfl
      | some definition =>
          simp only [List.map_map, Function.comp_def, Value.type_mapAddress]
          congr 2
          apply List.map_congr_left
          intro value member
          exact Value.wellFormed_mapAddress decls encode value
termination_by sizeOf value


namespace StaticList

theorem mapM_some {f : α → Option β} {g : α → β} (xs : List α)
    (each : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [List.mapM_cons, each x (by simp), ih (fun y h => each y (by simp [h]))]

theorem mapM_congr (xs : List α) {f g : α → Option β}
    (each : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.mapM_cons, each x (by simp), ih (fun y h => each y (by simp [h]))]

theorem mapM_some_iff {f : α → Option β} {xs : List α} {ys : List β} :
    xs.mapM f = some ys ↔ List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih =>
      cases hx : f x <;> cases hs : xs.mapM f <;>
        simp [List.mapM_cons, hx, hs, List.forall₂_cons_left_iff, ← ih, eq_comm]

end StaticList

@[simp] theorem Constant.toValue_type (value : Constant F) :
    (value.toValue : Value F A).type = value.type := by
  exact Value.type_mapAddress Empty.elim value

@[simp] theorem Constant.toValue_mapAddress (value : Constant F) (encode : A → B) :
    (value.toValue : Value F A).mapAddress encode = value.toValue := by
  cases value with
  | field => simp [Constant.toValue, Value.mapAddress]
  | ptr _ address => exact Empty.elim address
  | tuple values | construct _ _ values =>
      simp only [Constant.toValue, Value.mapAddress, List.map_map,
        Value.tuple.injEq, Value.construct.injEq, true_and]
      exact List.map_congr_left (fun value _ => Constant.toValue_mapAddress value encode)
termination_by sizeOf value

@[simp] theorem Constant.toValue_wellFormed (decls : Declarations) (value : Constant F) :
    (value.toValue : Value F A).wellFormed decls = value.wellFormed decls := by
  exact Value.wellFormed_mapAddress decls Empty.elim value

@[simp] theorem Constant.toValue_pointerFree (value : Constant F) :
    (value.toValue : Value F A).pointerFree = true := by
  cases value with
  | field => simp [Constant.toValue, Value.mapAddress, Value.pointerFree, Value.toConstant?]
  | ptr _ address => exact Empty.elim address
  | tuple items | construct _ _ items =>
      simp only [Constant.toValue, Value.mapAddress, Value.pointerFree, List.map_map,
        List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro value member
      exact Constant.toValue_pointerFree value
termination_by sizeOf value

@[simp] theorem Constant.toConstant_toValue (value : Constant F) :
    (value.toValue : Value F A).toConstant? = some value := by
  cases value with
  | field => simp [Constant.toValue, Value.mapAddress, Value.pointerFree, Value.toConstant?]
  | ptr _ address => exact Empty.elim address
  | tuple items | construct _ _ items =>
      simp only [Constant.toValue, Value.mapAddress, Value.toConstant?, List.mapM_map]
      have mapped := StaticList.mapM_some (f := fun item : Constant F =>
        (item.toValue : Value F A).toConstant?) (g := id) items
        (fun item _ => Constant.toConstant_toValue item)
      simp only [List.map_id] at mapped
      change (Option.map _ (items.mapM _)) = _
      rw [show items.mapM (Value.toConstant? ∘ Value.mapAddress (Empty.elim : Empty → A)) =
        some items from mapped]
      rfl
termination_by sizeOf value

@[simp] theorem Value.toConstant_mapAddress (value : Value F A) (encode : A → B) :
    (value.mapAddress encode).toConstant? = value.toConstant? := by
  cases value with
  | field | ptr => simp [Value.mapAddress, Value.toConstant?]
  | tuple items | construct _ _ items =>
      simp only [Value.mapAddress, Value.toConstant?, List.mapM_map]
      congr 1
      apply StaticList.mapM_congr
      intro item member
      exact Value.toConstant_mapAddress item encode
termination_by sizeOf value

/-- A successful extraction reconstructs exactly the original value. -/
theorem Value.toConstant_spec {value : Value F A} {constant : Constant F}
    (extracted : value.toConstant? = some constant) : constant.toValue = value := by
  cases value with
  | field x =>
      simp only [Value.toConstant?, Option.some.injEq] at extracted
      subst constant
      simp [Constant.toValue, Value.mapAddress]
  | ptr => simp [Value.toConstant?] at extracted
  | tuple items =>
      simp only [Value.toConstant?] at extracted
      cases mapped : items.mapM Value.toConstant? with
      | none => simp [mapped] at extracted
      | some constants =>
          simp [mapped] at extracted
          subst constant
          simp only [Constant.toValue, Value.mapAddress, Value.tuple.injEq]
          have related := StaticList.mapM_some_iff.mp mapped
          have each : ∀ item ∈ items, ∀ c, item.toConstant? = some c → c.toValue = item :=
            fun item _ _ found => Value.toConstant_spec found
          clear mapped
          induction related with
          | nil => rfl
          | @cons item c items constants found rest ih =>
              exact congrArg₂ List.cons (each item (by simp) c found)
                (ih (fun v h => each v (by simp [h])))
  | construct name ctor items =>
      simp only [Value.toConstant?] at extracted
      cases mapped : items.mapM Value.toConstant? with
      | none => simp [mapped] at extracted
      | some constants =>
          simp [mapped] at extracted
          subst constant
          simp only [Constant.toValue, Value.mapAddress, Value.construct.injEq, true_and]
          have related := StaticList.mapM_some_iff.mp mapped
          have each : ∀ item ∈ items, ∀ c, item.toConstant? = some c → c.toValue = item :=
            fun item _ _ found => Value.toConstant_spec found
          clear mapped
          induction related with
          | nil => rfl
          | @cons item c items constants found rest ih =>
              exact congrArg₂ List.cons (each item (by simp) c found)
                (ih (fun v h => each v (by simp [h])))
termination_by sizeOf value

/-- A pointer-free value has a constant representation in any address space. -/
theorem Value.exists_constant (value : Value F A) :
    value.pointerFree = true → ∃ constant : Constant F, constant.toValue = value := by
  induction value using Value.rec
    (motive_2 := fun values => (∀ value ∈ values, value.pointerFree = true) →
      ∃ constants : List (Constant F), constants.map Constant.toValue = values) with
  | field x => intro _; exact ⟨.field x, by simp [Constant.toValue, Value.mapAddress]⟩
  | ptr => simp [Value.pointerFree]
  | tuple values ih =>
      intro free
      obtain ⟨constants, rfl⟩ := ih (by simpa [Value.pointerFree] using free)
      exact ⟨.tuple constants, by simp [Constant.toValue, Value.mapAddress]⟩
  | construct name ctor values ih =>
      intro free
      obtain ⟨constants, rfl⟩ := ih (by simpa [Value.pointerFree] using free)
      exact ⟨.construct name ctor constants, by simp [Constant.toValue, Value.mapAddress]⟩
  | nil => exact ⟨[], rfl⟩
  | cons head tail headIH tailIH =>
      rename_i free
      obtain ⟨constant, rfl⟩ := headIH (free head (by simp))
      obtain ⟨constants, rfl⟩ := tailIH (fun v h => free v (by simp [h]))
      exact ⟨constant :: constants, rfl⟩

end Aiur
