import Aiur.Optimized.Depth.StructuralSound
import Aiur.Memory.WireProvenance

/-!
# Measures of values with store provenance

A value with finite store provenance (`ROM.Provenance`) has finitely many parts, so it has a
natural height that every proper part lies strictly below (`exists_height`). This is where
"no cyclic data structure" enters the argument for exempt SCCs: a structurally recursive call
on such a value lowers the height.

`move_parts`, `move_down` and `move_up` say what a `Measure.move` means of the argument values
of a call whose static relations hold.
-/

namespace Aiur.Optimized.Depth.Structural

variable {F : Type} [Field F] [DecidableEq F] {rom : ROM F} {params : List (Value F)}

/-- A component of a value with store provenance has store provenance. A valid ROM holds one
value of each type at an address, so the cell a pointer's provenance names is the one a load
reads. -/
theorem Component.provenance (valid : rom.Valid) {part whole : Value F}
    (step : Component rom part whole) (good : rom.Provenance whole) : rom.Provenance part := by
  cases step with
  | tuple member => exact ROM.Provenance.tuple_iff.mp good _ member
  | construct member => exact ROM.Provenance.construct_iff.mp good _ member
  | load cell typed => exact good.load valid cell typed

theorem Part.provenance (valid : rom.Valid) {part whole : Value F}
    (inside : Part rom part whole) (good : rom.Provenance whole) : rom.Provenance part := by
  induction inside with
  | single step => exact step.provenance valid good
  | tail _ step ih => exact ih (step.provenance valid good)

/-- `Below rom bound value`: every chain of `Component` steps down from `value` is shorter
than `bound`. -/
def Below (rom : ROM F) : Nat → Value F → Prop
  | 0, _ => False
  | bound + 1, value => ∀ part, Component rom part value → Below rom bound part

omit [Field F] [DecidableEq F] in
theorem Below.succ : ∀ {bound : Nat} {value : Value F},
    Below rom bound value → Below rom (bound + 1) value
  | 0, _, below => below.elim
  | _ + 1, _, below => fun part step => (below part step).succ

omit [Field F] [DecidableEq F] in
theorem Below.mono {low high : Nat} {value : Value F} (below : Below rom low value)
    (order : low ≤ high) : Below rom high value := by
  induction order with
  | refl => exact below
  | step _ ih => exact ih.succ

/-- Finitely many bounded values have a common bound. -/
theorem Below.common : ∀ {values : List (Value F)},
    (∀ value ∈ values, ∃ bound, Below rom bound value) →
    ∃ bound, ∀ value ∈ values, Below rom bound value
  | [], _ => ⟨0, by simp⟩
  | first :: rest, each => by
      obtain ⟨head, headBelow⟩ := each first List.mem_cons_self
      obtain ⟨tail, tailBelow⟩ :=
        Below.common fun value member => each value (List.mem_cons_of_mem _ member)
      refine ⟨max head tail, fun value member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact headBelow.mono (Nat.le_max_left _ _)
      · exact (tailBelow value member).mono (Nat.le_max_right _ _)

/-- The component chains below a value with store provenance are bounded. -/
theorem Below.of_provenance (valid : rom.Valid) {value : Value F} (good : rom.Provenance value) :
    ∃ bound, Below rom bound value := by
  induction good with
  | field => exact ⟨1, fun part step => by cases step⟩
  | tuple _ ih =>
      obtain ⟨bound, below⟩ := Below.common ih
      exact ⟨bound + 1, fun part step => by cases step with | tuple member => exact below _ member⟩
  | construct _ ih =>
      obtain ⟨bound, below⟩ := Below.common ih
      exact ⟨bound + 1, fun part step => by
        cases step with | construct member => exact below _ member⟩
  | ptr cell _ ih =>
      obtain ⟨bound, below⟩ := ih
      refine ⟨bound + 1, fun part step => ?_⟩
      cases step with
      | load other typed =>
          have same := ROM.functional valid cell other typed.symm
          exact same ▸ below

/-- Values with store provenance have a height that falls on proper parts. -/
theorem exists_height (valid : rom.Valid) :
    ∃ height : Value F → Nat, ∀ {part whole : Value F}, rom.Provenance whole →
      Part rom part whole → height part < height whole := by
  classical
  let height : Value F → Nat := fun value =>
    if bounded : ∃ bound, Below rom bound value then Nat.find bounded else 0
  have falls : ∀ {part whole : Value F}, rom.Provenance whole → Component rom part whole →
      height part < height whole := by
    intro part whole good step
    have bounded := Below.of_provenance valid good
    have least := Nat.find_spec bounded
    have whole_eq : height whole = Nat.find bounded := by simp only [height, bounded, ↓reduceDIte]
    cases found : Nat.find bounded with
    | zero => rw [found] at least; exact least.elim
    | succ bound =>
        rw [found] at least
        have inner : ∃ bound, Below rom bound part := ⟨bound, least part step⟩
        have part_eq : height part = Nat.find inner := by simp only [height, inner, ↓reduceDIte]
        have small : Nat.find inner ≤ bound := Nat.find_min' inner (least part step)
        omega
  refine ⟨height, ?_⟩
  intro part whole good inside
  induction inside with
  | single step => exact falls good step
  | tail _ step ih => exact Nat.lt_trans (ih (step.provenance valid good)) (falls good step)

/-- A static relation of the `j`-th argument holds of the `j`-th argument value. -/
theorem argument_holds {args : List Parts} {values : List (Value F)}
    (sound : List.Forall₂ (Sound rom params) args values) :
    ∀ {j : Nat} {fact : Nat × Relation}, fact ∈ args.getD j [] →
      ∃ value, values[j]? = some value ∧ Holds rom params value fact := by
  induction sound with
  | nil => intro j fact member; simp at member
  | cons head _ ih =>
      intro j fact member
      cases j with
      | zero => exact ⟨_, rfl, head _ (by simpa using member)⟩
      | succ j => simpa using ih (j := j) (by simpa using member)

/-- What the test of a move between two `parts` measures says of the argument values. -/
theorem within_holds {args : List Parts} {values : List (Value F)} {source target : List Nat}
    {relations : List Relation} (sound : List.Forall₂ (Sound rom params) args values)
    (within : (!target.isEmpty && target.all fun j => source.any fun i =>
      relations.any fun relation => (args.getD j []).contains (i, relation)) = true) :
    target ≠ [] ∧ ∀ j ∈ target, ∃ i ∈ source, ∃ relation ∈ relations, ∃ value,
      values[j]? = some value ∧ Holds rom params value (i, relation) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    List.any_eq_true, List.contains_iff_mem] at within
  refine ⟨within.1, fun j member => ?_⟩
  obtain ⟨i, inside, relation, listed, found⟩ := within.2 j member
  exact ⟨i, inside, relation, listed, argument_holds sound found⟩

/-- What a move between two `parts` measures says of the argument values. -/
theorem move_parts {args : List Parts} {values : List (Value F)} {source target : List Nat}
    (sound : List.Forall₂ (Sound rom params) args values) :
    (Measure.move args (.parts source) (.parts target) = .lowers →
      target ≠ [] ∧ ∀ j ∈ target, ∃ i ∈ source, ∃ value param,
        values[j]? = some value ∧ params[i]? = some param ∧ Part rom value param) ∧
    (Measure.move args (.parts source) (.parts target) = .keeps →
      target ≠ [] ∧ ∀ j ∈ target, ∃ i ∈ source, ∃ value param,
        values[j]? = some value ∧ params[i]? = some param ∧ (value = param ∨ Part rom value param)) := by
  constructor
  · intro moved
    simp only [Measure.move] at moved
    split at moved
    · rename_i within
      obtain ⟨nonempty, each⟩ := within_holds sound within
      refine ⟨nonempty, fun j member => ?_⟩
      obtain ⟨i, inside, relation, listed, value, found, holds⟩ := each j member
      simp only [List.mem_singleton] at listed
      subst listed
      obtain ⟨param, at_, inner⟩ := holds
      exact ⟨i, inside, value, param, found, at_, inner⟩
    · split at moved <;> cases moved
  · intro moved
    simp only [Measure.move] at moved
    split at moved
    · cases moved
    · split at moved
      · rename_i within
        obtain ⟨nonempty, each⟩ := within_holds sound within
        refine ⟨nonempty, fun j member => ?_⟩
        obtain ⟨i, inside, relation, listed, value, found, holds⟩ := each j member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
        rcases listed with rfl | rfl
        · exact ⟨i, inside, value, value, found, holds, .inl rfl⟩
        · obtain ⟨param, at_, inner⟩ := holds
          exact ⟨i, inside, value, param, found, at_, .inr inner⟩
      · cases moved

/-- What a move between two `down` measures says of the argument values. -/
theorem move_down {args : List Parts} {values : List (Value F)} {i j : Nat}
    (sound : List.Forall₂ (Sound rom params) args values) :
    (Measure.move args (.down i) (.down j) = .lowers →
      ∃ (x : F) (n : Nat), 0 < n ∧ n ≤ maxStep ∧ values[j]? = some (.field x) ∧
        params[i]? = some (.field (x + (n : F)))) ∧
    (Measure.move args (.down i) (.down j) = .keeps →
      ∃ value, values[j]? = some value ∧ params[i]? = some value) := by
  constructor
  · intro moved
    simp only [Measure.move] at moved
    split at moved
    · rename_i found
      obtain ⟨value, at_, holds⟩ := argument_holds sound (List.contains_iff_mem.mp found)
      obtain ⟨x, n, positive, small, rfl, param⟩ := holds
      exact ⟨x, n, positive, small, at_, param⟩
    · split at moved <;> cases moved
  · intro moved
    simp only [Measure.move] at moved
    split at moved
    · cases moved
    · split at moved
      · rename_i found
        obtain ⟨value, at_, holds⟩ := argument_holds sound (List.contains_iff_mem.mp found)
        exact ⟨value, at_, holds⟩
      · cases moved

/-- What a move between two `up` measures says of the argument values. -/
theorem move_up {args : List Parts} {values : List (Value F)} {i j : Nat}
    (sound : List.Forall₂ (Sound rom params) args values) :
    (Measure.move args (.up i) (.up j) = .lowers →
      ∃ (x : F) (n : Nat), 0 < n ∧ n ≤ maxStep ∧ values[j]? = some (.field (x + (n : F))) ∧
        params[i]? = some (.field x)) ∧
    (Measure.move args (.up i) (.up j) = .keeps →
      ∃ value, values[j]? = some value ∧ params[i]? = some value) := by
  constructor
  · intro moved
    simp only [Measure.move] at moved
    split at moved
    · rename_i found
      obtain ⟨value, at_, holds⟩ := argument_holds sound (List.contains_iff_mem.mp found)
      obtain ⟨x, n, positive, small, rfl, param⟩ := holds
      exact ⟨x, n, positive, small, at_, param⟩
    · split at moved <;> cases moved
  · intro moved
    simp only [Measure.move] at moved
    split at moved
    · cases moved
    · split at moved
      · rename_i found
        obtain ⟨value, at_, holds⟩ := argument_holds sound (List.contains_iff_mem.mp found)
        exact ⟨value, at_, holds⟩
      · cases moved

/-- A move that is known joins two measures of one kind. -/
theorem move_kind {args : List Parts} {source target : Measure}
    (known : Measure.move args source target ≠ .unknown) :
    (∃ s t, source = .parts s ∧ target = .parts t) ∨ (∃ i j, source = .down i ∧ target = .down j) ∨
      (∃ i j, source = .up i ∧ target = .up j) := by
  cases source <;> cases target <;>
    first
    | exact .inl ⟨_, _, rfl, rfl⟩
    | exact .inr (.inl ⟨_, _, rfl, rfl⟩)
    | exact .inr (.inr ⟨_, _, rfl, rfl⟩)
    | exact absurd rfl known

end Aiur.Optimized.Depth.Structural
