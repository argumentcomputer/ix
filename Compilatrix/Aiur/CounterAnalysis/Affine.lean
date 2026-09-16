import Compilatrix.Aiur.CounterAnalysis.Field
import Ix.Aiur.Compiler.UnitCounter

namespace Compilatrix.Aiur.CounterAnalysis

open _root_.Aiur (G)
open _root_.Aiur.Bytecode

private theorem field_val_eq (a b : G) : a.val = b.val ↔ a = b :=
  ⟨Subtype.ext, congrArg Subtype.val⟩

theorem affine_beq_eq (left right : UnitCounter.Affine) : (left == right) = true ↔ left = right := by
  rcases left with ⟨leftBase, leftOffset⟩
  rcases right with ⟨rightBase, rightOffset⟩
  change ((leftBase == rightBase) && (leftOffset == rightOffset)) = true ↔ _
  simp [field_val_eq]

theorem optional_affine_beq_eq (left right : Option UnitCounter.Affine) :
    (left == right) = true ↔ left = right := by
  cases left <;> cases right <;> simp [affine_beq_eq]

/-- A known affine expression denotes an actual register value. A base
must name an existing register, so absent entries never mean zero. -/
def Denotes (values : Array G) (expression : UnitCounter.Affine) (value : G) : Prop :=
  match expression.base with
  | none => value = expression.offset
  | some base => ∃ source, values[base]? = some source ∧ value = source + expression.offset

def ValueSound (values : Array G) (expression : Option UnitCounter.Affine) (value : G) : Prop :=
  ∀ affine, expression = some affine → Denotes values affine value

theorem valueSound_none (values : Array G) (value : G) : ValueSound values none value := by
  intro _ impossible
  cases impossible

theorem denotes_constant (values : Array G) (value : G) :
    Denotes values (UnitCounter.constant value) value := rfl

theorem denotes_variable (values : Array G) (index : Nat) (value : G)
    (read : values[index]? = some value) : Denotes values (UnitCounter.affVar index) value := by
  exact ⟨value, read, (Field.add_zero value).symm⟩

theorem denotes_extend {before after : Array G} {expression : UnitCounter.Affine} {value : G}
    (preserves : ∀ (index : Nat) (field : G), before[index]? = some field → after[index]? = some field)
    (sound : Denotes before expression value) : Denotes after expression value := by
  rcases expression with ⟨base, offset⟩
  cases base with
  | none => exact sound
  | some index =>
      obtain ⟨source, read, equal⟩ := sound
      exact ⟨source, preserves index source read, equal⟩

theorem valueSound_extend {before after : Array G} {expression : Option UnitCounter.Affine} {value : G}
    (preserves : ∀ (index : Nat) (field : G), before[index]? = some field → after[index]? = some field)
    (sound : ValueSound before expression value) : ValueSound after expression value :=
  fun affine known => denotes_extend preserves (sound affine known)

theorem add_sound (values : Array G) (left right : Option UnitCounter.Affine) (a b : G)
    (hl : ValueSound values left a) (hr : ValueSound values right b) :
    ValueSound values (UnitCounter.add left right) (a + b) := by
  intro result checked
  cases left with
  | none => simp [UnitCounter.add] at checked
  | some left =>
    cases right with
    | none => simp [UnitCounter.add] at checked
    | some right =>
      have hl := hl left rfl
      have hr := hr right rfl
      rcases left with ⟨leftBase, leftOffset⟩
      rcases right with ⟨rightBase, rightOffset⟩
      cases leftBase <;> cases rightBase <;>
        simp only [UnitCounter.add, Option.pure_def] at checked
      · cases checked
        change a + b = leftOffset + rightOffset
        rw [hl, hr]
      · cases checked
        obtain ⟨source, read, equal⟩ := hr
        refine ⟨source, read, ?_⟩
        change a + b = source + (leftOffset + rightOffset)
        rw [hl, equal, ← add_assoc, G.add_comm leftOffset source, add_assoc]
      · cases checked
        obtain ⟨source, read, equal⟩ := hl
        exact ⟨source, read, by rw [equal, hr, add_assoc]⟩
      · cases checked

theorem sub_sound (values : Array G) (left right : Option UnitCounter.Affine) (a b : G)
    (hl : ValueSound values left a) (hr : ValueSound values right b) :
    ValueSound values (UnitCounter.sub left right) (a - b) := by
  intro result checked
  cases left with
  | none => simp [UnitCounter.sub] at checked
  | some left =>
    cases right with
    | none => simp [UnitCounter.sub] at checked
    | some right =>
      have hl := hl left rfl
      have hr := hr right rfl
      rcases left with ⟨leftBase, leftOffset⟩
      rcases right with ⟨rightBase, rightOffset⟩
      cases rightBase with
      | some _ => simp [UnitCounter.sub] at checked
      | none =>
        simp only [UnitCounter.sub, Option.pure_def] at checked
        cases checked
        cases leftBase with
        | none => change a - b = leftOffset - rightOffset; rw [hl, hr]
        | some _ =>
          obtain ⟨source, read, equal⟩ := hl
          exact ⟨source, read, by rw [equal, hr, add_sub_assoc]⟩

theorem mul_sound (values : Array G) (left right : Option UnitCounter.Affine) (a b : G)
    (hl : ValueSound values left a) (hr : ValueSound values right b) :
    ValueSound values (UnitCounter.mul left right) (a * b) := by
  intro result checked
  cases left with
  | none => simp [UnitCounter.mul] at checked
  | some left =>
    cases right with
    | none => simp [UnitCounter.mul] at checked
    | some right =>
      have hl := hl left rfl
      have hr := hr right rfl
      rcases left with ⟨leftBase, leftOffset⟩
      rcases right with ⟨rightBase, rightOffset⟩
      cases leftBase <;> cases rightBase
      · by_cases oneLeft : leftOffset = 1
        · simp [UnitCounter.mul, field_val_eq, oneLeft] at checked
          cases checked
          change a * b = rightOffset
          rw [hl, hr, oneLeft, one_mul]
        · by_cases oneRight : rightOffset = 1
          · simp [UnitCounter.mul, field_val_eq, oneLeft, oneRight] at checked
            cases checked
            change a * b = leftOffset
            rw [hl, hr, oneRight, mul_one]
          · simp [UnitCounter.mul, field_val_eq, oneLeft, oneRight] at checked
            cases checked
            change a * b = leftOffset * rightOffset
            rw [hl, hr]
      · by_cases oneLeft : leftOffset = 1
        · simp [UnitCounter.mul, field_val_eq, oneLeft] at checked
          cases checked
          rw [hl, oneLeft, one_mul]
          exact hr
        · simp [UnitCounter.mul, field_val_eq, oneLeft] at checked
      · by_cases oneRight : rightOffset = 1
        · simp [UnitCounter.mul, field_val_eq, oneRight] at checked
          cases checked
          rw [hr, oneRight, mul_one]
          exact hl
        · simp [UnitCounter.mul, field_val_eq, oneRight] at checked
      · simp [UnitCounter.mul] at checked

end Compilatrix.Aiur.CounterAnalysis
