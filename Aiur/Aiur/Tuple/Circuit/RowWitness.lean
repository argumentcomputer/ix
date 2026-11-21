import Aiur.Tuple.Circuit.WitnessBasic
import Mathlib.Data.List.OfFn

namespace Aiur.Tuple.Circuit

/-- Store the allocated prefix of a witness assignment as a finite row. -/
def Row.ofAssignment (name : String) (bound : Nat) (assignment : Var → F) : Row F :=
  ⟨name, List.ofFn (fun id : Fin bound => assignment id)⟩

@[simp] theorem Row.ofAssignment_length (name : String) (bound : Nat) (assignment : Var → F) :
    (Row.ofAssignment name bound assignment).values.length = bound := by simp [Row.ofAssignment]

theorem Row.ofAssignment_agree [Zero F] (name : String) (bound : Nat) (assignment : Var → F)
    (id : Var) (inside : id < bound) :
    (Row.ofAssignment name bound assignment).assignment id = assignment id := by
  simp [Row.assignment, Scalar.Circuit.Row.assignment, Row.ofAssignment, inside]

namespace Compiler

@[simp] theorem bounded_vars {bound : Nat} {value : Value Var} :
    Bounded (F := F) bound (value.map ArithExpr.var) ↔ ∀ id ∈ value.flatten, id < bound := by
  simp [Bounded, Value.flatten_map, ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds]

theorem BuildState.finite_witness [Field F] {calls : CallRelation F} {state : BuildState F}
    {assignment : Var → F} (layout : state.WellFormed) (valid : state.Valid calls assignment)
    (name : String) :
    Extension calls state state assignment (Row.ofAssignment name state.nextVar assignment).assignment :=
  ⟨le_rfl, Row.ofAssignment_agree _ _ _, layout,
    valid.of_agree layout (Row.ofAssignment_agree _ _ _)⟩

theorem chip_wellFormed {name : String} {inputs : List (Value Var)} {output : Value Var} {state : BuildState F}
    (layout : state.WellFormed)
    (inputsBound : ∀ input ∈ inputs, Bounded (F := F) state.nextVar (input.map ArithExpr.var))
    (outputBound : Bounded (F := F) state.nextVar (output.map ArithExpr.var)) :
    (Chip.mk name inputs output state.nextVar state.constraints.toList state.sends.toList).wellFormed = true := by
  simp only [Chip.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, layout.constraints⟩, layout.sends⟩
  intro id member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨input, member, leaf⟩ := List.mem_flatMap.mp member
    exact bounded_vars.mp (inputsBound input member) id leaf
  · exact bounded_vars.mp outputBound id member

end Compiler
end Aiur.Tuple.Circuit
