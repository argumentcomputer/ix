import Compilatrix.X86.HeapPreservation
import Compilatrix.X86.ScalarCalls

namespace Compilatrix.X86.HeapTarget
open WordRegion PhysicalHeap

theorem Plan.entry_valid {checked : X86.Checked} {entries : Array BlockId} {exit : BlockId} {plan : Plan}
    (matched : plan.matches checked.program entries exit = true) : checked.program.hasBlock plan.entry = true := by
  cases plan with
  | ret =>
      simp only [Plan.matches, Bool.and_eq_true] at matched
      exact (Scalar.blockMatches_code matched.2).hasBlock
  | primitive =>
      simp only [Plan.matches, Bool.and_eq_true] at matched
      exact (Scalar.blockMatches_code matched.1.2).hasBlock
  | jump =>
      simp only [Plan.matches, Bool.and_eq_true] at matched
      exact (Scalar.blockMatches_code matched.1.2).hasBlock
  | branch =>
      simp only [Plan.matches, Bool.and_eq_true] at matched
      exact (Scalar.blockMatches_code matched.1.1.1.1.2).hasBlock
  | call entry function operands destination next =>
      simp only [Plan.matches, Bool.and_eq_true] at matched
      cases found : entries[function]? with
      | none => simp [found] at matched
      | some target =>
          simp only [found, Bool.and_eq_true] at matched
          exact (Scalar.blockMatches_code matched.2.1).hasBlock
  | tailCall entry kind function operands =>
      simp only [Plan.matches, Bool.and_eq_true] at matched
      cases found : entries[function]? with
      | none => simp [found] at matched
      | some target =>
          simp only [found] at matched
          exact (Scalar.blockMatches_code matched.2).hasBlock

structure FunctionCode (checked : X86.Checked) (entries : Array BlockId) (parameters : Nat) (plan : FunctionPlan) : Prop where
  small : parameters ≤ 2
  prologue : BlockCode checked plan.entry (Scalar.prologue parameters) (.jump plan.body.entry)
  exit : BlockCode checked plan.exit Scalar.successInstructions .ret
  body : plan.body.matches checked.program entries plan.exit = true

theorem FunctionPlan.code {checked : X86.Checked} {entries : Array BlockId} {parameters : Nat} {tree : Tree} {plan : FunctionPlan}
    (matched : plan.matches checked.program entries parameters tree = true) : FunctionCode checked entries parameters plan := by
  simp only [FunctionPlan.matches, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at matched
  exact ⟨matched.1.1.1.2, Scalar.blockMatches_code matched.1.1.2, Scalar.blockMatches_code matched.1.2, matched.2⟩

def Output.parameters {schemas program root baseline} {selected : PhysicalHeap.Selected schemas program root}
    (_output : Output selected baseline) : Array Nat := selected.rows.map (·.interface.parameters.size)

def FunctionsCode (checked : X86.Checked) (plans : Array FunctionPlan) (parameters : Array Nat) : Prop :=
  ∀ (index : Nat) (plan : FunctionPlan), plans[index]? = some plan →
    FunctionCode checked (plans.map (·.entry)) (parameters[index]?.getD 0) plan

theorem Output.functions_code {schemas program root baseline} {selected : PhysicalHeap.Selected schemas program root}
    (output : Output selected baseline) : FunctionsCode output.target output.plans output.parameters := by
  intro index plan found
  obtain ⟨bound, same⟩ := Array.getElem?_eq_some_iff.mp found
  have rowBound : index < selected.rows.size := by rw [← output.size]; exact bound
  have accepted := Array.all_eq_true.mp output.verified index (by simp only [Array.size_zip, output.size]; omega)
  simp only [Array.getElem_zip, same] at accepted
  have parameters : output.parameters[index]?.getD 0 = selected.rows[index].interface.parameters.size := by
    simp [Output.parameters, Array.getElem?_eq_getElem rowBound]
  rw [parameters]
  exact FunctionPlan.code accepted

end Compilatrix.X86.HeapTarget
