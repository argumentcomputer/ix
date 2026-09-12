import Compilatrix.X86.PhysicalHeapCallSimulation

namespace Compilatrix.X86.PhysicalHeap
open IxIR2.Eval (Store RVal)

theorem Selected.declarations {schemas program root} (selected : Selected schemas program root)
    (oracle : Ixon.Address → List RVal → Option RVal) :
    Declarations (IxIR2.Eval.Context.ofProgram program schemas oracle) selected.entries := by
  intro index interface found
  obtain ⟨bound, atIndex⟩ := Array.getElem?_eq_some_iff.mp found
  have accepted := Array.all_eq_true.mp selected.declared index bound
  simpa only [atIndex, beq_iff_eq, IxIR2.Eval.Context.ofProgram, PhysicalScalar.lookup] using accepted

theorem Selected.row_index {schemas program root} (selected : Selected schemas program root)
    {index : Nat} (bound : index < selected.rows.size) : selected.rows[index].index = index := by
  have member : (selected.rows[index], index) ∈ selected.rows.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [Array.getElem?_eq_getElem bound])
  exact beq_iff_eq.mp (List.all_eq_true.mp selected.indexed _ member)

theorem Output.summaries {context : PhysicalContext} {program root baseline}
    {selected : Selected context.schemas program root} (output : HeapTarget.Output selected baseline)
    (declarations : Declarations context selected.entries) :
    ∀ index interface, selected.entries[index]? = some interface →
      Nonempty (FunctionSummary context selected.constructors selected.entries output.plans output.parameters index interface) := by
  intro index
  induction index using Nat.strongRecOn with
  | ind index ih =>
      intro interface found
      have bound := (Array.getElem?_eq_some_iff.mp found).1
      have rowBound : index < selected.rows.size := by rw [selected.complete]; exact bound
      have planBound : index < output.plans.size := by rw [output.size]; exact rowBound
      let row := selected.rows[index]
      let plan := output.plans[index]
      have rowIndex : row.index = index := selected.row_index rowBound
      have interfaceEq : row.interface = interface := by
        have atInterface := row.found
        rw [rowIndex] at atInterface
        exact Option.some.inj (atInterface.symm.trans found)
      have matched : plan.matches output.target.program (output.plans.map (·.entry)) row.interface.parameters.size row.source.tree = true := by
        have zipBound : index < (output.plans.zip selected.rows).size := by simp only [Array.size_zip]; omega
        have accepted := Array.all_eq_true.mp output.verified index zipBound
        have pair : (output.plans.zip selected.rows)[index] = (plan, row) := Array.getElem_zip
        rw [pair] at accepted
        exact accepted
      have treeEq : plan.body.tree = row.source.tree := by
        simp only [HeapTarget.FunctionPlan.matches, Bool.and_eq_true, beq_iff_eq] at matched
        exact matched.1.1.1.1
      have nativeCode := HeapTarget.FunctionPlan.code matched
      have code : Code context.schemas selected.constructors selected.entries index interface.definition 0 0
          (Scope.initial interface.parameters) row.source.tree := by
        simpa only [rowIndex, interfaceEq] using row.source.code
      have earlier : Callees context selected.constructors selected.entries output.plans output.parameters index := by
        intro previous callee calleeAt before
        exact ih previous before callee calleeAt
      have simulated := code.simulate declarations earlier
      have allocationEq : plan.body.tree.allocations (selected.entries.map (·.allocations)) = interface.allocations :=
        (congrArg (fun tree => tree.allocations (selected.entries.map (·.allocations))) treeEq).trans
          (by simpa only [interfaceEq] using row.source.allocations)
      refine ⟨{
        plan, found := Array.getElem?_eq_getElem planBound
        parameterCount := ?_, small := by simpa only [interfaceEq] using row.source.small
        arity := by simpa only [interfaceEq] using row.source.arity
        nonempty := by simpa only [interfaceEq] using row.source.nonempty
        result := (congrArg Tree.result treeEq).trans (by simpa only [interfaceEq] using row.source.result)
        allocations := allocationEq
        controls := (congrArg (fun tree => tree.controls (selected.entries.map (·.controls))) treeEq).trans
          (by simpa only [interfaceEq] using row.source.controls)
        contract := ?_ }⟩
      · simp only [HeapTarget.Output.parameters, Array.getElem?_map, Array.getElem?_eq_getElem rowBound, Option.map_some, Option.getD_some]
        exact congrArg (fun entry : Interface => entry.parameters.size) interfaceEq
      · intro layout offset frame store heapFuel values state exit final outside frames heap locals balanced budget successful
        apply simulated layout offset frame store heapFuel values #[] state exit final outside plan.body treeEq
          (by rw [← treeEq]; exact plan_copiesValid nativeCode.body) frames heap locals balanced _ successful
        simpa only [← treeEq, allocationEq] using budget

end Compilatrix.X86.PhysicalHeap
