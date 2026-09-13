import Compilatrix.X86.HeapGraphEmit

namespace Compilatrix.X86.HeapGraph
open PhysicalHeap PhysicalHeap.Graph

private structure AcceptedFunction (selection : Graph.Selected schemas program root)
    (target : X86.Program) (entries : Array BlockId) where
  index : Nat
  plan : HeapTarget.FunctionPlan
  verified : ∀ (row : Graph.Row schemas selection.selected.constructors selection.selected.entries),
    selection.graphs[index]? = some row →
    plan.matches target entries row.row.interface.parameters.size row.row.source.tree = true

private def checkFunctionAt (selection : Graph.Selected schemas program root) (target : X86.Program)
    (entries : Array BlockId) (index : Nat) (candidate : FunctionPlan) :
    Except String (AcceptedFunction selection target entries) := do
  match found : selection.graphs[index]? with
  | none => throw "heap graph native function coverage has extra rows"
  | some row =>
    let checked ← checkFunction row.graph target entries row.row.interface.parameters.size candidate
    return {
      index, plan := checked.val
      verified := by
        intro actual present
        have equal := Option.some.inj (present.symm.trans found)
        subst actual
        exact checked.property.2 }

private theorem accepted_plans {selection : Graph.Selected schemas program root} {target entries}
    (checked : Array (AcceptedFunction selection target entries))
    (indexed : checked.toList.zipIdx.all (fun (row, index) => row.index == index) = true) :
    ((checked.map (·.plan)).zip selection.selected.rows).all (fun (plan, row) =>
      plan.matches target entries row.interface.parameters.size row.source.tree) = true := by
  apply Array.all_eq_true'.mpr
  intro pair member
  obtain ⟨index, found⟩ := Array.getElem?_of_mem member
  obtain ⟨planAt, rowAt⟩ := Array.getElem?_zip_eq_some.mp found
  simp only [Array.getElem?_map] at planAt
  cases checkedAt : checked[index]? with
  | none => simp [checkedAt] at planAt
  | some item =>
    have samePlan : item.plan = pair.1 := by simpa [checkedAt] using planAt
    have member : (item, index) ∈ checked.toList.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa only [Array.getElem?_toList] using checkedAt)
    have sameIndex : item.index = index := beq_iff_eq.mp (List.all_eq_true.mp indexed _ member)
    rw [← selection.same, Array.getElem?_map] at rowAt
    cases graphAt : selection.graphs[index]? with
    | none => simp [graphAt] at rowAt
    | some row =>
      have sameRow : row.row = pair.2 := by simpa [graphAt] using rowAt
      have sameTree := congrArg (fun (value : PhysicalHeap.Row schemas
        selection.selected.constructors selection.selected.entries) => value.source.tree) sameRow
      have verified := item.verified row (by simpa only [sameIndex] using graphAt)
      simpa only [samePlan, sameRow, sameTree] using verified

private theorem check_program {program : X86.Program} {target : X86.Checked}
    (accepted : (X86.Program.check program).mapError reprStr = .ok target) : target.program = program := by
  unfold X86.Program.check at accepted
  split at accepted
  · cases accepted
    rfl
  · contradiction

/-- Check only local graph obligations. The result contains the same complete
native certificate used by the existing physical and source simulations. -/
private def checkProposed (selection : Graph.Selected schemas program root) (baseline : Bool)
    (candidate : Candidate) :
    Except String { output : HeapTarget.Output selection.selected baseline // output.target.program = candidate.program } := do
  if candidate.functions.size != selection.graphs.size then throw "heap graph native function coverage is incomplete"
  let target ← checkedExcept ((X86.Program.check candidate.program).mapError reprStr)
  let mut checked : Array (AcceptedFunction selection target.val.program candidate.entries) := #[]
  for function in candidate.functions do
    checked := checked.push (← checkFunctionAt selection target.val.program candidate.entries checked.size function)
  if indexed : checked.toList.zipIdx.all (fun (row, index) => row.index == index) = true then
    if complete : checked.size = selection.selected.rows.size then
      let planArray : Array HeapTarget.FunctionPlan := checked.map (·.plan)
      if sameEntries : planArray.map (·.entry) = candidate.entries then
        if entryAt : target.val.program.entry = candidate.entry.entry then
          if entryVerified : candidate.entry.matches target.val.program baseline
              ((planArray.map (·.entry))[selection.selected.entry]?.getD 0)
              selection.selected.entryInterface.allocations = true then
            have sized : planArray.size = selection.selected.rows.size := by
              simpa only [planArray, Array.size_map] using complete
            have verified : (planArray.zip selection.selected.rows).all (fun (plan, row) =>
                HeapTarget.FunctionPlan.matches target.val.program (planArray.map (·.entry))
                  row.interface.parameters.size row.source.tree plan) = true := by
              rw [sameEntries]
              exact accepted_plans checked indexed
            let output : HeapTarget.Output selection.selected baseline := {
              target := target.val, plans := planArray, size := sized
              entry := candidate.entry, entryAt
              verified := verified
              entryVerified := entryVerified }
            return ⟨output, check_program target.property⟩
          else throw "heap graph native capacity adapter certificate failed"
        else throw "heap graph native entry changed"
      else throw "heap graph native callee entries changed"
    else throw "heap graph native function coverage changed during checking"
  else throw "heap graph native function indices disagree"

def checkCandidate (selection : Graph.Selected schemas program root) (baseline : Bool) (candidate : Candidate) :
    Except String (HeapTarget.Output selection.selected baseline) := do
  return (← checkProposed selection baseline candidate).val

theorem checkCandidate_program {selection : Graph.Selected schemas program root} {baseline candidate output}
    (accepted : checkCandidate selection baseline candidate = .ok output) :
    output.target.program = candidate.program := by
  unfold checkCandidate at accepted
  cases checked : checkProposed selection baseline candidate with
  | error message => simp [checked, bind, Except.bind] at accepted
  | ok result =>
    have same : result.val = output := by simpa [checked, bind, Except.bind, pure, Except.pure] using accepted
    rw [← same]
    exact result.property

def compile (selection : Graph.Selected schemas program root) (baseline : Bool := false) :
    Except String (HeapTarget.Output selection.selected baseline) := do
  checkCandidate selection baseline (← emitCandidate selection baseline)

end Compilatrix.X86.HeapGraph
