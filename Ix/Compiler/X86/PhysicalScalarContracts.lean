import Ix.Compiler.X86.PhysicalScalarSelect
import Ix.Compiler.X86.PhysicalScalarSim

namespace Ix.Compiler.X86.PhysicalScalar
open IxIR2.Eval

theorem Selected.rowAt {program root} (selected : Selected program root) {index : Nat} {target : Scalar.Function}
    (found : selected.scalar.program.functions[index]? = some target) :
    ∃ row : Row selected.entries, selected.rows[index]? = some row ∧ row.index = index ∧
      selected.entries[index]? = some (row.address, row.definition) ∧ row.target = target := by
  rw [selected.functions, Array.getElem?_map] at found
  cases rowAt : selected.rows[index]? with
  | none => simp [rowAt] at found
  | some row =>
    have targetEq : row.target = target := by simpa [rowAt] using found
    obtain ⟨bound, rowEq⟩ := Array.getElem?_eq_some_iff.mp rowAt
    have member : (row, index) ∈ selected.rows.toList.zipIdx := by
      have h := List.getElem_mem (l := selected.rows.toList.zipIdx) (n := index) (by simpa using bound)
      simpa [rowEq] using h
    have checked := List.all_eq_true.mp selected.indexed (row, index) member
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    exact ⟨row, rfl, checked.1, checked.2, targetEq⟩

theorem Selected.declarations {program root} (selected : Selected program root)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema)
    (oracle : Ixon.Address → List RVal → Option RVal) :
    Declarations (Context.ofProgram program schemas oracle) selected.entries := by
  intro index address definition found
  obtain ⟨bound, eq⟩ := Array.getElem?_eq_some_iff.mp found
  have checked := Array.all_eq_true.mp selected.declared index bound
  change lookup program address = some (.fn definition)
  simpa only [eq, beq_iff_eq] using checked

/-- Universal call contracts for all accepted physical functions. This is a
single strong induction on the checked nonrecursive function order. -/
theorem Selected.contract {program root} (selected : Selected program root)
    {context : Context} {mode : Interpretation} (declarations : Declarations context selected.entries)
    {index : Nat} {address : Ixon.Address} {definition : IxIR2.Function} {target : Scalar.Function}
    (entryAt : selected.entries[index]? = some (address, definition))
    (targetAt : selected.scalar.program.functions[index]? = some target) :
    FunctionContract context mode definition selected.scalar.program.functions target := by
  induction index using Nat.strongRecOn generalizing address definition target with
  | ind index ih =>
    obtain ⟨row, _, rowIndex, entry, rowTarget⟩ := selected.rowAt targetAt
    have definitions : definition = row.definition := congrArg Prod.snd (Option.some.inj (entryAt.symm.trans entry))
    subst definition
    have callees : Callees context mode selected.entries selected.scalar.program.functions index := by
      intro callee address definition target found earlier targetAt
      exact ih callee earlier found targetAt
    refine ⟨by simpa [rowTarget] using row.arity, row.nonempty, ?_⟩
    intro values result arity evaluated
    have code : Code selected.entries index row.definition 0 0 (parameters target.parameters) target.parameters target.body := by
      simpa [rowIndex, rowTarget] using row.code
    apply code.simulate declarations callees arity _ evaluated
    simpa [arity] using EnvRel.parameters values

/-- Compare the constructed execution with any successful physical run,
even when its control and traversal budgets differ. The complete input heap
is preserved (apart from the evaluator's initial peak bookkeeping). -/
theorem Runs.agrees {context mode definition arguments word controlFuel heapFuel store result}
    (executed : Runs context mode (frame definition 0 0 arguments) word)
    (arity : arguments.size = definition.signature.params.size) (nonempty : definition.blocks.isEmpty = false)
    (actual : runFunction context mode definition (arguments.map rval) controlFuel heapFuel store = .ok result) :
    result.value = rval word ∧ result.store = (initialMachine definition (arguments.map rval) 0 store).store := by
  rw [runFunction_eq_runMachine (by simpa using arity) nonempty] at actual
  obtain ⟨actualCount, _, actualSteps⟩ := runMachine_steps actual
  obtain ⟨count, heap, selectedSteps⟩ := executed
    (initialMachine definition (arguments.map rval) 0 store).store .halt 0
  have selectedSteps : IxIR2.Eval.Steps context mode count
      (initialMachine definition (arguments.map rval) heap store)
      { store := (initialMachine definition (arguments.map rval) 0 store).store
        heapFuel := 0, control := .halted (rval word) } := by
    simpa [initialMachine, frame, Exit.stack, Exit.result] using selectedSteps
  have left := actualSteps.addHeapFuel heap
  have right := selectedSteps.addHeapFuel heapFuel
  have common : (initialMachine definition (arguments.map rval) heap store).addHeapFuel heapFuel =
      (initialMachine definition (arguments.map rval) heapFuel store).addHeapFuel heap := by
    simp [initialMachine, IxIR2.Eval.Machine.addHeapFuel, Nat.add_comm]
  rw [common] at right
  obtain ⟨_, heaps, _, values⟩ := left.halted_unique right
  exact ⟨values, heaps⟩

end Ix.Compiler.X86.PhysicalScalar
