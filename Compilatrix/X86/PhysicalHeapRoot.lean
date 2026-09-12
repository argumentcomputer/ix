import Compilatrix.X86.PhysicalHeapInitial

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open IxIR2.Eval (Store RVal Result)

/-- Every physical allocation has been reclaimed. Header counters are exact
natural numbers, and every used native cell has the free tag. -/
structure HeapObservation (offset demand : Nat) (store : Store) (words : Words) : Prop where
  live : store.live = 0
  empty : ∀ location, store.get? location = none
  freed : store.heap.allocs = store.heap.frees
  used : store.heap.nodes.size - offset ≤ demand
  cursor : (words 0).toNat = 32 * (store.heap.nodes.size - offset)
  statistics : ∀ field, 2 ≤ field → field ≤ 8 → (words field).toNat = counters store field
  reservations : words 9 = 0
  cells : ∀ index < store.heap.nodes.size - offset, words (cellSlot index 0) = 0

/-- A successful physical run supplies the entire native execution. Neither
callee summaries nor native-run assumptions occur in this entry contract. -/
theorem Output.physicalReturns {schemas program root baseline}
    {selected : Selected schemas program root} (output : HeapTarget.Output selected baseline)
    (values : Array Word) (arity : values.size = selected.entryInterface.definition.signature.params.size)
    (oracle : Ixon.Address → List RVal → Option RVal) {controlFuel heapFuel : Nat} {result : Result}
    (physical : IxIR2.Eval.Policy.runFunction .suspendedCallsV1
      (IxIR2.Eval.Context.ofProgram program schemas oracle) .physical selected.entryInterface.definition
      (values.map PhysicalScalar.rval) controlFuel heapFuel (initialStore baseline) = .ok result)
    (workspace : Workspace) (depth : selected.entry < workspace.depth) (core : Core)
    (stack : core.readReg .rsp = workspace.layout.region.address workspace.externalTop)
    (base : core.readReg .rdx = workspace.layout.region.base)
    (arguments : Scalar.ArgumentsAt values (HeapEntry.stateOf workspace core))
    (enough : selected.entryInterface.allocations ≤ (core.memory.read64 (workspace.layout.region.address 1)).toNat)
    (bound : (core.memory.read64 (workspace.layout.region.address 1)).toNat ≤ capacity)
    (readable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.readable (workspace.layout.region.address index) 8 = true)
    (writable : ∀ index < workspace.layout.region.slots, Memory.rangeAllowed core.memory.writable (workspace.layout.region.address index) 8 = true) :
    ∃ word words, result.value = PhysicalScalar.rval word ∧
      HeapObservation (initialOffset baseline) selected.entryInterface.allocations result.store words ∧
      Nonempty (HeapEntry.RootRun output.target core workspace word 0 words) := by
  let context := IxIR2.Eval.Context.ofProgram program schemas oracle
  obtain ⟨summary⟩ := Output.summaries output (selected.declarations oracle) selected.entry selected.entryInterface selected.entryFound
  dsimp only [IxIR2.Eval.Context.ofProgram] at summary
  have run := physical
  rw [IxIR2.Eval.Policy.runFunction_eq_runMachine (by simpa using arity) summary.nonempty,
    initialMachine_eq] at run
  obtain ⟨count, _, steps⟩ := IxIR2.Eval.Policy.runMachine_steps run
  have successful : Successful context
      ⟨initialStore baseline, heapFuel, .running ⟨selected.entryInterface.definition, 0, 0, values.map PhysicalScalar.rval, #[]⟩ []⟩ result :=
    ⟨count, steps⟩
  let before := HeapEntry.called baseline workspace output.entry (HeapEntry.stateOf workspace core)
  have vector : ValueVector workspace.layout (initialOffset baseline) 0 selected.entryInterface.parameters.toList
      (values.map PhysicalScalar.rval).toList values.toList := by
    have allScalar : selected.entryInterface.parameters.toList.all (fun kind => kind == .scalar) = true := by
      simpa using selected.entryParameters
    simpa only [Array.toList_map] using ValueVector.scalars
      (fun kind member => beq_iff_eq.mp (List.all_eq_true.mp allScalar kind member))
      (by simp only [Array.length_toList]; exact summary.arity.trans arity.symm)
  have heap := (initialHeap_called (schemas := schemas) (constructors := selected.constructors)
    baseline workspace output.entry (HeapEntry.stateOf workspace core)).enter workspace.frame workspace.separate
      selected.entryInterface.parameters.size
  have locals := ScopeAt.enter (frame := workspace.frame) (state := before) vector
    (entry_arguments (baseline := baseline) (entry := output.entry) arguments)
  have balanced : Balance (initialStore baseline) (Scope.initial selected.entryInterface.parameters).owners 0 := by
    rw [scalar_owners selected.entryParameters]
    exact initialStore_balanced baseline
  obtain ⟨executed⟩ := summary.contract workspace.layout (initialOffset baseline) workspace.frame
    (initialStore baseline) heapFuel (values.map PhysicalScalar.rval)
    (Scalar.enterState workspace.frame selected.entryInterface.parameters.size before) .halt result 0
    (workspace.rank_capacity depth) (by simpa [activeReservations, IxIR2.Eval.Frame.reservations,
      IxIR2.Eval.Frame.liveCredits, Exit.stack, suspendedReservations, IxIR2.Eval.Context.ofProgram, before] using heap)
    (by simpa using locals) balanced
    (by simpa [maxAllocations, capacity] using selected.allocationBound) successful
  obtain ⟨storeEq, _, valueEq⟩ := executed.suffix.halted
  have represented := executed.represented
  rw [summary.result, selected.entryResult] at represented
  have value : result.value = PhysicalScalar.rval (executed.state.registers .rax) :=
    valueEq.symm.trans represented.scalar_value
  have freed : result.store.heap.allocs = result.store.heap.frees := by
    have balanced := executed.balanced
    simpa only [Balance, summary.result, selected.entryResult, Kind.owners, Nat.add_zero, storeEq] using balanced
  have accounted := executed.steps.allocationAccounting
    (initialStore_accounted baseline selected.entryInterface.definition (values.map PhysicalScalar.rval) heapFuel)
  have live : result.store.live = 0 := by
    simp only [IxIR2.Eval.Machine.AllocationAccounting, Exit.machine, IxIR2.Eval.Machine.presentCredits,
      storeEq, Nat.add_zero, freed] at accounted
    omega
  have heap : HeapAt schemas selected.constructors (initialOffset baseline) result.store [] executed.state.words := by
    simpa only [Exit.reservations, Exit.stack, suspendedReservations, List.flatMap_nil, storeEq,
      IxIR2.Eval.Context.ofProgram] using executed.heap
  have empty := Store.empty_of_live_zero live
  have reclaimed := heap.reclaimed empty
  have used : result.store.heap.nodes.size - initialOffset baseline ≤ selected.entryInterface.allocations := by
    have growth := executed.growth.2
    rw [initialStore_size, summary.allocations, storeEq] at growth
    omega
  have statistics : ∀ field, 2 ≤ field → field ≤ 8 → (executed.state.words field).toNat = counters result.store field := by
    intro field lower upper
    rw [heap.statistics field lower upper]
    apply UInt64.toNat_ofNat_of_lt'
    have bounded := executed.counters field lower upper
    have initial := (initialStore_counter baseline lower upper).2
    have controls := executed.controls
    rw [summary.controls] at controls
    rw [storeEq] at bounded
    have limit := selected.controlBound
    simp only [UInt64.size, maxControls] at *
    omega
  have native := HeapEntry.Output.root_run output summary.found workspace core executed.state
    (by rw [summary.parameterCount]; exact executed.native) stack base enough bound readable writable
  refine ⟨executed.state.registers .rax, executed.state.words, value,
    ⟨live, empty, freed, used, ?_, statistics, reclaimed.1, reclaimed.2⟩, native⟩
  rw [heap.cursor]
  apply UInt64.toNat_ofNat_of_lt'
  have bounded := heap.bounded
  simp only [capacity, UInt64.size] at *
  omega

end Compilatrix.X86.PhysicalHeap
