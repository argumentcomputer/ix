import Compilatrix.X86.PhysicalHeapBranches

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapPrimitives
open IxIR2.Eval (Store RVal Frame)

theorem simulates_call {context constructors entries plans parameters rank}
    {definition : IxIR2.Function} {block pc : Nat} {scope : Scope} {body : IxIR2.Block}
    {address arguments kinds operands consumed index callee nextScope next}
    (declarations : Declarations context entries) (callees : Callees context constructors entries plans parameters rank)
    (blockAt : definition.blocks[block]? = some body) (instructionAt : body.instructions[pc]? = some (.call address arguments))
    (selected : ArgumentsCode scope arguments kinds operands consumed)
    (found : entries[index]? = some callee) (earlier : index < rank)
    (addressed : callee.address = address) (parameterKinds : callee.parameters = kinds)
    (pushed : consumed.pushValue callee.result = .ok nextScope)
    (rest : Simulates context constructors entries plans parameters rank definition block (pc + 1) nextScope next) :
    Simulates context constructors entries plans parameters rank definition block pc scope (.call index operands scope.values.size next) := by
  intro layout offset frame store heapFuel values credits before exit final outside plan shape valid frames heap locals balanced budget successful
  cases plan with
  | call entry actualIndex actualOperands actualDestination nextPlan =>
      obtain ⟨indexEq, operandsEq, destinationEq, nextShape⟩ := Tree.call.inj shape
      subst actualIndex actualOperands actualDestination
      obtain ⟨summary⟩ := callees index callee found earlier
      have declared : context.declarations address = some (.fn callee.definition) := by simpa only [addressed] using declarations index callee found
      obtain ⟨output, head, suffix⟩ := successful.first
      obtain ⟨supplied, resolved, outputEq⟩ := physical_call_case blockAt instructionAt declared head
      subst output
      obtain ⟨suppliedVector, remaining⟩ := ArgumentsCode.related selected resolved locals
      have calleeVector : ValueVector layout offset (store.heap.nodes.size - offset) callee.parameters.toList supplied.toList
          (HeapRuns.argumentValues frame before operands).toList := by simpa only [parameterKinds, HeapRuns.argumentValues] using suppliedVector
      have operandSize : operands.size = callee.parameters.size := by
        have lengths := calleeVector.lengths
        simp only [Array.length_toList, HeapRuns.argumentValues, Array.size_map] at lengths
        omega
      have small : operands.size ≤ 2 := operandSize ▸ summary.small
      let enough := frames.enough
      let child := frame.child enough
      have childRoom : FrameRoom child index := frames.child earlier
      have childSeparate := childRoom.separate
      let caller : Frame := ⟨definition, block, pc + 1, values, credits⟩
      let calleeExit := Exit.resume caller exit.stack
      let called := Scalar.enterState child (parameters[index]?.getD 0) (HeapRuns.called frame before operands enough entry)
      have calleeHeap : HeapAt context.schemas constructors offset store
          (activeReservations ⟨callee.definition, 0, 0, supplied, #[]⟩ calleeExit.stack) called.words :=
        (heap.call frame operands enough childSeparate entry).enter child childSeparate _
      have calleeLocals : ScopeAt layout offset (store.heap.nodes.size - offset) child (Scope.initial callee.parameters) supplied #[] called := by
        simpa only [called, summary.parameterCount] using ScopeAt.enter calleeVector (called_arguments frame before operands enough entry small)
      have calleeBalance : Balance store (Scope.initial callee.parameters).owners (consumed.owners + outside) := by
        have owners := TakeValues.owners selected
        rw [Scope.initial_owners, parameterKinds]
        unfold Balance at *
        omega
      have callBudget : store.heap.nodes.size - offset + callee.allocations ≤ capacity := by
        simp only [Tree.allocations, Array.getElem?_map, found, Option.map_some, Option.getD_some] at budget
        omega
      obtain ⟨calledResult⟩ := summary.contract layout offset child store heapFuel supplied called calleeExit final (consumed.owners + outside)
        childRoom calleeHeap calleeLocals calleeBalance callBudget suffix
      have childPreserves := calledResult.native.preserves childSeparate
      have callerPreserves := HeapRuns.call_preserves frame (parameters[index]?.getD 0) before calledResult.state operands enough entry childPreserves
      have usedGrowth : store.heap.nodes.size - offset ≤ calledResult.store.heap.nodes.size - offset := by
        have := calledResult.growth.1
        omega
      have returnedLocals := (remaining.grow usedGrowth).preserved callerPreserves
      have returnedHeap : HeapAt context.schemas constructors offset calledResult.store
          (activeReservations ⟨definition, block, pc + 1, values.push calledResult.value, credits⟩ exit.stack)
          (HeapRuns.resumed frame before calledResult.state operands enough).words := calledResult.heap
      have returnedValue : ValueAt layout offset (calledResult.store.heap.nodes.size - offset) callee.result calledResult.value
          ((HeapRuns.resumed frame before calledResult.state operands enough).registers .rax) := by
        rw [← summary.result]
        exact calledResult.represented.resumed frame
      have sameSize : consumed.values.size = scope.values.size := remaining.valueSize.trans locals.valueSize.symm
      have room := pushValue_room pushed
      have destinationBound : scope.values.size < Scalar.maxLocals := by
        simp only [maxValues, Scalar.maxLocals] at *; omega
      have nextHeap := returnedHeap.setStack frame frames.separate destinationBound
        ((HeapRuns.resumed frame before calledResult.state operands enough).registers .rax)
      have nextLocals : ScopeAt layout offset (calledResult.store.heap.nodes.size - offset) frame nextScope
          (values.push calledResult.value) credits (save frame (HeapRuns.resumed frame before calledResult.state operands enough) scope.values.size) := by
        simpa only [sameSize] using returnedLocals.saveValue pushed returnedValue
      have nextBalance : Balance calledResult.store nextScope.owners outside := by
        have returnedBalance := calledResult.balanced
        rw [summary.result] at returnedBalance
        have owners := Scope.pushValue_owners pushed
        unfold Balance at *
        omega
      have nextBudget : calledResult.store.heap.nodes.size - offset + next.allocations (entries.map (·.allocations)) ≤ capacity := by
        have growth := calledResult.growth
        rw [summary.allocations] at growth
        have extent := heap.extent
        simp only [Tree.allocations, Array.getElem?_map, found, Option.map_some, Option.getD_some] at budget
        omega
      obtain ⟨tail⟩ := rest.atFrame nextShape rfl rfl rfl valid frames nextHeap nextLocals nextBalance nextBudget calledResult.suffix
      refine ⟨tail.prepend (calledResult.count + 1) (.cons rfl head calledResult.steps)
        (.call summary.found enough childSeparate calledResult.native tail.native) rfl ?_ ?_ ?_⟩
      · have calleeControls := calledResult.controls
        rw [summary.controls] at calleeControls
        have controlBound := tail.controls
        simp only [HeapTarget.Plan.tree, Tree.controls, Array.getElem?_map, found, Option.map_some, Option.getD_some]
        omega
      · have calleeGrowth := calledResult.growth
        rw [summary.allocations] at calleeGrowth
        have growth := tail.growth
        simp only [HeapTarget.Plan.tree, Tree.allocations, Array.getElem?_map, found, Option.map_some, Option.getD_some]
        omega
      · simpa only [Nat.add_comm] using (CounterGrowth.refl store 1).trans calledResult.counters
  | ret | primitive | jump | branch | tailCall => cases shape

theorem simulates_tailCall {context constructors entries plans parameters rank}
    {definition : IxIR2.Function} {block pc : Nat} {scope : Scope} {body : IxIR2.Block}
    {address arguments kinds operands consumed index callee}
    (declarations : Declarations context entries) (callees : Callees context constructors entries plans parameters rank)
    (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
    (term : body.terminator = .tailCall address arguments)
    (selected : ArgumentsCode scope arguments kinds operands consumed) (finished : consumed.finished = true)
    (found : entries[index]? = some callee) (earlier : index < rank)
    (addressed : callee.address = address) (parameterKinds : callee.parameters = kinds) :
    Simulates context constructors entries plans parameters rank definition block pc scope (.tailCall callee.result index operands) := by
  intro layout offset frame store heapFuel values credits before exit final outside plan shape valid frames heap locals balanced budget successful
  cases plan with
  | tailCall entry actualKind actualIndex actualOperands =>
      obtain ⟨kindEq, indexEq, operandsEq⟩ := Tree.tailCall.inj shape
      subst actualKind actualIndex actualOperands
      obtain ⟨summary⟩ := callees index callee found earlier
      have declared : context.declarations address = some (.fn callee.definition) := by simpa only [addressed] using declarations index callee found
      obtain ⟨output, head, suffix⟩ := successful.first
      have terminal := physical_terminator_case blockAt endAt term head
      generalize stackEq : exit.stack = stack at terminal
      cases terminal with
      | @tailCallFn stack address arguments supplied actualDefinition noCredits resolved declaration arity nonempty =>
          subst stack
          have definitionEq := IxIR2.Decl.fn.inj (Option.some.inj (declaration.symm.trans declared))
          subst actualDefinition
          obtain ⟨suppliedVector, remaining⟩ := ArgumentsCode.related selected resolved locals
          have calleeVector : ValueVector layout offset (store.heap.nodes.size - offset) callee.parameters.toList supplied.toList
              (HeapRuns.argumentValues frame before operands).toList := by simpa only [parameterKinds, HeapRuns.argumentValues] using suppliedVector
          have operandSize : operands.size = callee.parameters.size := by
            have lengths := calleeVector.lengths
            simp only [Array.length_toList, HeapRuns.argumentValues, Array.size_map] at lengths
            omega
          have small : operands.size ≤ 2 := operandSize ▸ summary.small
          let enough := frames.enough
          let child := frame.child enough
          have childRoom : FrameRoom child index := frames.child earlier
          have childSeparate := childRoom.separate
          let called := Scalar.enterState child (parameters[index]?.getD 0) (HeapRuns.called frame before operands enough entry)
          have noReservations : HeapAt context.schemas constructors offset store exit.reservations before.words := by
            simpa only [activeReservations, noCredits.reservations_nil, List.nil_append, Exit.reservations] using heap
          have calleeHeap : HeapAt context.schemas constructors offset store
              (activeReservations ⟨callee.definition, 0, 0, supplied, #[]⟩ exit.stack) called.words :=
            (noReservations.call frame operands enough childSeparate entry).enter child childSeparate _
          have calleeLocals : ScopeAt layout offset (store.heap.nodes.size - offset) child (Scope.initial callee.parameters) supplied #[] called := by
            simpa only [called, summary.parameterCount] using ScopeAt.enter calleeVector (called_arguments frame before operands enough entry small)
          have calleeBalance : Balance store (Scope.initial callee.parameters).owners outside := by
            have owners := TakeValues.owners selected
            have empty := Scope.finished_owners finished
            rw [Scope.initial_owners, parameterKinds]
            unfold Balance at *
            omega
          have callBudget : store.heap.nodes.size - offset + callee.allocations ≤ capacity := by
            simpa only [Tree.allocations, Array.getElem?_map, found, Option.map_some, Option.getD_some] using budget
          obtain ⟨calledResult⟩ := summary.contract layout offset child store heapFuel supplied called exit final outside
            childRoom calleeHeap calleeLocals calleeBalance callBudget suffix
          refine ⟨{
            state := HeapRuns.resumed frame before calledResult.state operands enough
            store := calledResult.store, heapFuel := calledResult.heapFuel, value := calledResult.value, count := calledResult.count + 1
            native := .tailCall summary.found enough childSeparate calledResult.native
            steps := .cons rfl head calledResult.steps, suffix := calledResult.suffix
            controls := ?_, heap := calledResult.heap, represented := ?_, growth := ?_, balanced := ?_, counters := ?_ }⟩
          · have calleeControls := calledResult.controls
            rw [summary.controls] at calleeControls
            simp only [HeapTarget.Plan.tree, Tree.controls, Array.getElem?_map, found, Option.map_some, Option.getD_some]
            omega
          · change ValueAt layout offset _ callee.result calledResult.value _
            rw [← summary.result]
            exact calledResult.represented.resumed frame
          · simpa only [HeapTarget.Plan.tree, Tree.allocations, Array.getElem?_map, found, Option.map_some, Option.getD_some,
              summary.allocations] using calledResult.growth
          · simpa only [HeapTarget.Plan.tree, Tree.result, summary.result] using calledResult.balanced
          · simpa only [Nat.add_comm] using (CounterGrowth.refl store 1).trans calledResult.counters
  | ret | primitive | jump | branch | call => cases shape

theorem Code.simulate {context constructors entries plans parameters rank definition block pc scope tree}
    (code : Code context.schemas constructors entries rank definition block pc scope tree)
    (declarations : Declarations context entries) (callees : Callees context constructors entries plans parameters rank) :
    Simulates context constructors entries plans parameters rank definition block pc scope tree := by
  induction code with
  | ret a b c d e => exact simulates_ret a b c d e
  | primitive a b c _ ih => exact simulates_primitive a b c ih
  | jump a b c d _ ih => exact simulates_jump a b c d ih
  | branch a b c d e f g _ _ ihZero ihSucc => exact simulates_branch a b c d e f g ihZero ihSucc
  | constructor a b c d e _ ih => exact simulates_constructor a b c d e ih
  | present a b c d e _ ih => exact simulates_present a b c d e ih
  | call a b c d e f g h _ ih => exact simulates_call declarations callees a b c d e f g h ih
  | tailCall a b c d e f g h i => exact simulates_tailCall declarations callees a b c d e f g h i

end Compilatrix.X86.PhysicalHeap
