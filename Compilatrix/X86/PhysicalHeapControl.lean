import Compilatrix.X86.PhysicalHeapExecution

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapPrimitives
open IxIR2.Eval (Store RVal Frame)

theorem simulates_ret {context constructors entries plans parameters rank}
    {definition : IxIR2.Function} {block pc : Nat} {scope : Scope} {body : IxIR2.Block} {source kind operand next}
    (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
    (term : body.terminator = .ret source) (taken : scope.take source = .ok (kind, operand, next))
    (finished : next.finished = true) :
    Simulates context constructors entries plans parameters rank definition block pc scope (.ret kind operand) := by
  intro layout offset frame store heapFuel values credits before exit final outside plan shape valid frames heap locals balanced budget successful
  cases plan with
  | ret entry actualKind actualOperand =>
      obtain ⟨kindEq, operandEq⟩ := Tree.ret.inj shape
      subst actualKind actualOperand
      obtain ⟨output, head, suffix⟩ := successful.first
      have terminal := physical_terminator_case blockAt endAt term head
      obtain ⟨value, resolved, noCredits, outputEq⟩ := exit.returned terminal
      subst output
      have peeked := (locals.take taken).1
      have represented := locals.resolved peeked resolved
      have returnedHeap : HeapAt context.schemas constructors offset store exit.reservations before.words := by
        simpa only [activeReservations, noCredits.reservations_nil, List.nil_append, Exit.reservations] using heap
      have owners := Scope.take_owners taken
      have empty := Scope.finished_owners finished
      refine ⟨{
        state := load frame before operand, store, heapFuel, value, count := 1
        native := .ret, steps := .cons rfl head (.refl _), suffix
        controls := by simp [HeapTarget.Plan.tree, Tree.controls]
        heap := returnedHeap, represented
        growth := by simp [HeapTarget.Plan.tree, Tree.allocations]
        balanced := ?_, counters := .refl store 1 }⟩
      change Balance store kind.owners outside
      unfold Balance at *
      omega
  | primitive | jump | branch | call | tailCall => cases shape

theorem simulates_primitive {context constructors entries plans parameters rank}
    {definition : IxIR2.Function} {block pc : Nat} {scope : Scope} {body : IxIR2.Block}
    {instruction operation nextScope next}
    (blockAt : definition.blocks[block]? = some body) (instructionAt : body.instructions[pc]? = some instruction)
    (selected : PrimitiveCode context.schemas constructors scope instruction operation nextScope)
    (rest : Simulates context constructors entries plans parameters rank definition block (pc + 1) nextScope next) :
    Simulates context constructors entries plans parameters rank definition block pc scope (.primitive operation next) := by
  intro layout offset frame store heapFuel values credits before exit final outside plan shape valid frames heap locals balanced budget successful
  cases plan with
  | primitive entry actualOperation nextPlan =>
      obtain ⟨operationEq, nextShape⟩ := Tree.primitive.inj shape
      subst actualOperation
      obtain ⟨output, head, suffix⟩ := successful.first
      have transferred := physical_instruction_case blockAt instructionAt selected.noCall head
      have primitiveRoom : store.heap.nodes.size - offset + operation.allocations ≤ capacity := by
        simp only [Tree.allocations] at budget; omega
      obtain ⟨middle⟩ := selected.executes transferred heap locals frames.separate primitiveRoom
      have machineEq := runningMachine_eq middle.running
      rw [machineEq] at head suffix
      have nextBudget : output.store.heap.nodes.size - offset + next.allocations (entries.map (·.allocations)) ≤ capacity := by
        have extent := heap.extent
        have growth := middle.growth
        simp only [Tree.allocations] at budget
        omega
      obtain ⟨tail⟩ := rest.atFrame nextShape middle.definition middle.block middle.pc valid frames middle.heap middle.locals
        (middle.statistics.balance selected balanced) nextBudget suffix
      refine ⟨tail.prepend 1 (.cons rfl head (.refl _)) (.primitive middle.executed tail.native) rfl ?_ ?_
        (middle.statistics.counterGrowth selected)⟩
      · have controlBound := tail.controls
        simp only [HeapTarget.Plan.tree, Tree.controls]
        omega
      · have growth := tail.growth
        have changed := middle.growth
        simp only [HeapTarget.Plan.tree, Tree.allocations]
        omega
  | ret | jump | branch | call | tailCall => cases shape

theorem simulates_jump {context constructors entries plans parameters rank}
    {definition : IxIR2.Function} {block pc : Nat} {scope : Scope} {body : IxIR2.Block} {edge transfer next}
    (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
    (term : body.terminator = .jump edge) (selected : TransferCode definition scope edge none transfer)
    (rest : Simulates context constructors entries plans parameters rank definition edge.target 0 transfer.scope next) :
    Simulates context constructors entries plans parameters rank definition block pc scope (.jump transfer next) := by
  intro layout offset frame store heapFuel values credits before exit final outside plan shape valid frames heap locals balanced budget successful
  cases plan with
  | jump entry actualTransfer nextPlan =>
      obtain ⟨transferEq, nextShape⟩ := Tree.jump.inj shape
      subst actualTransfer
      obtain ⟨output, head, suffix⟩ := successful.first
      have terminal := physical_terminator_case blockAt endAt term head
      generalize stackEq : exit.stack = stack at terminal
      cases terminal with
      | jump transferred =>
          subst stack
          obtain ⟨definitionEq, blockEq, pcEq, nextLocals⟩ := selected.related transferred locals .nil valid.1
          have nextHeap := (heap.copies frames.separate valid.1).reservations_perm
            (transferred.reservations.append_right (suspendedReservations exit.stack))
          have nextBalance : Balance store transfer.scope.owners outside := by rw [selected.owners]; exact balanced
          obtain ⟨tail⟩ := rest.atFrame nextShape definitionEq blockEq pcEq valid.2 frames nextHeap nextLocals nextBalance budget suffix
          refine ⟨tail.prepend 1 (.cons rfl head (.refl _)) (.jump tail.native) rfl ?_ tail.growth (.refl store 1)⟩
          have controlBound := tail.controls
          simp only [HeapTarget.Plan.tree, Tree.controls]
          omega
  | ret | primitive | branch | call | tailCall => cases shape

end Compilatrix.X86.PhysicalHeap
