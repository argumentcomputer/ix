import Compilatrix.X86.PhysicalHeapControl

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapPrimitives
open IxIR2.Eval (Store RVal Frame Credit)

theorem ScopeAt.present {layout offset used frame scope state values credits index id raw credit}
    (locals : ScopeAt layout offset used frame scope values credits state)
    (active : scope.credits[index]? = some (some id))
    (slots : raw.credits = credits) (lookedUp : IxIR2.Eval.CreditLookup raw index credit) : credit.isPresent = true := by
  obtain ⟨actual, found, ⟨represented⟩⟩ := locals.credits index id active
  have actualLookup := IxIR2.Eval.CreditLookup.of_getElem (slots ▸ found)
  have equal := Except.ok.inj (actualLookup.symm.trans lookedUp)
  subst actual
  have presence := represented.presence
  cases credit
  simp_all [Credit.isPresent]

theorem simulates_constructor {context constructors entries plans parameters rank}
    {definition : IxIR2.Function} {block pc : Nat} {scope : Scope} {body : IxIR2.Block}
    {source alternative peel operand transfer next}
    (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
    (term : body.terminator = .switchValue source #[alternative] peel) (node : scope.node source = .ok operand)
    (selected : TransferCode definition scope alternative.edge none transfer)
    (rest : Simulates context constructors entries plans parameters rank definition alternative.edge.target 0 transfer.scope next) :
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
      | switchCtor resolved found nodeAt alternativeAt transferred =>
          subst stack
          have chosen := Array.mem_of_find?_eq_some alternativeAt
          simp only [Array.mem_singleton] at chosen
          cases chosen
          obtain ⟨definitionEq, blockEq, pcEq, nextLocals⟩ := selected.related transferred locals .nil valid.1
          have nextHeap := (heap.copies frames.separate valid.1).reservations_perm
            (transferred.reservations.append_right (suspendedReservations exit.stack))
          have nextBalance : Balance store transfer.scope.owners outside := by rw [selected.owners]; exact balanced
          obtain ⟨tail⟩ := rest.atFrame nextShape definitionEq blockEq pcEq valid.2 frames nextHeap nextLocals nextBalance budget suffix
          refine ⟨tail.prepend 1 (.cons rfl head (.refl _)) (.jump tail.native) rfl ?_ tail.growth (.refl store 1)⟩
          have controlBound := tail.controls
          simp only [HeapTarget.Plan.tree, Tree.controls]
          omega
      | switchNatZero resolved transferred | switchNatSucc resolved transferred =>
          obtain ⟨location, atNode, _⟩ := locals.node node
          cases Except.ok.inj (atNode.symm.trans resolved)
  | ret | primitive | branch | call | tailCall => cases shape

theorem simulates_present {context constructors entries plans parameters rank}
    {definition : IxIR2.Function} {block pc : Nat} {scope : Scope} {body : IxIR2.Block}
    {credit yes no id transfer next}
    (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
    (term : body.terminator = .branchCredit credit yes no) (active : scope.credits[credit]? = some (some id))
    (selected : TransferCode definition scope yes none transfer)
    (rest : Simulates context constructors entries plans parameters rank definition yes.target 0 transfer.scope next) :
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
      | branchPresent lookedUp present transferred =>
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
      | branchAbsent lookedUp absent transferred =>
          have present := locals.present active rfl lookedUp
          simp [present] at absent
  | ret | primitive | branch | call | tailCall => cases shape

theorem simulates_branch {context constructors entries plans parameters rank}
    {definition : IxIR2.Function} {block pc : Nat} {scope : Scope} {body : IxIR2.Block}
    {source alternatives peel operand zeroTransfer zero succTransfer successor}
    (blockAt : definition.blocks[block]? = some body) (endAt : pc = body.instructions.size)
    (term : body.terminator = .switchValue source alternatives (some peel)) (scalar : scope.scalar source = .ok operand)
    (zeroSelected : TransferCode definition scope peel.zero none zeroTransfer)
    (succSelected : TransferCode definition scope peel.succ (some operand) succTransfer)
    (sameResult : zero.result = successor.result)
    (zeroCode : Simulates context constructors entries plans parameters rank definition peel.zero.target 0 zeroTransfer.scope zero)
    (succCode : Simulates context constructors entries plans parameters rank definition peel.succ.target 0 succTransfer.scope successor) :
    Simulates context constructors entries plans parameters rank definition block pc scope
      (.branch operand zeroTransfer zero succTransfer successor) := by
  intro layout offset frame store heapFuel values credits before exit final outside plan shape valid frames heap locals balanced budget successful
  cases plan with
  | branch entry zeroEdge succEdge actualOperand actualZeroTransfer zeroPlan actualSuccTransfer succPlan =>
      obtain ⟨operandEq, zeroTransferEq, zeroShape, succTransferEq, succShape⟩ := Tree.branch.inj shape
      subst actualOperand actualZeroTransfer actualSuccTransfer
      obtain ⟨output, head, suffix⟩ := successful.first
      have terminal := physical_terminator_case blockAt endAt term head
      have scalarAt := locals.scalar scalar
      have loadedLocals := locals.setReg .rax (HeapCopies.atomValue frame before operand)
      have loadedHeap : HeapAt context.schemas constructors offset store
          (activeReservations ⟨definition, block, pc, values, credits⟩ exit.stack) (load frame before operand).words := heap
      generalize stackEq : exit.stack = stack at terminal
      cases terminal with
      | switchCtor resolved => cases Except.ok.inj (scalarAt.symm.trans resolved)
      | switchNatZero resolved transferred =>
          subst stack
          have number := Except.ok.inj (scalarAt.symm.trans resolved)
          simp only [PhysicalScalar.rval, IxIR1.RVal.lit.injEq, IxIR0.Literal.nat.injEq] at number
          have test : HeapCopies.atomValue frame before operand = 0 := UInt64.toNat_inj.mp number
          obtain ⟨definitionEq, blockEq, pcEq, nextLocals⟩ := zeroSelected.related transferred loadedLocals .nil valid.1
          have nextHeap := (loadedHeap.copies frames.separate valid.1).reservations_perm
            (transferred.reservations.append_right (suspendedReservations exit.stack))
          have nextBalance : Balance store zeroTransfer.scope.owners outside := by rw [zeroSelected.owners]; exact balanced
          have nextBudget : store.heap.nodes.size - offset + zero.allocations (entries.map (·.allocations)) ≤ capacity := by
            simp only [Tree.allocations] at budget; omega
          obtain ⟨tail⟩ := zeroCode.atFrame zeroShape definitionEq blockEq pcEq valid.2.2.1 frames nextHeap nextLocals nextBalance nextBudget suffix
          refine ⟨tail.prepend 1 (.cons rfl head (.refl _)) (.zero test tail.native) rfl ?_ ?_ (.refl store 1)⟩
          · have controlBound := tail.controls
            simp only [HeapTarget.Plan.tree, Tree.controls]
            omega
          · have growth := tail.growth
            simp only [HeapTarget.Plan.tree, Tree.allocations]
            omega
      | @switchNatSucc stack scrutinee alternatives peel predecessor target resolved transferred =>
          subst stack
          have number := Except.ok.inj (scalarAt.symm.trans resolved)
          simp only [PhysicalScalar.rval, IxIR1.RVal.lit.injEq, IxIR0.Literal.nat.injEq] at number
          have test : HeapCopies.atomValue frame before operand ≠ 0 := by
            intro zero
            rw [zero] at number
            simp at number
          have predecessorAt : (HeapCopies.atomValue frame before operand - 1).toNat = predecessor := by
            rw [ExactNat.predecessor_exact test, number]
            omega
          have implicitVector : ValueVector layout offset (store.heap.nodes.size - offset) (implicitKinds (some operand))
              #[IxIR1.RVal.lit (.nat predecessor)].toList (implicitWords frame (load frame before operand) (some operand)) := by
            apply ValueVector.cons (word := HeapCopies.atomValue frame before operand - 1) _ .nil
            simpa only [predecessorAt] using ValueAt.scalar (layout := layout) (offset := offset)
              (used := store.heap.nodes.size - offset) (HeapCopies.atomValue frame before operand - 1)
          obtain ⟨definitionEq, blockEq, pcEq, nextLocals⟩ := succSelected.related transferred loadedLocals implicitVector valid.2.1
          have nextHeap := (loadedHeap.copies frames.separate valid.2.1).reservations_perm
            (transferred.reservations.append_right (suspendedReservations exit.stack))
          have nextBalance : Balance store succTransfer.scope.owners outside := by rw [succSelected.owners]; exact balanced
          have nextBudget : store.heap.nodes.size - offset + successor.allocations (entries.map (·.allocations)) ≤ capacity := by
            simp only [Tree.allocations] at budget; omega
          obtain ⟨tail⟩ := succCode.atFrame succShape definitionEq blockEq pcEq valid.2.2.2 frames nextHeap nextLocals nextBalance nextBudget suffix
          refine ⟨tail.prepend 1 (.cons rfl head (.refl _)) (.successor test tail.native) ?_ ?_ ?_ (.refl store 1)⟩
          · simpa only [HeapTarget.Plan.tree, Tree.result, zeroShape, succShape] using sameResult
          · have controlBound := tail.controls
            simp only [HeapTarget.Plan.tree, Tree.controls]
            omega
          · have growth := tail.growth
            simp only [HeapTarget.Plan.tree, Tree.allocations]
            omega
  | ret | primitive | jump | call | tailCall => cases shape

end Compilatrix.X86.PhysicalHeap
