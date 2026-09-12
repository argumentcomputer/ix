import Compilatrix.X86.PhysicalHeapStatistics

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapMacros HeapPrimitives
open IxIR2.Eval (Store RVal Credit Frame Continuation Machine)

theorem ValueAt.nonNode {layout offset used kind value word}
    (represented : ValueAt layout offset used kind value word) (scalar : kind ≠ .node) :
    IxIR2.Eval.RVal.isScalar value = true := by
  cases represented <;> simp_all [IxIR2.Eval.RVal.isScalar]

theorem ScopeAt.resolved {layout offset used frame scope values credits state source kind operand value}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.peek source = .ok (kind, operand))
    (resolved : IxIR2.Eval.resolveAtom values source = .ok value) :
    ValueAt layout offset used kind value (HeapCopies.atomValue frame state operand) := by
  obtain ⟨actual, found, represented⟩ := related.peek selected
  cases Except.ok.inj (found.symm.trans resolved)
  exact represented

theorem ScopeAt.creditPresent {layout offset used frame scope values credits state index id consumed credit}
    (related : ScopeAt layout offset used frame scope values credits state)
    (selected : scope.takeCredit index = .ok (id, consumed))
    (found : credits[index]? = some (some credit)) :
    ∃ location, credit.presence = .present (some location) := by
  obtain ⟨actual, actualAt, ⟨represented⟩, _⟩ := related.takeCredit selected
  cases Option.some.inj (Option.some.inj (actualAt.symm.trans found))
  exact ⟨represented.location, represented.presence⟩

theorem primitive_retain {schemas constructors layout offset store reserved frame scope nextScope values credits state source kind operand value}
    (heap : HeapAt schemas constructors offset store reserved state.words)
    (locals : ScopeAt layout offset (store.heap.nodes.size - offset) frame scope values credits state)
    (separate : heapWords ≤ frame.stackIndex)
    (peeked : scope.peek source = .ok (kind, operand))
    (resolved : IxIR2.Eval.resolveAtom values source = .ok value)
    (pushed : scope.pushValue kind = .ok nextScope) :
    HeapAt schemas constructors offset store reserved (save frame (load frame state operand) scope.values.size).words ∧
      ScopeAt layout offset (store.heap.nodes.size - offset) frame nextScope (values.push value) credits
        (save frame (load frame state operand) scope.values.size) := by
  have represented := locals.resolved peeked resolved
  have enough := pushValue_room pushed
  have bound : scope.values.size < Scalar.maxLocals := by simp only [maxValues, Scalar.maxLocals] at *; omega
  exact ⟨heap.setStack frame separate bound _, (locals.setReg .rax _).saveValue pushed represented⟩

/-- One actual physical instruction produces the selected finite-word
operation, advances the same CFG frame, and preserves both heap and slots. -/
structure PrimitiveOutcome (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (layout : HeapArena.Layout) (offset : Nat) (store : Store)
    (nativeFrame : Scalar.Frame layout.region) (raw : Frame) (stack : List Continuation)
    (operation : Primitive) (nextScope : Scope) (before : State) (output : IxIR2.Eval.Machine) where
  state : State
  frame : Frame
  running : output.control = .running frame stack
  definition : frame.definition = raw.definition
  block : frame.block = raw.block
  pc : frame.pc = raw.pc + 1
  executed : Executes layout nativeFrame operation before state
  heap : HeapAt schemas constructors offset output.store (activeReservations frame stack) state.words
  locals : ScopeAt layout offset (output.store.heap.nodes.size - offset) nativeFrame nextScope frame.values frame.credits state
  growth : output.store.heap.nodes.size = store.heap.nodes.size + operation.allocations
  statistics : Statistics store output.store operation

theorem PrimitiveCode.executes {context : IxIR2.Eval.Context} {constructors layout offset store heapFuel nativeFrame raw stack scope instruction operation nextScope before output}
    (code : PrimitiveCode context.schemas constructors scope instruction operation nextScope)
    (transfer : IxIR2.Eval.InstructionTransferCase context .physical store heapFuel raw stack instruction output)
    (heap : HeapAt context.schemas constructors offset store (activeReservations raw stack) before.words)
    (locals : ScopeAt layout offset (store.heap.nodes.size - offset) nativeFrame scope raw.values raw.credits before)
    (separate : heapWords ≤ nativeFrame.stackIndex)
    (room : store.heap.nodes.size - offset + operation.allocations ≤ capacity) :
    Nonempty (PrimitiveOutcome context.schemas constructors layout offset store nativeFrame raw stack operation nextScope before output) := by
  cases code with
  | move taken pushed =>
      cases transfer with
      | move resolved =>
          obtain ⟨value, found, nextHeap, nextLocals⟩ := primitive_move heap locals separate taken pushed
          cases Except.ok.inj (found.symm.trans resolved)
          exact ⟨⟨_, _, rfl, rfl, rfl, rfl, .move _ _ _, nextHeap, nextLocals, rfl, statistics_move _ _ _⟩⟩
  | retain peeked scalar pushed =>
      cases transfer with
      | retainShared resolved retained =>
          have equal := scalar_retain ((locals.resolved peeked resolved).nonNode scalar) retained
          subst_vars
          obtain ⟨nextHeap, nextLocals⟩ := primitive_retain heap locals separate peeked resolved pushed
          exact ⟨⟨_, _, rfl, rfl, rfl, rfl, .move _ _ _, nextHeap, nextLocals, rfl, statistics_move _ _ _⟩⟩
  | @release source kind operand next taken =>
      cases transfer with
      | releaseShared resolved released =>
          obtain ⟨peeked, remaining⟩ := locals.take taken
          have represented := locals.resolved peeked resolved
          by_cases node : kind = .node
          · subst kind
            obtain ⟨location, valueEq, _, _, _⟩ := represented.node_value
            subst_vars
            have outputEq := heap.release_node released
            subst_vars
            obtain ⟨executed, nextHeap, nextLocals⟩ := primitive_free (world := .shared) heap locals separate taken resolved
            exact ⟨⟨_, _, rfl, rfl, rfl, rfl, executed, nextHeap, nextLocals, by simp [releaseStore, Store.kill, IxIR1.Store.kill, Store.rcTick, IxIR1.Store.rcTick, Primitive.allocations], statistics_release _ .shared _ _⟩⟩
          · have equal := scalar_release (represented.nonNode node) released
            subst_vars
            simp only [show (kind == .node) = false from beq_eq_false_iff_ne.mpr node, ↓reduceIte]
            exact ⟨⟨_, _, rfl, rfl, rfl, rfl, .nop _, heap, remaining, rfl, statistics_nop _⟩⟩
  | @drop source kind operand next taken =>
      cases transfer with
      | dropUnique resolved dropped =>
          obtain ⟨peeked, remaining⟩ := locals.take taken
          have represented := locals.resolved peeked resolved
          by_cases node : kind = .node
          · subst kind
            obtain ⟨location, valueEq, _, _, _⟩ := represented.node_value
            subst_vars
            have outputEq := heap.drop_node dropped
            subst_vars
            obtain ⟨executed, nextHeap, nextLocals⟩ := primitive_free (world := .unique) heap locals separate taken resolved
            exact ⟨⟨_, _, rfl, rfl, rfl, rfl, executed, nextHeap, nextLocals, by simp [Store.kill, IxIR1.Store.kill, Primitive.allocations], statistics_release _ .unique _ _⟩⟩
          · have equal := scalar_drop (represented.nonNode node) dropped
            subst_vars
            simp only [show (kind == .node) = false from beq_eq_false_iff_ne.mpr node, ↓reduceIte]
            exact ⟨⟨_, _, rfl, rfl, rfl, rfl, .nop _, heap, remaining, rfl, statistics_nop _⟩⟩
  | @alloc world cid arguments ctor operands next selected arity fields pushed =>
      obtain ⟨cidEq, accepted⟩ := constructor_sound selected
      cases transfer with
      | alloc schemaAt resolved fieldWorlds =>
          have actual := locals.scalars (by have := accepted.small; omega) fields
          cases Except.ok.inj (resolved.symm.trans actual.2)
          have room' : store.heap.nodes.size - offset < capacity := by simp only [Primitive.allocations] at room; omega
          obtain ⟨nextHeap, nextLocals⟩ := primitive_alloc heap locals separate accepted (actual.1.trans arity) pushed room'
          rw [cidEq] at nextHeap nextLocals
          exact ⟨⟨_, _, rfl, rfl, rfl, rfl, .alloc _ _ _ _ _ _ room' heap.cursor, nextHeap, nextLocals,
            by simp [Store.allocNode_heap, IxIR1.Store.allocNode, Primitive.allocations], statistics_alloc _ _ _ _ _ _ _⟩⟩
  | @reuse index world cid arguments ctor operands consumed next selected arity fields taken pushed =>
      obtain ⟨cidEq, accepted⟩ := constructor_sound selected
      cases transfer with
      | allocWithAbsent schemaAt resolved fieldWorlds physicalTake layoutEq absent =>
          obtain ⟨location, present⟩ := locals.creditPresent taken physicalTake.target_eq.2
          simp [present] at absent
      | allocWithLogical mode => cases mode
      | @allocWithPhysical creditId credit world cid arguments schema values target location outStore mode schemaAt resolved fieldWorlds physicalTake layoutEq present reused =>
          have schemaEq : schema = ctor.schema := Option.some.inj (schemaAt.symm.trans (by simpa only [cidEq] using accepted.schema))
          subst schema
          have actual := locals.scalars (by have := accepted.small; omega) fields
          cases Except.ok.inj (resolved.symm.trans actual.2)
          have preserved := reservation_take_kept physicalTake present stack
          obtain ⟨targetEq, found⟩ := physicalTake.target_eq
          subst target
          have reused' := reused
          rw [← cidEq] at reused'
          obtain ⟨executed, nextHeap, nextLocals⟩ := primitive_reuse heap locals separate accepted (actual.1.trans arity)
            taken pushed found present reused' preserved.1 preserved.2
          exact ⟨⟨_, _, rfl, rfl, rfl, rfl, executed, nextHeap, nextLocals, by simp [(reuse_parts reused').2.1, Primitive.allocations], statistics_reuse reused' _ _ _⟩⟩
  | @takeUnique source cid ctor operand consumed fieldScope next selected taken fieldsPushed creditPushed =>
      obtain ⟨cidEq, accepted⟩ := constructor_sound selected
      cases transfer with
      | takeUniqueLogical mode => cases mode
      | @takeUniquePhysical target cid schema location box fields mode schemaAt resolved view unitRC =>
          have schemaEq : schema = ctor.schema := Option.some.inj (schemaAt.symm.trans (by simpa only [cidEq] using accepted.schema))
          subst schema
          have kept := reservation_push raw stack ctor.schema.layout location
          have view' := view
          rw [← cidEq] at view'
          obtain ⟨executed, nextHeap, nextLocals⟩ := primitive_reserve heap locals separate accepted taken fieldsPushed creditPushed
            resolved view' (fun _ _ member => kept.1 _ member) kept.2.1 kept.2.2
          exact ⟨⟨_, _, rfl, rfl, rfl, rfl, executed, nextHeap, nextLocals, by simp [Store.reserve, Primitive.allocations], statistics_reserve _ .unique _ _ _ _ _⟩⟩
  | @resetShared source cid ctor operand consumed fieldScope next selected taken fieldsPushed creditPushed =>
      obtain ⟨cidEq, accepted⟩ := constructor_sound selected
      cases transfer with
      | resetSharedLogicalHot mode => cases mode
      | @resetSharedPhysicalHot target cid schema location box fields mode schemaAt resolved view unitRC =>
          have schemaEq : schema = ctor.schema := Option.some.inj (schemaAt.symm.trans (by simpa only [cidEq] using accepted.schema))
          subst schema
          have kept := reservation_push raw stack ctor.schema.layout location
          have view' := view
          rw [← cidEq] at view'
          obtain ⟨executed, nextHeap, nextLocals⟩ := primitive_reserve heap locals separate accepted taken fieldsPushed creditPushed
            resolved view' (fun _ _ member => kept.1 _ member) kept.2.1 kept.2.2
          exact ⟨⟨_, _, rfl, rfl, rfl, rfl, executed, nextHeap, nextLocals, by simp [Store.reserve, Store.tickResetAttempt, Store.tickHotReset, Primitive.allocations], statistics_reserve _ .shared _ _ _ _ _⟩⟩
      | resetSharedCold schemaAt resolved view shared retained =>
          rcases (heap.live _ _ view.parts.1).2 with ⟨content⟩
          have := content.unique
          omega
  | discard taken =>
      cases transfer with
      | discardAbsent physicalTake absent =>
          obtain ⟨location, present⟩ := locals.creditPresent taken physicalTake.target_eq.2
          simp [present] at absent
      | discardLogical mode => cases mode
      | discardPhysical mode physicalTake present released =>
          have preserved := reservation_take_kept physicalTake present stack
          obtain ⟨targetEq, found⟩ := physicalTake.target_eq
          subst_vars
          obtain ⟨executed, nextHeap, nextLocals⟩ := primitive_discard heap locals separate taken found present released preserved.1 preserved.2
          exact ⟨⟨_, _, rfl, rfl, rfl, rfl, executed, nextHeap, nextLocals, by simp [releaseReservation_kill released, Store.kill, IxIR1.Store.kill, Primitive.allocations], statistics_discard _ released⟩⟩
  | free selected taken =>
      cases transfer with
      | freeUnique resolved view scalarFields =>
          obtain ⟨executed, nextHeap, nextLocals⟩ := primitive_free (world := .unique) heap locals separate taken resolved
          exact ⟨⟨_, _, rfl, rfl, rfl, rfl, executed, nextHeap, nextLocals, by simp [Store.kill, IxIR1.Store.kill, Primitive.allocations], statistics_release _ .unique _ _⟩⟩
  | fetch peeked small pushed =>
      cases transfer with
      | fetch resolved found node fieldAt =>
          obtain ⟨executed, nextHeap, nextLocals⟩ := primitive_fetch heap locals separate peeked resolved found node fieldAt small pushed
          exact ⟨⟨_, _, rfl, rfl, rfl, rfl, executed, nextHeap, nextLocals, rfl, statistics_fetch _ _ _ _⟩⟩

end Compilatrix.X86.PhysicalHeap
