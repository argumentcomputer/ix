import Compilatrix.X86.PhysicalHeapVectors

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena HeapCopies
open IxIR2.Eval (Frame)

theorem copy_execute_member {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    {transfer : Transfer} (valid : HeapTarget.transferValid transfer = true) {copy : Copy}
    (member : copy ∈ transfer.copies.toList) :
    (execute frame state transfer).words (frame.localIndex copy.destination) = value frame state copy.source := by
  obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
  have found : index < transfer.copies.size := by simpa using bound
  have same : transfer.copies[index] = copy := by simpa only [Array.getElem_toList] using equal
  simpa only [same] using execute_at frame state valid index found

theorem valueCopies_member {operands : List Scalar.Atom} {index : Nat} {operand : Scalar.Atom}
    (found : operands[index]? = some operand) (start : Nat) :
    ⟨.atom operand, start + index⟩ ∈ valueCopies start operands := by
  induction operands generalizing start index with
  | nil => simp at found
  | cons head rest ih =>
      cases index with
      | zero => simp_all [valueCopies]
      | succ index =>
          have tail := ih (by simpa using found) (start + 1)
          exact List.mem_cons_of_mem _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail)

theorem creditCopies_member {sources : List IxIR2.CreditId} {index : Nat} {source : IxIR2.CreditId}
    (found : sources[index]? = some source) (start : Nat) :
    ⟨.atom (.var (creditBase + source)), creditBase + start + index⟩ ∈ creditCopies start sources := by
  induction sources generalizing start index with
  | nil => simp at found
  | cons head rest ih =>
      cases index with
      | zero => simp_all [creditCopies]
      | succ index =>
          have tail := ih (by simpa using found) (start + 1)
          exact List.mem_cons_of_mem _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail)

theorem HeapAt.stage {schemas constructors offset store reserved} {layout : HeapArena.Layout} (frame : Scalar.Frame layout.region)
    (separate : heapWords ≤ frame.stackIndex) (original : State) (copies : List Copy) :
    ∀ start state, start + copies.length ≤ maxEdge → HeapAt schemas constructors offset store reserved state.words →
      HeapAt schemas constructors offset store reserved (stage frame original start copies state).words := by
  induction copies with
  | nil => intro start state _ related; exact related
  | cons copy copies ih =>
      intro start state bound related
      have slot : scratchBase + start < Scalar.maxLocals := by
        simp only [maxEdge, scratchBase, Scalar.maxLocals, List.length_cons] at *; omega
      exact ih (start + 1) (put frame state (scratchBase + start) (value frame original copy.source))
        (by simp only [List.length_cons] at bound; omega) (related.setStack frame separate slot _)

theorem HeapAt.commit {schemas constructors offset store reserved} {layout : HeapArena.Layout} (frame : Scalar.Frame layout.region)
    (separate : heapWords ≤ frame.stackIndex) (staged : State) (copies : List Copy) :
    ∀ start state, (∀ copy ∈ copies, copy.destination < Scalar.maxLocals) → HeapAt schemas constructors offset store reserved state.words →
      HeapAt schemas constructors offset store reserved (commit frame staged start copies state).words := by
  induction copies with
  | nil => intro start state _ related; exact related
  | cons copy copies ih =>
      intro start state bound related
      exact ih (start + 1) (put frame state copy.destination (staged.words (frame.localIndex (scratchBase + start))))
        (fun item member => bound item (by simp [member])) (related.setStack frame separate (bound copy (by simp)) _)

theorem HeapAt.copies {schemas constructors offset store reserved state transfer} {layout : HeapArena.Layout} {frame : Scalar.Frame layout.region}
    (heap : HeapAt schemas constructors offset store reserved state.words)
    (separate : heapWords ≤ frame.stackIndex) (valid : HeapTarget.transferValid transfer = true) :
    HeapAt schemas constructors offset store reserved (execute (layout := layout.region) frame state transfer).words := by
  simp only [HeapTarget.transferValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  have staged := HeapAt.stage frame separate state transfer.copies.toList 0 state (by simpa using valid.1.1) heap
  apply HeapAt.commit frame separate _ _ 0 _ _ staged
  intro copy member
  have accepted := Array.all_eq_true_iff_forall_mem.mp valid.1.2 copy (by simpa using member)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
  have small : copy.destination < scratchBase := accepted.2
  simp only [scratchBase, Scalar.maxLocals] at *; omega

def implicitWords {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (implicitValue : Option Scalar.Atom) : List Word := implicitValue.toList.map (fun operand => atomValue frame state operand - 1)

theorem edge_value_words {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (implicitValue : Option Scalar.Atom) (kinds : List Kind) (operands : List Scalar.Atom)
    (sources : List IxIR2.CreditId) (ids : List IxIR2.LayoutId)
    (valid : HeapTarget.transferValid (edgeTransfer implicitValue kinds operands sources ids) = true)
    {index : Nat} {word : Word}
    (found : (implicitWords frame state implicitValue ++ operands.map (atomValue frame state))[index]? = some word) :
    (execute frame state (edgeTransfer implicitValue kinds operands sources ids)).words (frame.localIndex index) = word := by
  cases implicitValue with
  | none =>
      simp only [implicitWords, Option.toList_none, List.map_nil, List.nil_append] at found
      cases atOperand : operands[index]? with
      | none => simp [atOperand] at found
      | some operand =>
          simp only [List.getElem?_map, atOperand, Option.map_some, Option.some.injEq] at found
          subst word
          apply copy_execute_member frame state valid (copy := ⟨.atom operand, index⟩)
          simp only [edgeTransfer, implicitCopies, implicitKinds, List.length_nil, List.nil_append, List.toList_toArray]
          exact List.mem_append_left _ (by simpa using valueCopies_member atOperand 0)
  | some predecessor =>
      cases index with
      | zero =>
          simp only [implicitWords, Option.toList_some, List.map_cons, List.map_nil, List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at found
          subst word
          apply copy_execute_member frame state valid (copy := ⟨.predecessor predecessor, 0⟩)
          simp [edgeTransfer, implicitCopies]
      | succ index =>
          simp only [implicitWords, Option.toList_some, List.map_cons, List.map_nil, List.cons_append, List.getElem?_cons_succ, List.nil_append] at found
          cases atOperand : operands[index]? with
          | none => simp [atOperand] at found
          | some operand =>
              simp only [List.getElem?_map, atOperand, Option.map_some, Option.some.injEq] at found
              subst word
              apply copy_execute_member frame state valid (copy := ⟨.atom operand, index + 1⟩)
              simp only [edgeTransfer, implicitCopies, implicitKinds, List.length_cons, List.length_nil, Nat.zero_add,
                List.cons_append, List.nil_append, List.toList_toArray]
              exact List.mem_cons_of_mem _ (List.mem_append_left _ (by simpa [Nat.add_comm] using valueCopies_member atOperand 1))

theorem edge_credit_words {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (implicitValue : Option Scalar.Atom) (kinds : List Kind) (operands : List Scalar.Atom)
    (sources : List IxIR2.CreditId) (ids : List IxIR2.LayoutId)
    (valid : HeapTarget.transferValid (edgeTransfer implicitValue kinds operands sources ids) = true)
    {index : Nat} {word : Word}
    (found : (sources.map (fun source => state.words (frame.localIndex (creditBase + source))))[index]? = some word) :
    (execute frame state (edgeTransfer implicitValue kinds operands sources ids)).words (frame.localIndex (creditBase + index)) = word := by
  cases atSource : sources[index]? with
  | none => simp [atSource] at found
  | some source =>
      simp only [List.getElem?_map, atSource, Option.map_some, Option.some.injEq] at found
      subst word
      apply copy_execute_member frame state valid (copy := ⟨.atom (.var (creditBase + source)), creditBase + index⟩)
      simp only [edgeTransfer, List.toList_toArray]
      exact List.mem_append_right _ (by simpa using creditCopies_member atSource 0)

theorem TransferCode.related {definition scope edge implicitValue transfer layout offset used frame raw output state implicitValues}
    (selected : TransferCode definition scope edge implicitValue transfer)
    (transferred : IxIR2.Eval.EdgeTransfer raw edge implicitValues output)
    (locals : ScopeAt layout offset used frame scope raw.values raw.credits state)
    (implicitVector : ValueVector layout offset used (implicitKinds implicitValue) implicitValues.toList (implicitWords frame state implicitValue))
    (valid : HeapTarget.transferValid transfer = true) :
    output.definition = raw.definition ∧ output.block = edge.target ∧ output.pc = 0 ∧
      ScopeAt layout offset used frame transfer.scope output.values output.credits (execute frame state transfer) := by
  cases selected with
  | mk targetAt valueTake creditTake finished bounded =>
      obtain ⟨values, credits, after, block, resolved, taken, cleared, blockAt, valueArity, creditArity, targetEq⟩ := transferred.parts
      have shape := creditSequence_shape taken.sequence
      obtain ⟨valueVector, remaining⟩ := TakeValues.related valueTake (IxIR2.Lower.Sim.resolvedAtoms_of_resolveAtoms resolved) locals
      obtain ⟨creditVector, finalLocals⟩ := creditTake.related taken.sequence remaining
      subst output
      refine ⟨by rw [shape], rfl, rfl, ?_⟩
      have result := ScopeAt.ofVectors (implicitVector.append valueVector) creditVector bounded
        (fun index word found => edge_value_words frame state _ _ _ _ _ valid found)
        (fun index word found => edge_credit_words frame state _ _ _ _ _ valid found)
      simpa only [← List.append_toArray, Array.toArray_toList, ← List.map_toArray, edgeTransfer] using result

end Compilatrix.X86.PhysicalHeap
