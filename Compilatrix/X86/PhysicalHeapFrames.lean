import Compilatrix.X86.PhysicalHeapCopies

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open IxIR2.Eval (Store RVal)

def FrameRoom {layout : HeapArena.Layout} (frame : Scalar.Frame layout.region) (rank : Nat) : Prop :=
  heapWords + Scalar.frameStride * (rank + 1) - 1 ≤ frame.top

theorem FrameRoom.separate {layout : HeapArena.Layout} {frame : Scalar.Frame layout.region} {rank : Nat}
    (room : FrameRoom frame rank) : heapWords ≤ frame.stackIndex := by
  simp only [FrameRoom, Scalar.Frame.stackIndex, Scalar.frameStride, heapWords, headerWords, cellWords, capacity] at *
  omega

theorem FrameRoom.enough {layout : HeapArena.Layout} {frame : Scalar.Frame layout.region} {rank : Nat}
    (room : FrameRoom frame rank) : 67 ≤ frame.top := by
  simp only [FrameRoom, Scalar.frameStride, heapWords, headerWords, cellWords, capacity] at room
  omega

theorem FrameRoom.child {layout : HeapArena.Layout} {frame : Scalar.Frame layout.region} {rank earlier : Nat}
    (room : FrameRoom frame rank) (before : earlier < rank) : FrameRoom (frame.child room.enough) earlier := by
  have parent := room
  change heapWords + Scalar.frameStride * (rank + 1) - 1 ≤ frame.top at parent
  simp only [FrameRoom, Scalar.Frame.child, Scalar.frameStride, heapWords, headerWords, cellWords, capacity] at parent ⊢
  omega

theorem HeapAt.enter {schemas constructors offset store reserved state} {layout : HeapArena.Layout}
    (heap : HeapAt schemas constructors offset store reserved state.words)
    (frame : Scalar.Frame layout.region) (separate : heapWords ≤ frame.stackIndex) (parameters : Nat) :
    HeapAt schemas constructors offset store reserved (Scalar.enterState frame parameters state).words := by
  have framed : HeapAt schemas constructors offset store reserved (Scalar.frameState frame state).words := by
    apply heap.words
    intro index bound
    have above : heapWords ≤ frame.baseIndex := by
      simp only [Scalar.Frame.baseIndex, Scalar.Frame.stackIndex] at *; omega
    simp [Scalar.frameState, Scalar.pushState, show index ≠ frame.baseIndex by omega]
  unfold Scalar.enterState
  split
  · split
    · exact (framed.setStack frame separate (by decide) _).setStack frame separate (by decide) _
    · exact framed.setStack frame separate (by decide) _
  · split
    · exact framed.setStack frame separate (by decide) _
    · exact framed

theorem HeapAt.call {schemas constructors offset store reserved state} {layout : HeapArena.Layout}
    (heap : HeapAt schemas constructors offset store reserved state.words)
    (frame : Scalar.Frame layout.region) (arguments : Array Scalar.Atom) (enough : 67 ≤ frame.top)
    (separate : heapWords ≤ (frame.child enough).stackIndex) (entry : BlockId) :
    HeapAt schemas constructors offset store reserved (HeapRuns.called frame state arguments enough entry).words := by
  apply heap.words
  intro index bound
  have above : heapWords ≤ (frame.child enough).top := by
    simp only [Scalar.Frame.stackIndex] at separate; omega
  simp [HeapRuns.called, HeapRuns.ready, Scalar.argumentsState, State.call, show index ≠ (frame.child enough).top by omega]

theorem ScopeAt.enter {layout offset used frame state parameters values words}
    (vector : ValueVector layout offset used parameters.toList values.toList words.toList)
    (arguments : Scalar.ArgumentsAt words state) :
    ScopeAt layout offset used frame (Scope.initial parameters) values #[] (Scalar.enterState frame parameters.size state) := by
  have arity : parameters.size = words.size := by have := vector.lengths; simp only [Array.length_toList] at this; omega
  have stored := Scalar.enter_values frame state words arguments
  have bounded : (Scope.mk (parameters.toList.map some).toArray #[]).bounded = true := by
    simp only [Scope.bounded, List.size_toArray, List.length_map, Array.length_toList, Array.size_empty, List.length_nil, maxValues, maxCredits,
      decide_eq_true_eq, Bool.and_eq_true]
    have := arguments.1
    omega
  have result := ScopeAt.ofVectors vector (.nil : CreditVector layout offset used [] [] []) bounded
    (fun index word found => by
      have found : words[index]? = some word := by simpa using found
      obtain ⟨bound, equal⟩ := Array.getElem?_eq_some_iff.mp found
      exact (stored.2 index bound).trans equal)
    (fun _ _ impossible => by simp at impossible)
  simpa only [Scope.initial, ← List.map_toArray, Array.toArray_toList, Array.map_empty, arity] using result

theorem called_arguments {layout : HeapArena.Layout} (frame : Scalar.Frame layout.region) (state : State)
    (arguments : Array Scalar.Atom) (enough : 67 ≤ frame.top) (entry : BlockId) (small : arguments.size ≤ 2) :
    Scalar.ArgumentsAt (HeapRuns.argumentValues frame state arguments) (HeapRuns.called frame state arguments enough entry) := by
  have ready := Scalar.arguments_ready state (HeapRuns.argumentValues frame state arguments) (by simpa [HeapRuns.argumentValues] using small)
  refine ⟨ready.1, ?_⟩
  intro index bound
  simpa [HeapRuns.called, HeapRuns.ready, State.call] using ready.2 index bound

theorem ScopeAt.preserved {layout offset used frame scope values credits before after}
    (locals : ScopeAt layout offset used frame scope values credits before)
    (preserved : Scalar.Preserves frame Scalar.maxLocals before after) :
    ScopeAt layout offset used frame scope values credits after := by
  apply locals.words
  · intro index kind active
    have bound := locals.valueBound
    have slot := (Array.getElem?_eq_some_iff.mp active).1
    apply preserved.2
    simp only [Scalar.Frame.localIndex, Scalar.maxLocals, maxValues] at *; omega
  · intro index id active
    have bound := locals.creditBound
    have slot := (Array.getElem?_eq_some_iff.mp active).1
    apply preserved.2
    simp only [Scalar.Frame.localIndex, Scalar.maxLocals, creditBase, maxCredits] at *; omega

theorem HeapAt.resumed {schemas constructors offset store reserved before after arguments}
    {layout : HeapArena.Layout} (frame : Scalar.Frame layout.region) {enough : 67 ≤ frame.top}
    (heap : HeapAt schemas constructors offset store reserved after.words) :
    HeapAt schemas constructors offset store reserved (HeapRuns.resumed frame before after arguments enough).words := heap

theorem ValueAt.resumed {layout offset used kind value before after arguments}
    (frame : Scalar.Frame layout.region) {enough : 67 ≤ frame.top}
    (represented : ValueAt layout offset used kind value (after.registers .rax)) :
    ValueAt layout offset used kind value ((HeapRuns.resumed frame before after arguments enough).registers .rax) := by
  simpa [HeapRuns.resumed, HeapRuns.finished, Scalar.leaveState] using represented

end Compilatrix.X86.PhysicalHeap
