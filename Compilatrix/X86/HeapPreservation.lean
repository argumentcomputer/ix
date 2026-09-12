import Compilatrix.X86.HeapPrimitiveTrace

namespace Compilatrix.X86.HeapPrimitives
open WordRegion PhysicalHeap HeapArena HeapMacros

theorem write_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (slot : Nat) (word : Word) (below : slot < frame.top - 1) :
    Scalar.Preserves frame 0 state (state.setWord slot word) := by
  refine ⟨Scalar.Stable.setWord _ _ _, fun index above => Words.set_other _ _ _ _ (by omega)⟩

theorem local_below {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (slot : Nat) :
    frame.localIndex slot < frame.top - 1 := by
  have enough := frame.enough
  simp only [Scalar.Frame.localIndex]
  omega

theorem save_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State) (destination : Nat) :
    Scalar.Preserves frame 0 state (save frame state destination) :=
  write_preserves frame state _ _ (local_below frame destination)

theorem counter_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (field : Nat) (change : Word → Word) (below : field < frame.top - 1) :
    Scalar.Preserves frame 0 state (counter state field change) :=
  (Scalar.Preserves.setReg frame 0 state .rcx _ (by simp)).trans (write_preserves frame _ field _ below)

theorem tag_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index : Nat) (word : Word) (below : cellSlot index 0 < frame.top - 1) :
    Scalar.Preserves frame 0 state (tag state index word) :=
  (Scalar.Preserves.setReg frame 0 state .rcx _ (by simp)).trans (write_preserves frame _ _ _ below)

theorem writeCell_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index : Nat) (ctor : Constructor) (below : ∀ field < cellWords, cellSlot index field < frame.top - 1) :
    Scalar.Preserves frame 0 state (writeCell state index ctor) :=
  ((((tag_preserves frame state index ctor.tag (below 0 (by decide))).trans
    (write_preserves frame _ _ _ (below 1 (by decide)))).trans
    (write_preserves frame _ _ _ (below 2 (by decide)))).trans
    (Scalar.Preserves.setReg frame 0 _ .rcx _ (by simp))).trans
    (write_preserves frame _ _ _ (below 3 (by decide)))

theorem fields_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (arguments : Array Scalar.Atom) : Scalar.Preserves frame 0 state (fields frame state arguments) :=
  (Scalar.Preserves.setReg frame 0 state .r8 _ (by simp)).trans
    (Scalar.Preserves.setReg frame 0 _ .r9 _ (by simp))

theorem capture_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index field destination : Nat) : Scalar.Preserves frame 0 state (capture frame state index field destination) :=
  (Scalar.Preserves.setReg frame 0 state .rcx _ (by simp)).trans
    (write_preserves frame _ _ _ (local_below frame destination))

theorem captureFields_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (index count destination : Nat) : Scalar.Preserves frame 0 state (captureFields frame state index count destination) := by
  cases count with
  | zero => exact .refl _ _ _
  | succ count => cases count with
    | zero => exact capture_preserves _ _ _ _ _
    | succ count => exact (capture_preserves _ _ _ _ _).trans (capture_preserves _ _ _ _ _)

theorem sharedReset_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (world : Ixon.Owned) (below : 7 < frame.top - 1) : Scalar.Preserves frame 0 state (sharedReset world state) := by
  unfold sharedReset
  split
  · exact (counter_preserves frame _ 6 (· + 1) (by omega)).trans (counter_preserves frame _ 7 (· + 1) below)
  · exact .refl _ _ _

theorem sharedRelease_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (world : Ixon.Owned) (below : 5 < frame.top - 1) : Scalar.Preserves frame 0 state (sharedRelease world state) := by
  unfold sharedRelease
  split
  · exact counter_preserves frame _ 5 (· + 1) below
  · exact .refl _ _ _

/-- Primitive stores touch the arena and the current activation's locals.
The saved base pointer, return token, and all suspended caller slots survive. -/
theorem Executes.preserves {layout frame operation before after}
    (executed : Executes layout frame operation before after) (separate : heapWords ≤ frame.stackIndex) :
    Scalar.Preserves frame 0 before after := by
  have heapBelow {slot : Nat} (bound : slot < heapWords) : slot < frame.top - 1 := by
    simp only [Scalar.Frame.stackIndex] at separate
    have positive : 0 < heapWords := by decide
    omega
  have headerBelow {field : Nat} (bound : field < headerWords) : field < frame.top - 1 :=
    heapBelow (by simp only [heapWords, headerWords, cellWords, capacity] at *; omega)
  have cellBelow {index : Nat} (allocated : index < capacity) :
      ∀ field < cellWords, cellSlot index field < frame.top - 1 :=
    fun _ fieldBound => heapBelow (cellSlot_bound allocated fieldBound)
  cases executed with
  | nop => exact .refl _ _ _
  | move state destination source =>
      exact (Scalar.Preserves.setReg frame 0 before .rax _ (by simp)).trans (save_preserves frame _ destination)
  | alloc state index world ctor arguments destination allocated cursor =>
      unfold allocate
      exact (((((fields_preserves frame before arguments).trans
        (Scalar.Preserves.setReg frame 0 _ .rax _ (by simp))).trans
        (writeCell_preserves frame _ index ctor (cellBelow allocated))).trans
        (counter_preserves frame _ 0 (· + 32) (headerBelow (by decide)))).trans
        (counter_preserves frame _ 2 (· + 1) (headerBelow (by decide)))).trans (save_preserves frame _ destination)
  | fetch state index source field destination allocated pointer =>
      unfold HeapPrimitives.fetch load
      exact ((Scalar.Preserves.setReg frame 0 before .rax _ (by simp)).trans
        (Scalar.Preserves.setReg frame 0 _ .rax _ (by simp))).trans (save_preserves frame _ destination)
  | reserve state index world ctor source destination credit allocated pointer =>
      unfold HeapPrimitives.reserve load
      exact (((((Scalar.Preserves.setReg frame 0 before .rax _ (by simp)).trans
        (captureFields_preserves frame _ index ctor.schema.fields.size destination)).trans
        (tag_preserves frame _ index 1 (cellBelow allocated 0 (by decide)))).trans
        (counter_preserves frame _ 9 (· + 1) (headerBelow (by decide)))).trans
        (sharedReset_preserves frame _ world (headerBelow (by decide)))).trans (save_preserves frame _ (creditBase + credit))
  | reuse state index world ctor credit arguments destination allocated pointer =>
      unfold HeapPrimitives.reuse creditState
      exact ((((((fields_preserves frame before arguments).trans
        (Scalar.Preserves.setReg frame 0 _ .rax _ (by simp))).trans
        (writeCell_preserves frame _ index ctor (cellBelow allocated))).trans
        (counter_preserves frame _ 4 (· + 1) (headerBelow (by decide)))).trans
        (counter_preserves frame _ 8 (· + UInt64.ofNat ctor.schema.fields.size) (headerBelow (by decide)))).trans
        (counter_preserves frame _ 9 (· - 1) (headerBelow (by decide)))).trans (save_preserves frame _ destination)
  | release state index world source allocated pointer =>
      unfold HeapPrimitives.release load
      exact (((Scalar.Preserves.setReg frame 0 before .rax _ (by simp)).trans
        (tag_preserves frame _ index 0 (cellBelow allocated 0 (by decide)))).trans
        (counter_preserves frame _ 3 (· + 1) (headerBelow (by decide)))).trans
        (sharedRelease_preserves frame _ world (headerBelow (by decide)))
  | discard state index credit allocated pointer =>
      unfold HeapPrimitives.discard creditState
      exact (((Scalar.Preserves.setReg frame 0 before .rax _ (by simp)).trans
        (tag_preserves frame _ index 0 (cellBelow allocated 0 (by decide)))).trans
        (counter_preserves frame _ 3 (· + 1) (headerBelow (by decide)))).trans
        (counter_preserves frame _ 9 (· - 1) (headerBelow (by decide)))

end Compilatrix.X86.HeapPrimitives
