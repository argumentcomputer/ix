import Compilatrix.X86.HeapRuns

namespace Compilatrix.X86.HeapRuns
open WordRegion PhysicalHeap HeapArena HeapPrimitives

def ReadableHeap (layout : HeapArena.Layout) (holes : Stream.Holes) : Prop :=
  ∀ index < heapWords, Stream.ReadableData holes (layout.region.address index) 8

theorem ReadableHeap.mono {layout : HeapArena.Layout} {holes smaller : Stream.Holes}
    (readable : ReadableHeap layout holes) (subset : ∀ address, smaller address → holes address) :
    ReadableHeap layout smaller := fun index bound offset small hidden => readable index bound offset small (subset _ hidden)

theorem ReadableHeap.clear {layout : HeapArena.Layout} {holes : Stream.Holes}
    (readable : ReadableHeap layout holes) (address : Word) (count : Nat) :
    ReadableHeap layout (Stream.clearRange holes address count) := readable.mono (fun _ hidden => hidden.1)

theorem ReadableHeap.enter {layout : HeapArena.Layout} {holes : Stream.Holes}
    (readable : ReadableHeap layout holes) (frame : Scalar.Frame layout.region) (parameters : Nat) :
    ReadableHeap layout (Scalar.enterHoles frame parameters holes) := by
  unfold Scalar.enterHoles Scalar.pushHoles
  split <;> (try split)
  · exact ((readable.clear _ _).clear _ _).clear _ _
  · exact (readable.clear _ _).clear _ _
  · exact (readable.clear _ _).clear _ _
  · exact readable.clear _ _

theorem ReadableHeap.add_return {layout : HeapArena.Layout} {holes : Stream.Holes}
    (readable : ReadableHeap layout holes) {slot : Nat} (bound : slot < layout.region.slots) (above : heapWords ≤ slot) :
    ReadableHeap layout (Stream.addRange holes (layout.region.address slot) 8) := by
  intro index below offset small hidden
  rcases hidden with old | ⟨other, otherBound, equal⟩
  · exact readable index below offset small old
  · exact Scalar.byte_slots_distinct (Nat.lt_of_lt_of_le below layout.enough) bound (by omega) small otherBound equal

theorem ReadableHeap.access {layout : HeapArena.Layout} {holes : Stream.Holes} {returns : List ReturnFrame}
    (readable : ReadableHeap layout holes) {top : Nat} (above : heapWords ≤ top)
    (frames : Scalar.FramesAbove layout.region top returns) : Access layout holes returns :=
  ⟨readable, fun index below => frames.disjoint (Nat.lt_of_lt_of_le below layout.enough) (by omega)⟩

theorem enter_based {layout : HeapArena.Layout} {state : State} (based : Based layout state)
    (frame : Scalar.Frame layout.region) (parameters : Nat) : Based layout (Scalar.enterState frame parameters state) := by
  simpa [Based, Scalar.enter_registers, Scalar.frameState, Scalar.pushState] using based

theorem arguments_mapped {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    {arguments : Array Scalar.Atom} (small : arguments.size ≤ 2) (valid : arguments.all (·.valid maxValues) = true) :
    arguments.mapM (Scalar.Atom.eval (HeapCopies.slots frame state)) = some (argumentValues frame state arguments) := by
  rcases Scalar.array_le_two arguments small with rfl | ⟨first, rfl⟩ | ⟨first, second, rfl⟩
  · simp [Array.mapM_eq_mapM_toList, argumentValues]
  · have accepted : first.valid maxValues = true := by simpa using valid
    simp [Array.mapM_eq_mapM_toList, argumentValues, HeapCopies.atom_found frame state (atom_larger accepted)]
  · have accepted : first.valid maxValues = true ∧ second.valid maxValues = true := by simpa using valid
    simp [Array.mapM_eq_mapM_toList, argumentValues, HeapCopies.atom_found frame state (atom_larger accepted.1),
      HeapCopies.atom_found frame state (atom_larger accepted.2)]

structure BodyResult (checked : X86.Checked) (plan : HeapTarget.Plan) (exit : BlockId)
    (layout : HeapArena.Layout) (frame : Scalar.Frame layout.region) (before after : State)
    (rootTop : Nat) (returns : List ReturnFrame) (outside initialMemory : Memory) (initialHoles : Stream.Holes) where
  count : Nat
  memory : Memory
  holes : Stream.Holes
  represented : Realizes layout.region outside after.words memory
  safe : Scalar.HolesIn layout.region rootTop holes
  readable : ReadableHeap layout holes
  steps : Stream.SafeSteps Runtime.rejecting checked count initialHoles
    (inFrame (before.core initialMemory) plan.entry 0 returns) holes (inFrame (after.core memory) exit 0 returns)

def BodyContract (checked : X86.Checked) (plan : HeapTarget.Plan) (exit : BlockId)
    (layout : HeapArena.Layout) (frame : Scalar.Frame layout.region) (before after : State) : Prop :=
  ∀ rootTop returns outside memory holes,
    Environment layout frame before holes returns rootTop → Realizes layout.region outside before.words memory →
    Nonempty (BodyResult checked plan exit layout frame before after rootTop returns outside memory holes)

structure ActivationResult (checked : X86.Checked) (plan : HeapTarget.FunctionPlan)
    (layout : HeapArena.Layout) (frame : Scalar.Frame layout.region) (before bodyAfter : State)
    (rootTop : Nat) (returns : List ReturnFrame) (outside initialMemory : Memory) (initialHoles : Stream.Holes) where
  count : Nat
  memory : Memory
  holes : Stream.Holes
  represented : Realizes layout.region outside (finished frame bodyAfter).words memory
  safe : Scalar.HolesIn layout.region rootTop holes
  readable : ReadableHeap layout holes
  steps : Stream.SafeSteps Runtime.rejecting checked count initialHoles
    (inFrame (before.core initialMemory) plan.entry 0 returns) holes
    (inFrame ((finished frame bodyAfter).core memory) plan.exit Scalar.successInstructions.length returns)

theorem activate {checked : X86.Checked} {entries : Array BlockId} {parameters : Nat} {plan : HeapTarget.FunctionPlan}
    {layout : HeapArena.Layout} {frame : Scalar.Frame layout.region} {before after : State}
    (code : HeapTarget.FunctionCode checked entries parameters plan)
    (preserved : Scalar.Preserves frame 0 (Scalar.enterState frame parameters before) after)
    (body : BodyContract checked plan.body plan.exit layout frame (Scalar.enterState frame parameters before) after)
    (rootTop : Nat) (returns : List ReturnFrame) (outside memory : Memory) (holes : Stream.Holes)
    (based : Based layout before) (stack : before.registers .rsp = layout.region.address frame.top)
    (safe : Scalar.HolesIn layout.region rootTop holes) (frames : Scalar.FramesAbove layout.region frame.top returns)
    (readable : ReadableHeap layout holes) (separate : heapWords ≤ frame.stackIndex) (below : frame.top ≤ rootTop)
    (represented : Realizes layout.region outside before.words memory) :
    Nonempty (ActivationResult checked plan layout frame before after rootTop returns outside memory holes) := by
  obtain ⟨bodyMemory, bodyView, prologueSteps⟩ := (Scalar.enter_safeTrace frame parameters before holes stack frames).jump
    outside memory represented checked plan.entry plan.body.entry code.prologue (HeapTarget.Plan.entry_valid code.body)
  have bodyReadable := readable.enter frame parameters
  have bodyEnvironment : Environment layout frame (Scalar.enterState frame parameters before)
      (Scalar.enterHoles frame parameters holes) returns rootTop :=
    ⟨Scalar.enter_framed frame parameters before, enter_based based frame parameters, safe.enter frame parameters,
      frames, bodyReadable.access (by simp only [Scalar.Frame.stackIndex] at separate; omega) frames, separate, below⟩
  obtain ⟨executed⟩ := body rootTop returns outside bodyMemory _ bodyEnvironment bodyView
  have tagged := preserved.trans (Scalar.Preserves.setReg frame 0 after .rdx 0 (by simp))
  have framed := tagged.1.framed (Scalar.enter_framed frame parameters before)
  have exitTrace := (SafeTrace.mov layout.region returns after executed.holes .rdx (.imm 0)).append
    (Scalar.leave_safeTrace frame (after.setReg .rdx 0) executed.holes framed executed.safe)
  have exitTrace : SafeTrace layout.region returns Scalar.successInstructions after executed.holes
      (finished frame after) executed.holes := exitTrace
  obtain ⟨exitMemory, exitView, exitSteps⟩ := exitTrace.steps outside executed.memory executed.represented
    Runtime.rejecting checked plan.exit 0 code.exit.segment (by simpa using code.exit.fits)
  exact ⟨{
    count := (Scalar.prologue parameters).length + 1 + executed.count + Scalar.successInstructions.length
    memory := exitMemory, holes := executed.holes, represented := exitView, safe := executed.safe, readable := executed.readable
    steps := by simpa only [Nat.zero_add] using (prologueSteps.append executed.steps).append exitSteps }⟩

end Compilatrix.X86.HeapRuns
