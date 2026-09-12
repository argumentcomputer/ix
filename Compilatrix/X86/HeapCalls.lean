import Compilatrix.X86.HeapCallFrames

namespace Compilatrix.X86.HeapRuns
open WordRegion PhysicalHeap HeapArena HeapPrimitives

structure CallResult (checked : X86.Checked) (entry : BlockId)
    (layout : HeapArena.Layout) (frame : Scalar.Frame layout.region) (before bodyAfter : State)
    (arguments : Array Scalar.Atom) (enough : 67 ≤ frame.top)
    (rootTop : Nat) (returns : List ReturnFrame) (outside initialMemory : Memory) (initialHoles : Stream.Holes) where
  count : Nat
  memory : Memory
  holes : Stream.Holes
  represented : Realizes layout.region outside (resumed frame before bodyAfter arguments enough).words memory
  safe : Scalar.HolesIn layout.region rootTop holes
  readable : ReadableHeap layout holes
  steps : Stream.SafeSteps Runtime.rejecting checked count initialHoles
    (inFrame (before.core initialMemory) entry 0 returns) holes
    (inFrame ((resumed frame before bodyAfter arguments enough).core memory) entry 3 returns)

theorem call_steps {checked : X86.Checked} {entries : Array BlockId} {parameters : Nat} {callee : HeapTarget.FunctionPlan}
    {layout : HeapArena.Layout} {frame : Scalar.Frame layout.region} {before after : State}
    {entry : BlockId} {arguments : Array Scalar.Atom} {tail : List Instr} {terminator : X86.Terminator}
    (enough : 67 ≤ frame.top) (separate : heapWords ≤ (frame.child enough).stackIndex)
    (small : arguments.size ≤ 2) (valid : arguments.all (·.valid maxValues) = true)
    (code : BlockCode checked entry (HeapTarget.arguments callee.entry arguments ++ tail) terminator)
    (calleeCode : HeapTarget.FunctionCode checked entries parameters callee)
    (preserved : Scalar.Preserves (frame.child enough) 0
      (Scalar.enterState (frame.child enough) parameters (called frame before arguments enough entry)) after)
    (body : BodyContract checked callee.body callee.exit layout (frame.child enough)
      (Scalar.enterState (frame.child enough) parameters (called frame before arguments enough entry)) after)
    (rootTop : Nat) (returns : List ReturnFrame) (outside memory : Memory) (holes : Stream.Holes)
    (environment : Environment layout frame before holes returns rootTop)
    (represented : Realizes layout.region outside before.words memory) :
    Nonempty (CallResult checked entry layout frame before after arguments enough rootTop returns outside memory holes) := by
  have argumentTrace := Scalar.arguments_safeTrace (returns := returns) environment.framed
    (HeapCopies.slots_at frame before) environment.safe small (arguments_mapped frame before small valid)
  have argumentSegment : Straight.Segment checked entry 0
      [Scalar.load .rdi (arguments[0]?.getD (.constant 0)), Scalar.load .rsi (arguments[1]?.getD (.constant 0))] := by
    refine ⟨_, code.found, ?_⟩
    intro index bound
    have alternatives : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at bound; omega
    rcases alternatives with rfl | rfl <;> rfl
  obtain ⟨argumentMemory, argumentView, argumentSteps⟩ := argumentTrace.steps outside memory represented
    Runtime.rejecting checked entry 0 argumentSegment (by change 2 < UInt32.size; decide)
  have readyPreserved := Scalar.arguments_preserves frame 0 before (argumentValues frame before arguments)
  have readyFramed := readyPreserved.1.framed environment.framed
  have readyBased := environment.based.stable readyPreserved.1
  have address : (ready frame before arguments).registers .rsp - 8 = layout.region.address (frame.child enough).top :=
    readyFramed.2 ▸ frame.child_address enough
  have callSegment : Straight.Segment checked entry 2 [.call callee.entry] := by
    refine ⟨_, code.found, ?_⟩
    intro index bound
    have zero : index = 0 := by simp only [List.length_cons, List.length_nil] at bound; omega
    subst index
    rfl
  have disjoint := environment.frames.disjoint (frame.child enough).bound (by simp only [Scalar.Frame.child, Scalar.frameStride]; omega)
  obtain ⟨callMemory, callView, callSteps⟩ := call_safeStep argumentView (frame.child enough).bound address callSegment
    (by decide) calleeCode.prologue.hasBlock (readyFramed.2 ▸ frame.call_aligned) disjoint (holes := holes)
  let active := callFrame ((ready frame before arguments).core argumentMemory) entry 2
  have activeSlot : active.returnSlot = layout.region.address (frame.child enough).top := address
  have activeFrames := environment.frames.child enough active activeSlot
  have below : (frame.child enough).top < rootTop := by
    have := environment.below
    simp only [Scalar.Frame.child, Scalar.frameStride]
    omega
  have hidden := environment.safe.add_return (frame.child enough).bound below (frame.child enough).partition
  have heapReadable : ReadableHeap layout (Stream.addRange holes (layout.region.address (frame.child enough).top) 8) :=
    ReadableHeap.add_return environment.access.reads (frame.child enough).bound
      (by simp only [Scalar.Frame.stackIndex] at separate; omega)
  have calleeBased : Based layout (called frame before arguments enough entry) := by
    simpa [Based, called, ready, State.call] using readyBased
  obtain ⟨executed⟩ := activate calleeCode preserved body rootTop (active :: returns) outside callMemory _ calleeBased
    (by simp [called, State.call]) hidden activeFrames heapReadable separate (Nat.le_of_lt below) callView
  have finishedPreserved := finish_preserves (frame.child enough) parameters (called frame before arguments enough entry) after
    (by simp [called, State.call]) preserved
  have stack : ((finished (frame.child enough) after).core executed.memory).readReg .rsp = active.returnSlot := by
    change (finished (frame.child enough) after).registers .rsp = active.returnSlot
    rw [finishedPreserved.1 .rsp (by simp), activeSlot]
    simp [called, State.call]
  have returnReadable : executed.memory.read64? active.returnSlot = .ok active.continuation.encode := by
    rw [activeSlot]
    simp only [Memory.read64?, Memory.read?, Width.bytes, executed.represented.readable _ (frame.child enough).bound,
      ↓reduceIte, Except.ok.injEq]
    change executed.memory.read64 (layout.region.address (frame.child enough).top) = active.continuation.encode
    rw [executed.represented.view _ (frame.child enough).bound, finishedPreserved.2 _ (Nat.le_refl _)]
    simp [called, State.call, active, callFrame]
  have saved : ((finished (frame.child enough) after).core executed.memory).calleeSavedMatch active.calleeSaved = true := by
    simp only [Core.calleeSavedMatch, beq_iff_eq]
    rw [finishedPreserved.1.snapshot callMemory executed.memory]
    simp [active, callFrame, Core.calleeSavedSnapshot, SysV.calleeSaved, called, State.call,
      State.core, Core.readReg, State.setReg, State.setWord, Registers.set]
  have retSteps := calleeCode.exit.safe_ret Runtime.rejecting ((finished (frame.child enough) after).core executed.memory)
    active returns executed.holes stack returnReadable saved
  have returnAddress : active.returnSlot + 8 = (ready frame before arguments).registers .rsp := by
    change ((ready frame before arguments).registers .rsp - 8) + 8 = _
    exact UInt64.sub_add_cancel _ _
  have retEffect :
      { core := ((finished (frame.child enough) after).core executed.memory).setReg .rsp (active.returnSlot + 8),
        pc := active.continuation, returns, status := Status.running } =
      inFrame ((resumed frame before after arguments enough).core executed.memory) entry 3 returns := by
    rw [returnAddress]
    rfl
  rw [retEffect] at retSteps
  refine ⟨{
    count := 2 + 1 + executed.count + 1, memory := executed.memory, holes := executed.holes
    represented := executed.represented, safe := executed.safe, readable := executed.readable
    steps := ?_ }⟩
  simpa only [List.length_cons, List.length_nil, Nat.zero_add] using
    ((argumentSteps.append callSteps).append executed.steps).append retSteps

theorem Environment.returned {layout frame before after holes finalHoles returns rootTop}
    (environment : Environment layout frame before holes returns rootTop) (stable : Scalar.Stable before after)
    (safe : Scalar.HolesIn layout.region rootTop finalHoles) (readable : ReadableHeap layout finalHoles) :
    Environment layout frame after finalHoles returns rootTop :=
  ⟨stable.framed environment.framed, environment.based.stable stable, safe, environment.frames,
    readable.access (by have := environment.separate; simp only [Scalar.Frame.stackIndex] at this; omega) environment.frames,
    environment.separate, environment.below⟩

end Compilatrix.X86.HeapRuns
