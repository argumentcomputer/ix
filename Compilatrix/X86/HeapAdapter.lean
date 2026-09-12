import Compilatrix.X86.HeapEntryCode

namespace Compilatrix.X86.HeapEntry
open WordRegion HeapArena

theorem segment_between {checked : X86.Checked} {block : BlockId} {leading body trailing : List Instr} {terminator : X86.Terminator}
    (code : BlockCode checked block (leading ++ body ++ trailing) terminator) :
    Straight.Segment checked block leading.length body := by
  refine ⟨_, code.found, ?_⟩
  intro index bound
  simp only [List.getElem?_toArray, List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact List.getElem?_append_left bound

theorem Code.preamble_segment {checked baseline target demand plan} (code : Code checked baseline target demand plan) :
    Straight.Segment checked plan.adapter 0 (preamble baseline) := by
  apply segment_between (leading := []) (trailing := [.call target, .pop .r15])
  simpa only [List.nil_append, adapter_eq] using code.adapter

theorem Code.call_segment {checked baseline target demand plan} (code : Code checked baseline target demand plan) :
    Straight.Segment checked plan.adapter callOffset [.call target] := by
  have accepted : BlockCode checked plan.adapter (preamble baseline ++ [.call target] ++ [.pop .r15]) .ret := by
    simpa only [adapter_eq, List.append_assoc, List.singleton_append] using code.adapter
  simpa only [prefix_length] using segment_between accepted

theorem Code.pop_segment {checked baseline target demand plan} (code : Code checked baseline target demand plan) :
    Straight.Segment checked plan.adapter (callOffset + 1) [.pop .r15] := by
  have accepted : BlockCode checked plan.adapter ((preamble baseline ++ [.call target]) ++ [.pop .r15] ++ []) .ret := by
    simpa only [adapter_eq, List.append_assoc, List.singleton_append, List.append_nil] using code.adapter
  simpa only [List.length_append, prefix_length, List.length_cons, List.length_nil] using segment_between accepted

theorem adapter_length (baseline : Bool) (target : BlockId) : (HeapTarget.adapter baseline target).length = callOffset + 2 := by
  rw [adapter_eq, List.length_append, prefix_length]
  rfl

structure AdapterResult (checked : X86.Checked) (baseline : Bool) (target : BlockId) (entry : HeapTarget.EntryPlan)
    (workspace : Workspace) (before after : State) (outside initialMemory : Memory) where
  count : Nat
  memory : Memory
  holes : Stream.Holes
  represented : Realizes workspace.layout.region outside (completed workspace after).words memory
  safe : Scalar.HolesIn workspace.layout.region workspace.externalTop holes
  readable : HeapRuns.ReadableHeap workspace.layout holes
  steps : Stream.SafeSteps Runtime.rejecting checked count (fun _ => False)
    (inFrame ((guarded before).core initialMemory) entry.adapter 0 []) holes
    (inFrame ((completed workspace after).core memory) entry.adapter (HeapTarget.adapter baseline target).length [])

theorem adapter_steps {checked : X86.Checked} {baseline : Bool} {demand parameters : Nat} {entry : HeapTarget.EntryPlan}
    {callee : HeapTarget.FunctionPlan} {entries : Array BlockId} (code : Code checked baseline callee.entry demand entry)
    (calleeCode : HeapTarget.FunctionCode checked entries parameters callee)
    (workspace : Workspace) (before after : State)
    (preserved : Scalar.Preserves workspace.frame 0
      (Scalar.enterState workspace.frame parameters (called baseline workspace entry before)) after)
    (body : HeapRuns.BodyContract checked callee.body callee.exit workspace.layout workspace.frame
      (Scalar.enterState workspace.frame parameters (called baseline workspace entry before)) after)
    (outside memory : Memory) (represented : Realizes workspace.layout.region outside (guarded before).words memory)
    (stack : before.registers .rsp = workspace.layout.region.address workspace.externalTop)
    (base : before.registers .rdx = workspace.layout.region.base) :
    Nonempty (AdapterResult checked baseline callee.entry entry workspace before after outside memory) := by
  obtain ⟨preparedMemory, preparedView, prefixSteps⟩ := (prefix_trace baseline stack base).steps outside memory represented Runtime.rejecting checked
    entry.adapter 0 code.preamble_segment (by rw [Nat.zero_add, prefix_length]; decide)
  rw [Nat.zero_add, prefix_length] at prefixSteps
  have address : (prepared baseline workspace before).registers .rsp - 8 = workspace.layout.region.address workspace.frame.top := by
    rw [prepared_stack]
    exact workspace.call_address
  obtain ⟨callMemory, callView, callSteps⟩ := call_safeStep (returns := []) preparedView workspace.frame.bound address code.call_segment
    (by decide) calleeCode.prologue.hasBlock (by rw [prepared_stack]; exact workspace.call_aligned)
    (by simp [Stream.FramesDisjoint]) (holes := fun _ => False)
  let active := callFrame ((prepared baseline workspace before).core preparedMemory) entry.adapter callOffset
  have activeSlot : active.returnSlot = workspace.layout.region.address workspace.frame.top := address
  have activeFrames : Scalar.FramesAbove workspace.layout.region workspace.frame.top [active] := by
    intro frame member
    have same : frame = active := by simpa using member
    subst frame
    exact ⟨workspace.frame.top, workspace.frame.bound, Nat.le_refl _, activeSlot⟩
  have hidden := (Scalar.HolesIn.empty workspace.layout.region workspace.externalTop).add_return workspace.frame.bound
    (by simp only [Workspace.externalTop]; omega) workspace.frame.partition
  have readable := HeapRuns.ReadableHeap.add_return (layout := workspace.layout) (holes := fun _ => False)
    (fun _ _ _ _ h => h) workspace.frame.bound (by have := workspace.separate; simp only [Scalar.Frame.stackIndex] at this; omega)
  have based : Based workspace.layout (called baseline workspace entry before) := by
    simpa [Based, called, State.call] using (prepared_based (baseline := baseline) base)
  obtain ⟨executed⟩ := HeapRuns.activate calleeCode preserved body workspace.externalTop [active] outside callMemory _ based
    (by simp [called, State.call]) hidden activeFrames readable workspace.separate
    (by simp only [Workspace.externalTop]; omega) callView
  have finishPreserved := HeapRuns.finish_preserves workspace.frame parameters (called baseline workspace entry before) after
    (by simp [called, State.call]) preserved
  have returnStack : ((HeapRuns.finished workspace.frame after).core executed.memory).readReg .rsp = active.returnSlot := by
    change (HeapRuns.finished workspace.frame after).registers .rsp = active.returnSlot
    rw [finishPreserved.1 .rsp (by simp), activeSlot]
    simp [called, State.call]
  have returnReadable : executed.memory.read64? active.returnSlot = .ok active.continuation.encode := by
    rw [activeSlot]
    simp only [Memory.read64?, Memory.read?, Width.bytes, executed.represented.readable _ workspace.frame.bound,
      ↓reduceIte, Except.ok.injEq]
    change executed.memory.read64 (workspace.layout.region.address workspace.frame.top) = active.continuation.encode
    rw [executed.represented.view _ workspace.frame.bound, finishPreserved.2 _ (Nat.le_refl _)]
    simp [called, State.call, active, callFrame]
  have saved : ((HeapRuns.finished workspace.frame after).core executed.memory).calleeSavedMatch active.calleeSaved = true := by
    simp only [Core.calleeSavedMatch, beq_iff_eq]
    rw [finishPreserved.1.snapshot callMemory executed.memory]
    simp [active, callFrame, Core.calleeSavedSnapshot, SysV.calleeSaved, called, State.call,
      State.core, Core.readReg, State.setReg, State.setWord, Registers.set]
  have retSteps := calleeCode.exit.safe_ret Runtime.rejecting ((HeapRuns.finished workspace.frame after).core executed.memory)
    active [] executed.holes returnStack returnReadable saved
  let resumed := (HeapRuns.finished workspace.frame after).setReg .rsp (workspace.layout.region.address workspace.savedTop)
  have returnAddress : active.returnSlot + 8 = workspace.layout.region.address workspace.savedTop := by
    rw [activeSlot]
    simpa [Workspace.savedTop] using workspace.layout.region.add workspace.frame.top 1
  have retEffect :
      { core := ((HeapRuns.finished workspace.frame after).core executed.memory).setReg .rsp (active.returnSlot + 8),
        pc := active.continuation, returns := [], status := Status.running } =
      inFrame (resumed.core executed.memory) entry.adapter (callOffset + 1) [] := by
    rw [returnAddress]
    rfl
  rw [retEffect] at retSteps
  have popped := SafeTrace.pop workspace.layout.region [] resumed executed.holes .r15 workspace.savedTop workspace.saved_bound
    (by simp [resumed]) (executed.safe.readable workspace.saved_bound (.inl workspace.saved_ordinary))
  have popped : SafeTrace workspace.layout.region [] [.pop .r15] resumed executed.holes
      (completed workspace after) executed.holes := by
    simpa [resumed, completed, workspace.pop_address, HeapRuns.finished, Scalar.leaveState] using popped
  obtain ⟨finalMemory, finalView, popSteps⟩ := popped.steps outside executed.memory executed.represented Runtime.rejecting checked
    entry.adapter (callOffset + 1) code.pop_segment (by change callOffset + 2 < UInt32.size; decide)
  exact ⟨{
    count := callOffset + 1 + executed.count + 1 + 1, memory := finalMemory, holes := executed.holes
    represented := finalView, safe := executed.safe, readable := executed.readable
    steps := by simpa only [adapter_length, List.length_cons, List.length_nil] using
      (((prefixSteps.append callSteps).append executed.steps).append retSteps).append popSteps }⟩

end Compilatrix.X86.HeapEntry
