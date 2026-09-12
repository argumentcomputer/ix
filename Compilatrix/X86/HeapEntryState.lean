import Compilatrix.X86.HeapHeader

namespace Compilatrix.X86.HeapEntry
open WordRegion HeapArena

def guarded (state : State) : State := state.setReg .rax (state.words 1)

def pushArena (workspace : Workspace) (state : State) : State :=
  (state.setReg .rsp (workspace.layout.region.address workspace.savedTop)).setWord workspace.savedTop (state.registers .r15)

def installArena (workspace : Workspace) (state : State) : State :=
  (pushArena workspace state).setReg .r15 (state.registers .rdx)

def prepared (baseline : Bool) (workspace : Workspace) (state : State) : State :=
  HeapHeader.initialState baseline (installArena workspace (guarded state))

def preamble (baseline : Bool) : List Instr :=
  [.push .r15, .mov .w64 .r15 (.reg .rdx)] ++ HeapTarget.headerInit baseline

def callOffset : Nat := 20

theorem prefix_length (baseline : Bool) : (preamble baseline).length = callOffset := by
  cases baseline <;> rfl

theorem adapter_eq (baseline : Bool) (target : BlockId) :
    HeapTarget.adapter baseline target = preamble baseline ++ [.call target, .pop .r15] := by
  simp [HeapTarget.adapter, preamble]

def called (baseline : Bool) (workspace : Workspace) (entry : HeapTarget.EntryPlan) (state : State) : State :=
  (prepared baseline workspace state).call workspace.layout.region workspace.frame.top entry.adapter callOffset

def completed (workspace : Workspace) (after : State) : State :=
  ((HeapRuns.finished workspace.frame after).setReg .rsp (workspace.layout.region.address workspace.externalTop)).setReg .r15
    (after.words workspace.savedTop)

@[simp] theorem completed_words (workspace : Workspace) (after : State) : (completed workspace after).words = after.words := rfl

@[simp] theorem completed_value (workspace : Workspace) (after : State) :
    (completed workspace after).registers .rax = after.registers .rax := by
  simp [completed, HeapRuns.finished, Scalar.leaveState]

@[simp] theorem completed_tag (workspace : Workspace) (after : State) : (completed workspace after).registers .rdx = 0 := by
  simp [completed, HeapRuns.finished, Scalar.leaveState]

theorem saved_above (workspace : Workspace) : 10 ≤ workspace.savedTop := by
  have := workspace.frame.enough
  simp only [Workspace.savedTop]
  omega

theorem external_above (workspace : Workspace) : 10 ≤ workspace.externalTop := by
  have := workspace.frame.enough
  simp only [Workspace.externalTop]
  omega

theorem prepared_saved (baseline : Bool) (workspace : Workspace) (state : State) :
    (prepared baseline workspace state).words workspace.savedTop = state.registers .r15 := by
  rw [prepared, HeapHeader.initialize_other _ _ (Or.inr (saved_above workspace))]
  simp [installArena, pushArena, guarded]

theorem prepared_external (baseline : Bool) (workspace : Workspace) (state : State) :
    (prepared baseline workspace state).words workspace.externalTop = state.words workspace.externalTop := by
  rw [prepared, HeapHeader.initialize_other _ _ (Or.inr (external_above workspace))]
  simp [installArena, pushArena, guarded, Workspace.savedTop, Workspace.externalTop]

theorem prepared_register {baseline : Bool} {workspace : Workspace} {state : State} {register : GPR}
    (notRax : register ≠ .rax) (notRcx : register ≠ .rcx) (notRsp : register ≠ .rsp) (notR15 : register ≠ .r15) :
    (prepared baseline workspace state).registers register = state.registers register := by
  simp [prepared, HeapHeader.initialize_register notRcx, installArena, pushArena, guarded, notRax, notRsp, notR15]

theorem prepared_stack (baseline : Bool) (workspace : Workspace) (state : State) :
    (prepared baseline workspace state).registers .rsp = workspace.layout.region.address workspace.savedTop := by
  simp [prepared, installArena, pushArena, guarded]

theorem prepared_based {baseline : Bool} {workspace : Workspace} {state : State}
    (base : state.registers .rdx = workspace.layout.region.base) : Based workspace.layout (prepared baseline workspace state) := by
  simpa [Based, prepared, installArena, guarded] using base

theorem called_saved (baseline : Bool) (workspace : Workspace) (entry : HeapTarget.EntryPlan) (state : State) :
    (called baseline workspace entry state).words workspace.savedTop = state.registers .r15 := by
  simpa [called, State.call, Workspace.savedTop] using prepared_saved baseline workspace state

theorem called_external (baseline : Bool) (workspace : Workspace) (entry : HeapTarget.EntryPlan) (state : State) :
    (called baseline workspace entry state).words workspace.externalTop = state.words workspace.externalTop := by
  simpa [called, State.call, Workspace.externalTop] using prepared_external baseline workspace state

theorem completed_stable {baseline : Bool} {workspace : Workspace} {entry : HeapTarget.EntryPlan} {before after : State} {parameters : Nat}
    (stack : before.registers .rsp = workspace.layout.region.address workspace.externalTop)
    (preserved : Scalar.Preserves workspace.frame 0
      (Scalar.enterState workspace.frame parameters (called baseline workspace entry before)) after) :
    Scalar.Stable before (completed workspace after) := by
  have finished := HeapRuns.finish_preserves workspace.frame parameters (called baseline workspace entry before) after
    (by simp [called, State.call]) preserved
  have arenaSaved : after.words workspace.savedTop = before.registers .r15 := by
    rw [← called_saved baseline workspace entry before]
    exact finished.2 _ (by simp only [Workspace.savedTop]; omega)
  intro register saved
  have same := finished.1 register saved
  cases register <;> simp only [Scalar.callerSaved] at saved <;> (try contradiction)
  all_goals simp_all [completed, called, State.call, prepared_register]

theorem prefix_trace {workspace : Workspace} {state : State} (baseline : Bool)
    (stack : state.registers .rsp = workspace.layout.region.address workspace.externalTop)
    (base : state.registers .rdx = workspace.layout.region.base) :
    SafeTrace workspace.layout.region [] (preamble baseline) (guarded state) (fun _ => False)
      (prepared baseline workspace state) (fun _ => False) := by
  have pushed := SafeTrace.push workspace.layout.region [] (guarded state) (fun _ => False) .r15 workspace.savedTop
    workspace.saved_bound (by simpa [guarded, stack] using workspace.push_address)
    (by simp [Stream.FramesDisjoint])
  have pushed : SafeTrace workspace.layout.region [] [.push .r15] (guarded state) (fun _ => False)
      (pushArena workspace (guarded state)) (fun _ => False) := by
    have clear := HeapArena.clear_readable (holes := fun _ => False)
      (address := workspace.layout.region.address workspace.savedTop) (count := 8) (fun _ _ h => h)
    simpa only [pushArena, clear] using pushed
  have installed := SafeTrace.mov workspace.layout.region [] (pushArena workspace (guarded state)) (fun _ => False) .r15 (.reg .rdx)
  have installed : SafeTrace workspace.layout.region [] [.mov .w64 .r15 (.reg .rdx)]
      (pushArena workspace (guarded state)) (fun _ => False) (installArena workspace (guarded state)) (fun _ => False) := by
    simpa [installArena, pushArena, guarded] using installed
  have initialized := HeapHeader.initialize_trace (state := installArena workspace (guarded state))
    (by simpa [Based, installArena, guarded] using base) (Access.empty workspace.layout) baseline
  simpa only [preamble, prepared, List.singleton_append] using (pushed.append installed).append initialized

end Compilatrix.X86.HeapEntry
