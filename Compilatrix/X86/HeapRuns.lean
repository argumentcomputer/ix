import Compilatrix.X86.HeapFunctionCode

namespace Compilatrix.X86.HeapRuns
open WordRegion PhysicalHeap HeapArena HeapPrimitives

def argumentValues {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (arguments : Array Scalar.Atom) : Array Word := arguments.map (HeapCopies.atomValue frame state)

def ready {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (arguments : Array Scalar.Atom) : State := Scalar.argumentsState state (argumentValues frame state arguments)

def called {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State)
    (arguments : Array Scalar.Atom) (enough : 67 ≤ frame.top) (entry : BlockId) : State :=
  (ready frame state arguments).call layout (frame.child enough).top entry 2

def finished {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (state : State) : State :=
  Scalar.leaveState frame (state.setReg .rdx 0)

def resumed {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (before after : State)
    (arguments : Array Scalar.Atom) (enough : 67 ≤ frame.top) : State :=
  (finished (frame.child enough) after).setReg .rsp ((ready frame before arguments).registers .rsp)

/-- A finite execution of the selected control tree in word memory. Calls
enter an earlier function's body and resume with its scalar or owning result.
Return tokens are bookkeeping in this model; no x86 step is assumed. -/
inductive Run (layout : HeapArena.Layout) (plans : Array HeapTarget.FunctionPlan) (parameters : Array Nat) :
    (frame : Scalar.Frame layout.region) → HeapTarget.Plan → State → State → Prop where
  | ret {frame entry kind source before} :
      Run layout plans parameters frame (.ret entry kind source) before (load frame before source)
  | primitive {frame entry operation next before middle after}
      (performed : Executes layout frame operation before middle)
      (rest : Run layout plans parameters frame next middle after) :
      Run layout plans parameters frame (.primitive entry operation next) before after
  | jump {frame entry copies next before after}
      (rest : Run layout plans parameters frame next (HeapCopies.execute frame before copies) after) :
      Run layout plans parameters frame (.jump entry copies next) before after
  | zero {frame entry zeroEdge succEdge source zeroTransfer zero succTransfer successor before after}
      (test : HeapCopies.atomValue frame before source = 0)
      (rest : Run layout plans parameters frame zero
        (HeapCopies.execute frame (load frame before source) zeroTransfer) after) :
      Run layout plans parameters frame (.branch entry zeroEdge succEdge source zeroTransfer zero succTransfer successor) before after
  | successor {frame entry zeroEdge succEdge source zeroTransfer zero succTransfer successor before after}
      (test : HeapCopies.atomValue frame before source ≠ 0)
      (rest : Run layout plans parameters frame successor
        (HeapCopies.execute frame (load frame before source) succTransfer) after) :
      Run layout plans parameters frame (.branch entry zeroEdge succEdge source zeroTransfer zero succTransfer successor) before after
  | call {frame entry function arguments destination next before after callee calleeAfter}
      (found : plans[function]? = some callee) (enough : 67 ≤ frame.top)
      (separate : heapWords ≤ (frame.child enough).stackIndex)
      (invocation : Run layout plans parameters (frame.child enough) callee.body
        (Scalar.enterState (frame.child enough) (parameters[function]?.getD 0) (called frame before arguments enough entry)) calleeAfter)
      (rest : Run layout plans parameters frame next (save frame (resumed frame before calleeAfter arguments enough) destination) after) :
      Run layout plans parameters frame (.call entry function arguments destination next) before after
  | tailCall {frame entry kind function arguments before callee calleeAfter}
      (found : plans[function]? = some callee) (enough : 67 ≤ frame.top)
      (separate : heapWords ≤ (frame.child enough).stackIndex)
      (invocation : Run layout plans parameters (frame.child enough) callee.body
        (Scalar.enterState (frame.child enough) (parameters[function]?.getD 0) (called frame before arguments enough entry)) calleeAfter) :
      Run layout plans parameters frame (.tailCall entry kind function arguments) before
        (resumed frame before calleeAfter arguments enough)

theorem leave_stable {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (parameters : Nat) (before after : State)
    (stack : before.registers .rsp = layout.address frame.top)
    (preserved : Scalar.Preserves frame 0 (Scalar.enterState frame parameters before) after) :
    Scalar.Stable before (Scalar.leaveState frame after) := by
  have base : after.words frame.baseIndex = before.registers .rbp := by
    rw [preserved.2 _ (by simp only [Scalar.Frame.baseIndex]; omega), Scalar.enter_savedBase]
  intro register saved
  have same := preserved.1 register saved
  cases register <;> simp only [Scalar.callerSaved] at saved <;> (try contradiction)
  all_goals simp_all [Scalar.leaveState, Scalar.frameState, Scalar.pushState]

theorem finish_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (parameters : Nat) (before after : State)
    (stack : before.registers .rsp = layout.address frame.top)
    (preserved : Scalar.Preserves frame 0 (Scalar.enterState frame parameters before) after) :
    Scalar.Stable before (finished frame after) ∧
      ∀ index, frame.top ≤ index → (finished frame after).words index = before.words index := by
  have tagged := preserved.trans (Scalar.Preserves.setReg frame 0 after .rdx 0 (by simp))
  refine ⟨leave_stable frame parameters before _ stack tagged, fun index above => ?_⟩
  change (after.setReg .rdx 0).words index = before.words index
  rw [tagged.2 _ (by omega), Scalar.enter_words_above _ _ _ _ above]

theorem call_preserves {layout : WordRegion.Layout} (frame : Scalar.Frame layout) (parameters : Nat)
    (before after : State) (arguments : Array Scalar.Atom) (enough : 67 ≤ frame.top) (entry : BlockId)
    (preserved : Scalar.Preserves (frame.child enough) 0
      (Scalar.enterState (frame.child enough) parameters (called frame before arguments enough entry)) after) :
    Scalar.Preserves frame Scalar.maxLocals before (resumed frame before after arguments enough) := by
  have finished := finish_preserves (frame.child enough) parameters (called frame before arguments enough entry) after
    (by simp [called, State.call]) preserved
  have restored := Scalar.call_preserves frame enough (Nat.le_refl Scalar.maxLocals) (ready frame before arguments)
    (HeapRuns.finished (frame.child enough) after) entry finished.1 finished.2
  exact (Scalar.arguments_preserves frame Scalar.maxLocals before (argumentValues frame before arguments)).trans restored

theorem Run.preserves {layout plans parameters frame plan before after}
    (executed : Run layout plans parameters frame plan before after) (separate : heapWords ≤ frame.stackIndex) :
    Scalar.Preserves frame 0 before after := by
  induction executed with
  | ret => exact Scalar.Preserves.setReg _ _ _ _ _ (by simp)
  | primitive operation rest ih => exact (operation.preserves separate).trans (ih separate)
  | jump rest ih => exact (HeapCopies.execute_preserves _ _ _).trans (ih separate)
  | zero test rest ih | successor test rest ih =>
      exact ((Scalar.Preserves.setReg _ _ _ .rax _ (by simp)).trans (HeapCopies.execute_preserves _ _ _)).trans (ih separate)
  | call found enough childSeparate invocation rest ihCallee ihRest =>
      exact (((call_preserves _ _ _ _ _ enough _ (ihCallee childSeparate)).weaken (Nat.zero_le _)).trans
        (save_preserves _ _ _)).trans (ihRest separate)
  | tailCall found enough childSeparate invocation ih =>
      exact (call_preserves _ _ _ _ _ enough _ (ih childSeparate)).weaken (Nat.zero_le _)

end Compilatrix.X86.HeapRuns
