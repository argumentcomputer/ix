import Compilatrix.X86.HeapCalls

namespace Compilatrix.X86.HeapRuns
open WordRegion PhysicalHeap HeapArena HeapPrimitives

theorem branch_contract {checked : X86.Checked} {layout : HeapArena.Layout} {frame : Scalar.Frame layout.region}
    {before after : State} {plan next : HeapTarget.Plan} {entry zeroEdge succEdge exit : BlockId}
    {source : Scalar.Atom} {copies : Transfer} {answer : Bool}
    (entryAt : plan.entry = entry) (sourceValid : source.valid maxValues = true)
    (copiesValid : HeapTarget.transferValid copies = true)
    (test : (HeapCopies.atomValue frame before source == 0) = answer)
    (code : BlockCode checked entry [Scalar.load .rax source] (.branch Scalar.zeroCompare .eq zeroEdge succEdge))
    (edgeCode : BlockCode checked (if answer then zeroEdge else succEdge) (HeapTarget.transfer copies) (.jump next.entry))
    (nextValid : checked.program.hasBlock next.entry = true)
    (rest : BodyContract checked next exit layout frame (HeapCopies.execute frame (load frame before source) copies) after) :
    BodyContract checked plan exit layout frame before after := by
  intro rootTop returns outside memory holes environment represented
  have holds : Scalar.zeroCompare.holds .eq ((load frame before source).core Memory.unmapped) = answer :=
    (Scalar.zero_holds before (HeapCopies.atomValue frame before source) Memory.unmapped).trans test
  obtain ⟨branchMemory, branchView, branchSteps⟩ :=
    (load_trace environment.framed environment.safe sourceValid).branch outside memory represented checked entry zeroEdge succEdge
      Scalar.zeroCompare .eq code answer holds edgeCode.hasBlock
  have loaded := environment.advance (load_stable frame before source)
  have copiesTrace := HeapCopies.execute_trace loaded.framed loaded.safe loaded.frames copiesValid
  obtain ⟨edgeMemory, edgeView, edgeSteps⟩ := copiesTrace.jump outside branchMemory branchView checked _ next.entry edgeCode nextValid
  have transferred := loaded.advance (HeapCopies.execute_preserves frame _ copies).1
  obtain ⟨trailing⟩ := rest rootTop returns outside edgeMemory holes transferred edgeView
  exact ⟨{
    count := 2 + ((HeapTarget.transfer copies).length + 1) + trailing.count
    memory := trailing.memory, holes := trailing.holes, represented := trailing.represented, safe := trailing.safe, readable := trailing.readable
    steps := by simpa only [entryAt, List.length_cons, List.length_nil] using (branchSteps.append edgeSteps).append trailing.steps }⟩

/-- Every finite execution of an accepted word-memory control tree has an
E2-safe x86 execution. The induction composes real CALL/RET instructions,
heap writes, and simultaneous edge copies; it assumes no native run. -/
theorem Run.native {layout plans parameters frame plan before after}
    (executed : Run layout plans parameters frame plan before after)
    {checked : X86.Checked} (functions : HeapTarget.FunctionsCode checked plans parameters) :
    ∀ exit, plan.matches checked.program (plans.map (·.entry)) exit = true →
      checked.program.hasBlock exit = true → BodyContract checked plan exit layout frame before after := by
  induction executed with
  | @ret frame entry kind source before =>
      intro exit matched exitValid rootTop returns outside memory holes environment represented
      simp only [HeapTarget.Plan.matches, Bool.and_eq_true] at matched
      obtain ⟨nextMemory, nextView, steps⟩ :=
        (load_trace environment.framed environment.safe matched.1).jump outside memory represented checked entry exit
          (Scalar.blockMatches_code matched.2) exitValid
      exact ⟨{
        count := 2, memory := nextMemory, holes, represented := nextView, safe := environment.safe, readable := environment.access.reads
        steps := steps }⟩
  | @primitive frame entry operation next before middle after performed rest ih =>
      intro exit matched exitValid rootTop returns outside memory holes environment represented
      simp only [HeapTarget.Plan.matches, Bool.and_eq_true] at matched
      obtain ⟨nextMemory, nextView, steps⟩ := (performed.trace environment matched.1.1).jump outside memory represented checked entry next.entry
        (Scalar.blockMatches_code matched.1.2) (HeapTarget.Plan.entry_valid matched.2)
      obtain ⟨trailing⟩ := ih exit matched.2 exitValid rootTop returns outside nextMemory holes
        (environment.advance performed.stable) nextView
      exact ⟨{
        count := (HeapTarget.primitive operation).length + 1 + trailing.count
        memory := trailing.memory, holes := trailing.holes, represented := trailing.represented, safe := trailing.safe, readable := trailing.readable
        steps := steps.append trailing.steps }⟩
  | @jump frame entry copies next before after rest ih =>
      intro exit matched exitValid rootTop returns outside memory holes environment represented
      simp only [HeapTarget.Plan.matches, Bool.and_eq_true] at matched
      obtain ⟨nextMemory, nextView, steps⟩ :=
        (HeapCopies.execute_trace environment.framed environment.safe environment.frames matched.1.1).jump outside memory represented
          checked entry next.entry (Scalar.blockMatches_code matched.1.2) (HeapTarget.Plan.entry_valid matched.2)
      obtain ⟨trailing⟩ := ih exit matched.2 exitValid rootTop returns outside nextMemory holes
        (environment.advance (HeapCopies.execute_preserves frame before copies).1) nextView
      exact ⟨{
        count := (HeapTarget.transfer copies).length + 1 + trailing.count
        memory := trailing.memory, holes := trailing.holes, represented := trailing.represented, safe := trailing.safe, readable := trailing.readable
        steps := steps.append trailing.steps }⟩
  | @zero frame entry zeroEdge succEdge source zeroTransfer zero succTransfer successor before after test rest ih =>
      intro exit matched exitValid
      simp only [HeapTarget.Plan.matches, Bool.and_eq_true] at matched
      exact branch_contract (answer := true) (next := zero) rfl matched.1.1.1.1.1.1.1 matched.1.1.1.1.1.1.2 (by simp [test])
        (Scalar.blockMatches_code matched.1.1.1.1.2) (Scalar.blockMatches_code matched.1.1.1.2)
        (HeapTarget.Plan.entry_valid matched.1.2) (ih exit matched.1.2 exitValid)
  | @successor frame entry zeroEdge succEdge source zeroTransfer zero succTransfer successor before after test rest ih =>
      intro exit matched exitValid
      simp only [HeapTarget.Plan.matches, Bool.and_eq_true] at matched
      exact branch_contract (answer := false) (next := successor) rfl matched.1.1.1.1.1.1.1 matched.1.1.1.1.1.2 (by simp [test])
        (Scalar.blockMatches_code matched.1.1.1.1.2) (Scalar.blockMatches_code matched.1.1.2)
        (HeapTarget.Plan.entry_valid matched.2) (ih exit matched.2 exitValid)
  | @call frame entry function arguments destination next before after callee calleeAfter found enough separate invocation rest ihCallee ihRest =>
      intro exit matched exitValid rootTop returns outside memory holes environment represented
      have calleeCode := functions function callee found
      have entryFound : (plans.map (·.entry))[function]? = some callee.entry := by simp [found]
      simp only [HeapTarget.Plan.matches, entryFound, Bool.and_eq_true, decide_eq_true_eq] at matched
      have code := Scalar.blockMatches_code (checked := checked) matched.2.1
      have nextValid := HeapTarget.Plan.entry_valid (checked := checked) matched.2.2
      have calleePreserved := invocation.preserves separate
      obtain ⟨calledRun⟩ := call_steps enough separate matched.1.1.1 matched.1.1.2 code calleeCode calleePreserved
        (ihCallee callee.exit calleeCode.body calleeCode.exit.hasBlock) rootTop returns outside memory holes environment represented
      have resumedPreserved := call_preserves frame (parameters[function]?.getD 0) before calleeAfter arguments enough entry calleePreserved
      have resumedEnvironment := Environment.returned environment resumedPreserved.1 calledRun.safe calledRun.readable
      have saved := resumedEnvironment.save (by simp only [maxValues, Scalar.maxLocals] at *; omega : destination < Scalar.maxLocals)
      have saveSegment : Straight.Segment checked entry 3 [.spill (Scalar.slot destination) .rax] := by
        refine ⟨_, code.found, ?_⟩
        intro index bound
        have zero : index = 0 := by simp only [List.length_cons, List.length_nil] at bound; omega
        subst index
        rfl
      obtain ⟨savedMemory, savedView, saveSteps⟩ := saved.steps outside calledRun.memory calledRun.represented
        Runtime.rejecting checked entry 3 saveSegment (by change 4 < UInt32.size; decide)
      have jumpSteps := code.safe_jump nextValid Runtime.rejecting
        ((save frame (resumed frame before calleeAfter arguments enough) destination).core savedMemory) returns calledRun.holes
      obtain ⟨trailing⟩ := ihRest exit matched.2.2 exitValid rootTop returns outside savedMemory calledRun.holes
        (resumedEnvironment.advance (save_stable frame _ destination)) savedView
      exact ⟨{
        count := calledRun.count + 1 + 1 + trailing.count
        memory := trailing.memory, holes := trailing.holes, represented := trailing.represented, safe := trailing.safe, readable := trailing.readable
        steps := by simpa only [HeapTarget.Plan.entry, HeapTarget.arguments, Scalar.callInstructions, List.cons_append, List.nil_append,
          List.length_cons, List.length_nil] using ((calledRun.steps.append saveSteps).append jumpSteps).append trailing.steps }⟩
  | @tailCall frame entry kind function arguments before callee calleeAfter found enough separate invocation ih =>
      intro exit matched exitValid rootTop returns outside memory holes environment represented
      have calleeCode := functions function callee found
      have entryFound : (plans.map (·.entry))[function]? = some callee.entry := by simp [found]
      simp only [HeapTarget.Plan.matches, entryFound, Bool.and_eq_true, decide_eq_true_eq] at matched
      have code := Scalar.blockMatches_code (checked := checked) matched.2
      have calleePreserved := invocation.preserves separate
      obtain ⟨calledRun⟩ := call_steps (tail := []) enough separate matched.1.1 matched.1.2
        (by simpa only [List.append_nil] using code) calleeCode calleePreserved
        (ih callee.exit calleeCode.body calleeCode.exit.hasBlock) rootTop returns outside memory holes environment represented
      have jumpSteps := code.safe_jump exitValid Runtime.rejecting
        ((resumed frame before calleeAfter arguments enough).core calledRun.memory) returns calledRun.holes
      exact ⟨{
        count := calledRun.count + 1, memory := calledRun.memory, holes := calledRun.holes
        represented := calledRun.represented, safe := calledRun.safe, readable := calledRun.readable
        steps := by simpa only [HeapTarget.Plan.entry, HeapTarget.arguments, Scalar.callInstructions, List.length_cons, List.length_nil] using calledRun.steps.append jumpSteps }⟩

end Compilatrix.X86.HeapRuns
