import Ix.Compiler.IxIR2.CallReusePrefix

/-! Every synchronization point after a reset or in an unchanged block advances. -/

namespace Ix.Compiler.IxIR2.CallReuse.Sim

open Eval

theorem step_terminator {context : Context} {interpretation : Interpretation}
    {store : Store} {heapFuel : Nat} {frame : Frame} {stack : List Continuation}
    {block : Block} {target : Machine}
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (stepped : Eval.Step context interpretation { store, heapFuel, control := .running frame stack } target) :
    TerminatorTransferCase context interpretation store heapFuel frame stack block.terminator target := by
  cases stepped.classify with
  | instruction found beforeEnd _ _ =>
      have blocks := Option.some.inj (found.symm.trans blockAt)
      cases blocks
      omega
  | terminator found _ atTerminator classified =>
      have blocks := Option.some.inj (found.symm.trans blockAt)
      cases blocks
      simpa only [atTerminator] using classified

theorem Position.entry_parts {limits : Validate.Limits} {validation : Validate.Context} {block : Block}
    {leftPC rightPC : Nat} {credits : Array (Option Credit)}
    (position : Position limits validation block leftPC rightPC credits)
    {site : Site limits validation block} (produced : inspect limits validation block = some site)
    (zero : leftPC = 0) : rightPC = 0 ∧ credits = #[] := by
  cases position with
  | unchanged rejected cleared => rw [rejected] at produced; cases produced
  | entry => exact ⟨rfl, rfl⟩
  | body => omega
  | finished => omega

theorem Frame.entry_eq {frame : Frame} (pc : frame.pc = 0) (credits : frame.credits = #[]) :
    frame = { definition := frame.definition, block := frame.block, values := frame.values } := by
  cases frame
  simp_all

theorem stable_step_related {limits : Validate.Limits} {validation : Validate.Context}
    {leftContext rightContext : Context} {mapping : Array Nat}
    {leftStore rightStore : Store} {leftFuel rightFuel : Nat}
    {block : Block} {leftFrame rightFrame : Frame} {leftStack rightStack : List Continuation}
    {leftAfter : Machine}
    (contexts : ContextRel limits validation leftContext rightContext)
    (readyContext : ContextReady leftContext) (schemas : leftContext.schemas = validation.schemas)
    (machines : MachineRel limits validation leftContext mapping
      { store := leftStore, heapFuel := leftFuel, control := .running leftFrame leftStack }
      { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack })
    (frames : FrameRel limits validation mapping block leftFrame rightFrame)
    (stack : StackRel limits validation mapping leftStack rightStack)
    (outside : leftFrame.pc ≠ 0 ∨ inspect limits validation block = none)
    (stepped : Eval.Step leftContext .physical
      { store := leftStore, heapFuel := leftFuel, control := .running leftFrame leftStack } leftAfter) :
    ∃ after rightAfter,
      Policy.Step .suspendedCallsV1 rightContext .physical
        { store := rightStore, heapFuel := rightFuel, control := .running rightFrame rightStack } rightAfter ∧
      TransferRel limits validation leftContext mapping after leftStore rightStore leftAfter rightAfter := by
  rcases leftFrame with ⟨leftDefinition, leftBlock, leftPC, leftValues, leftCredits⟩
  rcases rightFrame with ⟨rightDefinition, rightBlock, rightPC, rightValues, rightCredits⟩
  have position := frames.position
  cases position with
  | unchanged rejected cleared =>
      have targetAt : rightDefinition.blocks[rightBlock]? = some block := by
        simpa only [rewriteBlock_rejected rejected] using frames.targetAt
      cases stepped.classify with
      | instruction found pc instructionAt classified =>
          have blocks := Option.some.inj (found.symm.trans frames.sourceAt)
          cases blocks
          have free := CreditFree.instructionAt (functionReady_creditFree frames.ready) frames.sourceAt pc
          rw [instructionAt] at free
          obtain ⟨after, target, targetCase, related⟩ := instruction_related contexts readyContext
            machines.heapState machines.fuel frames stack rejected free classified
          exact ⟨after, target, Policy.of_originalStep (targetCase.step targetAt pc instructionAt), related⟩
      | terminator found pc terminatorAt classified =>
          have blocks := Option.some.inj (found.symm.trans frames.sourceAt)
          cases blocks
          obtain ⟨after, target, targetCase, related⟩ := terminator_related contexts readyContext
            machines.heapState machines.fuel frames stack cleared classified
          exact ⟨after, target, Policy.of_originalStep (targetCase.step targetAt pc terminatorAt), related⟩
  | entry site produced =>
      rcases outside with nonzero | rejected
      · exact False.elim (nonzero rfl)
      · rw [rejected] at produced; cases produced
  | body site produced offset within credit layout physical =>
      have targetAt : rightDefinition.blocks[rightBlock]? = some site.shape.target := by
        simpa only [rewriteBlock_accepted produced] using frames.targetAt
      by_cases beforeAllocation : offset < site.shape.calls.size
      · obtain ⟨call, callAt⟩ := site.call_exists beforeAllocation
        have sourceInstruction : block.instructions[2 * site.shape.fieldCount + 1 + offset]? = some call.instruction := by
          simp only [site.exact, site.shape.call_at beforeAllocation,
            Array.getElem?_eq_getElem beforeAllocation, callAt]
        have targetInstruction : site.shape.target.instructions[site.shape.fieldCount + 1 + offset]? =
            some call.instruction := by
          simp only [site.shape.target_call_at beforeAllocation,
            Array.getElem?_eq_getElem beforeAllocation, callAt]
        obtain ⟨sourcePC, sourceOpcode⟩ := Array.getElem?_eq_some_iff.mp sourceInstruction
        obtain ⟨targetPC, targetOpcode⟩ := Array.getElem?_eq_some_iff.mp targetInstruction
        have classified := step_instruction frames.sourceAt sourcePC sourceOpcode stepped
        have advanced := frames.advanceBody produced beforeAllocation rfl rfl rfl layout physical
        obtain ⟨target, targetStep, related⟩ := callInstruction_related contexts readyContext machines
          frames advanced stack targetAt targetPC targetOpcode classified
        exact ⟨mapping, target, targetStep, related⟩
      · have atAllocation : offset = site.shape.calls.size := by omega
        subst offset
        have sourceInstruction : block.instructions[2 * site.shape.fieldCount + 1 + site.shape.calls.size]? =
            some (.alloc .shared site.shape.allocationConstructor site.shape.allocationArguments) := by
          simpa only [site.exact] using site.shape.alloc_at
        obtain ⟨sourcePC, sourceOpcode⟩ := Array.getElem?_eq_some_iff.mp sourceInstruction
        exact bodyAllocation_related contexts schemas machines frames stack produced rfl rfl rfl layout physical
          (step_instruction frames.sourceAt sourcePC sourceOpcode stepped)
  | finished site produced =>
      have sourcePC : 2 * site.shape.fieldCount + site.shape.calls.size + 2 = block.instructions.size := by
        simp only [site.exact, Shape.baseline_size]
      have targetPC : site.shape.fieldCount + site.shape.calls.size + 2 = site.shape.target.instructions.size := by simp
      have targetAt : rightDefinition.blocks[rightBlock]? = some site.shape.target := by
        simpa only [rewriteBlock_accepted produced] using frames.targetAt
      have classified := step_terminator frames.sourceAt sourcePC stepped
      obtain ⟨after, target, targetCase, related⟩ := terminator_related contexts readyContext
        machines.heapState machines.fuel frames stack (by simp [NoLiveCredits]) classified
      have sameTerminator : site.shape.target.terminator = block.terminator := by
        simp only [site.exact, Shape.target, Shape.baseline]
      exact ⟨after, target, Policy.of_originalStep (targetCase.step targetAt targetPC sameTerminator), related⟩

end Ix.Compiler.IxIR2.CallReuse.Sim
