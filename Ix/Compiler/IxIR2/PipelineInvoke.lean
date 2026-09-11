import Ix.Compiler.IxIR2.PipelinePhysical

/-! Successful runtime invocation through the actual structured lowering.
Entry ownership, reachable-heap provenance, and runtime invariants are the
usual semantic ABI obligations; all callee simulations come from the checked
attachment's existing recursive trace worker. -/

namespace Ix.Compiler.IxIR2.Pipeline

theorem CompiledAttachment.successfulFunctionSimulation
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {address : Ixon.Address} {definition : Function}
    (declared : attached.simulationTargetContext.declarations address = some (.fn definition))
    (papSafe : definition.signature.papSafe = true)
    (values : Array IxIR1.RVal)
    {sourceFuel : Nat} {store : IxIR1.Store} {output : IxIR1.Store × IxIR1.RVal}
    (run : IxIR1.invoke attached.simulationSourceContext sourceFuel address values.toList store = .ok output)
    (ownership : IxIR1.Sim.RootOwnership store (IxIR1.Sim.rootsFor .shared values.toList))
    (runtime : Lower.Sim.SourceRuntimeInvariant store values.toList.reverse)
    (image : attached.SourceStoreImage store) :
    ∃ controlFuel heapFuel targetOutput,
      Eval.runFunction attached.simulationTargetContext .physical definition values controlFuel heapFuel
        { heap := store } = .ok targetOutput ∧
      Lower.Sim.OutcomeRel output targetOutput := by
  obtain ⟨bodyFuel, _, invoked⟩ := IxIR1.invoke_success run
  cases invoked with
  | extern found _ _ _ =>
    exact False.elim (attached.sourceDeclaration_not_extern rfl found)
  | @fn sourceDefinition bodyOutput found arity bodyRun checked =>
    obtain ⟨targetDefinition, trace, member, matched, targetAt⟩ :=
      attached.functionTrace_of_source_declaration rfl rfl found
    have same : targetDefinition = definition :=
      Decl.fn.inj (Option.some.inj (targetAt.symm.trans declared))
    subst targetDefinition
    obtain ⟨outputEq, world⟩ := IxIR1.Sim.checkResultWorld_ok checked
    subst bodyOutput
    have sourceArity : values.size = trace.source.arity := by
      simpa [matched.source] using arity
    have targetArity : values.size = definition.signature.params.size := by
      simpa [matched.generated] using sourceArity.trans trace.sourceArity.symm
    have nonempty : definition.blocks.isEmpty = false := by
      have head := trace.headBlockAt
      rw [trace.rootHeadBlock, matched.generated] at head
      obtain ⟨bound, _⟩ := Array.getElem?_eq_some_iff.mp head
      simpa [Array.isEmpty] using (Nat.ne_of_gt bound)
    let frame : Eval.Frame := { definition, values }
    let machine := Eval.initialMachine definition values 0 { heap := store }
    have state : attached.sidecars.TraceStateRel trace trace.root store values.toList.reverse frame := by
      simpa [frame, matched.generated] using attached.functionEntryTraceState member values sourceArity
    have stores : Lower.Sim.StoreRel store machine.store := by constructor <;> rfl
    have entryOwnership : Lower.Sim.SourceOwnershipAt attached.target.artifact.trace.positions
        trace.root store values.toList.reverse [] := by
      intro position positionMember coordinate
      rw [attached.target.entryCapabilities member positionMember coordinate]
      have shape := attached.target.papSafeEntryCapabilities member (by simpa [matched.generated] using papSafe)
      apply Lower.Sim.SourceOwnershipInvariant.sharedEntry
      · simpa [matched.generated, targetArity] using shape
      · simpa using ownership
    have executed : IxIR1.runCode attached.simulationSourceContext bodyFuel trace.source store
        values.toList.reverse trace.root.sourceCode = .ok output := by
      simpa [trace.rootSourceCode, matched.source] using bodyRun
    have resultWorld : IxIR1.Sim.HasWorld output.1 trace.source.result output.2 := by
      simpa [matched.source] using world
    have reached := (attached.successfulTraceSimulation attached.simulationSourceContext
      attached.simulationTargetContext attached.successfulSimulationContracts bodyFuel)
      member Lower.CodeTrace.Descendant.refl state stores runtime entryOwnership executed resultWorld
      (show machine.control = .running frame [] from rfl) (show frame.credits = #[] from rfl) image
      (attached.haltReturnHandler attached.simulationSourceContext attached.simulationTargetContext .logical trace output)
    obtain ⟨heapFuel, controlFuel, final, steps, halted, finalStores⟩ := reached
    cases final with
    | mk targetStore heapRemaining finalControl =>
      dsimp only at halted
      subst finalControl
      let targetOutput : Eval.Result := { store := targetStore, value := output.2, controlRemaining := 0, heapRemaining }
      have logical : Eval.runFunction attached.simulationTargetContext .logical definition values controlFuel heapFuel
          { heap := store } = .ok targetOutput := by
        rw [Eval.runFunction_eq_runMachine targetArity nonempty]
        simpa [machine, targetOutput, Eval.initialMachine] using steps.runMachine_halted
      exact ⟨controlFuel, heapFuel, targetOutput,
        Eval.runFunction_creditFree attached.target.creditFree declared targetArity nonempty logical,
        { finalStores with value := rfl }⟩

end Ix.Compiler.IxIR2.Pipeline
