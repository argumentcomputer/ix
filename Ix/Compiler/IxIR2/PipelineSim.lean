import Ix.Compiler.IxIR2.LowerSim
import Ix.Compiler.IxIR2.Pipeline
import Ix.Compiler.IxIR1.EvalHistory
import Ix.Compiler.IxIR1.ReaddressOwnership
import Ix.Compiler.LoweredCompilationSim

/-!
# HPT-backed simulation adapters for the structured IxIR₂ pipeline

This module composes the executable source-site sidecars with the local
IxIR₁-to-IxIR₂ simulation rules.  Keeping the adapters here avoids making
the executable pipeline depend on the full simulation development.
-/

namespace Ix.Compiler.IxIR2.Pipeline

open Ix.Compiler.IxIR2

/-- The recursive IxIR₂ trace state paired with the two source-side facts
needed by the HPT-backed simulation: its retained coordinate names the exact
IxIR₁ suffix, and the concrete source environment satisfies the facts
replayed at that coordinate. -/
structure Sidecars.TraceStateRel (sidecars : Sidecars)
    (functionTrace : Lower.FunctionTrace) (trace : Lower.CodeTrace)
    (sourceStore : IxIR1.Store) (source : List IxIR1.RVal)
    (frame : Eval.Frame) : Prop where
  sourceCode : sidecars.sourceCodeAt? trace.source = some trace.sourceCode
  owner : trace.source.owner = functionTrace.owner
  environment : sidecars.SiteEnvironmentHolds sourceStore trace.source source
  target : Lower.Sim.CodeStateRel functionTrace trace source frame

/-- The compiler's root-coordinate certificate and retained function syntax
identify the same source body recovered by the sidecar. -/
theorem Sidecars.sourceCodeAt?_functionRoot (sidecars : Sidecars)
    {functionTrace : Lower.FunctionTrace}
    (currentAt : sidecars.analysisCurrent? functionTrace.owner =
      some functionTrace.source) :
    sidecars.sourceCodeAt? functionTrace.root.source =
      some functionTrace.root.sourceCode := by
  rw [functionTrace.rootSource, functionTrace.rootSourceCode]
  exact sidecars.sourceCodeAt?_root currentAt

/-- Any retained function begins in the combined trace/HPT state when its
resolved arguments are installed in call order. -/
theorem Sidecars.functionEntryTraceState (sidecars : Sidecars)
    {functionTrace : Lower.FunctionTrace} {sourceStore : IxIR1.Store}
    (currentAt : sidecars.analysisCurrent? functionTrace.owner =
      some functionTrace.source)
    (values : Array IxIR1.RVal)
    (arity : values.size = functionTrace.source.arity) :
    sidecars.TraceStateRel functionTrace functionTrace.root sourceStore
      values.toList.reverse
      { definition := functionTrace.generated, values } := by
  constructor
  · exact sidecars.sourceCodeAt?_functionRoot currentAt
  · rw [functionTrace.rootSource]
  · rw [functionTrace.rootSource]
    apply sidecars.siteEnvironmentHolds_root currentAt
    simpa using arity
  · exact Lower.Sim.functionEntryCodeState functionTrace values arity

/-- Every retained declaration trace starts in the combined state.  Attachment
alignment supplies the exact HPT analysis root, so recursive call simulation
needs no separately reconstructed source function. -/
theorem CompiledAttachment.declarationFunctionEntryTraceState
     {mainWorld : Ixon.Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace} {sourceStore : IxIR1.Store}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    (notMain : functionTrace.owner ≠ .main)
    (values : Array IxIR1.RVal)
    (arity : values.size = functionTrace.source.arity) :
    attached.sidecars.TraceStateRel functionTrace functionTrace.root
      sourceStore values.toList.reverse
      { definition := functionTrace.generated, values } := by
  exact attached.sidecars.functionEntryTraceState
    (attached.functionTraceAnalysisCurrent functionMember notMain) values arity

/-- A retained synthetic-main trace also has a combined entry state at any
store.  Whole-program trace order identifies its literal closed source body;
its zero arity reduces the argument environment to the empty main root. -/
theorem CompiledAttachment.mainFunctionEntryTraceState
     {mainWorld : Ixon.Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace} {sourceStore : IxIR1.Store}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    (owner : functionTrace.owner = .main)
    (values : Array IxIR1.RVal)
    (arity : values.size = functionTrace.source.arity) :
    attached.sidecars.TraceStateRel functionTrace functionTrace.root
      sourceStore values.toList.reverse
      { definition := functionTrace.generated, values } := by
  have mainMatch := attached.target.artifact.functionTraceOrderProof
    |>.main_of_mem_owner functionMember owner
  have sourceArityZero : functionTrace.source.arity = 0 := by
    rw [mainMatch.source, attached.targetSourceProduced]
    rfl
  have valuesEmpty : values = #[] :=
    Array.eq_empty_of_size_eq_zero (arity.trans sourceArityZero)
  subst values
  constructor
  · simpa [functionTrace.rootSource, owner, functionTrace.rootSourceCode,
      mainMatch.source, attached.targetSourceProduced,
      Lower.Input.mainDefinition] using
      attached.sidecars.sourceCodeAt?_main
  · rw [functionTrace.rootSource]
  · rw [functionTrace.rootSource, owner]
    exact attached.sidecars.siteEnvironmentHolds_main
  · exact Lower.Sim.functionEntryCodeState functionTrace #[] (by
      simp [sourceArityZero])

/-- Every retained function, including the fail-closed synthetic main, starts
in the combined state for its canonical reversed argument environment. -/
theorem CompiledAttachment.functionEntryTraceState
     {mainWorld : Ixon.Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace} {sourceStore : IxIR1.Store}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    (values : Array IxIR1.RVal)
    (arity : values.size = functionTrace.source.arity) :
    attached.sidecars.TraceStateRel functionTrace functionTrace.root
      sourceStore values.toList.reverse
      { definition := functionTrace.generated, values } := by
  by_cases owner : functionTrace.owner = .main
  · exact attached.mainFunctionEntryTraceState functionMember owner values arity
  · exact attached.declarationFunctionEntryTraceState functionMember owner
      values arity

/-- The exact checked target main starts in the combined source/HPT/target
trace state with empty source store and environment. -/
theorem CompiledAttachment.initialMainTraceState
     {mainWorld : Ixon.Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    attached.sidecars.TraceStateRel
      attached.target.artifact.mainTrace
      attached.target.artifact.mainTrace.root ({} : IxIR1.Store) []
      (Lower.Sim.initialMainFrame attached.target.artifact) := by
  constructor
  · rw [attached.target.artifact.mainTrace.rootSource,
      attached.target.artifact.mainOwner,
      attached.target.artifact.mainRootSourceCode,
      attached.targetSourceProduced]
    exact attached.sidecars.sourceCodeAt?_main
  · rw [attached.target.artifact.mainTrace.rootSource]
  · rw [attached.target.artifact.mainTrace.rootSource,
      attached.target.artifact.mainOwner]
    exact attached.sidecars.siteEnvironmentHolds_main
  · exact Lower.Sim.initialMainCodeState attached.target.artifact

/-- The checked synthetic main also starts with the exact trace-indexed
ownership state: both its source environment and retained input map are
empty, so there are no external owner tokens to account for. -/
theorem CompiledAttachment.initialMainSourceOwnership
     {mainWorld : Ixon.Owned}
    {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      attached.target.artifact.mainTrace.root ({} : IxIR1.Store) [] [] := by
  apply Lower.Sim.SourceOwnershipAt.empty
  rw [attached.target.artifact.mainEntryInput]
  rfl

/-- Generic linear induction step for the combined state. The operation's
target simulation supplies only the next target `CodeStateRel`; source syntax
and the HPT environment advance from the retained trace and successful source
operation. -/
theorem Sidecars.TraceStateRel.next
    {sidecars : Sidecars} {functionTrace : Lower.FunctionTrace}
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {sourceStore outputStore : IxIR1.Store}
    {source : List IxIR1.RVal} {operation : IxIR1.Op}
    {value : IxIR1.RVal} {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {instruction : Instr} {next : Lower.CodeTrace}
    {frame nextFrame : Eval.Frame}
    (state : sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) sourceStore source frame)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next))
    (postFixpoint : IxIR1.HPT.LocalPostFixpoint
      (IxIR1.Env.ofList sidecars.input.declarations)
      sidecars.hptCertificate.summaryEnv)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.Env.ofList sidecars.input.declarations)
    (currentCompatible : ∀ current,
      sidecars.analysisCurrent? site.owner = some current →
        current = sourceCurrent)
    (sourceRun : IxIR1.runOp sourceContext sourceFuel sourceCurrent
      sourceStore source operation = .ok (outputStore, value))
    (nextTarget : Lower.Sim.CodeStateRel functionTrace next
      (value :: source) nextFrame) :
    sidecars.TraceStateRel functionTrace next outputStore
      (value :: source) nextFrame := by
  have continuation := (functionTrace.descendantLetOpMatch descendant).1
  have sourceAt : sidecars.sourceCodeAt? site =
      some (.letOp operation next.sourceCode) := by
    simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceCode] using
      state.sourceCode
  have nextSourceAt := sidecars.sourceCodeAt?_next sourceAt
  have nextEnvironment :=
    sidecars.siteEnvironmentHolds_next_of_currentCompatible postFixpoint
      sourceDeclarations currentCompatible state.environment sourceAt sourceRun
  constructor
  · rw [continuation.nextSource]
    exact nextSourceAt
  · rw [continuation.nextSource]
    exact state.owner
  · rw [continuation.nextSource]
    exact nextEnvironment
  · exact nextTarget

/-- Attachment-facing linear transport. The attachment supplies the checked
HPT post-fixpoint and rewrites the source evaluator's declaration environment
to the exact sidecar environment; callers retain only function-owner
compatibility and the local successful operation. -/
theorem CompiledAttachment.traceState_next
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat} {sourceStore outputStore : IxIR1.Store}
    {source : List IxIR1.RVal} {operation : IxIR1.Op}
    {value : IxIR1.RVal} {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {instruction : Instr} {next : Lower.CodeTrace}
    {frame nextFrame : Eval.Frame} {functionTrace : Lower.FunctionTrace}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) sourceStore source frame)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next))
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (currentCompatible : ∀ current,
      attached.sidecars.analysisCurrent? functionTrace.owner = some current →
        current = sourceCurrent)
    (sourceRun : IxIR1.runOp sourceContext sourceFuel sourceCurrent
      sourceStore source operation = .ok (outputStore, value))
    (nextTarget : Lower.Sim.CodeStateRel functionTrace next
      (value :: source) nextFrame) :
    attached.sidecars.TraceStateRel functionTrace next outputStore
      (value :: source) nextFrame := by
  apply state.next descendant attached.hptSidecarLocalPostFixpoint
    (sourceDeclarations.trans attached.sidecarDeclarationEnvironment.symm)
  · intro current currentAt
    apply currentCompatible current
    rw [← state.owner]
    exact currentAt
  · exact sourceRun
  · exact nextTarget

/-- Declaration-trace specialization: the attachment's whole-trace alignment
discharges current-function compatibility for any retained function member. -/
theorem CompiledAttachment.traceState_next_of_member
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceStore outputStore : IxIR1.Store}
    {source : List IxIR1.RVal} {operation : IxIR1.Op}
    {value : IxIR1.RVal} {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {instruction : Instr} {next : Lower.CodeTrace}
    {frame nextFrame : Eval.Frame} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) sourceStore source frame)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next))
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun : IxIR1.runOp sourceContext sourceFuel functionTrace.source
      sourceStore source operation = .ok (outputStore, value))
    (nextTarget : Lower.Sim.CodeStateRel functionTrace next
      (value :: source) nextFrame) :
    attached.sidecars.TraceStateRel functionTrace next outputStore
      (value :: source) nextFrame := by
  exact attached.traceState_next state descendant sourceDeclarations
    (attached.functionTraceAnalysisCurrentCompatible functionMember)
    sourceRun nextTarget

/-- Distinguished-main specialization. It remains valid when main analysis
fails closed, and otherwise uses the producer-certified main source. -/
theorem CompiledAttachment.mainTraceState_next
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {sourceStore outputStore : IxIR1.Store}
    {source : List IxIR1.RVal} {operation : IxIR1.Op}
    {value : IxIR1.RVal} {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {instruction : Instr} {next : Lower.CodeTrace}
    {frame nextFrame : Eval.Frame}
    (state : attached.sidecars.TraceStateRel
      attached.target.artifact.mainTrace
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) sourceStore source frame)
    (descendant : attached.target.artifact.mainTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next))
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun : IxIR1.runOp sourceContext sourceFuel
      attached.target.artifact.mainTrace.source sourceStore source operation =
        .ok (outputStore, value))
    (nextTarget : Lower.Sim.CodeStateRel
      attached.target.artifact.mainTrace next (value :: source) nextFrame) :
    attached.sidecars.TraceStateRel attached.target.artifact.mainTrace next
      outputStore (value :: source) nextFrame := by
  apply attached.traceState_next state descendant sourceDeclarations
  · intro current currentAt
    apply attached.mainAnalysisCurrentCompatible current
    rw [← attached.target.artifact.mainOwner]
    exact currentAt
  · exact sourceRun
  · exact nextTarget

/-- The traced `pure`/`move` operation advances the attachment's combined
source/HPT/target state in one target step. -/
theorem CompiledAttachment.simulate_traced_pure_move_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {value : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push value }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source sourceStore
          source (.pure sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Step context interpretation machine
        { machine with control := .running nextFrame stack } ∧
      Lower.Sim.StoreRel sourceStore machine.store ∧
      attached.sidecars.TraceStateRel functionTrace next sourceStore
        (value :: source) nextFrame := by
  dsimp only
  have sourceOperation :
      IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source sourceStore
        source (.pure sourceAtom) = .ok (sourceStore, value) := by
    unfold IxIR1.runOp
    simp [sourceResolved]
  obtain ⟨targetStep, nextTarget⟩ :=
    Lower.Sim.simulate_traced_pure_move_state descendant state.target
      sourceResolved control
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceOperation nextTarget
  exact ⟨sourceOperation, targetStep, stores, nextState⟩

/-- Successful-source-run induction form of `pure`/`move`: invert the source
`letOp`, take the target step, and return the smaller-fuel continuation with
the combined trace state. -/
theorem CompiledAttachment.simulate_traced_pure_move_success_step
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat} {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {sourceOutput : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.pure sourceAtom) next.sourceCode) = .ok sourceOutput)
    (control : machine.control = .running frame stack) :
    ∃ value nextFrame,
      nextFrame =
          { frame with
            pc := frame.pc + 1
            values := frame.values.push value } ∧
        IxIR1.resolveAtom source sourceAtom = .ok value ∧
        IxIR1.runCode sourceContext (sourceFuel + 1) functionTrace.source
          sourceStore (value :: source) next.sourceCode = .ok sourceOutput ∧
        Eval.Step context interpretation machine
          { machine with control := .running nextFrame stack } ∧
        Lower.Sim.StoreRel sourceStore
          ({ machine with control := .running nextFrame stack } :
            Eval.Machine).store ∧
        attached.sidecars.TraceStateRel functionTrace next sourceStore
          (value :: source) nextFrame := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  obtain ⟨value, sourceResolved, operationOutput⟩ :=
    IxIR1.runOp_pure_success operationRun
  have middleStoreEq : middleStore = sourceStore :=
    congrArg Prod.fst operationOutput
  have operationValueEq : operationValue = value :=
    congrArg Prod.snd operationOutput
  subst middleStore
  subst operationValue
  obtain ⟨_, targetStep, nextStores, nextState⟩ :=
    attached.simulate_traced_pure_move_state (sourceFuel := sourceFuel)
      functionMember descendant state stores
      sourceDeclarations sourceResolved control
  exact ⟨value,
    { frame with
      pc := frame.pc + 1
      values := frame.values.push value },
    rfl, sourceResolved, continuationRun, targetStep, nextStores, nextState⟩

/-- Checked ordinary allocation advances the attachment's combined state.
Function membership supplies the schema/capability certificates and exact
HPT owner/current compatibility for the recursive continuation. -/
theorem CompiledAttachment.simulate_traced_alloc_checked_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    (contextSchemas : context.schemas =
      attached.target.artifact.validationContext.schemas)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceWorld targetWorld : Ixon.Owned}
    {sourceCid targetCid : IxIR1.CtorId}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {schema : CtorSchema} {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (control : machine.control = .running frame stack)
    (schemaAt : context.schemas sourceWorld sourceCid = some schema)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next)
      sourceStore source frameRoots) :
    let node := IxIR1.Node.ctorN sourceCid values.toArray
    let sourceAllocation := sourceStore.allocNode sourceWorld node
    let targetAllocation := machine.store.allocNode sourceWorld node
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push (.loc sourceAllocation.2) }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source sourceStore
          source (.alloc sourceWorld sourceCid sourceArguments) =
        .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
      Eval.Step context interpretation machine
        { machine with
          store := targetAllocation.1
          control := .running nextFrame stack } ∧
      Lower.Sim.StoreRel sourceAllocation.1 targetAllocation.1 ∧
      attached.sidecars.TraceStateRel functionTrace next sourceAllocation.1
        (.loc sourceAllocation.2 :: source) nextFrame := by
  dsimp only
  obtain ⟨sourceRun, targetStep, nextStores, nextTarget⟩ :=
    Lower.Sim.simulate_traced_alloc_checked_state
      (sourceContext := sourceContext)
      (sourceCurrent := functionTrace.source) (sourceFuel := sourceFuel)
      (interpretation := interpretation)
      (checked := attached.target) functionMember contextSchemas descendant
      state.target stores sourceResolved control schemaAt ownership
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨sourceRun, targetStep, nextStores, nextState⟩

/-- Successful-source-run form of attached checked allocation. Source
evaluation determines the exact field vector and fresh location; the result
contains the smaller-fuel continuation and combined recursive state. -/
theorem CompiledAttachment.simulate_traced_alloc_checked_success_step
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    (contextSchemas : context.schemas =
      attached.target.artifact.validationContext.schemas)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceWorld targetWorld : Ixon.Owned}
    {sourceCid targetCid : IxIR1.CtorId}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.alloc sourceWorld sourceCid sourceArguments)
          next.sourceCode) = .ok sourceOutput)
    (control : machine.control = .running frame stack)
    {schema : CtorSchema}
    (schemaAt : context.schemas sourceWorld sourceCid = some schema)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next)
      sourceStore source frameRoots) :
    ∃ values sourceAllocation targetAllocation nextFrame,
      sourceAllocation = sourceStore.allocNode sourceWorld
          (.ctorN sourceCid values.toArray) ∧
        targetAllocation = machine.store.allocNode sourceWorld
          (.ctorN sourceCid values.toArray) ∧
        IxIR1.resolveAtoms source sourceArguments = .ok values ∧
        IxIR1.runCode sourceContext (sourceFuel + 1) functionTrace.source
          sourceAllocation.1 (.loc sourceAllocation.2 :: source)
          next.sourceCode = .ok sourceOutput ∧
        nextFrame =
          { frame with
            pc := frame.pc + 1
            values := frame.values.push (.loc sourceAllocation.2) } ∧
        Eval.Step context .logical machine
          { machine with
            store := targetAllocation.1
            control := .running nextFrame stack } ∧
        Lower.Sim.StoreRel sourceAllocation.1 targetAllocation.1 ∧
        attached.sidecars.TraceStateRel functionTrace next sourceAllocation.1
          (.loc sourceAllocation.2 :: source) nextFrame := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  obtain ⟨values, sourceResolved, operationOutput⟩ :=
    IxIR1.runOp_alloc_success operationRun
  have middleStoreEq : middleStore =
      (sourceStore.allocNode sourceWorld
        (.ctorN sourceCid values.toArray)).1 :=
    congrArg Prod.fst operationOutput
  have operationValueEq : operationValue =
      .loc (sourceStore.allocNode sourceWorld
        (.ctorN sourceCid values.toArray)).2 :=
    congrArg Prod.snd operationOutput
  subst middleStore
  subst operationValue
  obtain ⟨_, targetStep, nextStores, nextState⟩ :=
    attached.simulate_traced_alloc_checked_state
      (sourceFuel := sourceFuel) functionMember contextSchemas descendant state
      stores sourceDeclarations sourceResolved control schemaAt ownership
  exact ⟨values,
    sourceStore.allocNode sourceWorld (.ctorN sourceCid values.toArray),
    machine.store.allocNode sourceWorld (.ctorN sourceCid values.toArray),
    { frame with
      pc := frame.pc + 1
      values := frame.values.push
        (.loc (sourceStore.allocNode sourceWorld
          (.ctorN sourceCid values.toArray)).2) },
    rfl, rfl, sourceResolved, continuationRun, rfl, targetStep, nextStores,
    nextState⟩

/-- Scalar `dup`/`retainShared` advances the combined attachment state without
changing either heap. -/
theorem CompiledAttachment.simulate_traced_dup_retain_scalar_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {value : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push value }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source sourceStore
          source (.dup sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Step context interpretation machine
        { machine with control := .running nextFrame stack } ∧
      Lower.Sim.StoreRel sourceStore machine.store ∧
      attached.sidecars.TraceStateRel functionTrace next sourceStore
        (value :: source) nextFrame := by
  dsimp only
  obtain ⟨sourceRun, targetStep, nextStores, nextTarget⟩ :=
    Lower.Sim.simulate_traced_dup_retain_scalar_state
      (sourceContext := sourceContext)
      (sourceCurrent := functionTrace.source) (sourceFuel := sourceFuel)
      descendant state.target stores sourceResolved scalar control
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨sourceRun, targetStep, nextStores, nextState⟩

/-- Heap-bearing shared `dup`/`retainShared` advances the combined attachment
state through the matched reference-count update. -/
theorem CompiledAttachment.simulate_traced_dup_retain_shared_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {location : Nat} {box : IxIR1.NodeBox}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (control : machine.control = .running frame stack) :
    let nextBox := { box with rc := box.rc + 1 }
    let sourceStore' := (sourceStore.setBox location nextBox).rcTick
    let targetStore' := (machine.store.setBox location nextBox).rcTick
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push (.loc location) }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source sourceStore
          source (.dup sourceAtom) = .ok (sourceStore', .loc location) ∧
      Eval.Step context interpretation machine
        { machine with
          store := targetStore'
          control := .running nextFrame stack } ∧
      Lower.Sim.StoreRel sourceStore' targetStore' ∧
      attached.sidecars.TraceStateRel functionTrace next sourceStore'
        (.loc location :: source) nextFrame := by
  dsimp only
  obtain ⟨sourceRun, targetStep, nextStores, nextTarget⟩ :=
    Lower.Sim.simulate_traced_dup_retain_shared_state
      (sourceContext := sourceContext)
      (sourceCurrent := functionTrace.source) (sourceFuel := sourceFuel)
      descendant state.target stores sourceResolved sourceGet shared control
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨sourceRun, targetStep, nextStores, nextState⟩

/-- Scalar shared release advances the combined state while consuming one
unit of target heap work and leaving both heaps unchanged. -/
theorem CompiledAttachment.simulate_traced_drop_release_scalar_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {value : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (heapFuel : machine.heapFuel = targetHeapFuel + 1)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source sourceStore
          source (.drop sourceAtom) = .ok (sourceStore, .erased) ∧
      Eval.Step context interpretation machine
        { store := machine.store
          heapFuel := targetHeapFuel
          control := .running nextFrame stack } ∧
      Lower.Sim.StoreRel sourceStore machine.store ∧
      attached.sidecars.TraceStateRel functionTrace next sourceStore
        (.erased :: source) nextFrame := by
  dsimp only
  obtain ⟨sourceRun, targetStep, nextStores, nextTarget⟩ :=
    Lower.Sim.simulate_traced_drop_release_scalar_state
      (sourceContext := sourceContext)
      (sourceCurrent := functionTrace.source) (sourceFuel := sourceFuel)
      descendant state.target stores sourceResolved scalar heapFuel control
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨sourceRun, targetStep, nextStores, nextState⟩

/-- Scalar unique drop advances the combined state while consuming one unit
of target heap work and leaving both heaps unchanged. -/
theorem CompiledAttachment.simulate_traced_dropU_dropUnique_scalar_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {value : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (heapFuel : machine.heapFuel = targetHeapFuel + 1)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source sourceStore
          source (.dropU sourceAtom) = .ok (sourceStore, .erased) ∧
      Eval.Step context interpretation machine
        { store := machine.store
          heapFuel := targetHeapFuel
          control := .running nextFrame stack } ∧
      Lower.Sim.StoreRel sourceStore machine.store ∧
      attached.sidecars.TraceStateRel functionTrace next sourceStore
        (.erased :: source) nextFrame := by
  dsimp only
  obtain ⟨sourceRun, targetStep, nextStores, nextTarget⟩ :=
    Lower.Sim.simulate_traced_dropU_dropUnique_scalar_state
      (sourceContext := sourceContext)
      (sourceCurrent := functionTrace.source) (sourceFuel := sourceFuel)
      descendant state.target stores sourceResolved scalar heapFuel control
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨sourceRun, targetStep, nextStores, nextState⟩

/-- Recursive unique destruction selects a sufficient target heap budget and
advances the combined attachment state to the exact post-drop heap. -/
theorem CompiledAttachment.simulate_traced_dropU_dropUnique_recursive_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next))
    {sourceStore sourceStore' : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceDropped :
      IxIR1.dropUVal sourceContext sourceFuel sourceStore (.loc location) =
        .ok sourceStore')
    (control : machine.control = .running frame stack) :
    ∃ targetHeapFuel targetStore,
      let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
      IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source
            sourceStore source (.dropU sourceAtom) =
          .ok (sourceStore', .erased) ∧
        Eval.Step context interpretation
          { machine with heapFuel := targetHeapFuel }
          { store := targetStore
            heapFuel := 0
            control := .running nextFrame stack } ∧
        Lower.Sim.StoreRel sourceStore' targetStore ∧
        attached.sidecars.TraceStateRel functionTrace next sourceStore'
          (.erased :: source) nextFrame := by
  obtain ⟨targetHeapFuel, targetStore, sourceRun, targetStep, nextStores,
      nextTarget⟩ :=
    Lower.Sim.simulate_traced_dropU_dropUnique_recursive_state
      (sourceCurrent := functionTrace.source) descendant state.target stores
      sourceResolved sourceDropped control
  refine ⟨targetHeapFuel, targetStore, ?_⟩
  dsimp only
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨sourceRun, targetStep, nextStores, nextState⟩

/-- Framed recursive unique destruction.  Its locally sufficient traversal
budget can be prefixed to any independently funded continuation. -/
theorem CompiledAttachment.simulate_traced_dropU_dropUnique_recursive_state_framed
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next))
    {sourceStore sourceStore' : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceDropped :
      IxIR1.dropUVal sourceContext sourceFuel sourceStore (.loc location) =
        .ok sourceStore')
    (control : machine.control = .running frame stack) :
    ∃ localFuel targetStore,
      let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
      IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source
            sourceStore source (.dropU sourceAtom) =
          .ok (sourceStore', .erased) ∧
        Eval.dropUnique localFuel machine.store (.loc location) =
          .ok (targetStore, 0) ∧
        (∀ suffixFuel,
          Eval.Step context interpretation
            { machine with heapFuel := localFuel + suffixFuel }
            { store := targetStore
              heapFuel := suffixFuel
              control := .running nextFrame stack }) ∧
        Lower.Sim.StoreRel sourceStore' targetStore ∧
        attached.sidecars.TraceStateRel functionTrace next sourceStore'
          (.erased :: source) nextFrame := by
  have translated : Lower.Sim.translateAtom input sourceAtom =
      some targetAtom := by
    simpa [Lower.OperationSyntax] using
      functionTrace.descendantOperationSyntax descendant
  obtain ⟨blockAt, pcBound, instructionAt⟩ :=
    state.target.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] = .dropUnique targetAtom :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    Lower.Sim.resolveAtom_of_envRel state.target.environments translated
      sourceResolved
  obtain ⟨localFuel, targetStore, targetRun, nextStores⟩ :=
    Lower.Sim.dropUVal_simulates_dropUniqueWork stores sourceDropped
  have exactDrop :
      Eval.dropUnique localFuel machine.store (.loc location) =
        .ok (targetStore, 0) := by
    simpa [Eval.dropUnique] using targetRun
  have targetStep : ∀ suffixFuel,
      Eval.Step context interpretation
        { machine with heapFuel := localFuel + suffixFuel }
        { store := targetStore
          heapFuel := suffixFuel
          control := .running { frame with pc := frame.pc + 1 } stack } := by
    intro suffixFuel
    have framedDrop :
        Eval.dropUnique (localFuel + suffixFuel) machine.store
            (.loc location) = .ok (targetStore, suffixFuel) :=
      Lower.Sim.dropUnique_add_suffix exactDrop
    have beforeControl :
        ({ machine with heapFuel := localFuel + suffixFuel } :
          Eval.Machine).control = .running frame stack := by
      simpa using control
    exact Eval.Step.dropUnique (context := context)
      (interpretation := interpretation) beforeControl blockAt pcBound
      instruction targetResolved framedDrop
  have sourceRun :
      IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source
          sourceStore source (.dropU sourceAtom) =
        .ok (sourceStore', .erased) := by
    unfold IxIR1.runOp
    simp only
    rw [sourceResolved]
    simp only [bind, Except.bind]
    rw [sourceDropped]
  have canonical := state.target.environments.bindErased
  have nextEnvironments := canonical.forgetTracedErased descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.dropUnique targetAtom) = some .erased by rfl)
  have nextTarget : Lower.Sim.CodeStateRel functionTrace next
      (.erased :: source) { frame with pc := frame.pc + 1 } := by
    refine state.target.letOpNext descendant rfl rfl rfl ?_ rfl
      nextEnvironments
    simp [Lower.Instr.baselineValueDelta]
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨localFuel, targetStore, sourceRun, exactDrop, targetStep, nextStores,
    nextState⟩

/-- Recursive shared destruction selects a sufficient target heap budget,
preserves positive shared reference counts, and advances the combined state. -/
theorem CompiledAttachment.simulate_traced_drop_release_recursive_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next))
    {sourceStore sourceStore' : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next)
      sourceStore source frame)
    (positive : Lower.Sim.PositiveSharedRC sourceStore)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceDropped :
      IxIR1.dropVal sourceContext sourceFuel sourceStore (.loc location) =
        .ok sourceStore')
    (control : machine.control = .running frame stack) :
    ∃ targetHeapFuel targetStore,
      let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
      IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source
            sourceStore source (.drop sourceAtom) =
          .ok (sourceStore', .erased) ∧
        Eval.Step context interpretation
          { machine with heapFuel := targetHeapFuel }
          { store := targetStore
            heapFuel := 0
            control := .running nextFrame stack } ∧
        Lower.Sim.StoreRel sourceStore' targetStore ∧
        Lower.Sim.PositiveSharedRC sourceStore' ∧
        attached.sidecars.TraceStateRel functionTrace next sourceStore'
          (.erased :: source) nextFrame := by
  obtain ⟨targetHeapFuel, targetStore, sourceRun, targetStep, nextStores,
      nextPositive, nextTarget⟩ :=
    Lower.Sim.simulate_traced_drop_release_recursive_state
      (sourceCurrent := functionTrace.source) descendant state.target positive
      stores sourceResolved sourceDropped control
  refine ⟨targetHeapFuel, targetStore, ?_⟩
  dsimp only
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨sourceRun, targetStep, nextStores, nextPositive, nextState⟩

/-- Framed recursive shared destruction.  The local traversal budget is
selected from the successful source drop, while an arbitrary continuation
budget passes through the target work list unchanged. -/
theorem CompiledAttachment.simulate_traced_drop_release_recursive_state_framed
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next))
    {sourceStore sourceStore' : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next)
      sourceStore source frame)
    (positive : Lower.Sim.PositiveSharedRC sourceStore)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceDropped :
      IxIR1.dropVal sourceContext sourceFuel sourceStore (.loc location) =
        .ok sourceStore')
    (control : machine.control = .running frame stack) :
    ∃ localFuel targetStore,
      let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
      IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source
            sourceStore source (.drop sourceAtom) =
          .ok (sourceStore', .erased) ∧
        Eval.releaseShared localFuel machine.store (.loc location) =
          .ok (targetStore, 0) ∧
        (∀ suffixFuel,
          Eval.Step context interpretation
            { machine with heapFuel := localFuel + suffixFuel }
            { store := targetStore
              heapFuel := suffixFuel
              control := .running nextFrame stack }) ∧
        Lower.Sim.StoreRel sourceStore' targetStore ∧
        Lower.Sim.PositiveSharedRC sourceStore' ∧
        attached.sidecars.TraceStateRel functionTrace next sourceStore'
          (.erased :: source) nextFrame := by
  have translated : Lower.Sim.translateAtom input sourceAtom =
      some targetAtom := by
    simpa [Lower.OperationSyntax] using
      functionTrace.descendantOperationSyntax descendant
  obtain ⟨blockAt, pcBound, instructionAt⟩ :=
    state.target.instructionAt descendant
  have instruction :
      next.headBlock.2.instructions[frame.pc] =
        .releaseShared targetAtom :=
    (Array.getElem?_eq_some_iff.mp instructionAt).2
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    Lower.Sim.resolveAtom_of_envRel state.target.environments translated
      sourceResolved
  obtain ⟨localFuel, targetStore, targetRun, nextStores, nextPositive⟩ :=
    Lower.Sim.dropVal_simulates_releaseSharedWork positive stores sourceDropped
  have exactRelease :
      Eval.releaseShared localFuel machine.store (.loc location) =
        .ok (targetStore, 0) := by
    simpa [Eval.releaseShared] using targetRun
  have targetStep : ∀ suffixFuel,
      Eval.Step context interpretation
        { machine with heapFuel := localFuel + suffixFuel }
        { store := targetStore
          heapFuel := suffixFuel
          control := .running { frame with pc := frame.pc + 1 } stack } := by
    intro suffixFuel
    have framedRelease :
        Eval.releaseShared (localFuel + suffixFuel) machine.store
            (.loc location) = .ok (targetStore, suffixFuel) :=
      Lower.Sim.releaseShared_add_suffix exactRelease
    have beforeControl :
        ({ machine with heapFuel := localFuel + suffixFuel } :
          Eval.Machine).control = .running frame stack := by
      simpa using control
    exact Eval.Step.releaseShared (context := context)
      (interpretation := interpretation) beforeControl blockAt pcBound
      instruction targetResolved framedRelease
  have sourceRun :
      IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source
          sourceStore source (.drop sourceAtom) =
        .ok (sourceStore', .erased) := by
    unfold IxIR1.runOp
    simp only
    rw [sourceResolved]
    simp only [bind, Except.bind]
    rw [sourceDropped]
  have canonical := state.target.environments.bindErased
  have nextEnvironments := canonical.forgetTracedErased descendant
    (show Lower.Instr.baselineBinderAtom entryValueCount
      (.releaseShared targetAtom) = some .erased by rfl)
  have nextTarget : Lower.Sim.CodeStateRel functionTrace next
      (.erased :: source) { frame with pc := frame.pc + 1 } := by
    refine state.target.letOpNext descendant rfl rfl rfl ?_ rfl
      nextEnvironments
    simp [Lower.Instr.baselineValueDelta]
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨localFuel, targetStore, sourceRun, exactRelease, targetStep, nextStores,
    nextPositive, nextState⟩

/-- A strictly under-saturated function partial application allocates the
matched PAP node and advances the attachment's combined recursive state. -/
theorem CompiledAttachment.simulate_traced_papp_fn_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {targetDefinition : Function}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {sourceDefinition : IxIR1.FnDef}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAddress targetAddress : Ixon.Address}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.papp sourceAddress sourceArguments) index
        (.papp targetAddress targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.papp sourceAddress sourceArguments) index
        (.papp targetAddress targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceDeclaration :
      sourceContext.decls sourceAddress = some (.fn sourceDefinition))
    (targetDeclaration :
      context.declarations sourceAddress = some (.fn targetDefinition))
    (arity :
      targetDefinition.signature.params.size = sourceDefinition.arity)
    (papSafe : targetDefinition.signature.papSafe = true)
    (under : values.length < sourceDefinition.arity)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let node := IxIR1.Node.papN sourceAddress sourceDefinition.arity
      values.toArray
    let sourceAllocation := sourceStore.allocNode .shared node
    let targetAllocation := machine.store.allocNode .shared node
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push (.loc sourceAllocation.2) }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source sourceStore
          source (.papp sourceAddress sourceArguments) =
        .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
      Eval.Step context interpretation machine
        { machine with
          store := targetAllocation.1
          control := .running nextFrame stack } ∧
      Lower.Sim.StoreRel sourceAllocation.1 targetAllocation.1 ∧
      attached.sidecars.TraceStateRel functionTrace next sourceAllocation.1
        (.loc sourceAllocation.2 :: source) nextFrame := by
  dsimp only
  obtain ⟨sourceRun, targetStep, nextStores, nextTarget⟩ :=
    Lower.Sim.simulate_traced_papp_fn_state
      (sourceCurrent := functionTrace.source) descendant state.target stores
      sourceResolved sourceDeclaration targetDeclaration arity papSafe under
      noCredits control
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨sourceRun, targetStep, nextStores, nextState⟩

/-! ## Combined dynamic-application transitions -/

/-- Any successful dynamic-application transfer advances the attachment's
combined caller continuation.  The target dispatcher supplies the emitted
step and its future caller `CodeStateRel`; the completed source operation
advances the exact HPT coordinate and environment. -/
theorem CompiledAttachment.simulate_traced_apply_transfer_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine target : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {sourceStore outputStore : IxIR1.Store}
    {source : List IxIR1.RVal} {function : IxIR1.RVal}
    {values : List IxIR1.RVal} {value : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frame)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceFunctionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok function)
    (sourceArgumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceRun : IxIR1.runOp sourceContext sourceFuel functionTrace.source
      sourceStore source (.apply sourceFunction sourceArguments) =
        .ok (outputStore, value))
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack)
    (transferred : Eval.ApplyTransfer context interpretation machine.store
      machine.heapFuel function values.toArray
      { frame with pc := frame.pc + 1 } stack target) :
    Eval.Step context interpretation machine target ∧
      attached.sidecars.TraceStateRel functionTrace next outputStore
        (value :: source)
        { frame with
          pc := frame.pc + 1
          values := frame.values.push value } := by
  obtain ⟨targetStep, nextTargets⟩ :=
    Lower.Sim.simulate_traced_apply_transfer_state descendant state.target
      sourceFunctionResolved sourceArgumentsResolved noCredits control
      transferred
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun (nextTargets value)
  exact ⟨targetStep, nextState⟩

/-- Applying an erased function releases the resolved residual arguments and
advances the emitted `apply` instruction directly to the combined caller
continuation with an erased result. -/
theorem CompiledAttachment.simulate_traced_apply_erased_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {sourceStore sourceReleased : IxIR1.Store}
    {source : List IxIR1.RVal} {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (positive : Lower.Sim.PositiveSharedRC sourceStore)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok .erased)
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceRelease : IxIR1.dropMany sourceContext sourceFuel sourceStore
      values = .ok sourceReleased)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    ∃ (targetHeapFuel : Nat) (targetReleased : Eval.Store),
      IxIR1.runOp sourceContext (sourceFuel + 2) functionTrace.source
          sourceStore source (.apply sourceFunction sourceArguments) =
          .ok (sourceReleased, .erased) ∧
        Eval.Step context interpretation
          { machine with heapFuel := targetHeapFuel }
          { store := targetReleased
            heapFuel := 0
            control := .running
              { frame with
                pc := frame.pc + 1
                values := frame.values.push .erased } stack } ∧
        Lower.Sim.StoreRel sourceReleased targetReleased ∧
        Lower.Sim.PositiveSharedRC sourceReleased ∧
        attached.sidecars.TraceStateRel functionTrace next sourceReleased
          (.erased :: source)
          { frame with
            pc := frame.pc + 1
            values := frame.values.push .erased } := by
  obtain ⟨targetHeapFuel, targetReleased, sourceApply, transferred,
      nextStores, nextPositive⟩ :=
    Lower.Sim.simulate_applyGo_erased
      (resume := { frame with pc := frame.pc + 1 }) (stack := stack)
      positive stores sourceRelease
  have sourceRun :
      IxIR1.runOp sourceContext (sourceFuel + 2) functionTrace.source
          sourceStore source (.apply sourceFunction sourceArguments) =
          .ok (sourceReleased, .erased) := by
    rw [IxIR1.runOp.eq_def]
    dsimp only
    rw [functionResolved]
    simp only [bind, Except.bind]
    rw [argumentsResolved]
    exact sourceApply
  have beforeControl :
      ({ machine with heapFuel := targetHeapFuel } : Eval.Machine).control =
        .running frame stack := by
    simpa using control
  obtain ⟨targetStep, nextState⟩ :=
    attached.simulate_traced_apply_transfer_state functionMember descendant
      state sourceDeclarations functionResolved argumentsResolved sourceRun
      noCredits beforeControl transferred
  exact ⟨targetHeapFuel, targetReleased, sourceRun, targetStep, nextStores,
    nextPositive, nextState⟩

/-- Under-saturating a shared PAP completes in the dispatcher itself and
therefore advances directly to the caller's combined continuation state. -/
theorem CompiledAttachment.simulate_traced_apply_pap_under_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (positive : Lower.Sim.PositiveSharedRC sourceStore)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok (.loc location))
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalUnder : (captured.toList ++ values).length < arity)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let pap := IxIR1.Node.papN address arity (captured ++ values.toArray)
    let sourceAllocation := sourceReleased.allocNode .shared pap
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany machine.store captured targetRetained ∧
        Lower.Sim.StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        Lower.Sim.StoreRel sourceReleased targetReleased ∧
        let targetAllocation := targetReleased.allocNode .shared pap
        IxIR1.runOp sourceContext (sourceFuel + 2) functionTrace.source
            sourceStore source (.apply sourceFunction sourceArguments) =
            .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
          Eval.Step context interpretation
            { machine with heapFuel := targetHeapFuel }
            { store := targetAllocation.1
              heapFuel := 0
              control := .running
                { frame with
                  pc := frame.pc + 1
                  values := frame.values.push (.loc sourceAllocation.2) }
                stack } ∧
          Lower.Sim.StoreRel sourceAllocation.1 targetAllocation.1 ∧
          attached.sidecars.TraceStateRel functionTrace next
            sourceAllocation.1 (.loc sourceAllocation.2 :: source)
            { frame with
              pc := frame.pc + 1
              values := frame.values.push (.loc sourceAllocation.2) } := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores, sourceRun, transferred,
      nextStores⟩ :=
    Lower.Sim.simulate_apply_pap_under
      (sourceCurrent := functionTrace.source)
      (resume := { frame with pc := frame.pc + 1 })
      (stack := stack) stores positive functionResolved argumentsResolved
        sourceGet shared node capturedUnder sourceRetain sourceRelease
        totalUnder
  have beforeControl :
      ({ machine with heapFuel := targetHeapFuel } : Eval.Machine).control =
        .running frame stack := by
    simpa using control
  obtain ⟨targetStep, nextState⟩ :=
    attached.simulate_traced_apply_transfer_state functionMember descendant
      state sourceDeclarations functionResolved argumentsResolved sourceRun
      noCredits beforeControl transferred
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceRun, targetStep,
    nextStores, nextState⟩

/-- Exact PAP saturation enters the retained callee in the combined state.
The suspended caller continuation is returned as a builder indexed by the
eventual successful source application, which is precisely the recursive
callee-result handoff needed by the whole-code induction. -/
theorem CompiledAttachment.simulate_traced_apply_pap_saturated_enter_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    (callerMember : callerTrace ∈ attached.target.artifact.trace.functions)
    (calleeMember : calleeTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : callerTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel callerTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (positive : Lower.Sim.PositiveSharedRC sourceStore)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok (.loc location))
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalExact : (captured.toList ++ values).length = arity)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition))
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let sourceTotal := captured.toList ++ values
    let targetTotal := captured ++ values.toArray
    let resume : Eval.Frame := { frame with pc := frame.pc + 1 }
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := targetTotal }
    let targetMachine : Eval.Machine :=
      { store := machine.store
        heapFuel := 0
        control := .running calleeFrame (.resume resume :: stack) }
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany machine.store captured targetRetained ∧
        Lower.Sim.StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        Lower.Sim.StoreRel sourceReleased targetReleased ∧
        IxIR1.runOp sourceContext (sourceFuel + 2) callerTrace.source
            sourceStore source (.apply sourceFunction sourceArguments) =
          IxIR1.invoke sourceContext sourceFuel address sourceTotal
            sourceReleased ∧
        Eval.Step context interpretation
          { machine with heapFuel := targetHeapFuel }
          { targetMachine with store := targetReleased } ∧
        attached.sidecars.TraceStateRel calleeTrace calleeTrace.root
          sourceReleased sourceTotal.reverse calleeFrame ∧
        ∀ (outputStore : IxIR1.Store) (value : IxIR1.RVal),
          IxIR1.runOp sourceContext (sourceFuel + 2) callerTrace.source
              sourceStore source (.apply sourceFunction sourceArguments) =
              .ok (outputStore, value) →
            attached.sidecars.TraceStateRel callerTrace next outputStore
              (value :: source)
              { frame with
                pc := frame.pc + 1
                values := frame.values.push value } := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores, sourceEquation,
      targetStep, _, callerTargets⟩ :=
    Lower.Sim.simulate_traced_apply_pap_saturated_enter_state
      (sourceCurrent := callerTrace.source) descendant calleeMatch state.target
      stores positive functionResolved argumentsResolved sourceGet shared node
      capturedUnder sourceRetain sourceRelease totalExact papArity
      sourceDeclaration sourcePapSafe targetDeclaration noCredits control
  have entryArity :
      (captured ++ values.toArray).size = calleeTrace.source.arity := by
    calc
      (captured ++ values.toArray).size =
          (captured.toList ++ values).length := by simp
      _ = arity := totalExact
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
  have calleeState := attached.functionEntryTraceState
    (sourceStore := sourceReleased) calleeMember
      (captured ++ values.toArray) entryArity
  have combinedCallee : attached.sidecars.TraceStateRel calleeTrace
      calleeTrace.root sourceReleased (captured.toList ++ values).reverse
      { definition := targetDefinition
        values := captured ++ values.toArray } := by
    simpa [calleeMatch.generated] using calleeState
  have callerContinuation :
      ∀ (outputStore : IxIR1.Store) (value : IxIR1.RVal),
        IxIR1.runOp sourceContext (sourceFuel + 2) callerTrace.source
            sourceStore source (.apply sourceFunction sourceArguments) =
            .ok (outputStore, value) →
          attached.sidecars.TraceStateRel callerTrace next outputStore
            (value :: source)
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value } := by
    intro outputStore value sourceRun
    exact attached.traceState_next_of_member callerMember state descendant
      sourceDeclarations sourceRun (callerTargets value)
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceEquation, targetStep,
    combinedCallee, callerContinuation⟩

/-- Over-saturating a shared PAP enters the first retained callee in the
combined state and preserves the exact residual argument vector for the
`applyMore` continuation.  As in exact saturation, successful completion of
the whole source operation builds the original caller's combined successor. -/
theorem CompiledAttachment.simulate_traced_apply_pap_over_enter_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    (callerMember : callerTrace ∈ attached.target.artifact.trace.functions)
    (calleeMember : calleeTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : callerTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel callerTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (positive : Lower.Sim.PositiveSharedRC sourceStore)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok (.loc location))
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalOver : arity < (captured.toList ++ values).length)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition))
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let sourceTotal := captured.toList ++ values
    let sourceSupplied := sourceTotal.take arity
    let sourceRemaining := sourceTotal.drop arity
    let targetTotal := captured ++ values.toArray
    let targetSupplied := targetTotal.extract 0 arity
    let targetRemaining := targetTotal.extract arity targetTotal.size
    let resume : Eval.Frame := { frame with pc := frame.pc + 1 }
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := targetSupplied }
    let targetMachine : Eval.Machine :=
      { store := machine.store
        heapFuel := 0
        control := .running calleeFrame
          (.applyMore targetRemaining resume :: stack) }
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany machine.store captured targetRetained ∧
        Lower.Sim.StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        Lower.Sim.StoreRel sourceReleased targetReleased ∧
        IxIR1.runOp sourceContext (sourceFuel + 2) callerTrace.source
            sourceStore source (.apply sourceFunction sourceArguments) =
          (do
            let (nextStore, result) ←
              IxIR1.invoke sourceContext sourceFuel address sourceSupplied
                sourceReleased
            IxIR1.applyGo sourceContext sourceFuel nextStore result
              sourceRemaining) ∧
        Eval.Step context interpretation
          { machine with heapFuel := targetHeapFuel }
          { targetMachine with store := targetReleased } ∧
        targetRemaining.toList = sourceRemaining ∧
        attached.sidecars.TraceStateRel calleeTrace calleeTrace.root
          sourceReleased sourceSupplied.reverse calleeFrame ∧
        ∀ (outputStore : IxIR1.Store) (value : IxIR1.RVal),
          IxIR1.runOp sourceContext (sourceFuel + 2) callerTrace.source
              sourceStore source (.apply sourceFunction sourceArguments) =
              .ok (outputStore, value) →
            attached.sidecars.TraceStateRel callerTrace next outputStore
              (value :: source)
              { frame with
                pc := frame.pc + 1
                values := frame.values.push value } := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores, sourceEquation,
      targetStep, remainingEq, _, callerTargets⟩ :=
    Lower.Sim.simulate_traced_apply_pap_over_enter_state
      (sourceCurrent := callerTrace.source) descendant calleeMatch state.target
      stores positive functionResolved argumentsResolved sourceGet shared node
      capturedUnder sourceRetain sourceRelease totalOver papArity
      sourceDeclaration sourcePapSafe targetDeclaration noCredits control
  let sourceTotal := captured.toList ++ values
  let sourceSupplied := sourceTotal.take arity
  let targetTotal := captured ++ values.toArray
  let targetSupplied := targetTotal.extract 0 arity
  have totalArrayEq : sourceTotal.toArray = targetTotal := by
    apply Array.toList_inj.mp
    simp [sourceTotal, targetTotal]
  have suppliedArrayEq : targetSupplied = sourceSupplied.toArray := by
    calc
      targetSupplied = targetTotal.take arity := Array.take_eq_extract.symm
      _ = sourceTotal.toArray.take arity := by rw [totalArrayEq]
      _ = sourceSupplied.toArray := List.take_toArray
  have targetOver : arity < targetTotal.size := by
    simpa [sourceTotal, targetTotal] using totalOver
  have suppliedSize : targetSupplied.size = arity := by
    simp [targetSupplied, Array.size_extract]
    omega
  have entryArity : targetSupplied.size = calleeTrace.source.arity := by
    calc
      targetSupplied.size = arity := suppliedSize
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
  have calleeState := attached.functionEntryTraceState
    (sourceStore := sourceReleased) calleeMember targetSupplied entryArity
  have sourceEnvironment :
      targetSupplied.toList.reverse = sourceSupplied.reverse := by
    rw [suppliedArrayEq]
  rw [sourceEnvironment] at calleeState
  have combinedCallee : attached.sidecars.TraceStateRel calleeTrace
      calleeTrace.root sourceReleased sourceSupplied.reverse
      { definition := targetDefinition, values := targetSupplied } := by
    simpa [calleeMatch.generated] using calleeState
  have callerContinuation :
      ∀ (outputStore : IxIR1.Store) (value : IxIR1.RVal),
        IxIR1.runOp sourceContext (sourceFuel + 2) callerTrace.source
            sourceStore source (.apply sourceFunction sourceArguments) =
            .ok (outputStore, value) →
          attached.sidecars.TraceStateRel callerTrace next outputStore
            (value :: source)
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value } := by
    intro outputStore value sourceRun
    exact attached.traceState_next_of_member callerMember state descendant
      sourceDeclarations sourceRun (callerTargets value)
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceEquation, targetStep,
    remainingEq, combinedCallee, callerContinuation⟩

/-! ## Combined call-stack transitions -/

/-- An addressed source call enters the matched retained declaration in the
combined source/HPT/target state.  Whole-trace attachment alignment recovers
the callee's exact HPT root. -/
theorem CompiledAttachment.simulate_traced_call_fn_enter_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace calleeTrace : Lower.FunctionTrace}
    (calleeMember : calleeTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAddress targetAddress : Ixon.Address}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration sourceAddress) sourceDefinition targetDefinition)
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : sourceDefinition.arity = values.length)
    (declaration :
      context.declarations sourceAddress = some (.fn targetDefinition))
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := values.toArray }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source
          sourceStore source (.call sourceAddress sourceArguments) =
        IxIR1.invoke sourceContext sourceFuel sourceAddress values sourceStore ∧
      Eval.Step context interpretation machine
        { machine with
          control := .running calleeFrame
            (.resume { frame with pc := frame.pc + 1 } :: stack) } ∧
      Lower.Sim.StoreRel sourceStore machine.store ∧
      attached.sidecars.TraceStateRel calleeTrace calleeTrace.root sourceStore
        values.reverse calleeFrame := by
  dsimp only
  obtain ⟨sourceEquation, targetStep, nextStores, _⟩ :=
    Lower.Sim.simulate_traced_call_fn_enter_source_state
      (sourceContext := sourceContext) (sourceFuel := sourceFuel)
      (context := context) (interpretation := interpretation)
      descendant calleeMatch state.target stores sourceResolved argumentArity
        declaration noCredits control
  have entryArity : values.toArray.size = calleeTrace.source.arity := by
    simpa [calleeMatch.source] using argumentArity.symm
  have calleeState := attached.functionEntryTraceState
    (sourceStore := sourceStore) calleeMember values.toArray entryArity
  exact ⟨sourceEquation, targetStep, nextStores, by
    simpa [calleeMatch.generated] using calleeState⟩

/-- A recursive self-call in any retained function enters the same trace root
in the combined state while preserving the suspended caller continuation. -/
theorem CompiledAttachment.simulate_traced_call_self_enter_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : functionTrace.source.arity = values.length)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := frame.definition, values := values.toArray }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source
          sourceStore source (.callSelf sourceArguments) = (do
        let out ← IxIR1.runCode sourceContext sourceFuel functionTrace.source
          sourceStore values.reverse functionTrace.source.body
        IxIR1.checkResultWorld functionTrace.source.result out) ∧
      Eval.Step context interpretation machine
        { machine with
          control := .running calleeFrame
            (.resume { frame with pc := frame.pc + 1 } :: stack) } ∧
      Lower.Sim.StoreRel sourceStore machine.store ∧
      attached.sidecars.TraceStateRel functionTrace functionTrace.root
        sourceStore values.reverse calleeFrame := by
  dsimp only
  obtain ⟨sourceEquation, targetStep, nextStores, _⟩ :=
    Lower.Sim.simulate_traced_call_self_enter_source_state
      (sourceContext := sourceContext) (sourceFuel := sourceFuel)
      (context := context) (interpretation := interpretation)
      descendant state.target stores sourceResolved argumentArity noCredits
        control
  have entryArity : values.toArray.size = functionTrace.source.arity := by
    simpa using argumentArity.symm
  have calleeState := attached.functionEntryTraceState
    (sourceStore := sourceStore) functionMember values.toArray entryArity
  exact ⟨sourceEquation, targetStep, nextStores, by
    simpa [state.target.definition] using calleeState⟩

/-- An addressed tail call transfers directly into the matched declaration's
combined root state without retaining a caller continuation. -/
theorem CompiledAttachment.simulate_traced_tail_call_fn_enter_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace calleeTrace : Lower.FunctionTrace}
    (calleeMember : calleeTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {address : Ixon.Address} {sourceArguments : Array IxIR1.Atom}
    {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated) sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : sourceDefinition.arity = values.length)
    (declaration :
      context.declarations address = some (.fn targetDefinition))
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := values.toArray }
    IxIR1.runCode sourceContext (sourceFuel + 2) functionTrace.source
          sourceStore source
          (.letOp (.call address sourceArguments) (.ret (.var 0))) =
        IxIR1.invoke sourceContext sourceFuel address values sourceStore ∧
      Eval.Step context interpretation machine
        { machine with control := .running calleeFrame stack } ∧
      Lower.Sim.StoreRel sourceStore machine.store ∧
      attached.sidecars.TraceStateRel calleeTrace calleeTrace.root sourceStore
        values.reverse calleeFrame := by
  dsimp only
  obtain ⟨sourceEquation, targetStep, nextStores, _⟩ :=
    Lower.Sim.simulate_traced_tail_call_fn_enter_source_state
      (sourceContext := sourceContext) (sourceFuel := sourceFuel)
      (context := context) (interpretation := interpretation)
      descendant calleeMatch state.target stores sourceResolved argumentArity
        declaration noCredits control
  have entryArity : values.toArray.size = calleeTrace.source.arity := by
    simpa [calleeMatch.source] using argumentArity.symm
  have calleeState := attached.functionEntryTraceState
    (sourceStore := sourceStore) calleeMember values.toArray entryArity
  exact ⟨sourceEquation, targetStep, nextStores, by
    simpa [calleeMatch.generated] using calleeState⟩

/-- A self-tail-call in any retained function re-enters its own combined root
state while preserving the existing continuation stack. -/
theorem CompiledAttachment.simulate_traced_tail_call_self_enter_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceArguments : Array IxIR1.Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated) sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : functionTrace.source.arity = values.length)
    (noCredits : frame.credits = #[])
    (control : machine.control = .running frame stack) :
    let calleeFrame : Eval.Frame :=
      { definition := frame.definition, values := values.toArray }
    IxIR1.runCode sourceContext (sourceFuel + 2) functionTrace.source
          sourceStore source
          (.letOp (.callSelf sourceArguments) (.ret (.var 0))) = (do
        let out ← IxIR1.runCode sourceContext sourceFuel functionTrace.source
          sourceStore values.reverse functionTrace.source.body
        IxIR1.checkResultWorld functionTrace.source.result out) ∧
      Eval.Step context interpretation machine
        { machine with control := .running calleeFrame stack } ∧
      Lower.Sim.StoreRel sourceStore machine.store ∧
      attached.sidecars.TraceStateRel functionTrace functionTrace.root
        sourceStore values.reverse calleeFrame := by
  dsimp only
  obtain ⟨sourceEquation, targetStep, nextStores, _⟩ :=
    Lower.Sim.simulate_traced_tail_call_self_enter_source_state
      (sourceContext := sourceContext) (sourceFuel := sourceFuel)
      (context := context) (interpretation := interpretation)
      descendant state.target stores sourceResolved argumentArity noCredits
        control
  have entryArity : values.toArray.size = functionTrace.source.arity := by
    simpa using argumentArity.symm
  have calleeState := attached.functionEntryTraceState
    (sourceStore := sourceStore) functionMember values.toArray entryArity
  exact ⟨sourceEquation, targetStep, nextStores, by
    simpa [state.target.definition] using calleeState⟩

/-- A successful callee return under `applyMore` performs one target
redispatch step from the combined callee state.  Source return inversion and
the retained result contract discharge atom resolution and the evaluator's
dynamic world check; the supplied `ApplyTransfer` selects the next PAP branch. -/
theorem CompiledAttachment.simulate_traced_ret_apply_more_success
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine target : Eval.Machine} {frame caller : Eval.Frame}
    {arguments : Array IxIR1.RVal} {rest : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {sourceOutput : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 1)
      functionTrace.source sourceStore source (.ret sourceAtom) =
        .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control =
      .running frame (.applyMore arguments caller :: rest))
    (noCredits : frame.credits = #[])
    (transferred : Eval.ApplyTransfer context interpretation machine.store
      machine.heapFuel sourceOutput.2 arguments caller rest target) :
    ∃ value,
      sourceOutput = (sourceStore, value) ∧
        Eval.Steps context interpretation 1 machine target ∧
        Lower.Sim.StoreRel sourceStore machine.store := by
  obtain ⟨value, sourceResolved, outputEq⟩ :=
    IxIR1.runCode_ret_success sourceRun
  subst sourceOutput
  have targetWorld := state.target.resultWorld stores resultWorld
  obtain ⟨_, targetSteps, nextStores⟩ :=
    Lower.Sim.simulate_traced_ret_apply_more_state
      (sourceContext := sourceContext)
      (sourceCurrent := functionTrace.source) (sourceFuel := sourceFuel)
      descendant state.target stores sourceResolved control noCredits
        targetWorld transferred
  exact ⟨value, rfl, targetSteps, nextStores⟩

/-- Returning a PAP into `applyMore` at exact saturation enters the next
retained callee in one target step and establishes its full combined root
state.  This is the recursive exact-saturation handoff for over-application
chains. -/
theorem CompiledAttachment.simulate_traced_ret_apply_more_pap_saturated_enter_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {returnFuel applyFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame caller : Eval.Frame}
    {rest : List Eval.Continuation}
    {returningTrace calleeTrace : Lower.FunctionTrace}
    (calleeMember : calleeTrace ∈ attached.target.artifact.trace.functions)
    {returnSite : Lower.SourceSite} {returnBlock : BlockId}
    {returnInput : Lower.Sim.EnvMap} {returnEntryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {returnGenerated : Block}
    (returnDescendant : returningTrace.root.Descendant
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel returningTrace
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated) sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (positive : Lower.Sim.PositiveSharedRC sourceStore)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (resultWorld : IxIR1.Sim.HasWorld sourceStore
      returningTrace.source.result (.loc location))
    (control : machine.control =
      .running frame (.applyMore values.toArray caller :: rest))
    (noCredits : frame.credits = #[])
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext applyFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalExact : (captured.toList ++ values).length = arity)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition)) :
    let sourceTotal := captured.toList ++ values
    let targetTotal := captured ++ values.toArray
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := targetTotal }
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany machine.store captured targetRetained ∧
        Lower.Sim.StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        Lower.Sim.StoreRel sourceReleased targetReleased ∧
        IxIR1.runCode sourceContext (returnFuel + 1) returningTrace.source
            sourceStore source (.ret sourceAtom) =
            .ok (sourceStore, .loc location) ∧
        IxIR1.applyGo sourceContext (applyFuel + 1) sourceStore
            (.loc location) values =
          IxIR1.invoke sourceContext applyFuel address sourceTotal
            sourceReleased ∧
        Eval.Steps context interpretation 1
          { machine with heapFuel := targetHeapFuel }
          { store := targetReleased
            heapFuel := 0
            control := .running calleeFrame (.resume caller :: rest) } ∧
        attached.sidecars.TraceStateRel calleeTrace calleeTrace.root
          sourceReleased sourceTotal.reverse calleeFrame := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores, sourceApply, transferred,
      _⟩ :=
    Lower.Sim.simulate_applyGo_pap_saturated_enter
      (resume := caller) (stack := rest) calleeMatch stores positive sourceGet
      shared node capturedUnder sourceRetain sourceRelease totalExact papArity
      sourceDeclaration sourcePapSafe targetDeclaration
  have beforeControl :
      ({ machine with heapFuel := targetHeapFuel } : Eval.Machine).control =
        .running frame (.applyMore values.toArray caller :: rest) := by
    simpa using control
  have targetWorld := state.target.resultWorld stores resultWorld
  obtain ⟨sourceReturn, targetSteps, _⟩ :=
    Lower.Sim.simulate_traced_ret_apply_more_state
      (sourceContext := sourceContext)
      (sourceCurrent := returningTrace.source) (sourceFuel := returnFuel)
      (machine := { machine with heapFuel := targetHeapFuel })
      returnDescendant state.target stores sourceResolved beforeControl
        noCredits targetWorld transferred
  have entryArity :
      (captured ++ values.toArray).size = calleeTrace.source.arity := by
    calc
      (captured ++ values.toArray).size =
          (captured.toList ++ values).length := by simp
      _ = arity := totalExact
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
  have calleeState := attached.functionEntryTraceState
    (sourceStore := sourceReleased) calleeMember
      (captured ++ values.toArray) entryArity
  have combinedCallee : attached.sidecars.TraceStateRel calleeTrace
      calleeTrace.root sourceReleased (captured.toList ++ values).reverse
      { definition := targetDefinition
        values := captured ++ values.toArray } := by
    simpa [calleeMatch.generated] using calleeState
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceReturn, sourceApply,
    targetSteps, combinedCallee⟩

/-- Returning a PAP into `applyMore` with excess residual arguments enters
the next retained callee in the combined state and installs another exact
`applyMore` suffix.  This is the recursive over-saturation handoff. -/
theorem CompiledAttachment.simulate_traced_ret_apply_more_pap_over_enter_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {returnFuel applyFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame caller : Eval.Frame}
    {rest : List Eval.Continuation}
    {returningTrace calleeTrace : Lower.FunctionTrace}
    (calleeMember : calleeTrace ∈ attached.target.artifact.trace.functions)
    {returnSite : Lower.SourceSite} {returnBlock : BlockId}
    {returnInput : Lower.Sim.EnvMap} {returnEntryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {returnGenerated : Block}
    (returnDescendant : returningTrace.root.Descendant
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel returningTrace
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated) sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (positive : Lower.Sim.PositiveSharedRC sourceStore)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (resultWorld : IxIR1.Sim.HasWorld sourceStore
      returningTrace.source.result (.loc location))
    (control : machine.control =
      .running frame (.applyMore values.toArray caller :: rest))
    (noCredits : frame.credits = #[])
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext applyFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalOver : arity < (captured.toList ++ values).length)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition)) :
    let sourceTotal := captured.toList ++ values
    let sourceSupplied := sourceTotal.take arity
    let sourceRemaining := sourceTotal.drop arity
    let targetTotal := captured ++ values.toArray
    let targetSupplied := targetTotal.extract 0 arity
    let targetRemaining := targetTotal.extract arity targetTotal.size
    let calleeFrame : Eval.Frame :=
      { definition := targetDefinition, values := targetSupplied }
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany machine.store captured targetRetained ∧
        Lower.Sim.StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        Lower.Sim.StoreRel sourceReleased targetReleased ∧
        IxIR1.runCode sourceContext (returnFuel + 1) returningTrace.source
            sourceStore source (.ret sourceAtom) =
            .ok (sourceStore, .loc location) ∧
        IxIR1.applyGo sourceContext (applyFuel + 1) sourceStore
            (.loc location) values =
          (do
            let (nextStore, result) ←
              IxIR1.invoke sourceContext applyFuel address sourceSupplied
                sourceReleased
            IxIR1.applyGo sourceContext applyFuel nextStore result
              sourceRemaining) ∧
        Eval.Steps context interpretation 1
          { machine with heapFuel := targetHeapFuel }
          { store := targetReleased
            heapFuel := 0
            control := .running calleeFrame
              (.applyMore targetRemaining caller :: rest) } ∧
        targetRemaining.toList = sourceRemaining ∧
        attached.sidecars.TraceStateRel calleeTrace calleeTrace.root
          sourceReleased sourceSupplied.reverse calleeFrame := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores, sourceApply, transferred,
      remainingEq, _⟩ :=
    Lower.Sim.simulate_applyGo_pap_over_enter
      (resume := caller) (stack := rest) calleeMatch stores positive sourceGet
      shared node capturedUnder sourceRetain sourceRelease totalOver papArity
      sourceDeclaration sourcePapSafe targetDeclaration
  have beforeControl :
      ({ machine with heapFuel := targetHeapFuel } : Eval.Machine).control =
        .running frame (.applyMore values.toArray caller :: rest) := by
    simpa using control
  have targetWorld := state.target.resultWorld stores resultWorld
  obtain ⟨sourceReturn, targetSteps, _⟩ :=
    Lower.Sim.simulate_traced_ret_apply_more_state
      (sourceContext := sourceContext)
      (sourceCurrent := returningTrace.source) (sourceFuel := returnFuel)
      (machine := { machine with heapFuel := targetHeapFuel })
      returnDescendant state.target stores sourceResolved beforeControl
        noCredits targetWorld transferred
  let sourceTotal := captured.toList ++ values
  let sourceSupplied := sourceTotal.take arity
  let targetTotal := captured ++ values.toArray
  let targetSupplied := targetTotal.extract 0 arity
  have totalArrayEq : sourceTotal.toArray = targetTotal := by
    apply Array.toList_inj.mp
    simp [sourceTotal, targetTotal]
  have suppliedArrayEq : targetSupplied = sourceSupplied.toArray := by
    calc
      targetSupplied = targetTotal.take arity := Array.take_eq_extract.symm
      _ = sourceTotal.toArray.take arity := by rw [totalArrayEq]
      _ = sourceSupplied.toArray := List.take_toArray
  have targetOver : arity < targetTotal.size := by
    simpa [sourceTotal, targetTotal] using totalOver
  have suppliedSize : targetSupplied.size = arity := by
    simp [targetSupplied, Array.size_extract]
    omega
  have entryArity : targetSupplied.size = calleeTrace.source.arity := by
    calc
      targetSupplied.size = arity := suppliedSize
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
  have calleeState := attached.functionEntryTraceState
    (sourceStore := sourceReleased) calleeMember targetSupplied entryArity
  have sourceEnvironment :
      targetSupplied.toList.reverse = sourceSupplied.reverse := by
    rw [suppliedArrayEq]
  rw [sourceEnvironment] at calleeState
  have combinedCallee : attached.sidecars.TraceStateRel calleeTrace
      calleeTrace.root sourceReleased sourceSupplied.reverse
      { definition := targetDefinition, values := targetSupplied } := by
    simpa [calleeMatch.generated] using calleeState
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceReturn, sourceApply,
    targetSteps, remainingEq, combinedCallee⟩

/-- Returning a PAP into `applyMore` below saturation extends the PAP and
resumes the waiting caller immediately.  The source and target allocate the
same longer PAP at the related fresh location. -/
theorem CompiledAttachment.simulate_traced_ret_apply_more_pap_under_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {returnFuel applyFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame caller : Eval.Frame}
    {rest : List Eval.Continuation} {returningTrace : Lower.FunctionTrace}
    {returnSite : Lower.SourceSite} {returnBlock : BlockId}
    {returnInput : Lower.Sim.EnvMap} {returnEntryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {returnGenerated : Block}
    (returnDescendant : returningTrace.root.Descendant
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated))
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel returningTrace
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated) sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (positive : Lower.Sim.PositiveSharedRC sourceStore)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (resultWorld : IxIR1.Sim.HasWorld sourceStore
      returningTrace.source.result (.loc location))
    (control : machine.control =
      .running frame (.applyMore values.toArray caller :: rest))
    (noCredits : frame.credits = #[])
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext applyFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalUnder : (captured.toList ++ values).length < arity) :
    let pap := IxIR1.Node.papN address arity (captured ++ values.toArray)
    let sourceAllocation := sourceReleased.allocNode .shared pap
    ∃ (targetRetained targetReleased : Eval.Store) (targetHeapFuel : Nat),
      Eval.RetainSharedMany machine.store captured targetRetained ∧
        Lower.Sim.StoreRel sourceRetained targetRetained ∧
        Eval.releaseSharedWork targetHeapFuel targetRetained [.loc location] =
          .ok (targetReleased, 0) ∧
        Lower.Sim.StoreRel sourceReleased targetReleased ∧
        let targetAllocation := targetReleased.allocNode .shared pap
        IxIR1.runCode sourceContext (returnFuel + 1) returningTrace.source
            sourceStore source (.ret sourceAtom) =
            .ok (sourceStore, .loc location) ∧
          IxIR1.applyGo sourceContext (applyFuel + 1) sourceStore
              (.loc location) values =
              .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
          Eval.Steps context interpretation 1
            { machine with heapFuel := targetHeapFuel }
            { store := targetAllocation.1
              heapFuel := 0
              control := .running
                { caller with
                  values := caller.values.push (.loc sourceAllocation.2) }
                rest } ∧
          Lower.Sim.StoreRel sourceAllocation.1 targetAllocation.1 := by
  dsimp only
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores, sourceApply, transferred,
      nextStores⟩ :=
    Lower.Sim.simulate_applyGo_pap_under
      (resume := caller) (stack := rest) stores positive sourceGet shared node
      capturedUnder sourceRetain sourceRelease totalUnder
  have beforeControl :
      ({ machine with heapFuel := targetHeapFuel } : Eval.Machine).control =
        .running frame (.applyMore values.toArray caller :: rest) := by
    simpa using control
  have targetWorld := state.target.resultWorld stores resultWorld
  obtain ⟨sourceReturn, targetSteps, _⟩ :=
    Lower.Sim.simulate_traced_ret_apply_more_state
      (sourceContext := sourceContext)
      (sourceCurrent := returningTrace.source) (sourceFuel := returnFuel)
      (machine := { machine with heapFuel := targetHeapFuel })
      returnDescendant state.target stores sourceResolved beforeControl
        noCredits targetWorld transferred
  exact ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
    retainedStores, targetRelease, releasedStores, sourceReturn, sourceApply,
    targetSteps, nextStores⟩

/-- Returning `erased` into `applyMore` releases every residual shared
argument and resumes the waiting caller with `erased`, preserving the exact
store relation and positive shared-reference-count invariant. -/
theorem CompiledAttachment.simulate_traced_ret_apply_more_erased_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {returnFuel applyFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame caller : Eval.Frame}
    {rest : List Eval.Continuation} {returningTrace : Lower.FunctionTrace}
    {returnSite : Lower.SourceSite} {returnBlock : BlockId}
    {returnInput : Lower.Sim.EnvMap} {returnEntryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {returnGenerated : Block}
    (returnDescendant : returningTrace.root.Descendant
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated))
    {sourceStore sourceReleased : IxIR1.Store}
    {source : List IxIR1.RVal} {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel returningTrace
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated) sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (positive : Lower.Sim.PositiveSharedRC sourceStore)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok .erased)
    (resultWorld : IxIR1.Sim.HasWorld sourceStore
      returningTrace.source.result .erased)
    (control : machine.control =
      .running frame (.applyMore values.toArray caller :: rest))
    (noCredits : frame.credits = #[])
    (sourceRelease : IxIR1.dropMany sourceContext applyFuel sourceStore
      values = .ok sourceReleased) :
    ∃ (targetHeapFuel : Nat) (targetReleased : Eval.Store),
      IxIR1.runCode sourceContext (returnFuel + 1) returningTrace.source
          sourceStore source (.ret sourceAtom) = .ok (sourceStore, .erased) ∧
        IxIR1.applyGo sourceContext (applyFuel + 1) sourceStore .erased values =
          .ok (sourceReleased, .erased) ∧
        Eval.Steps context interpretation 1
          { machine with heapFuel := targetHeapFuel }
          { store := targetReleased
            heapFuel := 0
            control := .running
              { caller with values := caller.values.push .erased } rest } ∧
        Lower.Sim.StoreRel sourceReleased targetReleased ∧
        Lower.Sim.PositiveSharedRC sourceReleased := by
  obtain ⟨targetHeapFuel, targetReleased, sourceApply, transferred,
      nextStores, nextPositive⟩ :=
    Lower.Sim.simulate_applyGo_erased
      (resume := caller) (stack := rest) positive stores sourceRelease
  have beforeControl :
      ({ machine with heapFuel := targetHeapFuel } : Eval.Machine).control =
        .running frame (.applyMore values.toArray caller :: rest) := by
    simpa using control
  have targetWorld := state.target.resultWorld stores resultWorld
  obtain ⟨sourceReturn, targetSteps, _⟩ :=
    Lower.Sim.simulate_traced_ret_apply_more_state
      (sourceContext := sourceContext)
      (sourceCurrent := returningTrace.source) (sourceFuel := returnFuel)
      (machine := { machine with heapFuel := targetHeapFuel })
      returnDescendant state.target stores sourceResolved beforeControl
        noCredits targetWorld transferred
  exact ⟨targetHeapFuel, targetReleased, sourceReturn, sourceApply,
    targetSteps, nextStores, nextPositive⟩

/-- A callee return under an ordinary resume continuation restores the exact
caller continuation in the combined state.  The completed source operation
advances the suspended caller's HPT environment across its `letOp`, while the
target return theorem supplies checked map forgetting and frame progression. -/
theorem CompiledAttachment.simulate_traced_return_to_letOp_state
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel operationFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {calleeFrame callerFrame : Eval.Frame}
    {rest : List Eval.Continuation}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    (callerMember : callerTrace ∈ attached.target.artifact.trace.functions)
    {callSite : Lower.SourceSite} {callBlock : BlockId}
    {callInput nextInput : Lower.Sim.EnvMap}
    {callEntryValueCount callIndex : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    (callerDescendant : callerTrace.root.Descendant
      (.letOp callSite callBlock callInput nextInput callEntryValueCount
        operation callIndex instruction next))
    {returnSite : Lower.SourceSite} {returnBlock : BlockId}
    {returnInput : Lower.Sim.EnvMap} {returnEntryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {generated : Block}
    (calleeDescendant : calleeTrace.root.Descendant
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom generated))
    {callerStore outputStore : IxIR1.Store}
    {calleeSource callerSource : List IxIR1.RVal} {value : IxIR1.RVal}
    (callerState : attached.sidecars.TraceStateRel callerTrace
      (.letOp callSite callBlock callInput nextInput callEntryValueCount
        operation callIndex instruction next)
      callerStore callerSource callerFrame)
    (calleeState : attached.sidecars.TraceStateRel calleeTrace
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom generated) outputStore calleeSource calleeFrame)
    (binder : Lower.Instr.baselineBinderAtom callEntryValueCount instruction =
      some (.reg callEntryValueCount))
    (delta : Lower.Instr.baselineValueDelta instruction = some 1)
    (stores : Lower.Sim.StoreRel outputStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceOperation : IxIR1.runOp sourceContext operationFuel
      callerTrace.source callerStore callerSource operation =
        .ok (outputStore, value))
    (sourceResolved :
      IxIR1.resolveAtom calleeSource sourceAtom = .ok value)
    (control : machine.control = .running calleeFrame
      (.resume { callerFrame with pc := callerFrame.pc + 1 } :: rest))
    (noCredits : calleeFrame.credits = #[])
    (world : Eval.RVal.hasWorld machine.store
      calleeFrame.definition.signature.result value = true) :
    let nextCallerFrame : Eval.Frame :=
      { callerFrame with
        pc := callerFrame.pc + 1
        values := callerFrame.values.push value }
    IxIR1.runCode sourceContext (sourceFuel + 1) calleeTrace.source outputStore
          calleeSource (.ret sourceAtom) = .ok (outputStore, value) ∧
      Eval.Steps context interpretation 1 machine
        { machine with control := .running nextCallerFrame rest } ∧
      Lower.Sim.StoreRel outputStore machine.store ∧
      attached.sidecars.TraceStateRel callerTrace next outputStore
        (value :: callerSource) nextCallerFrame := by
  dsimp only
  obtain ⟨sourceReturn, targetSteps, nextStores, nextTarget⟩ :=
    Lower.Sim.simulate_traced_return_to_letOp_state
      (sourceContext := sourceContext) (sourceCurrent := calleeTrace.source)
      (sourceFuel := sourceFuel) (context := context)
      (interpretation := interpretation) callerDescendant calleeDescendant
      callerState.target calleeState.target binder delta stores sourceResolved
        control noCredits world
  have nextState := attached.traceState_next_of_member callerMember callerState
    callerDescendant sourceDeclarations sourceOperation nextTarget
  exact ⟨sourceReturn, targetSteps, nextStores, nextState⟩

/-- An attached terminal source return halts the target in one step.  The
combined state carries the exact target trace relation and its retained source
result contract supplies the executable target-world check. -/
theorem CompiledAttachment.simulate_traced_ret_halt_success
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {sourceOutput : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 1)
      functionTrace.source sourceStore source (.ret sourceAtom) =
        .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame [])
    (noCredits : frame.credits = #[]) :
    ∃ value,
      sourceOutput = (sourceStore, value) ∧
        Eval.Steps context interpretation 1 machine
          { machine with control := .halted value } ∧
        Lower.Sim.StoreRel sourceStore machine.store := by
  exact Lower.Sim.simulate_traced_ret_halt_success
    (sourceContext := sourceContext) (sourceCurrent := functionTrace.source)
    (sourceFuel := sourceFuel) (context := context)
    (interpretation := interpretation) descendant state.target stores
      sourceRun resultWorld control noCredits

/-- Successful source-case execution expressed in the indexed alternative
vocabulary retained by the compiler trace. -/
inductive IndexedCaseSuccess (ctx : IxIR1.Ctx) (fuel : Nat)
    (cur : IxIR1.FnDef) (store : IxIR1.Store) (env : List IxIR1.RVal)
    (scrutinee : IxIR1.Atom) (peelNat : Bool)
    (alternatives : Array IxIR1.Alt)
    (output : IxIR1.Store × IxIR1.RVal) : Prop
  | ctorBranch {location : Nat} {box : IxIR1.NodeBox}
      {cid : IxIR1.CtorId} {fields : Array IxIR1.RVal}
      {fieldCount alternativeIndex : Nat} {body : IxIR1.Code}
      (resolved : IxIR1.resolveAtom env scrutinee = .ok (.loc location))
      (found : store.get? location = some box)
      (node : box.node = .ctorN cid fields)
      (selected : Lower.sourceAlternativeAtTag? alternatives cid.cidx =
        some (.mk cid.cidx fieldCount body, alternativeIndex))
      (fieldArity : fields.size = fieldCount)
      (branchRun : IxIR1.runCode ctx fuel cur store
        (fields.toList.reverse ++ env) body = .ok output)
  | natZero {alternativeIndex : Nat} {body : IxIR1.Code}
      (peels : peelNat = true)
      (resolved : IxIR1.resolveAtom env scrutinee =
        .ok (.lit (.nat 0)))
      (selected : Lower.sourceAlternativeAtTag? alternatives 0 =
        some (.mk 0 0 body, alternativeIndex))
      (branchRun : IxIR1.runCode ctx fuel cur store env body = .ok output)
  | natSucc {predecessor alternativeIndex : Nat} {body : IxIR1.Code}
      (peels : peelNat = true)
      (resolved : IxIR1.resolveAtom env scrutinee =
        .ok (.lit (.nat (predecessor + 1))))
      (selected : Lower.sourceAlternativeAtTag? alternatives 1 =
        some (.mk 1 1 body, alternativeIndex))
      (branchRun : IxIR1.runCode ctx fuel cur store
        (.lit (.nat predecessor) :: env) body = .ok output)

/-- The exact target-side coordinates needed to enter one emitted
constructor branch.  Keeping the terminator, constructor, edge, and child
lookups in one witness prevents the exhaustive worker from carrying four
independently quantified but necessarily parallel indices. -/
structure ConstructorSwitchSelection (targetScrutinee : Atom)
    (generated : Block) (outgoing : List Lower.EdgeTrace)
    (children : List Lower.CodeTrace) (cid : CtorId) : Type where
  constructors : Array CtorAlt
  targetPeel : Option NatPeel
  index : Nat
  target : CtorAlt
  edge : Lower.EdgeTrace
  child : Lower.CodeTrace
  terminator : generated.terminator =
    .switchValue targetScrutinee constructors targetPeel
  targetAt : constructors[index]? = some target
  targetAlternative : constructors.find? (fun candidate =>
    candidate.cid == cid) = some target
  edgeAt : outgoing[index]? = some edge
  childAt : children[index]? = some child

/-- An exact path-local HPT constructor fact determines a complete emitted
switch selection. Attachment checks provide the identity lookup; recursive
trace coherence supplies the parallel target, edge, and child ordinals. -/
theorem CompiledAttachment.constructorSwitchSelection_of_exactHPT_nonempty
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace} {fact : IxIR1.HPT.Fact}
    {identity : CtorId}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    (selected : attached.sidecars.exactConstructorAt? site sourceScrutinee =
      some (fact, identity)) :
    Nonempty (ConstructorSwitchSelection targetScrutinee generated outgoing
      children identity) := by
  obtain ⟨constructors, targetPeel, _, terminator⟩ :=
    Lower.CodeTrace.switchSyntax_of_match
      (functionTrace.descendantSyntaxMatches descendant)
  obtain ⟨target, targetAlternative⟩ :=
    attached.exactCaseTarget_of_switch_descendant functionMember descendant
      selected terminator
  have targetMember : target ∈ constructors :=
    Array.mem_of_find?_eq_some targetAlternative
  obtain ⟨index, targetAt⟩ :=
    (Array.mem_iff_getElem?).mp targetMember
  have branchMatch := Lower.CodeTrace.switchNodeBranchesMatch_of_match
    (functionTrace.descendantSwitchBranchesMatch descendant)
  have branchMatch' := branchMatch
  unfold Lower.switchNodeBranchesMatch at branchMatch'
  rw [terminator] at branchMatch'
  simp only [Bool.and_eq_true] at branchMatch'
  obtain ⟨⟨⟨outgoingLength, childrenLength⟩, _⟩, _⟩ := branchMatch'
  have targetBound : index < constructors.size :=
    (Array.getElem?_eq_some_iff.mp targetAt).1
  have edgeBound : index < outgoing.length := by
    have lengthEq := beq_iff_eq.mp outgoingLength
    omega
  have childBound : index < children.length := by
    have lengthEq := beq_iff_eq.mp childrenLength
    omega
  let edge := outgoing[index]'edgeBound
  let child := children[index]'childBound
  have edgeAt : outgoing[index]? = some edge :=
    List.getElem?_eq_some_iff.mpr ⟨edgeBound, rfl⟩
  have childAt : children[index]? = some child :=
    List.getElem?_eq_some_iff.mpr ⟨childBound, rfl⟩
  exact ⟨
    { constructors
      targetPeel
      index
      target
      edge
      child
      terminator
      targetAt
      targetAlternative
      edgeAt
      childAt }⟩

/-- Proof-relevant form of
`constructorSwitchSelection_of_exactHPT_nonempty`. The executable attachment
check determines a unique first matching target; classical choice only
forgets the implementation details of extracting its parallel trace index. -/
noncomputable def CompiledAttachment.constructorSwitchSelection_of_exactHPT
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace} {fact : IxIR1.HPT.Fact}
    {identity : CtorId}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    (selected : attached.sidecars.exactConstructorAt? site sourceScrutinee =
      some (fact, identity)) :
    ConstructorSwitchSelection targetScrutinee generated outgoing children
      identity :=
  Classical.choice
    (attached.constructorSwitchSelection_of_exactHPT_nonempty functionMember
      descendant selected)

/-- At runtime, the exact HPT identity is the concrete constructor stored at
the resolved source location. Consequently the static attachment selection is
already the selection required by constructor dispatch. -/
noncomputable def CompiledAttachment.constructorSwitchSelection_of_exactHPT_runtime
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace} {fact : IxIR1.HPT.Fact}
    {identity cid : CtorId}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frame : Eval.Frame} {location : Nat} {box : IxIR1.NodeBox}
    {fields : Array IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frame)
    (selected : attached.sidecars.exactConstructorAt? site sourceScrutinee =
      some (fact, identity))
    (resolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN cid fields) :
    ConstructorSwitchSelection targetScrutinee generated outgoing children
      cid := by
  have identityEq : cid = identity :=
    attached.sidecars.exactConstructorAt?_matches_node selected
      state.environment resolved sourceGet node
  simpa [identityEq] using
    attached.constructorSwitchSelection_of_exactHPT functionMember descendant
      selected

/-- Source `case` success immediately selects the exact source ordinal used by
the lowering trace, in addition to exposing the smaller-fuel branch run. -/
theorem indexedCaseSuccess_of_run
    {ctx : IxIR1.Ctx} {fuel : Nat} {cur : IxIR1.FnDef}
    {store : IxIR1.Store} {env : List IxIR1.RVal}
    {scrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt}
    {output : IxIR1.Store × IxIR1.RVal}
    (run : IxIR1.runCode ctx (fuel + 1) cur store env
      (.case scrutinee peelNat alternatives) = .ok output) :
    IndexedCaseSuccess ctx fuel cur store env scrutinee peelNat alternatives
      output := by
  cases IxIR1.runCode_case_success run with
  | @ctorBranch location box cid fields fieldCount body resolved found node
      selected fieldArity branchRun =>
      have predicateEq :
          (fun alternative : IxIR1.Alt =>
            alternative.cidx == cid.cidx) =
          (fun alternative =>
            match alternative with
            | .mk candidate _ _ => candidate == cid.cidx) := by
        funext alternative
        cases alternative
        rfl
      have evaluatorSelected :
          alternatives.find? (fun alternative =>
            match alternative with
            | .mk candidate _ _ => candidate == cid.cidx) =
              some (.mk cid.cidx fieldCount body) := by
        rw [← predicateEq]
        exact selected
      obtain ⟨alternativeIndex, indexed⟩ :=
        Lower.sourceAlternativeAtTag?_of_find? evaluatorSelected
      exact .ctorBranch resolved found node indexed fieldArity branchRun
  | @natZero body peels resolved selected branchRun =>
      have predicateEq :
          (fun alternative : IxIR1.Alt => alternative.cidx == 0) =
          (fun alternative =>
            match alternative with
            | .mk candidate _ _ => candidate == 0) := by
        funext alternative
        cases alternative
        rfl
      have evaluatorSelected :
          alternatives.find? (fun alternative =>
            match alternative with
            | .mk candidate _ _ => candidate == 0) =
              some (.mk 0 0 body) := by
        rw [← predicateEq]
        exact selected
      obtain ⟨alternativeIndex, indexed⟩ :=
        Lower.sourceAlternativeAtTag?_of_find? evaluatorSelected
      exact .natZero peels resolved indexed branchRun
  | @natSucc predecessor body peels resolved selected branchRun =>
      have predicateEq :
          (fun alternative : IxIR1.Alt => alternative.cidx == 1) =
          (fun alternative =>
            match alternative with
            | .mk candidate _ _ => candidate == 1) := by
        funext alternative
        cases alternative
        rfl
      have evaluatorSelected :
          alternatives.find? (fun alternative =>
            match alternative with
            | .mk candidate _ _ => candidate == 1) =
              some (.mk 1 1 body) := by
        rw [← predicateEq]
        exact selected
      obtain ⟨alternativeIndex, indexed⟩ :=
        Lower.sourceAlternativeAtTag?_of_find? evaluatorSelected
      exact .natSucc peels resolved indexed branchRun

/-- Enter a constructor switch child while advancing source syntax, the HPT
environment, and the target recursive state together. -/
theorem Sidecars.TraceStateRel.constructorChild
    {sidecars : Sidecars} {functionTrace : Lower.FunctionTrace}
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace} {frame childFrame : Eval.Frame}
    {identity : CtorId} {tag fieldCount alternativeIndex : Nat}
    {body : IxIR1.Code} {child : Lower.CodeTrace}
    {location : Nat} {box : IxIR1.NodeBox}
    {fields : Array IxIR1.RVal}
    (state : sidecars.TraceStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frame)
    (sourceAlternative : Lower.sourceAlternativeAtTag? alternatives
      identity.cidx = some (.mk tag fieldCount body, alternativeIndex))
    (childSource : child.source = site.alternative alternativeIndex)
    (childCode : child.sourceCode = body)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN identity fields)
    (fieldArity : fields.size = fieldCount)
    (childTarget : Lower.Sim.CodeStateRel functionTrace child
      (fields.toList.reverse ++ source) childFrame) :
    sidecars.TraceStateRel functionTrace child sourceStore
      (fields.toList.reverse ++ source) childFrame := by
  have sourceAt : sidecars.sourceCodeAt? site =
      some (.case sourceScrutinee peelNat alternatives) := by
    simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceCode] using
      state.sourceCode
  have selected :=
    Lower.sourceAlternativeAtTag?_getElem? sourceAlternative
  have sourceTag := Lower.sourceAlternativeAtTag?_tag sourceAlternative
  have childSourceAt := sidecars.sourceCodeAt?_alternative sourceAt selected
  have childEnvironment := sidecars.siteEnvironmentHolds_alternative_ctor
    sourceAt selected state.environment sourceResolved sourceGet node
      sourceTag.symm fieldArity
  constructor
  · rw [childSource, childCode]
    exact childSourceAt
  · rw [childSource]
    exact state.owner
  · rw [childSource]
    exact childEnvironment
  · exact childTarget

/-- Enter the zero branch of a literal-Nat switch in the combined recursive
state. -/
theorem Sidecars.TraceStateRel.natZeroChild
    {sidecars : Sidecars} {functionTrace : Lower.FunctionTrace}
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List Lower.EdgeTrace} {children : List Lower.CodeTrace}
    {frame childFrame : Eval.Frame} {alternativeIndex : Nat}
    {body : IxIR1.Code} {child : Lower.CodeTrace}
    (state : sidecars.TraceStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frame)
    (sourceAlternative : Lower.sourceAlternativeAtTag? alternatives 0 =
      some (.mk 0 0 body, alternativeIndex))
    (childSource : child.source = site.alternative alternativeIndex)
    (childCode : child.sourceCode = body)
    (childTarget : Lower.Sim.CodeStateRel functionTrace child source
      childFrame) :
    sidecars.TraceStateRel functionTrace child sourceStore source
      childFrame := by
  have sourceAt : sidecars.sourceCodeAt? site =
      some (.case sourceScrutinee true alternatives) := by
    simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceCode] using
      state.sourceCode
  have selected :=
    Lower.sourceAlternativeAtTag?_getElem? sourceAlternative
  have childSourceAt := sidecars.sourceCodeAt?_alternative sourceAt selected
  have childEnvironment := sidecars.siteEnvironmentHolds_alternative_natZero
    sourceAt selected state.environment
  constructor
  · rw [childSource, childCode]
    exact childSourceAt
  · rw [childSource]
    exact state.owner
  · rw [childSource]
    exact childEnvironment
  · exact childTarget

/-- Enter the successor branch of a literal-Nat switch, preserving the peeled
predecessor in the combined recursive state. -/
theorem Sidecars.TraceStateRel.natSuccChild
    {sidecars : Sidecars} {functionTrace : Lower.FunctionTrace}
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List Lower.EdgeTrace} {children : List Lower.CodeTrace}
    {frame childFrame : Eval.Frame} {alternativeIndex predecessor : Nat}
    {body : IxIR1.Code} {child : Lower.CodeTrace}
    (state : sidecars.TraceStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frame)
    (sourceAlternative : Lower.sourceAlternativeAtTag? alternatives 1 =
      some (.mk 1 1 body, alternativeIndex))
    (childSource : child.source = site.alternative alternativeIndex)
    (childCode : child.sourceCode = body)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.lit (.nat (predecessor + 1))))
    (childTarget : Lower.Sim.CodeStateRel functionTrace child
      (.lit (.nat predecessor) :: source) childFrame) :
    sidecars.TraceStateRel functionTrace child sourceStore
      (.lit (.nat predecessor) :: source) childFrame := by
  have sourceAt : sidecars.sourceCodeAt? site =
      some (.case sourceScrutinee true alternatives) := by
    simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceCode] using
      state.sourceCode
  have selected :=
    Lower.sourceAlternativeAtTag?_getElem? sourceAlternative
  have childSourceAt := sidecars.sourceCodeAt?_alternative sourceAt selected
  have childEnvironment := sidecars.siteEnvironmentHolds_alternative_natSucc
    sourceAt selected state.environment sourceResolved
  constructor
  · rw [childSource, childCode]
    exact childSourceAt
  · rw [childSource]
    exact state.owner
  · rw [childSource]
    exact childEnvironment
  · exact childTarget

/-- Constructor dispatch composed with source-site/HPT transport. The result
enters the exact recursive child in the combined simulation state. -/
theorem Sidecars.simulate_traced_switch_ctor_state_hpt
    (sidecars : Sidecars)
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {location : Nat} {box : IxIR1.NodeBox} {cid : CtorId}
    {fields : Array IxIR1.RVal}
    (state : sidecars.TraceStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN cid fields)
    {tag fieldCount alternativeIndex : Nat} {body : IxIR1.Code}
    (sourceAlternative : Lower.sourceAlternativeAtTag? alternatives cid.cidx =
      some (.mk tag fieldCount body, alternativeIndex))
    (fieldArity : fields.size = fieldCount)
    {constructors : Array CtorAlt} {targetPeel : Option NatPeel}
    {index : Nat} {target : CtorAlt} {edge : Lower.EdgeTrace}
    {child : Lower.CodeTrace}
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors targetPeel)
    (targetAt : constructors[index]? = some target)
    (targetAlternative : constructors.find? (fun candidate =>
      candidate.cid == cid) = some target)
    (edgeAt : outgoing[index]? = some edge)
    (childAt : children[index]? = some child)
    (control : machine.control = .running frame stack)
    (frameCredits : frame.credits = #[]) :
    ∃ finalFrame,
      child.source = site.alternative alternativeIndex ∧
        child.sourceCode = body ∧
        Eval.Steps context interpretation (1 + fields.size) machine
          { machine with control := .running finalFrame stack } ∧
        Lower.Sim.StoreRel sourceStore machine.store ∧
        sidecars.TraceStateRel functionTrace child sourceStore
          (fields.toList.reverse ++ source) finalFrame := by
  obtain ⟨finalFrame, _edgeFrame, _childScrutinee, childSource, childCode,
      targetSteps, _, _, nextStores, childTarget, _parentBlockAt, _parentPc,
      _targetResolved, _targetGet, _transferred, _switchStep, _childBlockAt,
      _childPc, _childResolved, _prologue⟩ :=
    Lower.Sim.simulate_traced_switch_ctor_state descendant state.target stores
      sourceResolved sourceGet node sourceAlternative fieldArity terminator
      targetAt targetAlternative edgeAt childAt control frameCredits
  have childState := state.constructorChild sourceAlternative childSource
    childCode sourceResolved sourceGet node fieldArity childTarget
  exact ⟨finalFrame, childSource, childCode, targetSteps, nextStores,
    childState⟩

/-- Literal-zero dispatch composed with source-site/HPT transport. -/
theorem Sidecars.simulate_traced_switch_nat_zero_state_hpt
    (sidecars : Sidecars)
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List Lower.EdgeTrace} {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    (state : sidecars.TraceStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frame)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.lit (.nat 0)))
    (control : machine.control = .running frame stack)
    (frameCredits : frame.credits = #[]) :
    ∃ alternativeIndex body edge child childFrame,
      edge ∈ outgoing ∧ child ∈ children ∧
        Lower.sourceAlternativeAtTag? alternatives 0 =
          some (.mk 0 0 body, alternativeIndex) ∧
        child.source = site.alternative alternativeIndex ∧
        child.sourceCode = body ∧
        Eval.Step context interpretation machine
          { machine with control := .running childFrame stack } ∧
        sidecars.TraceStateRel functionTrace child sourceStore source
          childFrame := by
  obtain ⟨constructors, peel, branches, childFrame, _, edgeMember,
      childMember, sourceAlternative, childSource, childCode, targetStep,
      _, _, childTarget⟩ :=
    Lower.Sim.simulate_traced_switch_nat_zero_state descendant state.target
      sourceResolved control frameCredits
  have childState := state.natZeroChild sourceAlternative childSource
    childCode childTarget
  exact ⟨branches.zero.alternativeIndex, branches.zero.body,
    branches.zeroEdge, branches.zeroChild, childFrame, edgeMember,
    childMember, sourceAlternative, childSource, childCode, targetStep,
    childState⟩

/-- Literal-successor dispatch composed with source-site/HPT transport. -/
theorem Sidecars.simulate_traced_switch_nat_succ_state_hpt
    (sidecars : Sidecars)
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List Lower.EdgeTrace} {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {predecessor : Nat}
    (state : sidecars.TraceStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frame)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.lit (.nat (predecessor + 1))))
    (control : machine.control = .running frame stack)
    (frameCredits : frame.credits = #[]) :
    ∃ alternativeIndex body edge child childFrame,
      edge ∈ outgoing ∧ child ∈ children ∧
        Lower.sourceAlternativeAtTag? alternatives 1 =
          some (.mk 1 1 body, alternativeIndex) ∧
        child.source = site.alternative alternativeIndex ∧
        child.sourceCode = body ∧
        Eval.Step context interpretation machine
          { machine with control := .running childFrame stack } ∧
        sidecars.TraceStateRel functionTrace child sourceStore
          (.lit (.nat predecessor) :: source) childFrame := by
  obtain ⟨constructors, peel, branches, childFrame, _, edgeMember,
      childMember, sourceAlternative, childSource, childCode, targetStep,
      _, _, childTarget⟩ :=
    Lower.Sim.simulate_traced_switch_nat_succ_state descendant state.target
      sourceResolved control frameCredits
  have childState := state.natSuccChild sourceAlternative childSource
    childCode sourceResolved childTarget
  exact ⟨branches.succ.alternativeIndex, branches.succ.body,
    branches.succEdge, branches.succChild, childFrame, edgeMember,
    childMember, sourceAlternative, childSource, childCode, targetStep,
    childState⟩

/-- HPT discharges both erased premises of the traced shallow-free simulation:
the concrete constructor identity and its all-scalar field vector. -/
theorem Sidecars.simulate_traced_free_freeUnique_state_hpt
    (sidecars : Sidecars)
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {targetCid runtimeCid : IxIR1.CtorId} {fact : IxIR1.HPT.Fact}
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {location : Nat} {box : IxIR1.NodeBox} {fields : Array IxIR1.RVal}
    (selected : sidecars.scalarLeafAt? site sourceAtom =
      some (fact, targetCid))
    (environment : sidecars.SiteEnvironmentHolds sourceStore site source)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next))
    (state : Lower.Sim.CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next)
      source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (unique : box.world = .unique)
    (node : box.node = .ctorN runtimeCid fields)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.free sourceAtom) =
        .ok (sourceStore.kill location, .erased) ∧
      Eval.Step context interpretation machine
        { machine with
          store := machine.store.kill location
          control := .running nextFrame stack } ∧
      Lower.Sim.StoreRel (sourceStore.kill location)
        (machine.store.kill location) ∧
      Lower.Sim.CodeStateRel functionTrace next (.erased :: source)
        nextFrame := by
  obtain ⟨identity, scalarFields⟩ :=
    sidecars.scalarLeafAt?_matches_node selected environment sourceResolved
      sourceGet node
  subst runtimeCid
  exact Lower.Sim.simulate_traced_free_freeUnique_state descendant state
    stores sourceResolved sourceGet unique node scalarFields control

/-- HPT discharges the constructor-identity premise of the traced fetch
simulation.  A successful source fetch inversion supplies the remaining
generic node and field premises without trusting the emitted identity. -/
theorem Sidecars.simulate_traced_fetch_state_hpt
    (sidecars : Sidecars)
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {sourceField targetField : Nat}
    {targetCid runtimeCid : IxIR1.CtorId} {fact : IxIR1.HPT.Fact}
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {location : Nat} {box : IxIR1.NodeBox}
    {fields : Array IxIR1.RVal} {value : IxIR1.RVal}
    (selected : sidecars.exactConstructorAt? site sourceAtom =
      some (fact, targetCid))
    (environment : sidecars.SiteEnvironmentHolds sourceStore site source)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next))
    (state : Lower.Sim.CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next) source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN runtimeCid fields)
    (fieldAt : fields[sourceField]? = some value)
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push value }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.fetch sourceAtom sourceField) = .ok (sourceStore, value) ∧
      Eval.Step context interpretation machine
        { machine with control := .running nextFrame stack } ∧
      Lower.Sim.StoreRel sourceStore machine.store ∧
      Lower.Sim.CodeStateRel functionTrace next (value :: source)
        nextFrame := by
  have identity := sidecars.exactConstructorAt?_matches_node selected
    environment sourceResolved sourceGet node
  subst runtimeCid
  exact Lower.Sim.simulate_traced_fetch_state descendant state stores
    sourceResolved sourceGet node fieldAt control

/-- Successful source execution plus a held site environment supplies every
runtime fetch premise, including the constructor identity erased from IxIR₁. -/
theorem Sidecars.simulate_traced_fetch_state_of_run_hpt
    (sidecars : Sidecars)
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {sourceField targetField : Nat}
    {targetCid : IxIR1.CtorId} {fact : IxIR1.HPT.Fact}
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {value : IxIR1.RVal}
    (selected : sidecars.exactConstructorAt? site sourceAtom =
      some (fact, targetCid))
    (environment : sidecars.SiteEnvironmentHolds sourceStore site source)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next))
    (state : Lower.Sim.CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next) source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceRun :
      IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
        source (.fetch sourceAtom sourceField) = .ok (sourceStore, value))
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push value }
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.fetch sourceAtom sourceField) = .ok (sourceStore, value) ∧
      Eval.Step context interpretation machine
        { machine with control := .running nextFrame stack } ∧
      Lower.Sim.StoreRel sourceStore machine.store ∧
      Lower.Sim.CodeStateRel functionTrace next (value :: source)
        nextFrame := by
  obtain ⟨location, box, runtimeCid, fields, runtimeValue,
      sourceResolved, sourceGet, node, fieldAt, output⟩ :=
    IxIR1.runOp_fetch_success sourceRun
  have valueEq : value = runtimeValue := by
    exact congrArg Prod.snd output
  subst runtimeValue
  exact sidecars.simulate_traced_fetch_state_hpt selected environment
    descendant state stores sourceResolved sourceGet node fieldAt control

/-- A successful source shallow free determines its killed location.  The
strong scalar-leaf HPT selection supplies both erased safety checks required
by `freeUnique`. -/
theorem Sidecars.simulate_traced_free_freeUnique_state_of_run_hpt
    (sidecars : Sidecars)
    {sourceContext : IxIR1.Ctx} {sourceCurrent : IxIR1.FnDef}
    {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {targetCid : IxIR1.CtorId} {fact : IxIR1.HPT.Fact}
    {sourceStore outputStore : IxIR1.Store}
    {source : List IxIR1.RVal}
    (selected : sidecars.scalarLeafAt? site sourceAtom =
      some (fact, targetCid))
    (environment : sidecars.SiteEnvironmentHolds sourceStore site source)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next))
    (state : Lower.Sim.CodeStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next)
      source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceRun :
      IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
        source (.free sourceAtom) = .ok (outputStore, .erased))
    (control : machine.control = .running frame stack) :
    ∃ location,
      outputStore = sourceStore.kill location ∧
      let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
      Eval.Step context interpretation machine
          { machine with
            store := machine.store.kill location
            control := .running nextFrame stack } ∧
        Lower.Sim.StoreRel (sourceStore.kill location)
          (machine.store.kill location) ∧
        Lower.Sim.CodeStateRel functionTrace next (.erased :: source)
          nextFrame := by
  obtain ⟨location, box, sourceResolved, sourceGet, unique, output⟩ :=
    IxIR1.runOp_free_success sourceRun
  obtain ⟨exactBox, fields, exactGet, node, scalarFields⟩ :=
    sidecars.scalarLeafAt?_runtime selected environment sourceResolved
  have boxEq : exactBox = box :=
    Option.some.inj (exactGet.symm.trans sourceGet)
  subst exactBox
  obtain ⟨_, targetStep, nextStores, nextState⟩ :=
    Lower.Sim.simulate_traced_free_freeUnique_state
      (sourceContext := sourceContext) (sourceCurrent := sourceCurrent)
      (sourceFuel := sourceFuel) descendant state stores sourceResolved
      sourceGet unique node scalarFields control
  exact ⟨location, congrArg Prod.fst output, targetStep, nextStores,
    nextState⟩

/-- Attachment-facing fetch induction step. Trace membership recovers the
attachment-checked exact-constructor HPT evidence; the identity adapter
performs the target transition, and the checked post-fixpoint advances the
combined state to the recursive continuation. -/
theorem CompiledAttachment.simulate_traced_fetch_state_of_run_hpt
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {sourceField targetField : Nat}
    {targetCid : IxIR1.CtorId}
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {value : IxIR1.RVal}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next))
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun :
      IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source sourceStore
        source (.fetch sourceAtom sourceField) = .ok (sourceStore, value))
    (control : machine.control = .running frame stack) :
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push value }
    IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source sourceStore
          source (.fetch sourceAtom sourceField) = .ok (sourceStore, value) ∧
      Eval.Step context interpretation machine
        { machine with control := .running nextFrame stack } ∧
      Lower.Sim.StoreRel sourceStore machine.store ∧
      attached.sidecars.TraceStateRel functionTrace next sourceStore
        (value :: source) nextFrame := by
  obtain ⟨fact, selected⟩ :=
    attached.exactConstructorAt?_of_fetch_descendant functionMember descendant
  obtain ⟨_, targetStep, nextStores, nextTarget⟩ :=
    attached.sidecars.simulate_traced_fetch_state_of_run_hpt selected
      state.environment descendant state.target stores sourceRun control
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨sourceRun, targetStep, nextStores, nextState⟩

/-- Attachment-facing shallow-free induction step. Trace membership recovers
the attachment-checked scalar-leaf HPT evidence, so all erased target safety,
source-coordinate, and continuation-state obligations are internal. -/
theorem CompiledAttachment.simulate_traced_free_freeUnique_state_of_run_hpt
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {targetCid : IxIR1.CtorId}
    {sourceStore outputStore : IxIR1.Store}
    {source : List IxIR1.RVal}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next))
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun :
      IxIR1.runOp sourceContext (sourceFuel + 1) functionTrace.source sourceStore
        source (.free sourceAtom) = .ok (outputStore, .erased))
    (control : machine.control = .running frame stack) :
    ∃ location,
      outputStore = sourceStore.kill location ∧
      let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
      Eval.Step context interpretation machine
          { machine with
            store := machine.store.kill location
            control := .running nextFrame stack } ∧
        Lower.Sim.StoreRel (sourceStore.kill location)
          (machine.store.kill location) ∧
        attached.sidecars.TraceStateRel functionTrace next outputStore
          (.erased :: source) nextFrame := by
  obtain ⟨fact, selected⟩ :=
    attached.scalarLeafAt?_of_free_descendant functionMember descendant
  obtain ⟨location, outputStoreEq, targetStep, nextStores, nextTarget⟩ :=
    attached.sidecars.simulate_traced_free_freeUnique_state_of_run_hpt
      selected state.environment descendant state.target stores
      sourceRun control
  subst outputStore
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations sourceRun nextTarget
  exact ⟨location, rfl, targetStep, nextStores, nextState⟩

/-! ## Continuation-passing recursive simulation interface -/

/-- A target-machine postcondition indexed by the source store and value that
the current IxIR₁ computation has produced.  Keeping those indices explicit
lets a callee-return handler resume the suspended source continuation before
the eventual whole-main postcondition is discharged. -/
abbrev SourceMachinePost :=
  IxIR1.Store → IxIR1.RVal → Eval.Machine → Prop

/-- Finite target execution from `machine` to a state satisfying the supplied
source-indexed postcondition.  The exact control-step count remains available
for the final `runMachine`/`runMain` budget witness. -/
def ReachesPost (context : Eval.Context)
    (interpretation : Eval.Interpretation) (post : SourceMachinePost)
    (sourceStore : IxIR1.Store) (value : IxIR1.RVal)
    (machine : Eval.Machine) : Prop :=
  ∃ count final,
    Eval.Steps context interpretation count machine final ∧
      post sourceStore value final

/-- A postcondition already true at the current machine needs no target
control step. -/
theorem ReachesPost.refl {context : Eval.Context}
    {interpretation : Eval.Interpretation} {post : SourceMachinePost}
    {sourceStore : IxIR1.Store} {value : IxIR1.RVal}
    {machine : Eval.Machine} (holds : post sourceStore value machine) :
    ReachesPost context interpretation post sourceStore value machine := by
  exact ⟨0, machine, .refl machine, holds⟩

/-- Prefix a finite postcondition witness by another finite target execution.
This is the CPS composition rule used after every emitted instruction, switch
transfer, call entry, and return transition. -/
theorem ReachesPost.prepend {context : Eval.Context}
    {interpretation : Eval.Interpretation} {post : SourceMachinePost}
    {sourceStore : IxIR1.Store} {value : IxIR1.RVal}
    {before middle : Eval.Machine} {prefixCount : Nat}
    (initial : Eval.Steps context interpretation prefixCount before middle)
    (tail : ReachesPost context interpretation post sourceStore value middle) :
    ReachesPost context interpretation post sourceStore value before := by
  obtain ⟨tailCount, final, tailSteps, finalPost⟩ := tail
  exact ⟨prefixCount + tailCount, final, initial.trans tailSteps, finalPost⟩

/-- One genuine running target step followed by a successful CPS tail. -/
theorem ReachesPost.step {context : Eval.Context}
    {interpretation : Eval.Interpretation} {post : SourceMachinePost}
    {sourceStore : IxIR1.Store} {value : IxIR1.RVal}
    {before middle : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    (running : before.control = .running frame stack)
    (head : Eval.Step context interpretation before middle)
    (tail : ReachesPost context interpretation post sourceStore value middle) :
    ReachesPost context interpretation post sourceStore value before := by
  exact tail.prepend (head.toSteps running)

/-- A machine control/store shape admits some sufficient initial heap budget
for a finite execution satisfying `post`.  Heap fuel is selected backward
from the continuation: non-destructive steps preserve the chosen suffix,
while recursive release/drop steps prepend their own exact traversal cost. -/
def BudgetedReachesPost (context : Eval.Context)
    (interpretation : Eval.Interpretation) (post : SourceMachinePost)
    (sourceStore : IxIR1.Store) (value : IxIR1.RVal)
    (machine : Eval.Machine) : Prop :=
  ∃ heapFuel,
    ReachesPost context interpretation post sourceStore value
      { machine with heapFuel }

/-- Prefix an already funded continuation by target steps that preserve every
chosen heap budget. -/
theorem BudgetedReachesPost.prependPreserving {context : Eval.Context}
    {interpretation : Eval.Interpretation} {post : SourceMachinePost}
    {sourceStore : IxIR1.Store} {value : IxIR1.RVal}
    {before middle : Eval.Machine} {prefixCount : Nat}
    (initial : ∀ heapFuel,
      Eval.Steps context interpretation prefixCount
        { before with heapFuel } { middle with heapFuel })
    (tail : BudgetedReachesPost context interpretation post sourceStore value
      middle) :
    BudgetedReachesPost context interpretation post sourceStore value
      before := by
  obtain ⟨heapFuel, tail⟩ := tail
  exact ⟨heapFuel, tail.prepend (initial heapFuel)⟩

/-- Prefix an already funded continuation by a target execution whose local
heap cost is framed over the continuation's chosen suffix. -/
theorem BudgetedReachesPost.prependFramed {context : Eval.Context}
    {interpretation : Eval.Interpretation} {post : SourceMachinePost}
    {sourceStore : IxIR1.Store} {value : IxIR1.RVal}
    {before middle : Eval.Machine} {prefixCount localFuel : Nat}
    (initial : ∀ suffixFuel,
      Eval.Steps context interpretation prefixCount
        { before with heapFuel := localFuel + suffixFuel }
        { middle with heapFuel := suffixFuel })
    (tail : BudgetedReachesPost context interpretation post sourceStore value
      middle) :
    BudgetedReachesPost context interpretation post sourceStore value
      before := by
  obtain ⟨suffixFuel, tail⟩ := tail
  exact ⟨localFuel + suffixFuel, tail.prepend (initial suffixFuel)⟩

/-! ## Runtime constructor-universe closure

Ambiguous IxIR₁ cases erase the inductive block component of constructor
identity and dispatch only on `cidx`.  The lowerer therefore emits every
producer-known full identity compatible with an arm.  The following invariant
is the dynamic half of that argument: every live source constructor was
allocated by a statically audited operation in the attached program. -/

/-- Every live constructor node belongs to the producer's finite constructor
universe, with the arity recorded by the sidecar. -/
structure Sidecars.SourceConstructorsValid (sidecars : Sidecars)
    (store : IxIR1.Store) : Prop where
  constructorKnown : ∀ {location world rc identity fields},
    store.get? location =
        some ⟨world, rc, .ctorN identity fields⟩ →
      sidecars.constructorKnown identity fields.size = true

/-- Every callable source definition has passed the constructor-allocation
audit. -/
def Sidecars.ContextConstructorsKnown (sidecars : Sidecars)
    (context : IxIR1.Ctx) : Prop :=
  ∀ {address definition},
    context.decls address = some (.fn definition) →
      sidecars.codeConstructorsKnown definition.body = true

namespace Sidecars.SourceConstructorsValid

/-- The empty source heap contains no constructor outside the universe. -/
theorem empty (sidecars : Sidecars) :
    sidecars.SourceConstructorsValid ({} : IxIR1.Store) := by
  constructor
  intro location world rc identity fields found
  simp [IxIR1.Store.get?] at found

/-- Removing nodes or changing only reference counts preserves membership in
the constructor universe. -/
theorem ofRestricts {sidecars : Sidecars} {before after : IxIR1.Store}
    (valid : sidecars.SourceConstructorsValid before)
    (restricts : IxIR1.Sim.StoreGraphRestricts before after) :
    sidecars.SourceConstructorsValid after := by
  constructor
  intro location world rc identity fields found
  obtain ⟨beforeRc, beforeFound⟩ := restricts found
  exact valid.constructorKnown beforeFound

/-- Appending a constructor whose identity/arity is audited preserves the
global invariant. -/
theorem allocCtor {sidecars : Sidecars} {store : IxIR1.Store}
    (valid : sidecars.SourceConstructorsValid store)
    (world : Ixon.Owned) (identity : CtorId)
    (fields : Array IxIR1.RVal)
    (known : sidecars.constructorKnown identity fields.size = true) :
    sidecars.SourceConstructorsValid
      (store.allocNode world (.ctorN identity fields)).1 := by
  constructor
  intro location boxWorld rc foundIdentity foundFields found
  by_cases fresh : location = store.nodes.size
  · subst location
    have allocated := IxIR1.Sim.HeapIso.get?_allocNode_new store world
      (.ctorN identity fields)
    have boxEq :
        (⟨boxWorld, rc, .ctorN foundIdentity foundFields⟩ : IxIR1.NodeBox) =
          ⟨world, 1, .ctorN identity fields⟩ :=
      Option.some.inj (found.symm.trans allocated)
    cases boxEq
    exact known
  · exact valid.constructorKnown
      (IxIR1.Sim.HeapIso.get?_of_allocNode_old fresh found)

/-- Appending a PAP introduces no constructor node. -/
theorem allocPap {sidecars : Sidecars} {store : IxIR1.Store}
    (valid : sidecars.SourceConstructorsValid store)
    (world : Ixon.Owned) (address : Ixon.Address) (arity : Nat)
    (captured : Array IxIR1.RVal) :
    sidecars.SourceConstructorsValid
      (store.allocNode world (.papN address arity captured)).1 := by
  constructor
  intro location boxWorld rc identity fields found
  by_cases fresh : location = store.nodes.size
  · subst location
    have allocated := IxIR1.Sim.HeapIso.get?_allocNode_new store world
      (.papN address arity captured)
    have impossible :
        (⟨boxWorld, rc, .ctorN identity fields⟩ : IxIR1.NodeBox) =
          ⟨world, 1, .papN address arity captured⟩ :=
      Option.some.inj (found.symm.trans allocated)
    cases impossible
  · exact valid.constructorKnown
      (IxIR1.Sim.HeapIso.get?_of_allocNode_old fresh found)

/-- Replacing a live slot by a known constructor preserves the invariant.
The result shape includes the evaluator's reuse-counter tick. -/
theorem reuseCtor {sidecars : Sidecars} {store : IxIR1.Store}
    (valid : sidecars.SourceConstructorsValid store)
    {location : Nat} {old : IxIR1.NodeBox}
    (live : store.get? location = some old)
    (identity : CtorId) (fields : Array IxIR1.RVal)
    (known : sidecars.constructorKnown identity fields.size = true) :
    sidecars.SourceConstructorsValid
      { store.setBox location
          ⟨.unique, 1, .ctorN identity fields⟩ with
        reuses :=
          (store.setBox location
            ⟨.unique, 1, .ctorN identity fields⟩).reuses + 1 } := by
  constructor
  intro other world rc foundIdentity foundFields found
  change (store.setBox location
      ⟨.unique, 1, .ctorN identity fields⟩).get? other =
        some ⟨world, rc, .ctorN foundIdentity foundFields⟩ at found
  by_cases same : location = other
  · subst other
    have updated := IxIR1.Sim.get?_setBox_same
      (new := (⟨.unique, 1, .ctorN identity fields⟩ : IxIR1.NodeBox)) live
    have boxEq :
        (⟨world, rc, .ctorN foundIdentity foundFields⟩ : IxIR1.NodeBox) =
          ⟨.unique, 1, .ctorN identity fields⟩ :=
      Option.some.inj (found.symm.trans updated)
    cases boxEq
    exact known
  · exact valid.constructorKnown
      (IxIR1.Sim.get?_of_setBox_other same live found)

/-- Retaining shared roots changes reference counts only. -/
theorem dupVals {sidecars : Sidecars} {store store' : IxIR1.Store}
    {values : List IxIR1.RVal}
    (valid : sidecars.SourceConstructorsValid store)
    (run : IxIR1.dupVals store values = .ok store') :
    sidecars.SourceConstructorsValid store' := by
  induction values generalizing store with
  | nil =>
      change (.ok store : Except IxIR1.Err IxIR1.Store) = .ok store' at run
      injection run with storeEq
      subst store'
      exact valid
  | cons head tail ih =>
      cases head with
      | lit literal =>
          simp only [IxIR1.dupVals, List.foldlM_cons] at run
          exact ih valid run
      | erased =>
          simp only [IxIR1.dupVals, List.foldlM_cons] at run
          exact ih valid run
      | loc location =>
          simp only [IxIR1.dupVals, List.foldlM_cons] at run
          cases found : store.get? location with
          | none => simp [found] at run
          | some box =>
              cases box with
              | mk world rc node =>
                  cases world with
                  | unique => simp [found] at run
                  | shared =>
                      simp only [found] at run
                      exact ih
                        (valid.ofRestricts
                          (IxIR1.Sim.StoreGraphRestricts.incRcStore found))
                        run

/-- Shared destruction can only remove nodes or alter reference counts. -/
theorem dropVal {sidecars : Sidecars} {context : IxIR1.Ctx} {fuel : Nat}
    {store store' : IxIR1.Store} {value : IxIR1.RVal}
    (valid : sidecars.SourceConstructorsValid store)
    (run : IxIR1.dropVal context fuel store value = .ok store') :
    sidecars.SourceConstructorsValid store' :=
  valid.ofRestricts (IxIR1.Sim.dropVal_restricts run)

/-- Dropping a list likewise cannot introduce a constructor. -/
theorem dropMany {sidecars : Sidecars} {context : IxIR1.Ctx} {fuel : Nat}
    {store store' : IxIR1.Store} {values : List IxIR1.RVal}
    (valid : sidecars.SourceConstructorsValid store)
    (run : IxIR1.dropMany context fuel store values = .ok store') :
    sidecars.SourceConstructorsValid store' :=
  valid.ofRestricts (IxIR1.Sim.dropMany_restricts run)

/-- Unique destruction also only removes nodes. -/
theorem dropUVal {sidecars : Sidecars} {context : IxIR1.Ctx} {fuel : Nat}
    {store store' : IxIR1.Store} {value : IxIR1.RVal}
    (valid : sidecars.SourceConstructorsValid store)
    (run : IxIR1.dropUVal context fuel store value = .ok store') :
    sidecars.SourceConstructorsValid store' :=
  valid.ofRestricts (IxIR1.Sim.dropUVal_restricts run)

end Sidecars.SourceConstructorsValid

/-- Reflect a successful finite-universe lookup into the constructor-info
witness consumed by residual switch coverage. -/
theorem Sidecars.constructorKnown_witness (sidecars : Sidecars)
    {identity : CtorId} {arity : Nat}
    (known : sidecars.constructorKnown identity arity = true) :
    ∃ info ∈ sidecars.constructors,
      info.identity = identity ∧ info.arity = arity := by
  unfold Sidecars.constructorKnown at known
  cases found : sidecars.constructors.find?
      (fun info => info.identity == identity) with
  | none => simp [found] at known
  | some info =>
      have matched := List.find?_some found
      have identityEq : info.identity = identity := beq_iff_eq.mp matched
      exact ⟨info, List.mem_of_find?_eq_some found, identityEq,
        beq_iff_eq.mp (by simpa [found] using known)⟩

/-- The source-body half of the attachment audit selects any retained
function. -/
theorem CompiledAttachment.functionCodeConstructorsKnown
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (member : functionTrace ∈ attached.target.artifact.trace.functions) :
    attached.sidecars.codeConstructorsKnown
      functionTrace.source.body = true := by
  have functionKnown := List.all_eq_true.mp
    attached.sourceConstructorsProduced functionTrace member
  simp only [Bool.and_eq_true] at functionKnown
  exact functionKnown.1

/-- The trace-shaped half of the attachment audit selects any retained
function root. -/
theorem CompiledAttachment.functionTraceConstructorsKnown
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (member : functionTrace ∈ attached.target.artifact.trace.functions) :
    attached.sidecars.codeTraceConstructorsKnown functionTrace.root = true := by
  have functionKnown := List.all_eq_true.mp
    attached.sourceConstructorsProduced functionTrace member
  simp only [Bool.and_eq_true] at functionKnown
  exact functionKnown.2

/-- Every operation at a retained simulated suffix passed the producer
constructor audit. -/
theorem CompiledAttachment.descendantOperationConstructorsKnown
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (member : functionTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next)) :
    attached.sidecars.operationConstructorsKnown operation = true := by
  have localKnown := attached.sidecars.codeTraceConstructorsKnown_descendant
    (attached.functionTraceConstructorsKnown member) descendant
  simp only [Sidecars.codeTraceConstructorsKnown,
    Bool.and_eq_true] at localKnown
  exact localKnown.1

/-- A declaration-compatible source evaluator context inherits the audited
constructor-allocation property from the attached function trace. -/
theorem CompiledAttachment.sourceContextConstructorsKnown
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv
        attached.source.lowering.result.artifacts) :
    attached.sidecars.ContextConstructorsKnown sourceContext := by
  intro address definition lookup
  have sidecarLookup : IxIR1.Env.ofList
      attached.sidecars.input.declarations address =
        some (.fn definition) := by
    rw [attached.sidecarDeclarationEnvironment, ← sourceDeclarations]
    exact lookup
  have artifactLookup : IxIR1.Env.ofList
      attached.target.artifact.source.declarations address =
        some (.fn definition) := by
    rw [attached.targetSourceProduced]
    exact sidecarLookup
  obtain ⟨targetDefinition, functionTrace, targetLookup, member, matched⟩ :=
    attached.target.artifact.functionTrace_of_source_lookup artifactLookup
  simpa [matched.source] using
    attached.functionCodeConstructorsKnown member

private def EvalConstructorsValidAt (sidecars : Sidecars)
    (fuel : Nat) : Prop :=
  (∀ context current store environment code store' value,
    sidecars.ContextConstructorsKnown context →
    sidecars.codeConstructorsKnown current.body = true →
    sidecars.codeConstructorsKnown code = true →
    sidecars.SourceConstructorsValid store →
    IxIR1.runCode context fuel current store environment code =
        .ok (store', value) →
      sidecars.SourceConstructorsValid store') ∧
  (∀ context current store environment operation store' value,
    sidecars.ContextConstructorsKnown context →
    sidecars.codeConstructorsKnown current.body = true →
    sidecars.operationConstructorsKnown operation = true →
    sidecars.SourceConstructorsValid store →
    IxIR1.runOp context fuel current store environment operation =
        .ok (store', value) →
      sidecars.SourceConstructorsValid store') ∧
  (∀ context address arguments store store' value,
    sidecars.ContextConstructorsKnown context →
    sidecars.SourceConstructorsValid store →
    IxIR1.invoke context fuel address arguments store = .ok (store', value) →
      sidecars.SourceConstructorsValid store') ∧
  (∀ context store function arguments store' value,
    sidecars.ContextConstructorsKnown context →
    sidecars.SourceConstructorsValid store →
    IxIR1.applyGo context fuel store function arguments =
        .ok (store', value) →
      sidecars.SourceConstructorsValid store')

private theorem constructorsBindOk {error α β : Type} (value : α)
    (next : α → Except error β) :
    ((Except.ok value : Except error α) >>= next) = next value := rfl

private theorem constructorsBindError {error α β : Type} (failure : error)
    (next : α → Except error β) :
    ((Except.error failure : Except error α) >>= next) = .error failure := rfl

/-- Source evaluation preserves the producer constructor universe.  The
induction follows calls and higher-order application; fresh constructor and
reuse sites are the only branches that need their local executable audit. -/
private theorem evalConstructorsValidAt (sidecars : Sidecars) :
    ∀ fuel, EvalConstructorsValidAt sidecars fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro context current store environment code store' value contextKnown
        currentKnown codeKnown valid run
      rw [IxIR1.runCode.eq_def] at run
      simp at run
    · intro context current store environment operation store' value
        contextKnown currentKnown operationKnown valid run
      rw [IxIR1.runOp.eq_def] at run
      simp at run
    · intro context address arguments store store' value contextKnown valid run
      rw [IxIR1.invoke.eq_def] at run
      simp at run
    · intro context store function arguments store' value contextKnown valid run
      rw [IxIR1.applyGo.eq_def] at run
      simp at run
  | succ fuel ih =>
    obtain ⟨ihCode, ihOperation, ihInvoke, ihApply⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro context current store environment code store' value contextKnown
        currentKnown codeKnown valid run
      cases code with
      | ret atom =>
          rw [IxIR1.runCode.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtom environment atom with
          | error error => simp [resolved] at run
          | ok result =>
              rw [resolved, constructorsBindOk] at run
              have pair := Except.ok.inj run
              cases pair
              exact valid
      | letOp operation rest =>
          simp only [Sidecars.codeConstructorsKnown,
            Bool.and_eq_true] at codeKnown
          rw [IxIR1.runCode.eq_def] at run
          dsimp only at run
          cases operationRun : IxIR1.runOp context fuel current store
              environment operation with
          | error error => simp [operationRun] at run
          | ok result =>
              rcases result with ⟨middle, operationValue⟩
              rw [operationRun, constructorsBindOk] at run
              exact ihCode _ _ _ _ _ _ _ contextKnown currentKnown
                codeKnown.2
                (ihOperation _ _ _ _ _ _ _ contextKnown currentKnown
                  codeKnown.1 valid operationRun)
                run
      | case scrutinee peelNat alternatives =>
          rw [IxIR1.runCode.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtom environment scrutinee with
          | error error => simp [resolved] at run
          | ok scrutineeValue =>
              rw [resolved, constructorsBindOk] at run
              cases scrutineeValue with
              | loc location =>
                  cases found : store.get? location with
                  | none => simp [found] at run
                  | some box =>
                      simp only [found] at run
                      cases box with
                      | mk world rc node =>
                          cases node with
                          | papN address arity captured => simp at run
                          | ctorN identity fields =>
                              cases selected : alternatives.find?
                                  (fun alternative =>
                                    alternative.cidx == identity.cidx) with
                              | none => simp [selected] at run
                              | some alternative =>
                                  have alternativeMember : alternative ∈
                                      alternatives :=
                                    Array.mem_of_find?_eq_some selected
                                  cases alternative with
                                  | mk cidx fieldCount body =>
                                      have bodyKnown :=
                                        sidecars.codeConstructorsKnown_alternative
                                          codeKnown alternativeMember
                                      cases sizeMismatch :
                                          fields.size != fieldCount
                                      · simp only [selected, sizeMismatch,
                                            Bool.false_eq_true, if_false] at run
                                        exact ihCode _ _ _ _ _ _ _ contextKnown
                                          currentKnown bodyKnown valid run
                                      · simp [selected, sizeMismatch] at run
              | lit literal =>
                  cases literal with
                  | str string => simp at run
                  | nat n =>
                      cases peel : peelNat with
                      | false => simp [peel] at run
                      | true =>
                          cases n with
                          | zero =>
                              cases selected : alternatives.find?
                                  (fun alternative =>
                                    alternative.cidx == 0) with
                              | none => simp [peel, selected] at run
                              | some alternative =>
                                  have alternativeMember : alternative ∈
                                      alternatives :=
                                    Array.mem_of_find?_eq_some selected
                                  cases alternative with
                                  | mk cidx fieldCount body =>
                                      have bodyKnown :=
                                        sidecars.codeConstructorsKnown_alternative
                                          codeKnown alternativeMember
                                      cases fieldCount with
                                      | zero =>
                                          simp only [peel, selected] at run
                                          exact ihCode _ _ _ _ _ _ _
                                            contextKnown currentKnown bodyKnown
                                            valid run
                                      | succ fieldCount =>
                                          simp [peel, selected] at run
                          | succ n =>
                              cases selected : alternatives.find?
                                  (fun alternative =>
                                    alternative.cidx == 1) with
                              | none => simp [peel, selected] at run
                              | some alternative =>
                                  have alternativeMember : alternative ∈
                                      alternatives :=
                                    Array.mem_of_find?_eq_some selected
                                  cases alternative with
                                  | mk cidx fieldCount body =>
                                      have bodyKnown :=
                                        sidecars.codeConstructorsKnown_alternative
                                          codeKnown alternativeMember
                                      cases fieldCount with
                                      | zero => simp [peel, selected] at run
                                      | succ fieldCount =>
                                          cases fieldCount with
                                          | zero =>
                                              simp only [peel, selected] at run
                                              exact ihCode _ _ _ _ _ _ _
                                                contextKnown currentKnown
                                                bodyKnown valid run
                                          | succ fieldCount =>
                                              simp [peel, selected] at run
              | erased => simp at run
    · intro context current store environment operation store' value
        contextKnown currentKnown operationKnown valid run
      cases operation with
      | pure atom =>
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtom environment atom with
          | error error => simp [resolved] at run
          | ok result =>
              rw [resolved, constructorsBindOk] at run
              have pair := Except.ok.inj run
              cases pair
              exact valid
      | alloc world identity atoms =>
          simp only [Sidecars.operationConstructorsKnown] at operationKnown
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtoms environment atoms with
          | error error => simp [resolved] at run
          | ok values =>
              rw [resolved, constructorsBindOk] at run
              have pair := Except.ok.inj run
              cases pair
              have size : values.toArray.size = atoms.size := by
                simpa using IxIR1.resolveAtoms_length resolved
              exact valid.allocCtor world identity values.toArray
                (by simpa [size] using operationKnown)
      | reuse target identity atoms =>
          simp only [Sidecars.operationConstructorsKnown] at operationKnown
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases argumentsResolved : IxIR1.resolveAtoms environment atoms with
          | error error => simp [argumentsResolved] at run
          | ok values =>
              rw [argumentsResolved, constructorsBindOk] at run
              cases targetResolved : IxIR1.resolveAtom environment target with
              | error error => simp [targetResolved] at run
              | ok targetValue =>
                  rw [targetResolved, constructorsBindOk] at run
                  cases targetValue with
                  | lit literal => simp at run
                  | erased => simp at run
                  | loc location =>
                      cases found : store.get? location with
                      | none => simp [found] at run
                      | some box =>
                          simp only [found] at run
                          cases box with
                          | mk world rc node =>
                              cases world with
                              | shared => simp at run
                              | unique =>
                                  have pair := Except.ok.inj run
                                  cases pair
                                  have size : values.toArray.size = atoms.size :=
                                    by
                                      simpa using
                                        IxIR1.resolveAtoms_length
                                          argumentsResolved
                                  exact valid.reuseCtor found identity
                                    values.toArray
                                    (by simpa [size] using operationKnown)
      | free target =>
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtom environment target with
          | error error => simp [resolved] at run
          | ok targetValue =>
              rw [resolved, constructorsBindOk] at run
              cases targetValue with
              | lit literal => simp at run
              | erased => simp at run
              | loc location =>
                  cases found : store.get? location with
                  | none => simp [found] at run
                  | some box =>
                      simp only [found] at run
                      cases box with
                      | mk world rc node =>
                          cases world with
                          | shared => simp at run
                          | unique =>
                              have pair := Except.ok.inj run
                              cases pair
                              exact valid.ofRestricts
                                (IxIR1.Sim.StoreGraphRestricts.kill found)
      | dup target =>
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtom environment target with
          | error error => simp [resolved] at run
          | ok targetValue =>
              rw [resolved, constructorsBindOk] at run
              cases targetValue with
              | lit literal =>
                  have pair := Except.ok.inj run
                  cases pair
                  exact valid
              | erased =>
                  have pair := Except.ok.inj run
                  cases pair
                  exact valid
              | loc location =>
                  cases found : store.get? location with
                  | none => simp [found] at run
                  | some box =>
                      simp only [found] at run
                      cases box with
                      | mk world rc node =>
                          cases world with
                          | unique => simp at run
                          | shared =>
                              have pair := Except.ok.inj run
                              cases pair
                              simpa [IxIR1.Sim.incRcStore] using
                                valid.ofRestricts
                                  (IxIR1.Sim.StoreGraphRestricts.incRcStore
                                    found)
      | drop target =>
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtom environment target with
          | error error => simp [resolved] at run
          | ok targetValue =>
              rw [resolved, constructorsBindOk] at run
              cases targetValue with
              | lit literal =>
                  have pair := Except.ok.inj run
                  cases pair
                  exact valid
              | erased =>
                  have pair := Except.ok.inj run
                  cases pair
                  exact valid
              | loc location =>
                  dsimp only at run
                  cases dropped : IxIR1.dropVal context fuel store
                      (.loc location) with
                  | error error => simp [dropped] at run
                  | ok droppedStore =>
                      rw [dropped, constructorsBindOk] at run
                      have pair := Except.ok.inj run
                      cases pair
                      exact valid.dropVal dropped
      | dropU target =>
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtom environment target with
          | error error => simp [resolved] at run
          | ok targetValue =>
              rw [resolved, constructorsBindOk] at run
              cases targetValue with
              | lit literal =>
                  have pair := Except.ok.inj run
                  cases pair
                  exact valid
              | erased =>
                  have pair := Except.ok.inj run
                  cases pair
                  exact valid
              | loc location =>
                  dsimp only at run
                  cases dropped : IxIR1.dropUVal context fuel store
                      (.loc location) with
                  | error error => simp [dropped] at run
                  | ok droppedStore =>
                      rw [dropped, constructorsBindOk] at run
                      have pair := Except.ok.inj run
                      cases pair
                      exact valid.dropUVal dropped
      | fetch target field =>
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtom environment target with
          | error error => simp [resolved] at run
          | ok targetValue =>
              rw [resolved, constructorsBindOk] at run
              cases targetValue with
              | lit literal => simp at run
              | erased => simp at run
              | loc location =>
                  cases found : store.get? location with
                  | none => simp [found] at run
                  | some box =>
                      simp only [found] at run
                      cases box with
                      | mk world rc node =>
                          cases node with
                          | papN address arity captured => simp at run
                          | ctorN identity fields =>
                              cases fieldFound : fields[field]? with
                              | none => simp [fieldFound] at run
                              | some result =>
                                  simp only [fieldFound] at run
                                  have pair := Except.ok.inj run
                                  cases pair
                                  exact valid
      | call address atoms =>
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtoms environment atoms with
          | error error => simp [resolved] at run
          | ok values =>
              rw [resolved, constructorsBindOk] at run
              exact ihInvoke _ _ _ _ _ _ contextKnown valid run
      | callSelf atoms =>
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtoms environment atoms with
          | error error => simp [resolved] at run
          | ok values =>
              rw [resolved, constructorsBindOk] at run
              cases arityMismatch : values.length != current.arity
              · have sameArity : values.length = current.arity := by
                  simpa using arityMismatch
                simp [sameArity] at run
                cases bodyRun : IxIR1.runCode context fuel current store
                    values.reverse current.body with
                | error error =>
                    rw [bodyRun, constructorsBindError] at run
                    contradiction
                | ok result =>
                    rcases result with ⟨bodyStore, bodyValue⟩
                    rw [bodyRun, constructorsBindOk] at run
                    obtain ⟨resultEq, _⟩ := IxIR1.Sim.checkResultWorld_ok run
                    cases resultEq
                    exact ihCode _ _ _ _ _ _ _ contextKnown currentKnown
                      currentKnown valid bodyRun
              · have different : values.length ≠ current.arity :=
                  bne_iff_ne.mp arityMismatch
                simp [different] at run
      | papp address atoms =>
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtoms environment atoms with
          | error error => simp [resolved] at run
          | ok values =>
              rw [resolved, constructorsBindOk] at run
              cases declarationFound : context.decls address with
              | none => simp [declarationFound] at run
              | some declaration =>
                  simp only [declarationFound] at run
                  by_cases under : values.length < IxIR1.declArity declaration
                  · simp only [under, if_true] at run
                    have pair := Except.ok.inj run
                    cases pair
                    exact valid.allocPap .shared address
                      (IxIR1.declArity declaration) values.toArray
                  · simp [under] at run
      | apply function atoms =>
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases functionResolved : IxIR1.resolveAtom environment function with
          | error error => simp [functionResolved] at run
          | ok functionValue =>
              rw [functionResolved, constructorsBindOk] at run
              cases argumentsResolved : IxIR1.resolveAtoms environment atoms with
              | error error => simp [argumentsResolved] at run
              | ok values =>
                  rw [argumentsResolved, constructorsBindOk] at run
                  exact ihApply _ _ _ _ _ _ contextKnown valid run
      | extern address atoms =>
          rw [IxIR1.runOp.eq_def] at run
          dsimp only at run
          cases resolved : IxIR1.resolveAtoms environment atoms with
          | error error => simp [resolved] at run
          | ok values =>
              rw [resolved, constructorsBindOk] at run
              cases called : IxIR1.callScalarOracle context address values with
              | error error => simp [called] at run
              | ok result =>
                  rw [called, constructorsBindOk] at run
                  have pair := Except.ok.inj run
                  cases pair
                  exact valid
    · intro context address arguments store store' value contextKnown valid run
      rw [IxIR1.invoke.eq_def] at run
      dsimp only at run
      cases declarationFound : context.decls address with
      | none => simp [declarationFound] at run
      | some declaration =>
          simp only [declarationFound] at run
          cases declaration with
          | extern arity =>
              cases arityMismatch : arguments.length != arity
              · simp only [arityMismatch, Bool.false_eq_true, if_false] at run
                cases called : IxIR1.callScalarOracle context address
                    arguments with
                | error error => simp [called] at run
                | ok result =>
                    simp only [called] at run
                    have pair := Except.ok.inj run
                    cases pair
                    exact valid
              · simp [arityMismatch] at run
          | fn definition =>
              cases arityMismatch : arguments.length != definition.arity
              · simp only [arityMismatch, Bool.false_eq_true, if_false] at run
                cases bodyRun : IxIR1.runCode context fuel definition store
                    arguments.reverse definition.body with
                | error error => simp [bodyRun] at run
                | ok result =>
                    rcases result with ⟨bodyStore, bodyValue⟩
                    rw [bodyRun, constructorsBindOk] at run
                    obtain ⟨resultEq, _⟩ := IxIR1.Sim.checkResultWorld_ok run
                    cases resultEq
                    have bodyKnown := contextKnown declarationFound
                    exact ihCode _ _ _ _ _ _ _ contextKnown bodyKnown
                      bodyKnown valid bodyRun
              · simp [arityMismatch] at run
    · intro context store function arguments store' value contextKnown valid run
      rw [IxIR1.applyGo.eq_def] at run
      dsimp only at run
      cases function with
      | lit literal => simp at run
      | erased =>
          cases dropped : IxIR1.dropMany context fuel store arguments with
          | error error => simp [dropped] at run
          | ok droppedStore =>
              rw [dropped, constructorsBindOk] at run
              have pair := Except.ok.inj run
              cases pair
              exact valid.dropMany dropped
      | loc location =>
          cases found : store.get? location with
          | none => simp [found] at run
          | some box =>
              simp only [found] at run
              cases box with
              | mk world rc node =>
                  cases node with
                  | ctorN identity fields => simp at run
                  | papN address arity captured =>
                      dsimp only at run
                      cases retained : IxIR1.dupVals store captured.toList with
                      | error error => simp [retained] at run
                      | ok retainedStore =>
                          rw [retained, constructorsBindOk] at run
                          cases released : IxIR1.dropVal context fuel
                              retainedStore (.loc location) with
                          | error error => simp [released] at run
                          | ok readyStore =>
                              rw [released, constructorsBindOk] at run
                              have readyValid :=
                                (valid.dupVals retained).dropVal released
                              by_cases under :
                                  (captured.toList ++ arguments).length < arity
                              · simp only [under, if_true] at run
                                have pair := Except.ok.inj run
                                cases pair
                                exact readyValid.allocPap .shared address arity
                                  (captured.toList ++ arguments).toArray
                              · simp only [under, if_false] at run
                                by_cases exactArity :
                                    (captured.toList ++ arguments).length = arity
                                · simp only [exactArity, beq_self_eq_true,
                                      if_true] at run
                                  cases declarationFound :
                                      context.decls address with
                                  | none => simp [declarationFound] at run
                                  | some declaration =>
                                      cases papSafe :
                                          IxIR1.declPapSafe declaration with
                                      | false =>
                                          simp [declarationFound, papSafe] at run
                                      | true =>
                                          simp only [declarationFound, papSafe,
                                            if_true] at run
                                          exact ihInvoke _ _ _ _ _ _
                                            contextKnown readyValid run
                                · have notExact :
                                      ((captured.toList ++ arguments).length ==
                                          arity) = false :=
                                    beq_eq_false_iff_ne.mpr exactArity
                                  simp only [notExact, Bool.false_eq_true,
                                    if_false] at run
                                  cases declarationFound :
                                      context.decls address with
                                  | none => simp [declarationFound] at run
                                  | some declaration =>
                                      cases papSafe :
                                          IxIR1.declPapSafe declaration with
                                      | false =>
                                          simp [declarationFound, papSafe] at run
                                      | true =>
                                          simp only [declarationFound, papSafe,
                                            if_true] at run
                                          cases invoked : IxIR1.invoke context
                                              fuel address
                                              ((captured.toList ++ arguments).take
                                                arity) readyStore with
                                          | error error => simp [invoked] at run
                                          | ok called =>
                                              rcases called with
                                                ⟨calledStore, calledValue⟩
                                              simp only [invoked] at run
                                              exact ihApply _ _ _ _ _ _
                                                contextKnown
                                                (ihInvoke _ _ _ _ _ _
                                                  contextKnown readyValid invoked)
                                                run

/-- Operation-level projection of constructor-universe preservation. -/
theorem Sidecars.SourceConstructorsValid.runOp
    {sidecars : Sidecars} {context : IxIR1.Ctx} {fuel : Nat}
    {current : IxIR1.FnDef} {store store' : IxIR1.Store}
    {environment : List IxIR1.RVal} {operation : IxIR1.Op}
    {value : IxIR1.RVal}
    (contextKnown : sidecars.ContextConstructorsKnown context)
    (currentKnown : sidecars.codeConstructorsKnown current.body = true)
    (operationKnown : sidecars.operationConstructorsKnown operation = true)
    (valid : sidecars.SourceConstructorsValid store)
    (run : IxIR1.runOp context fuel current store environment operation =
      .ok (store', value)) :
    sidecars.SourceConstructorsValid store' :=
  (evalConstructorsValidAt sidecars fuel).2.1 _ _ _ _ _ _ _ contextKnown
    currentKnown operationKnown valid run

/-- Higher-order application projection of constructor-universe
preservation. -/
theorem Sidecars.SourceConstructorsValid.applyGo
    {sidecars : Sidecars} {context : IxIR1.Ctx} {fuel : Nat}
    {store store' : IxIR1.Store} {function : IxIR1.RVal}
    {arguments : List IxIR1.RVal} {value : IxIR1.RVal}
    (contextKnown : sidecars.ContextConstructorsKnown context)
    (valid : sidecars.SourceConstructorsValid store)
    (run : IxIR1.applyGo context fuel store function arguments =
      .ok (store', value)) :
    sidecars.SourceConstructorsValid store' :=
  (evalConstructorsValidAt sidecars fuel).2.2.2 _ _ _ _ _ _ contextKnown
    valid run

/-- A final source heap is reachable through the attachment's certified
raw-to-emitted address action. This is deliberately an image predicate rather
than an injectivity requirement: several raw declarations may share one
content address. -/
def CompiledAttachment.SourceStoreImage
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) (store : IxIR1.Store) : Prop :=
  ∃ sourceStore,
    IxIR1.Readdress.Store.mapAddresses
      (attached.source.lowering.result.rebuildRename
        attached.source.lowering.raw) sourceStore = store ∧
      attached.sidecars.SourceConstructorsValid store

/-- CPS boundary for a function return under one exact target continuation
stack.  A handler is deliberately universal over the returning function and
terminal trace coordinates: the recursive worker discovers the actual `ret`
leaf, while the handler owns what happens after that return (halt, ordinary
resume, or `applyMore`).  This lets tail calls reuse the enclosing handler
without rebuilding the unchanged target stack. -/
def SuccessfulReturnHandler
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    (sourceContext : IxIR1.Ctx) (context : Eval.Context)
    (interpretation : Eval.Interpretation)
    (_functionTrace : Lower.FunctionTrace)
    (frameRoots : List IxIR1.Sim.Root)
    (stack : List Eval.Continuation)
    (expected : IxIR1.Store × IxIR1.RVal)
    (outcome : IxIR1.Store × IxIR1.RVal)
    (post : SourceMachinePost) : Prop :=
  ∀ {returningTrace : Lower.FunctionTrace}
      {sourceFuel : Nat} {site : Lower.SourceSite} {blockId : BlockId}
      {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
      {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {generated : Block}
      {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
      {frame : Eval.Frame} {machine : Eval.Machine},
    returningTrace ∈ attached.target.artifact.trace.functions →
    returningTrace.root.Descendant
        (.ret site blockId input entryValueCount sourceAtom targetAtom
          generated) →
    attached.sidecars.TraceStateRel returningTrace
        (.ret site blockId input entryValueCount sourceAtom targetAtom
          generated) sourceStore source frame →
    Lower.Sim.StoreRel sourceStore machine.store →
    Lower.Sim.SourceRuntimeInvariant sourceStore source →
    Lower.Sim.SourceOwnershipAt attached.target.artifact.trace.positions
      (.ret site blockId input entryValueCount sourceAtom targetAtom generated)
      sourceStore source frameRoots →
    IxIR1.runCode sourceContext (sourceFuel + 1) returningTrace.source
        sourceStore source (.ret sourceAtom) = .ok expected →
    IxIR1.Sim.HasWorld expected.1 returningTrace.source.result expected.2 →
    machine.control = .running frame stack →
    frame.credits = #[] →
    attached.SourceStoreImage sourceStore →
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine

/-- The exact-fuel semantic worker property.  Its source recursion is
continuation-passing: local trace steps keep the handler, ordinary calls build
a `.resume` handler for their callee, and over-application builds an
`applyMore` handler.  This is the induction predicate whose closure at every
fuel yields `SuccessfulMainSimulation`. -/
def SuccessfulTraceSimulationAt
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    (sourceContext : IxIR1.Ctx) (context : Eval.Context)
    (interpretation : Eval.Interpretation) (fuel : Nat) : Prop :=
  ∀ {functionTrace : Lower.FunctionTrace} {trace : Lower.CodeTrace}
      {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
      {frameRoots : List IxIR1.Sim.Root}
      {sourceOutput : IxIR1.Store × IxIR1.RVal}
      {outcome : IxIR1.Store × IxIR1.RVal}
      {frame : Eval.Frame} {machine : Eval.Machine}
      {stack : List Eval.Continuation} {post : SourceMachinePost},
    functionTrace ∈ attached.target.artifact.trace.functions →
    functionTrace.root.Descendant trace →
    attached.sidecars.TraceStateRel functionTrace trace sourceStore source
      frame →
    Lower.Sim.StoreRel sourceStore machine.store →
    Lower.Sim.SourceRuntimeInvariant sourceStore source →
    Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions trace sourceStore source
        frameRoots →
    IxIR1.runCode sourceContext fuel functionTrace.source sourceStore source
        trace.sourceCode = .ok sourceOutput →
    IxIR1.Sim.HasWorld sourceOutput.1 functionTrace.source.result
        sourceOutput.2 →
    machine.control = .running frame stack →
    frame.credits = #[] →
    attached.SourceStoreImage sourceStore →
    SuccessfulReturnHandler attached sourceContext context interpretation
      functionTrace frameRoots stack sourceOutput outcome post →
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine

/-- Canonical IxIR₁ evaluator context named by an attached source artifact. -/
def CompiledAttachment.simulationSourceContext
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) : IxIR1.Ctx :=
  { decls :=
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts }

/-- The canonical source context used by the IxIR₂ simulation is exactly
the final emitted IxIR₁ context with its closed-world oracle. -/
theorem CompiledAttachment.simulationSourceContext_eq_addressedCtx
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    attached.simulationSourceContext =
      attached.source.lowering.result.addressedCtx (fun _ _ => none) := by
  unfold CompiledAttachment.simulationSourceContext
    IxIR1.ReaddressAll.Result.addressedCtx
    IxIR1.ReaddressAll.Result.asReaddressResult
    IxIR1.ReaddressAll.Result.declarations
    IxIR1.Readdress.Result.addressedCtx
    IxIR1.Readdress.Result.declarations
  simp only [List.append_nil]
  congr 1
  change IxIR1.HPT.programDeclEnv
      attached.source.lowering.result.artifacts =
    IxIR1.Env.ofList (IxIR1.HPT.declarationEntries
      attached.source.lowering.result.artifacts)
  exact (IxIR1.HPT.OptimizeProgram.envOfList_declarationEntries
    attached.source.lowering.result.artifacts).symm

/-- The successful fully addressed lowering retained by an attachment exposes
the executable exact-source audit used by all raw-to-emitted provenance
arguments. -/
theorem CompiledAttachment.sourceRebuildSemanticAudit
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    attached.source.lowering.result.rebuildSemanticAudit
      attached.source.lowering.raw attached.source.lowering.mainCode = true := by
  have hrun :=
    IxIR1.Lower.readdressAll_run_of_lowerAllIndexedFullyAddressed_eq_ok
      attached.source.lowering.lowerRun
      attached.source.lowering.addressedRun
  exact IxIR1.ReaddressAll.rebuildSemanticAudit_of_run_eq_ok hrun

/-- The rebuild audit supplies the exact context relation from the raw
lowerer output to the final emitted source context used by IxIR₂. -/
theorem CompiledAttachment.sourceContextRenames
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    IxIR1.Readdress.Ctx.Renames
      (attached.source.lowering.result.rebuildRename
        attached.source.lowering.raw)
      (attached.source.exactTargetCtx (fun _ _ => none))
      attached.simulationSourceContext := by
  rw [attached.simulationSourceContext_eq_addressedCtx]
  unfold Ix.Compiler.Pipeline.LoweredCompilation.exactTargetCtx
  exact attached.source.lowering.result.renames_rebuildSourceCtx
    attached.sourceRebuildSemanticAudit
    (fun _ _ => none)

/-- Declaration equality is enough to instantiate the raw-to-emitted context
relation for an arbitrary final oracle. The raw oracle is pulled back through
the same total address action. -/
theorem CompiledAttachment.sourceContextRenamesOfDeclarations
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    (sourceContext : IxIR1.Ctx)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts) :
    IxIR1.Readdress.Ctx.Renames
      (attached.source.lowering.result.rebuildRename
        attached.source.lowering.raw)
      (attached.source.exactTargetCtx sourceContext.oracle) sourceContext := by
  have contexts :=
    attached.source.lowering.result.renames_rebuildSourceCtx
      attached.sourceRebuildSemanticAudit sourceContext.oracle
  unfold Ix.Compiler.Pipeline.LoweredCompilation.exactTargetCtx
  have targetEq : attached.source.lowering.result.addressedCtx
      sourceContext.oracle = sourceContext := by
    cases sourceContext with
    | mk declarations oracle =>
        simp only at sourceDeclarations
        unfold IxIR1.ReaddressAll.Result.addressedCtx
          IxIR1.ReaddressAll.Result.asReaddressResult
          IxIR1.ReaddressAll.Result.declarations
          IxIR1.Readdress.Result.addressedCtx
          IxIR1.Readdress.Result.declarations
        simp only [List.append_nil]
        congr 1
        rw [sourceDeclarations]
        exact IxIR1.HPT.OptimizeProgram.envOfList_declarationEntries
          attached.source.lowering.result.artifacts
  rw [targetEq] at contexts
  exact contexts

/-- Every literal source suffix retained by the checked IxIR₂ sidecar has an
exact raw IxIR₁ syntax preimage. The proof combines source-site traversal with
the rebuild audit's selected-declaration producer witness, so it remains valid
when content addressing merges equal declarations. -/
theorem CompiledAttachment.sourceCodeAddressImage
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {site : Lower.SourceSite} {code : IxIR1.Code}
    (found : attached.sidecars.sourceCodeAt? site = some code) :
    ∃ rawCode,
      IxIR1.Readdress.Code.mapAddresses
        (attached.source.lowering.result.rebuildRename
          attached.source.lowering.raw) rawCode = code := by
  refine attached.sidecars.sourceCodeAt?_addressImage
      (attached.source.lowering.result.rebuildRename
        attached.source.lowering.raw) ?_ ?_ found
  · refine ⟨attached.source.lowering.mainCode, ?_⟩
    rw [attached.inputProduced]
    exact (attached.source.lowering.result.main_eq_rebuildMapAddresses
      attached.sourceRebuildSemanticAudit).symm
  · intro address definition lookup
    rw [attached.inputProduced] at lookup
    change IxIR1.Env.ofList attached.source.lowering.result.declarations
      address = some (.fn definition) at lookup
    obtain ⟨sourceAddress, sourceDeclaration, sourceLookup, renameEq,
        declarationImage⟩ :=
      attached.source.lowering.result
        |>.declaration_preimage_of_lookup_of_rebuildSemanticAudit
          attached.sourceRebuildSemanticAudit lookup
    cases sourceDeclaration with
    | extern arity =>
        simp [IxIR1.Readdress.Decl.mapAddresses] at declarationImage
    | fn sourceDefinition =>
        simp only [IxIR1.Readdress.Decl.mapAddresses,
          IxIR1.Decl.fn.injEq] at declarationImage
        exact ⟨sourceDefinition, declarationImage⟩

/-- Every retained IxIR₂ function trace names a final IxIR₁ function whose
body has an exact raw syntax preimage. Signature metadata is unchanged by
readdressing, so the body witness lifts to the complete function record. -/
theorem CompiledAttachment.functionSourceAddressImage
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions) :
    ∃ rawDefinition,
      IxIR1.Readdress.FnDef.mapAddresses
        (attached.source.lowering.result.rebuildRename
          attached.source.lowering.raw) rawDefinition = functionTrace.source := by
  have rootFound : attached.sidecars.sourceCodeAt?
      functionTrace.root.source = some functionTrace.root.sourceCode := by
    by_cases owner : functionTrace.owner = .main
    · have mainMatch := attached.target.artifact.functionTraceOrderProof
        |>.main_of_mem_owner functionMember owner
      simpa [functionTrace.rootSource, owner, functionTrace.rootSourceCode,
        mainMatch.source, attached.targetSourceProduced,
        Lower.Input.mainDefinition] using
        attached.sidecars.sourceCodeAt?_main
    · exact attached.sidecars.sourceCodeAt?_functionRoot
        (attached.functionTraceAnalysisCurrent functionMember owner)
  obtain ⟨rawBody, bodyImage⟩ := attached.sourceCodeAddressImage rootFound
  rw [functionTrace.rootSourceCode] at bodyImage
  cases sourceEq : functionTrace.source with
  | mk arity result papSafe body =>
      have bodyImage' : IxIR1.Readdress.Code.mapAddresses
        (attached.source.lowering.result.rebuildRename
          attached.source.lowering.raw) rawBody = body := by
        simpa [sourceEq] using bodyImage
      refine ⟨⟨arity, result, papSafe, rawBody⟩, ?_⟩
      simpa [IxIR1.Readdress.FnDef.mapAddresses] using bodyImage'

/-- At a retained `letOp`, both the current function and the exact operation
are raw syntax images. This packages the two syntax premises consumed by
single-operation evaluator reflection. -/
theorem CompiledAttachment.letOpAddressImages
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frame : Eval.Frame}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) sourceStore source frame) :
    ∃ rawCurrent rawOperation,
      IxIR1.Readdress.FnDef.mapAddresses
          (attached.source.lowering.result.rebuildRename
            attached.source.lowering.raw) rawCurrent = functionTrace.source ∧
        IxIR1.Readdress.Op.mapAddresses
          (attached.source.lowering.result.rebuildRename
            attached.source.lowering.raw) rawOperation = operation := by
  obtain ⟨rawCurrent, currentImage⟩ :=
    attached.functionSourceAddressImage functionMember
  have sourceAt : attached.sidecars.sourceCodeAt? site =
      some (.letOp operation next.sourceCode) := by
    simpa [Lower.CodeTrace.source, Lower.CodeTrace.sourceCode] using
      state.sourceCode
  obtain ⟨rawCode, codeImage⟩ := attached.sourceCodeAddressImage sourceAt
  cases rawCode with
  | ret atom =>
      simp [IxIR1.Readdress.Code.mapAddresses] at codeImage
  | case scrutinee peelNat alternatives =>
      simp [IxIR1.Readdress.Code.mapAddresses] at codeImage
  | letOp rawOperation rawNext =>
      simp only [IxIR1.Readdress.Code.mapAddresses,
        IxIR1.Code.letOp.injEq] at codeImage
      exact ⟨rawCurrent, rawOperation, currentImage, codeImage.1⟩

/-- The validated IxIR₁ compiler constructs the higher-order ownership
contract on the exact raw context, before final declaration readdressing. -/
theorem CompiledAttachment.rawApplyOwnership
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    IxIR1.Sim.ApplyOwnershipContract
      (attached.source.exactTargetCtx (fun _ _ => none)) :=
  (attached.source.exactCompilerContracts (fun _ _ => none)).1.apply

/-- The empty source heap is an exact image for every attachment. -/
theorem CompiledAttachment.sourceStoreImage_empty
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    attached.SourceStoreImage ({} : IxIR1.Store) := by
  exact ⟨{}, by simp [IxIR1.Readdress.Store.mapAddresses],
    Sidecars.SourceConstructorsValid.empty attached.sidecars⟩

/-- Every successful retained source operation preserves exact raw heap-image
provenance. The sidecar supplies raw preimages for the current function and
operation, while evaluator reflection supplies the output heap witness. -/
theorem CompiledAttachment.runOp_preservesSourceStoreImage
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next))
    {store store' : IxIR1.Store} {source : List IxIR1.RVal}
    {frame : Eval.Frame} {fuel : Nat} {value : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) store source frame)
    (image : attached.SourceStoreImage store)
    (run : IxIR1.runOp sourceContext fuel
      functionTrace.source store source operation = .ok (store', value)) :
    attached.SourceStoreImage store' := by
  obtain ⟨rawStore, storeImage, constructorsValid⟩ := image
  have outputConstructors :
      attached.sidecars.SourceConstructorsValid store' :=
    constructorsValid.runOp
      (attached.sourceContextConstructorsKnown sourceDeclarations)
      (attached.functionCodeConstructorsKnown functionMember)
      (attached.descendantOperationConstructorsKnown functionMember descendant)
      run
  obtain ⟨rawCurrent, rawOperation, currentImage, operationImage⟩ :=
    attached.letOpAddressImages functionMember state
  rw [← storeImage, ← currentImage, ← operationImage] at run
  obtain ⟨rawStore', rawRun, outputImage⟩ :=
    IxIR1.Readdress.runOp_success_preimage
      (attached.sourceContextRenamesOfDeclarations sourceContext
        sourceDeclarations) run
  exact ⟨rawStore', outputImage.symm, outputConstructors⟩

/-- Reference-count duplication preserves the attachment's exact heap-image
predicate, including the intermediate stores used to enter PAP callees. -/
theorem CompiledAttachment.dupVals_preservesSourceStoreImage
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {store store' : IxIR1.Store} {values : List IxIR1.RVal}
    (image : attached.SourceStoreImage store)
    (run : IxIR1.dupVals store values = .ok store') :
    attached.SourceStoreImage store' := by
  obtain ⟨rawStore, storeImage, constructorsValid⟩ := image
  have outputConstructors := constructorsValid.dupVals run
  subst store
  obtain ⟨rawStore', rawRun, outputImage⟩ :=
    IxIR1.Readdress.dupVals_success_preimage run
  exact ⟨rawStore', outputImage.symm, outputConstructors⟩

/-- Shared destruction preserves exact heap-image provenance in every final
context whose declarations agree with the attached source artifact. -/
theorem CompiledAttachment.dropVal_preservesSourceStoreImage
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    {fuel : Nat} {store store' : IxIR1.Store} {value : IxIR1.RVal}
    (image : attached.SourceStoreImage store)
    (run : IxIR1.dropVal sourceContext fuel store value = .ok store') :
    attached.SourceStoreImage store' := by
  obtain ⟨rawStore, storeImage, constructorsValid⟩ := image
  have outputConstructors := constructorsValid.dropVal run
  subst store
  obtain ⟨rawStore', rawRun, outputImage⟩ :=
    IxIR1.Readdress.dropVal_success_preimage
      (attached.sourceContextRenamesOfDeclarations sourceContext
        sourceDeclarations) run
  exact ⟨rawStore', outputImage.symm, outputConstructors⟩

/-- List destruction preserves exact heap-image provenance in every compatible
final source context. -/
theorem CompiledAttachment.dropMany_preservesSourceStoreImage
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    {fuel : Nat} {store store' : IxIR1.Store} {values : List IxIR1.RVal}
    (image : attached.SourceStoreImage store)
    (run : IxIR1.dropMany sourceContext fuel store values = .ok store') :
    attached.SourceStoreImage store' := by
  obtain ⟨rawStore, storeImage, constructorsValid⟩ := image
  have outputConstructors := constructorsValid.dropMany run
  subst store
  obtain ⟨rawStore', rawRun, outputImage⟩ :=
    IxIR1.Readdress.dropMany_success_preimage
      (attached.sourceContextRenamesOfDeclarations sourceContext
        sourceDeclarations) run
  exact ⟨rawStore', outputImage.symm, outputConstructors⟩

/-- A successful application from the compiler-certified raw context has an
identical run in the emitted context on the address-renamed heap, and the
renamed output retains exact root ownership. This is the forward image needed
by compiled executions; it deliberately makes no claim about arbitrary final
heaps that are not images of raw heaps. -/
theorem CompiledAttachment.applyGo_exactImage
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {fuel : Nat} {store store' : IxIR1.Store}
    {function : IxIR1.RVal} {args : List IxIR1.RVal}
    {value : IxIR1.RVal} {rest : List IxIR1.Sim.Root}
    (ownership : IxIR1.Sim.RootOwnership store
      (⟨.shared, function⟩ ::
        IxIR1.Sim.rootsFor .shared args ++ rest))
    (run : IxIR1.applyGo
      (attached.source.exactTargetCtx (fun _ _ => none))
      fuel store function args = .ok (store', value)) :
    IxIR1.applyGo attached.simulationSourceContext fuel
        (IxIR1.Readdress.Store.mapAddresses
          (attached.source.lowering.result.rebuildRename
            attached.source.lowering.raw) store)
        function args =
      .ok
        (IxIR1.Readdress.Store.mapAddresses
          (attached.source.lowering.result.rebuildRename
            attached.source.lowering.raw) store', value) ∧
    IxIR1.Sim.RootOwnership
      (IxIR1.Readdress.Store.mapAddresses
        (attached.source.lowering.result.rebuildRename
          attached.source.lowering.raw) store')
      (⟨.shared, value⟩ :: rest) := by
  constructor
  · rw [IxIR1.Readdress.applyGo_mapAddresses
      attached.sourceContextRenames, run]
    rfl
  · apply (IxIR1.Sim.rootOwnership_mapAddresses_iff
      (attached.source.lowering.result.rebuildRename
        attached.source.lowering.raw) store'
      (⟨.shared, value⟩ :: rest)).mpr
    exact attached.rawApplyOwnership.preserves ownership run

/-- On an exact source-heap image, every successful emitted-context
application both preserves the image invariant and obtains its ownership
postcondition from the compiler-certified raw contract. This is the
worker-facing direction of `applyGo_exactImage`. -/
theorem CompiledAttachment.applyGo_owned_of_sourceStoreImage
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {fuel : Nat} {store store' : IxIR1.Store}
    {function : IxIR1.RVal} {args : List IxIR1.RVal}
    {value : IxIR1.RVal} {rest : List IxIR1.Sim.Root}
    (image : attached.SourceStoreImage store)
    (ownership : IxIR1.Sim.RootOwnership store
      (⟨.shared, function⟩ ::
        IxIR1.Sim.rootsFor .shared args ++ rest))
    (run : IxIR1.applyGo attached.simulationSourceContext fuel store
      function args = .ok (store', value)) :
    attached.SourceStoreImage store' ∧
      IxIR1.Sim.RootOwnership store' (⟨.shared, value⟩ :: rest) := by
  obtain ⟨sourceStore, sourceStoreEq, constructorsValid⟩ := image
  have outputConstructors :
      attached.sidecars.SourceConstructorsValid store' :=
    constructorsValid.applyGo
      (attached.sourceContextConstructorsKnown (sourceDeclarations := rfl)) run
  subst store
  obtain ⟨sourceStore', sourceRun, outputStoreEq⟩ :=
    IxIR1.Readdress.applyGo_success_preimage
      attached.sourceContextRenames run
  have sourceOwnership : IxIR1.Sim.RootOwnership sourceStore
      (⟨.shared, function⟩ ::
        IxIR1.Sim.rootsFor .shared args ++ rest) :=
    (IxIR1.Sim.rootOwnership_mapAddresses_iff
      (attached.source.lowering.result.rebuildRename
        attached.source.lowering.raw) sourceStore
      (⟨.shared, function⟩ ::
        IxIR1.Sim.rootsFor .shared args ++ rest)).mp ownership
  have sourceOutputOwnership : IxIR1.Sim.RootOwnership sourceStore'
      (⟨.shared, value⟩ :: rest) :=
    attached.rawApplyOwnership.preserves sourceOwnership sourceRun
  constructor
  · exact ⟨sourceStore', outputStoreEq.symm, outputConstructors⟩
  · rw [outputStoreEq]
    exact (IxIR1.Sim.rootOwnership_mapAddresses_iff
      (attached.source.lowering.result.rebuildRename
        attached.source.lowering.raw) sourceStore'
      (⟨.shared, value⟩ :: rest)).mpr sourceOutputOwnership

/-- Declaration-compatible source contexts obtain the same image-restricted
application theorem for their own oracle. This is the generic trace-worker
form; certified programs contain no externs, but retaining the oracle exactly
keeps the evaluator transport statement total. -/
theorem CompiledAttachment.applyGo_owned_of_sourceStoreImage_of_declarations
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    {fuel : Nat} {store store' : IxIR1.Store}
    {function : IxIR1.RVal} {args : List IxIR1.RVal}
    {value : IxIR1.RVal} {rest : List IxIR1.Sim.Root}
    (image : attached.SourceStoreImage store)
    (ownership : IxIR1.Sim.RootOwnership store
      (⟨.shared, function⟩ ::
        IxIR1.Sim.rootsFor .shared args ++ rest))
    (run : IxIR1.applyGo sourceContext fuel store function args =
      .ok (store', value)) :
    attached.SourceStoreImage store' ∧
      IxIR1.Sim.RootOwnership store' (⟨.shared, value⟩ :: rest) := by
  obtain ⟨sourceStore, sourceStoreEq, constructorsValid⟩ := image
  have outputConstructors :
      attached.sidecars.SourceConstructorsValid store' :=
    constructorsValid.applyGo
      (attached.sourceContextConstructorsKnown sourceDeclarations) run
  subst store
  let contexts := attached.sourceContextRenamesOfDeclarations sourceContext
    sourceDeclarations
  obtain ⟨sourceStore', sourceRun, outputStoreEq⟩ :=
    IxIR1.Readdress.applyGo_success_preimage contexts run
  have sourceOwnership : IxIR1.Sim.RootOwnership sourceStore
      (⟨.shared, function⟩ ::
        IxIR1.Sim.rootsFor .shared args ++ rest) :=
    (IxIR1.Sim.rootOwnership_mapAddresses_iff
      (attached.source.lowering.result.rebuildRename
        attached.source.lowering.raw) sourceStore
      (⟨.shared, function⟩ ::
        IxIR1.Sim.rootsFor .shared args ++ rest)).mp ownership
  have rawContract : IxIR1.Sim.ApplyOwnershipContract
      (attached.source.exactTargetCtx sourceContext.oracle) :=
    (attached.source.exactCompilerContracts sourceContext.oracle).1.apply
  have sourceOutputOwnership : IxIR1.Sim.RootOwnership sourceStore'
      (⟨.shared, value⟩ :: rest) :=
    rawContract.preserves sourceOwnership sourceRun
  constructor
  · exact ⟨sourceStore', outputStoreEq.symm, outputConstructors⟩
  · rw [outputStoreEq]
    exact (IxIR1.Sim.rootOwnership_mapAddresses_iff
      (attached.source.lowering.result.rebuildRename
        attached.source.lowering.raw) sourceStore'
      (⟨.shared, value⟩ :: rest)).mpr sourceOutputOwnership

/-- The generic image theorem exposes precisely the fixed-input law required
by checked trace ownership. -/
theorem CompiledAttachment.applyOwnershipPreservesFrom_sourceStoreImage_of_declarations
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    {fuel : Nat} {store : IxIR1.Store}
    (image : attached.SourceStoreImage store) :
    IxIR1.Sim.ApplyOwnershipPreservesFrom sourceContext fuel store := by
  intro store' function args value rest ownership run
  exact (attached.applyGo_owned_of_sourceStoreImage_of_declarations
    sourceDeclarations image ownership run).2

/-- Exact heap-image provenance specializes the raw compiler theorem to the
fixed-input ownership interface consumed by trace simulation. -/
theorem CompiledAttachment.applyOwnershipPreservesFrom_sourceStoreImage
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {fuel : Nat} {store : IxIR1.Store}
    (image : attached.SourceStoreImage store) :
    IxIR1.Sim.ApplyOwnershipPreservesFrom
      attached.simulationSourceContext fuel store := by
  intro store' function args value rest ownership run
  exact (attached.applyGo_owned_of_sourceStoreImage image ownership run).2

/-- At an HPT-ambiguous case, exact source-heap provenance identifies the
runtime constructor as a member of the producer universe.  The attachment's
residual coverage audit therefore supplies the complete parallel target
branch selection. -/
theorem CompiledAttachment.constructorSwitchSelection_of_residual_nonempty
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    {sourceStore : IxIR1.Store} {location : Nat} {box : IxIR1.NodeBox}
    {identity : CtorId} {fields : Array IxIR1.RVal}
    {fieldCount alternativeIndex : Nat} {body : IxIR1.Code}
    (ambiguous : attached.sidecars.exactConstructorAt? site sourceScrutinee =
      none)
    (image : attached.SourceStoreImage sourceStore)
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN identity fields)
    (sourceAlternative : Lower.sourceAlternativeAtTag? alternatives
      identity.cidx =
        some (.mk identity.cidx fieldCount body, alternativeIndex))
    (fieldArity : fields.size = fieldCount) :
    Nonempty (ConstructorSwitchSelection targetScrutinee generated outgoing
      children identity) := by
  obtain ⟨rawStore, storeImage, constructorsValid⟩ := image
  have runtimeKnown : attached.sidecars.constructorKnown identity
      fields.size = true := by
    cases box with
    | mk world rc boxNode =>
        change boxNode = .ctorN identity fields at node
        subst boxNode
        exact constructorsValid.constructorKnown sourceGet
  have known : ∃ info ∈ attached.sidecars.constructors,
      info.identity = identity ∧ info.arity = fieldCount :=
    attached.sidecars.constructorKnown_witness
      (by simpa [fieldArity] using runtimeKnown)
  obtain ⟨constructors, targetPeel, _, terminator⟩ :=
    Lower.CodeTrace.switchSyntax_of_match
      (functionTrace.descendantSyntaxMatches descendant)
  have rootCoverage :=
    attached.sidecars.functionCodeResidualCaseTargetsMatch
      attached.traceResidualCaseTargetsProduced functionMember
  have localCoverage :=
    attached.sidecars.codeResidualCaseTargetsMatch_descendant rootCoverage
      descendant
  obtain ⟨target, targetAlternative⟩ :=
    attached.sidecars.residualCaseTarget_of_codeResidualCaseTargetsMatch
      localCoverage ambiguous known sourceAlternative terminator
  have targetMember : target ∈ constructors :=
    Array.mem_of_find?_eq_some targetAlternative
  obtain ⟨index, targetAt⟩ := (Array.mem_iff_getElem?).mp targetMember
  have branchMatch := Lower.CodeTrace.switchNodeBranchesMatch_of_match
    (functionTrace.descendantSwitchBranchesMatch descendant)
  have branchMatch' := branchMatch
  unfold Lower.switchNodeBranchesMatch at branchMatch'
  rw [terminator] at branchMatch'
  simp only [Bool.and_eq_true] at branchMatch'
  obtain ⟨⟨⟨outgoingLength, childrenLength⟩, _⟩, _⟩ := branchMatch'
  have targetBound : index < constructors.size :=
    (Array.getElem?_eq_some_iff.mp targetAt).1
  have edgeBound : index < outgoing.length := by
    have lengthEq := beq_iff_eq.mp outgoingLength
    omega
  have childBound : index < children.length := by
    have lengthEq := beq_iff_eq.mp childrenLength
    omega
  let edge := outgoing[index]'edgeBound
  let child := children[index]'childBound
  have edgeAt : outgoing[index]? = some edge :=
    List.getElem?_eq_some_iff.mpr ⟨edgeBound, rfl⟩
  have childAt : children[index]? = some child :=
    List.getElem?_eq_some_iff.mpr ⟨childBound, rfl⟩
  exact ⟨
    { constructors
      targetPeel
      index
      target
      edge
      child
      terminator
      targetAt
      targetAlternative
      edgeAt
      childAt }⟩

/-- Proof-relevant residual constructor selection derived wholly from an
attached producer artifact and its reachable source-heap image. -/
noncomputable def CompiledAttachment.constructorSwitchSelection_of_residual
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    {sourceStore : IxIR1.Store} {location : Nat} {box : IxIR1.NodeBox}
    {identity : CtorId} {fields : Array IxIR1.RVal}
    {fieldCount alternativeIndex : Nat} {body : IxIR1.Code}
    (ambiguous : attached.sidecars.exactConstructorAt? site sourceScrutinee =
      none)
    (image : attached.SourceStoreImage sourceStore)
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN identity fields)
    (sourceAlternative : Lower.sourceAlternativeAtTag? alternatives
      identity.cidx =
        some (.mk identity.cidx fieldCount body, alternativeIndex))
    (fieldArity : fields.size = fieldCount) :
    ConstructorSwitchSelection targetScrutinee generated outgoing children
      identity :=
  Classical.choice
    (attached.constructorSwitchSelection_of_residual_nonempty functionMember
      descendant ambiguous image sourceGet node sourceAlternative fieldArity)

/-- Canonical IxIR₂ evaluator context named by an attached target artifact. -/
def CompiledAttachment.simulationTargetContext
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) : Eval.Context :=
  Eval.Context.ofProgram attached.target.artifact.program
    attached.target.artifact.validationContext.schemas

/-- Semantic/environment obligations shared by every branch of the exhaustive
fuel worker. Declaration and schema identities pin both evaluators to the
attached artifact. Reuse freedom and reachable-heap application ownership are
derived from the attachment, as are exact and ambiguous-HPT constructor
selections. -/
structure SuccessfulSimulationContracts
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) (sourceContext : IxIR1.Ctx) (context : Eval.Context) : Type
    where
  sourceDeclarations : sourceContext.decls =
    IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts
  targetDeclarations : context.declarations =
    (Eval.Context.ofProgram attached.target.artifact.program
      attached.target.artifact.validationContext.schemas).declarations
  targetSchemas : context.schemas =
    attached.target.artifact.validationContext.schemas

/-- Construct the worker contract over the exact contexts carried by an
attachment, discharging all identity fields definitionally. -/
def CompiledAttachment.successfulSimulationContracts
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    SuccessfulSimulationContracts attached attached.simulationSourceContext
      attached.simulationTargetContext :=
  { sourceDeclarations := rfl
    targetDeclarations := rfl
    targetSchemas := rfl }

/-- Fuel zero is the vacuous base of the recursive trace worker: no IxIR₁
code shape can return successfully without one control-fuel constructor. -/
theorem successfulTraceSimulationAt_zero
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    (sourceContext : IxIR1.Ctx) (context : Eval.Context)
    (interpretation : Eval.Interpretation) :
    SuccessfulTraceSimulationAt attached sourceContext context interpretation
      0 := by
  intro functionTrace trace sourceStore source frameRoots sourceOutput outcome
    frame machine stack post member descendant state stores runtime ownership
    sourceRun
  rw [IxIR1.runCode.eq_def] at sourceRun
  contradiction

/-- The outermost empty continuation is a concrete successful-return handler:
one checked target return halts with the same value and exact related heap. -/
theorem CompiledAttachment.haltReturnHandler
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    (sourceContext : IxIR1.Ctx) (context : Eval.Context)
    (interpretation : Eval.Interpretation)
    (functionTrace : Lower.FunctionTrace)
    (sourceOutput : IxIR1.Store × IxIR1.RVal) :
    SuccessfulReturnHandler attached sourceContext context interpretation
      functionTrace [] [] sourceOutput sourceOutput
      (fun sourceStore value machine =>
        machine.control = .halted value ∧
          Lower.Sim.StoreRel sourceStore machine.store) := by
  intro returningTrace sourceFuel site blockId input entryValueCount sourceAtom
    targetAtom generated sourceStore source frame machine returningMember
    descendant state stores runtime ownership sourceRun resultWorld control
    noCredits image
  obtain ⟨value, outputEq, targetSteps, nextStores⟩ :=
    attached.simulate_traced_ret_halt_success descendant state stores sourceRun
      resultWorld control noCredits
  cases outputEq
  have reached : ReachesPost context interpretation
      (fun sourceStore value machine =>
        machine.control = .halted value ∧
          Lower.Sim.StoreRel sourceStore machine.store)
      sourceStore value machine :=
    ⟨1, { machine with control := .halted value }, targetSteps, rfl,
      nextStores⟩
  exact ⟨machine.heapFuel, by simpa using reached⟩

/-- Turn the smaller-fuel caller worker into the return handler for an
ordinary callee.  The callee's terminal step restores the exact suspended
caller trace state; the caller worker then consumes its source continuation.
This lemma is the central `.resume` knot of the CPS induction. -/
private theorem resumeReturnHandlerWithOwnership
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {callerFuel operationFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    (callerMember : callerTrace ∈ attached.target.artifact.trace.functions)
    {callSite : Lower.SourceSite} {callBlock : BlockId}
    {callInput nextInput : Lower.Sim.EnvMap}
    {callEntryValueCount callIndex : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    (callerDescendant : callerTrace.root.Descendant
      (.letOp callSite callBlock callInput nextInput callEntryValueCount
        operation callIndex instruction next))
    {callerStore outputStore finalStore : IxIR1.Store}
    {callerSource : List IxIR1.RVal} {value finalValue : IxIR1.RVal}
    {calleeFrameRoots callerFrameRoots : List IxIR1.Sim.Root}
    {callerFrame : Eval.Frame} {rest : List Eval.Continuation}
    (callerState : attached.sidecars.TraceStateRel callerTrace
      (.letOp callSite callBlock callInput nextInput callEntryValueCount
        operation callIndex instruction next)
      callerStore callerSource callerFrame)
    (binder : Lower.Instr.baselineBinderAtom callEntryValueCount instruction =
      some (.reg callEntryValueCount))
    (delta : Lower.Instr.baselineValueDelta instruction = some 1)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceOperation : IxIR1.runOp sourceContext operationFuel
      callerTrace.source callerStore callerSource operation =
        .ok (outputStore, value))
    (callerRuntime : Lower.Sim.SourceRuntimeInvariant outputStore
      (value :: callerSource))
    (callerOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions next outputStore
        (value :: callerSource) callerFrameRoots)
    (callerRun : IxIR1.runCode sourceContext callerFuel callerTrace.source
      outputStore (value :: callerSource) next.sourceCode =
        .ok (finalStore, finalValue))
    (callerResultWorld : IxIR1.Sim.HasWorld finalStore
      callerTrace.source.result finalValue)
    (callerNoCredits : callerFrame.credits = #[])
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation callerTrace callerFrameRoots rest
        (finalStore, finalValue) outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation callerFuel) :
    SuccessfulReturnHandler attached sourceContext context interpretation
      calleeTrace calleeFrameRoots
      (.resume { callerFrame with pc := callerFrame.pc + 1 } :: rest)
      (outputStore, value) outcome post := by
  intro returningTrace returnFuel returnSite returnBlock returnInput
    returnEntryValueCount sourceAtom targetAtom returnGenerated sourceStore
    calleeSource calleeFrame machine returningMember calleeDescendant
    calleeState stores calleeRuntime calleeOwnership sourceReturn resultWorld
    control noCredits calleeImage
  obtain ⟨returnedValue, sourceResolved, outputEq⟩ :=
    IxIR1.runCode_ret_success sourceReturn
  have storeEq : sourceStore = outputStore := by
    exact (congrArg Prod.fst outputEq).symm
  have valueEq : returnedValue = value := by
    exact (congrArg Prod.snd outputEq).symm
  subst sourceStore
  subst returnedValue
  let nextCallerFrame : Eval.Frame :=
    { callerFrame with
      pc := callerFrame.pc + 1
      values := callerFrame.values.push value }
  obtain ⟨_, returnSteps, nextStores, nextState⟩ :=
    attached.simulate_traced_return_to_letOp_state
      (sourceFuel := returnFuel) (context := context)
      (interpretation := interpretation) callerMember
      callerDescendant calleeDescendant callerState calleeState binder delta
      stores sourceDeclarations sourceOperation sourceResolved control noCredits
      (calleeState.target.resultWorld stores resultWorld)
  have nextDescendant : callerTrace.root.Descendant next := by
    exact .step callerDescendant (by simp [Lower.CodeTrace.children])
  have nextControl :
      ({ machine with control := .running nextCallerFrame rest } :
        Eval.Machine).control = .running nextCallerFrame rest := rfl
  have nextNoCredits : nextCallerFrame.credits = #[] := by
    simpa [nextCallerFrame] using callerNoCredits
  have tail := worker (machine :=
      { machine with control := .running nextCallerFrame rest })
    (stack := rest) callerMember nextDescendant nextState nextStores
      callerRuntime callerOwnership callerRun callerResultWorld nextControl
      nextNoCredits calleeImage finish
  obtain ⟨tailHeapFuel, tail⟩ := tail
  let fundedMachine : Eval.Machine := { machine with heapFuel := tailHeapFuel }
  have fundedStores : Lower.Sim.StoreRel outputStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control = .running calleeFrame
      (.resume { callerFrame with pc := callerFrame.pc + 1 } :: rest) := by
    simpa [fundedMachine] using control
  obtain ⟨_, fundedReturnSteps, _, _⟩ :=
    attached.simulate_traced_return_to_letOp_state
      (machine := fundedMachine) (sourceFuel := returnFuel)
      (context := context) (interpretation := interpretation) callerMember
      callerDescendant calleeDescendant callerState calleeState binder delta
      fundedStores sourceDeclarations sourceOperation sourceResolved
      fundedControl noCredits
      (calleeState.target.resultWorld fundedStores resultWorld)
  refine ⟨tailHeapFuel, ?_⟩
  simpa [fundedMachine] using tail.prepend fundedReturnSteps

/-- An exact source result can resume one suspended target frame and then
reach the enclosing postcondition.  This is the target-facing tail shared by
immediate `applyMore` results and by the ordinary return of an exactly
saturated recursive callee. -/
def SuccessfulResumeContinuation
    (context : Eval.Context) (interpretation : Eval.Interpretation)
    (caller : Eval.Frame) (rest : List Eval.Continuation)
    (sourceOutput outcome : IxIR1.Store × IxIR1.RVal)
    (post : SourceMachinePost) : Prop :=
  ∀ {machine : Eval.Machine},
    Lower.Sim.StoreRel sourceOutput.1 machine.store →
    machine.control = .running
      { caller with values := caller.values.push sourceOutput.2 } rest →
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine

/-- A successful resume continuation induces the universal return handler
for any retained callee on the corresponding `.resume` stack.  The terminal
target step preserves heap fuel, so the continuation chooses its own suffix
budget unchanged. -/
private theorem resumeReturnHandlerOfContinuation
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    (functionTrace : Lower.FunctionTrace)
    (frameRoots : List IxIR1.Sim.Root)
    (caller : Eval.Frame) (rest : List Eval.Continuation)
    (sourceOutput outcome : IxIR1.Store × IxIR1.RVal)
    (post : SourceMachinePost)
    (continuation : SuccessfulResumeContinuation context interpretation
      caller rest sourceOutput outcome post) :
    SuccessfulReturnHandler attached sourceContext context interpretation
      functionTrace frameRoots (.resume caller :: rest) sourceOutput outcome
      post := by
  intro returningTrace returnFuel site blockId input entryValueCount sourceAtom
    targetAtom generated sourceStore source frame machine returningMember
    descendant state stores runtime ownership sourceRun resultWorld control
    noCredits image
  obtain ⟨returnedValue, sourceResolved, outputEq⟩ :=
    IxIR1.runCode_ret_success sourceRun
  have storeEq : sourceStore = sourceOutput.1 := by
    exact (congrArg Prod.fst outputEq).symm
  have valueEq : returnedValue = sourceOutput.2 := by
    exact (congrArg Prod.snd outputEq).symm
  subst sourceStore
  subst returnedValue
  let nextMachine : Eval.Machine :=
    { machine with
      control := .running
        { caller with values := caller.values.push sourceOutput.2 } rest }
  have nextStores : Lower.Sim.StoreRel sourceOutput.1 nextMachine.store := by
    simpa [nextMachine] using stores
  have nextControl : nextMachine.control = .running
      { caller with values := caller.values.push sourceOutput.2 } rest := rfl
  have tail := continuation nextStores nextControl
  obtain ⟨tailHeapFuel, tail⟩ := tail
  let fundedMachine : Eval.Machine := { machine with heapFuel := tailHeapFuel }
  let fundedNext : Eval.Machine := { nextMachine with heapFuel := tailHeapFuel }
  have fundedStores : Lower.Sim.StoreRel sourceOutput.1
      fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control =
      .running frame (.resume caller :: rest) := by
    simpa [fundedMachine] using control
  obtain ⟨_, returnSteps, _, _⟩ :=
    Lower.Sim.simulate_traced_ret_resume_state
      (sourceContext := sourceContext)
      (sourceCurrent := returningTrace.source) (sourceFuel := returnFuel)
      (context := context) (interpretation := interpretation)
      (machine := fundedMachine)
      (callerSource := caller.values.toList.reverse)
      (callerMapping := Lower.Sim.entryMap caller.values.size)
      descendant state.target fundedStores (Lower.Sim.EnvRel.entry caller.values)
      sourceResolved fundedControl noCredits
      (state.target.resultWorld fundedStores resultWorld)
  refine ⟨tailHeapFuel, ?_⟩
  have tail' : ReachesPost context interpretation post outcome.1 outcome.2
      fundedNext := by
    simpa [fundedNext, nextMachine] using tail
  simpa [fundedMachine, fundedNext, nextMachine] using
    tail'.prepend returnSteps

/-- Package a recursive caller worker as the exact resumed-frame continuation
consumed by every terminal `applyMore` branch. -/
private theorem resumeContinuationOfWorker
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {callerFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {callerTrace : Lower.FunctionTrace} {next : Lower.CodeTrace}
    (callerMember : callerTrace ∈ attached.target.artifact.trace.functions)
    (nextDescendant : callerTrace.root.Descendant next)
    {outputStore finalStore : IxIR1.Store}
    {callerSource : List IxIR1.RVal} {value finalValue : IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {resumeFrame nextFrame : Eval.Frame} {stack : List Eval.Continuation}
    (nextFrameEq : nextFrame =
      { resumeFrame with values := resumeFrame.values.push value })
    (nextState : attached.sidecars.TraceStateRel callerTrace next outputStore
      (value :: callerSource) nextFrame)
    (runtime : Lower.Sim.SourceRuntimeInvariant outputStore
      (value :: callerSource))
    (image : attached.SourceStoreImage outputStore)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions next outputStore
        (value :: callerSource) frameRoots)
    (callerRun : IxIR1.runCode sourceContext callerFuel callerTrace.source
      outputStore (value :: callerSource) next.sourceCode =
        .ok (finalStore, finalValue))
    (resultWorld : IxIR1.Sim.HasWorld finalStore
      callerTrace.source.result finalValue)
    (noCredits : nextFrame.credits = #[])
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation callerTrace frameRoots stack
        (finalStore, finalValue) outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation callerFuel) :
    SuccessfulResumeContinuation context interpretation resumeFrame stack
      (outputStore, value) outcome post := by
  intro machine stores control
  apply worker callerMember nextDescendant nextState stores runtime ownership
    callerRun resultWorld ?_ noCredits image finish
  simpa [nextFrameEq] using control

/-- A source-success decomposition of one dynamic `applyGo` chain aligned to
the checked target declarations and retained function traces.  The recursive
over-saturated constructor stores the residual plan at the evaluator's
strictly smaller fuel; the other constructors are terminal dispatcher
outcomes. -/
inductive ApplyMorePlan
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    (sourceContext : IxIR1.Ctx) (context : Eval.Context) :
    Nat → IxIR1.Store → IxIR1.RVal → List IxIR1.RVal →
      IxIR1.Store → IxIR1.RVal → Prop where
  | erased {fuel : Nat} {sourceStore sourceReleased : IxIR1.Store}
      {values : List IxIR1.RVal}
      (sourceRelease : IxIR1.dropMany sourceContext fuel sourceStore values =
        .ok sourceReleased) :
      ApplyMorePlan attached sourceContext context (fuel + 1) sourceStore
        .erased values sourceReleased .erased
  | papUnder {fuel : Nat}
      {sourceStore sourceRetained sourceReleased : IxIR1.Store}
      {location : Nat} {box : IxIR1.NodeBox}
      {address : Ixon.Address} {arity : Nat}
      {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
      (sourceGet : sourceStore.get? location = some box)
      (node : box.node = .papN address arity captured)
      (sourceRetain : IxIR1.dupVals sourceStore captured.toList =
        .ok sourceRetained)
      (sourceRelease : IxIR1.dropVal sourceContext fuel sourceRetained
        (.loc location) = .ok sourceReleased)
      (totalUnder : (captured.toList ++ values).length < arity) :
      ApplyMorePlan attached sourceContext context (fuel + 1) sourceStore
        (.loc location) values
        (sourceReleased.allocNode .shared
          (.papN address arity (captured ++ values.toArray))).1
        (.loc (sourceReleased.allocNode .shared
          (.papN address arity (captured ++ values.toArray))).2)
  | papSaturatedFn {fuel calleeFuel : Nat}
      {sourceStore sourceRetained sourceReleased outputStore : IxIR1.Store}
      {location : Nat} {box : IxIR1.NodeBox}
      {address : Ixon.Address} {arity : Nat}
      {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
      {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
      {calleeTrace : Lower.FunctionTrace} {value : IxIR1.RVal}
      (calleeMember : calleeTrace ∈
        attached.target.artifact.trace.functions)
      (calleeMatch : Lower.FunctionTraceMatch calleeTrace
        (.declaration address) sourceDefinition targetDefinition)
      (sourceGet : sourceStore.get? location = some box)
      (node : box.node = .papN address arity captured)
      (sourceRetain : IxIR1.dupVals sourceStore captured.toList =
        .ok sourceRetained)
      (sourceRelease : IxIR1.dropVal sourceContext fuel sourceRetained
        (.loc location) = .ok sourceReleased)
      (totalExact : (captured.toList ++ values).length = arity)
      (papArity : arity = sourceDefinition.arity)
      (sourceDeclaration : sourceContext.decls address =
        some (.fn sourceDefinition))
      (sourcePapSafe : sourceDefinition.papSafe = true)
      (targetDeclaration : context.declarations address =
        some (.fn targetDefinition))
      (calleeRun : IxIR1.runCode sourceContext calleeFuel sourceDefinition
        sourceReleased (captured.toList ++ values).reverse
          sourceDefinition.body = .ok (outputStore, value))
      (calleeResultWorld : IxIR1.Sim.HasWorld outputStore
        sourceDefinition.result value)
      (calleeSmaller : calleeFuel < fuel + 1) :
      ApplyMorePlan attached sourceContext context (fuel + 1) sourceStore
        (.loc location) values outputStore value
  | papOverFn {fuel calleeFuel : Nat}
      {sourceStore sourceRetained sourceReleased calledStore outputStore :
        IxIR1.Store}
      {location : Nat} {box : IxIR1.NodeBox}
      {address : Ixon.Address} {arity : Nat}
      {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
      {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
      {calleeTrace : Lower.FunctionTrace}
      {calledValue outputValue : IxIR1.RVal}
      (calleeMember : calleeTrace ∈
        attached.target.artifact.trace.functions)
      (calleeMatch : Lower.FunctionTraceMatch calleeTrace
        (.declaration address) sourceDefinition targetDefinition)
      (sourceGet : sourceStore.get? location = some box)
      (node : box.node = .papN address arity captured)
      (sourceRetain : IxIR1.dupVals sourceStore captured.toList =
        .ok sourceRetained)
      (sourceRelease : IxIR1.dropVal sourceContext fuel sourceRetained
        (.loc location) = .ok sourceReleased)
      (totalOver : arity < (captured.toList ++ values).length)
      (papArity : arity = sourceDefinition.arity)
      (sourceDeclaration : sourceContext.decls address =
        some (.fn sourceDefinition))
      (sourcePapSafe : sourceDefinition.papSafe = true)
      (targetDeclaration : context.declarations address =
        some (.fn targetDefinition))
      (calleeRun : IxIR1.runCode sourceContext calleeFuel sourceDefinition
        sourceReleased ((captured.toList ++ values).take arity).reverse
          sourceDefinition.body = .ok (calledStore, calledValue))
      (calleeResultWorld : IxIR1.Sim.HasWorld calledStore
        sourceDefinition.result calledValue)
      (calleeSmaller : calleeFuel < fuel + 1)
      (residual : ApplyMorePlan attached sourceContext context fuel calledStore
        calledValue ((captured.toList ++ values).drop arity) outputStore
        outputValue) :
      ApplyMorePlan attached sourceContext context (fuel + 1) sourceStore
        (.loc location) values outputStore outputValue

/-- Every residual plan describes a finite successful source application.
The evaluator bound can exceed the plan's induction index: each stored callee
and release is raised to a common bound when their runs are composed. -/
theorem ApplyMorePlan.sourceRun
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    {attached : CompiledAttachment mainWorld lowerFuel}
    {sourceContext : IxIR1.Ctx} {context : Eval.Context}
    {planFuel : Nat} {sourceStore outputStore : IxIR1.Store}
    {function value : IxIR1.RVal} {arguments : List IxIR1.RVal}
    (plan : ApplyMorePlan attached sourceContext context planFuel
      sourceStore function arguments outputStore value) :
    ∃ fuel, IxIR1.applyGo sourceContext fuel sourceStore function arguments =
      .ok (outputStore, value) := by
  induction plan with
  | @erased fuel store released values sourceRelease =>
      exact ⟨fuel + 1, by
        simp [IxIR1.applyGo, sourceRelease, bind, Except.bind]⟩
  | @papUnder fuel store retained released location box address arity captured
      values sourceGet node sourceRetain sourceRelease totalUnder =>
      refine ⟨fuel + 1, ?_⟩
      simp only [IxIR1.applyGo, sourceGet, node, sourceRetain, sourceRelease,
        totalUnder, if_true, bind, Except.bind]
      have argumentsEq : (captured.toList ++ values).toArray =
          captured ++ values.toArray := by
        apply Array.toList_inj.mp
        simp
      rw [argumentsEq]
  | papSaturatedFn _calleeMember _calleeMatch sourceGet node sourceRetain
      sourceRelease totalExact papArity sourceDeclaration sourcePapSafe
      _targetDeclaration calleeRun calleeResultWorld _calleeSmaller =>
      have called := IxIR1.invoke_of_body_run sourceDeclaration
        (totalExact.trans papArity) calleeRun calleeResultWorld
      obtain ⟨fuel, run⟩ := IxIR1.applyGo_exact_of_invoke sourceGet node
        sourceRetain sourceRelease totalExact sourceDeclaration sourcePapSafe
        called
      exact ⟨fuel + 1, run⟩
  | papOverFn _calleeMember _calleeMatch sourceGet node sourceRetain
      sourceRelease totalOver papArity sourceDeclaration sourcePapSafe
      _targetDeclaration calleeRun calleeResultWorld _calleeSmaller
      _residual ih =>
      have called := IxIR1.invoke_of_body_run (run := calleeRun)
        sourceDeclaration (by
          simpa only [List.length_take,
            Nat.min_eq_left (Nat.le_of_lt totalOver)] using papArity)
        calleeResultWorld
      obtain ⟨residualFuel, residualRun⟩ := ih
      obtain ⟨fuel, run⟩ := IxIR1.applyGo_over_of_invoke sourceGet node
        sourceRetain sourceRelease totalOver sourceDeclaration sourcePapSafe
        called residualRun
      exact ⟨fuel + 1, run⟩

/-- Recover the two dynamic heap facts needed by a target PAP dispatch from
the invariants available at any retained source trace position.  Keeping
these facts out of `ApplyMorePlan` makes the plan a pure decomposition of
`applyGo`; recursive return handlers re-establish them for their current
heap. -/
private theorem CompiledAttachment.livePapFacts
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {functionTrace : Lower.FunctionTrace} {trace : Lower.CodeTrace}
    {store : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (member : functionTrace ∈ attached.target.artifact.trace.functions)
    (descendant : functionTrace.root.Descendant trace)
    (runtime : Lower.Sim.SourceRuntimeInvariant store source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions trace store source frameRoots)
    {location : Nat} {box : IxIR1.NodeBox} {address : Ixon.Address}
    {arity : Nat} {captured : Array IxIR1.RVal}
    (sourceGet : store.get? location = some box)
    (node : box.node = .papN address arity captured) :
    box.world = .shared ∧ captured.size < arity := by
  obtain ⟨position, positionMember, coordinate⟩ :=
    attached.target.position member descendant
  have exactOwnership := ownership position positionMember coordinate
  refine ⟨exactOwnership.ownership.pap_shared sourceGet node, ?_⟩
  cases box with
  | mk world rc actualNode =>
      simp only at node
      subst actualNode
      exact runtime.papsUnder.captured_lt sourceGet

/-- A source declaration selected by the evaluator's first-match environment
selects the correspondingly retained target declaration and function trace.
The lookup-facing whole-program trace theorem handles duplicate raw keys in
the same way as both evaluator contexts. -/
theorem CompiledAttachment.functionTrace_of_source_declaration
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {context : Eval.Context}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (targetDeclarations : context.declarations =
      (Eval.Context.ofProgram attached.target.artifact.program
        attached.target.artifact.validationContext.schemas).declarations)
    {address : Ixon.Address} {sourceDefinition : IxIR1.FnDef}
    (sourceDeclaration : sourceContext.decls address =
      some (.fn sourceDefinition)) :
    ∃ targetDefinition calleeTrace,
      calleeTrace ∈ attached.target.artifact.trace.functions ∧
        Lower.FunctionTraceMatch calleeTrace (.declaration address)
          sourceDefinition targetDefinition ∧
        context.declarations address = some (.fn targetDefinition) := by
  have artifactLookup :
      IxIR1.Env.ofList attached.target.artifact.source.declarations address =
        some (.fn sourceDefinition) := by
    rw [attached.targetSourceProduced]
    rw [attached.sidecarDeclarationEnvironment]
    rw [← sourceDeclarations]
    exact sourceDeclaration
  obtain ⟨targetDefinition, calleeTrace, targetLookup, calleeMember,
      calleeMatch⟩ :=
    attached.target.artifact.functionTrace_of_source_lookup artifactLookup
  refine ⟨targetDefinition, calleeTrace, calleeMember, calleeMatch, ?_⟩
  rw [targetDeclarations]
  exact targetLookup

/-- Inverse lookup-facing form of
`CompiledAttachment.functionTrace_of_source_declaration`.  A concrete target function
selected by the evaluator determines the exact source declaration and
retained callee trace at the same address, including first-binding-wins
behavior for repeated raw declaration keys. -/
theorem CompiledAttachment.functionTrace_of_target_declaration
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {context : Eval.Context}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (targetDeclarations : context.declarations =
      (Eval.Context.ofProgram attached.target.artifact.program
        attached.target.artifact.validationContext.schemas).declarations)
    {address : Ixon.Address} {targetDefinition : Function}
    (targetDeclaration : context.declarations address =
      some (.fn targetDefinition)) :
    ∃ sourceDefinition calleeTrace,
      calleeTrace ∈ attached.target.artifact.trace.functions ∧
        Lower.FunctionTraceMatch calleeTrace (.declaration address)
          sourceDefinition targetDefinition ∧
        sourceContext.decls address = some (.fn sourceDefinition) := by
  have artifactLookup :
      (attached.target.artifact.program.declarations.find? fun entry =>
        entry.1 == address).map (·.2) = some (.fn targetDefinition) := by
    simpa [Eval.Context.ofProgram] using
      (congrFun targetDeclarations address).symm.trans targetDeclaration
  obtain ⟨sourceDefinition, calleeTrace, sourceLookup, calleeMember,
      calleeMatch⟩ :=
    attached.target.artifact.functionTrace_of_target_lookup artifactLookup
  refine ⟨sourceDefinition, calleeTrace, calleeMember, calleeMatch, ?_⟩
  rw [sourceDeclarations]
  rw [← attached.sidecarDeclarationEnvironment]
  rw [← attached.targetSourceProduced]
  exact sourceLookup

/-- Certified pipeline source environments contain no executable extern
declarations.  This is the contradiction used when successful `invoke`
inversion exposes its scalar branch. -/
theorem CompiledAttachment.sourceDeclaration_not_extern
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    {address : Ixon.Address} {arity : Nat}
    (sourceDeclaration : sourceContext.decls address =
      some (.extern arity)) : False := by
  apply attached.source.targetDeclEnv_ne_extern
  change IxIR1.HPT.programDeclEnv
      attached.source.lowering.result.artifacts address =
    some (.extern arity)
  rw [← sourceDeclarations]
  exact sourceDeclaration

/-- A successful target extern lookup is impossible for a certified pipeline
attachment.  Declaration-order alignment reflects it to the source side,
whose emitted environment is closed to extern declarations. -/
theorem CompiledAttachment.targetDeclaration_not_extern
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {context : Eval.Context}
    (targetDeclarations : context.declarations =
      (Eval.Context.ofProgram attached.target.artifact.program
        attached.target.artifact.validationContext.schemas).declarations)
    {address : Ixon.Address} {arity : Nat}
    (targetDeclaration : context.declarations address =
      some (.extern arity)) : False := by
  have artifactLookup :
      (attached.target.artifact.program.declarations.find? fun entry =>
        entry.1 == address).map (·.2) = some (.extern arity) := by
    simpa [Eval.Context.ofProgram] using
      (congrFun targetDeclarations address).symm.trans targetDeclaration
  have sourceLookup :=
    attached.target.artifact.sourceExtern_of_target_lookup artifactLookup
  apply attached.source.targetDeclEnv_ne_extern
  change IxIR1.HPT.programDeclEnv
      attached.source.lowering.result.artifacts address =
    some (.extern arity)
  rw [← attached.sidecarDeclarationEnvironment]
  rw [← attached.targetSourceProduced]
  exact sourceLookup

/-- Every successful source `applyGo` computation admits exactly the
evaluator-aligned plan consumed by `applyMoreReturnHandler_of_plan`.  The
recursive over-application case follows the evaluator's predecessor fuel;
function invocation is inverted to expose the body run and result-world
check, while certified source/target declaration lookup supplies the retained
callee trace. -/
theorem CompiledAttachment.applyMorePlan_of_applyGo
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {context : Eval.Context}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (targetDeclarations : context.declarations =
      (Eval.Context.ofProgram attached.target.artifact.program
        attached.target.artifact.validationContext.schemas).declarations)
    {applyFuel : Nat} {sourceStore outputStore : IxIR1.Store}
    {function outputValue : IxIR1.RVal} {values : List IxIR1.RVal}
    (run : IxIR1.applyGo sourceContext applyFuel sourceStore function values =
      .ok (outputStore, outputValue)) :
    ApplyMorePlan attached sourceContext context applyFuel sourceStore function
      values outputStore outputValue := by
  induction applyFuel generalizing sourceStore function values outputStore
      outputValue with
  | zero =>
      rw [IxIR1.applyGo.eq_def] at run
      contradiction
  | succ fuel ih =>
      rw [IxIR1.applyGo.eq_def] at run
      dsimp only at run
      cases function with
      | lit literal => simp at run
      | erased =>
          cases sourceRelease :
              IxIR1.dropMany sourceContext fuel sourceStore values with
          | error error =>
              rw [sourceRelease] at run
              simp only [bind, Except.bind] at run
              contradiction
          | ok sourceReleased =>
              rw [sourceRelease] at run
              simp only [bind, Except.bind] at run
              have outputEq :
                  (sourceReleased, IxIR1.RVal.erased) =
                    (outputStore, outputValue) :=
                Except.ok.inj run
              cases outputEq
              exact .erased sourceRelease
      | loc location =>
          cases sourceGet : sourceStore.get? location with
          | none => simp [sourceGet] at run
          | some box =>
              simp only [sourceGet] at run
              cases node : box.node with
              | ctorN identity fields =>
                  rw [node] at run
                  contradiction
              | papN address arity captured =>
                  rw [node] at run
                  dsimp only at run
                  cases sourceRetain :
                      IxIR1.dupVals sourceStore captured.toList with
                  | error error =>
                      rw [sourceRetain] at run
                      simp only [bind, Except.bind] at run
                      contradiction
                  | ok sourceRetained =>
                      rw [sourceRetain] at run
                      simp only [bind, Except.bind] at run
                      cases sourceRelease : IxIR1.dropVal sourceContext fuel
                          sourceRetained (.loc location) with
                      | error error =>
                          rw [sourceRelease] at run
                          contradiction
                      | ok sourceReleased =>
                          rw [sourceRelease] at run
                          let total := captured.toList ++ values
                          by_cases totalUnder : total.length < arity
                          · have totalUnderRaw :
                                (captured.toList ++ values).length < arity := by
                              simpa [total] using totalUnder
                            simp only [totalUnderRaw, if_true] at run
                            have totalArrayEq :
                                (captured.toList ++ values).toArray =
                                  captured ++ values.toArray := by
                              apply Array.toList_inj.mp
                              simp
                            rw [totalArrayEq] at run
                            have outputEq :
                                (outputStore, outputValue) =
                                  ((sourceReleased.allocNode .shared
                                    (.papN address arity
                                      (captured ++ values.toArray))).1,
                                    .loc (sourceReleased.allocNode .shared
                                      (.papN address arity
                                        (captured ++ values.toArray))).2) := by
                              symm
                              simpa using Except.ok.inj run
                            cases outputEq
                            exact .papUnder sourceGet node sourceRetain
                              sourceRelease totalUnderRaw
                          · have totalNotUnderRaw :
                                ¬(captured.toList ++ values).length < arity := by
                              simpa [total] using totalUnder
                            simp only [totalNotUnderRaw, if_false] at run
                            cases totalExactBool :
                                (captured.toList ++ values).length == arity with
                            | false =>
                                simp only [totalExactBool, Bool.false_eq_true,
                                  if_false] at run
                                have totalNotExact : total.length ≠ arity := by
                                  simpa [total] using totalExactBool
                                have totalOver : arity < total.length := by
                                  omega
                                cases sourceDeclarationRaw :
                                    sourceContext.decls address with
                                | none => simp [sourceDeclarationRaw] at run
                                | some declaration =>
                                    cases sourcePapSafeRaw :
                                        IxIR1.declPapSafe declaration with
                                    | false =>
                                        simp [sourceDeclarationRaw,
                                          sourcePapSafeRaw] at run
                                    | true =>
                                        simp only [sourceDeclarationRaw,
                                          sourcePapSafeRaw, if_true] at run
                                        cases invocationRun : IxIR1.invoke
                                            sourceContext fuel address
                                            ((captured.toList ++ values).take
                                              arity) sourceReleased with
                                        | error error =>
                                            rw [invocationRun] at run
                                            contradiction
                                        | ok called =>
                                            rcases called with
                                              ⟨calledStore, calledValue⟩
                                            rw [invocationRun] at run
                                            obtain ⟨calleeFuel, fuelEq,
                                                invocation⟩ :=
                                              IxIR1.invoke_success invocationRun
                                            cases invocation with
                                            | @fn sourceDefinition bodyOutput
                                                sourceDeclaration argumentArity
                                                calleeRun resultRun =>
                                                have declarationEq : declaration =
                                                    .fn sourceDefinition := by
                                                  exact Option.some.inj
                                                    (sourceDeclarationRaw.symm.trans
                                                      sourceDeclaration)
                                                subst declaration
                                                have sourcePapSafe :
                                                    sourceDefinition.papSafe =
                                                      true := by
                                                  simpa [IxIR1.declPapSafe] using
                                                    sourcePapSafeRaw
                                                obtain ⟨bodyOutputEq,
                                                    calleeResultWorld⟩ :=
                                                  IxIR1.Sim.checkResultWorld_ok
                                                    resultRun
                                                cases bodyOutputEq
                                                obtain ⟨targetDefinition,
                                                    calleeTrace, calleeMember,
                                                    calleeMatch,
                                                    targetDeclaration⟩ :=
                                                  attached.functionTrace_of_source_declaration
                                                    sourceDeclarations
                                                    targetDeclarations
                                                    sourceDeclaration
                                                have suppliedLength :
                                                    (total.take arity).length =
                                                      arity := by
                                                  simp [List.length_take,
                                                    Nat.min_eq_left
                                                      (Nat.le_of_lt totalOver)]
                                                have papArity : arity =
                                                    sourceDefinition.arity :=
                                                  suppliedLength.symm.trans (by
                                                    simpa [total] using
                                                      argumentArity)
                                                have residual := ih
                                                  (sourceStore := calledStore)
                                                  (function := calledValue)
                                                  (values := total.drop arity)
                                                  (outputStore := outputStore)
                                                  (outputValue := outputValue)
                                                  (by simpa [total] using run)
                                                exact .papOverFn calleeMember
                                                  calleeMatch sourceGet node
                                                  sourceRetain sourceRelease
                                                  (by simpa [total] using
                                                    totalOver)
                                                  papArity sourceDeclaration
                                                  sourcePapSafe
                                                  targetDeclaration
                                                  (by simpa [total] using
                                                    calleeRun)
                                                  calleeResultWorld (by omega)
                                                  (by simpa [total] using
                                                    residual)
                                            | @extern externArity externValue
                                                sourceDeclaration _ _ _ =>
                                                exact False.elim
                                                  (attached.sourceDeclaration_not_extern
                                                    sourceDeclarations
                                                    sourceDeclaration)
                            | true =>
                                simp only [totalExactBool, if_true] at run
                                have totalExact : total.length = arity := by
                                  simpa [total] using totalExactBool
                                cases sourceDeclarationRaw :
                                    sourceContext.decls address with
                                | none => simp [sourceDeclarationRaw] at run
                                | some declaration =>
                                    cases sourcePapSafeRaw :
                                        IxIR1.declPapSafe declaration with
                                    | false =>
                                        simp [sourceDeclarationRaw,
                                          sourcePapSafeRaw] at run
                                    | true =>
                                        simp only [sourceDeclarationRaw,
                                          sourcePapSafeRaw, if_true] at run
                                        obtain ⟨calleeFuel, fuelEq,
                                            invocation⟩ :=
                                          IxIR1.invoke_success run
                                        cases invocation with
                                        | @fn sourceDefinition bodyOutput
                                            sourceDeclaration argumentArity
                                            calleeRun resultRun =>
                                            have declarationEq : declaration =
                                                .fn sourceDefinition := by
                                              exact Option.some.inj
                                                (sourceDeclarationRaw.symm.trans
                                                  sourceDeclaration)
                                            subst declaration
                                            have sourcePapSafe :
                                                sourceDefinition.papSafe =
                                                  true := by
                                              simpa [IxIR1.declPapSafe] using
                                                sourcePapSafeRaw
                                            obtain ⟨bodyOutputEq,
                                                calleeResultWorld⟩ :=
                                              IxIR1.Sim.checkResultWorld_ok
                                                resultRun
                                            cases bodyOutputEq
                                            obtain ⟨targetDefinition,
                                                calleeTrace, calleeMember,
                                                calleeMatch,
                                                targetDeclaration⟩ :=
                                              attached.functionTrace_of_source_declaration
                                                sourceDeclarations
                                                targetDeclarations
                                                sourceDeclaration
                                            have papArity : arity =
                                                sourceDefinition.arity :=
                                              totalExact.symm.trans (by
                                                simpa [total] using
                                                  argumentArity)
                                            exact .papSaturatedFn calleeMember
                                              calleeMatch sourceGet node
                                              sourceRetain sourceRelease
                                              (by simpa [total] using totalExact)
                                              papArity sourceDeclaration
                                              sourcePapSafe targetDeclaration
                                              (by simpa [total] using calleeRun)
                                              calleeResultWorld (by omega)
                                        | @extern externArity externValue
                                            sourceDeclaration _ _ _ =>
                                            exact False.elim
                                              (attached.sourceDeclaration_not_extern
                                                sourceDeclarations
                                                sourceDeclaration)

/-- Complete CPS composition for the `pure`/`move` trace branch.  Source
success is inverted once, the generated target instruction takes one genuine
step, and the exact smaller-fuel worker continues from the retained child
trace with the same return handler. -/
theorem CompiledAttachment.simulate_traced_pure_move_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace} {sourceAtom : IxIR1.Atom}
    {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.pure sourceAtom) index (.move targetAtom) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.pure sourceAtom) next.sourceCode) = .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation (sourceFuel + 1)) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨value, nextFrame, nextFrameEq, sourceResolved, continuationRun,
      _, nextStores, nextState⟩ :=
    attached.simulate_traced_pure_move_success_step
      (context := context) (interpretation := interpretation) functionMember
      descendant state stores sourceDeclarations sourceRun control
  subst nextFrame
  have nextDescendant : functionTrace.root.Descendant next := by
    exact .step descendant (by simp [Lower.CodeTrace.children])
  have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore
      (value :: source) :=
    ⟨runtime.order,
      IxIR1.Reclamation.ValuesInBounds.cons
        (runtime.resolveAtom sourceResolved) runtime.rootsInBounds,
      runtime.papsUnder⟩
  have nextOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions next sourceStore
        (value :: source) frameRoots :=
    Lower.Sim.SourceOwnershipAt.pure (checked := attached.target)
      functionMember descendant ownership sourceResolved
  let nextFrame : Eval.Frame :=
    { frame with
      pc := frame.pc + 1
      values := frame.values.push value }
  let nextMachine : Eval.Machine :=
    { machine with control := .running nextFrame stack }
  have nextControl : nextMachine.control = .running nextFrame stack := rfl
  have nextNoCredits : nextFrame.credits = #[] := by
    simpa [nextFrame] using noCredits
  have tail := worker (machine := nextMachine) (stack := stack)
    functionMember nextDescendant nextState nextStores nextRuntime
      nextOwnership continuationRun resultWorld nextControl nextNoCredits image
      finish
  obtain ⟨tailHeapFuel, tail⟩ := tail
  let fundedMachine : Eval.Machine := { machine with heapFuel := tailHeapFuel }
  have fundedStores : Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  obtain ⟨_, fundedStep, _, _⟩ :=
    attached.simulate_traced_pure_move_state
      (sourceFuel := sourceFuel) (machine := fundedMachine) functionMember
      descendant state fundedStores sourceDeclarations sourceResolved
      fundedControl
  refine ⟨tailHeapFuel, ?_⟩
  simpa [fundedMachine, nextMachine, nextFrame] using
    tail.prepend (fundedStep.toSteps fundedControl)

/-- Complete CPS composition for shared duplication.  Both inert scalars and
live shared locations take one heap-fuel-preserving target step. -/
theorem CompiledAttachment.simulate_traced_dup_retain_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace} {sourceAtom : IxIR1.Atom}
    {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.dup sourceAtom) index (.retainShared targetAtom) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.dup sourceAtom) next.sourceCode) = .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation (sourceFuel + 1)) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  have middleImage : attached.SourceStoreImage middleStore :=
    attached.runOp_preservesSourceStoreImage sourceDeclarations functionMember
      descendant state image operationRun
  obtain ⟨value, sourceResolved, operationOutput⟩ :=
    IxIR1.runOp_dup_success operationRun
  have nextDescendant : functionTrace.root.Descendant next := by
    exact .step descendant (by simp [Lower.CodeTrace.children])
  have scalarCase (selected : IxIR1.RVal)
      (selectedResolved :
        IxIR1.resolveAtom source sourceAtom = .ok selected)
      (scalar : Eval.RVal.isScalar selected = true)
      (outputEq : (middleStore, operationValue) =
        (sourceStore, selected)) :
      BudgetedReachesPost context interpretation post outcome.1 outcome.2
        machine := by
    have middleStoreEq : middleStore = sourceStore :=
      congrArg Prod.fst outputEq
    have operationValueEq : operationValue = selected :=
      congrArg Prod.snd outputEq
    subst middleStore
    subst operationValue
    obtain ⟨_, targetStep, nextStores, nextState⟩ :=
      attached.simulate_traced_dup_retain_scalar_state
        (sourceFuel := sourceFuel) (context := context)
        (interpretation := interpretation) functionMember descendant state
        stores sourceDeclarations selectedResolved scalar control
    have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore
        (selected :: source) :=
      runtime.runOp rfl operationRun
    have nextOwnership : Lower.Sim.SourceOwnershipAt
        attached.target.artifact.trace.positions next sourceStore
          (selected :: source) frameRoots :=
      Lower.Sim.SourceOwnershipAt.dup (checked := attached.target)
        functionMember descendant ownership selectedResolved operationRun
    let nextFrame : Eval.Frame :=
      { frame with
        pc := frame.pc + 1
        values := frame.values.push selected }
    let nextMachine : Eval.Machine :=
      { machine with control := .running nextFrame stack }
    have nextControl : nextMachine.control =
        .running nextFrame stack := rfl
    have nextNoCredits : nextFrame.credits = #[] := by
      simpa [nextFrame] using noCredits
    have tail := worker (machine := nextMachine) (stack := stack)
      functionMember nextDescendant nextState nextStores nextRuntime
        nextOwnership continuationRun resultWorld nextControl nextNoCredits
        middleImage finish
    refine BudgetedReachesPost.prependPreserving
      (before := machine) (middle := nextMachine) (prefixCount := 1) ?_ tail
    intro heapFuel
    let fundedMachine : Eval.Machine := { machine with heapFuel }
    have fundedStores :
        Lower.Sim.StoreRel sourceStore fundedMachine.store := by
      simpa [fundedMachine] using stores
    have fundedControl : fundedMachine.control = .running frame stack := by
      simpa [fundedMachine] using control
    obtain ⟨_, fundedStep, _, _⟩ :=
      attached.simulate_traced_dup_retain_scalar_state
        (sourceFuel := sourceFuel) (context := context)
        (interpretation := interpretation) (machine := fundedMachine)
        functionMember descendant state fundedStores sourceDeclarations
        selectedResolved scalar fundedControl
    simpa [fundedMachine, nextMachine, nextFrame] using
      fundedStep.toSteps fundedControl
  cases value with
  | lit literal =>
      exact scalarCase (.lit literal) sourceResolved (by rfl) operationOutput
  | erased =>
      exact scalarCase .erased sourceResolved (by rfl) operationOutput
  | loc location =>
      obtain ⟨box, sourceGet, shared, outputEq⟩ := operationOutput
      let nextBox : IxIR1.NodeBox := { box with rc := box.rc + 1 }
      let sourceStore' : IxIR1.Store :=
        (sourceStore.setBox location nextBox).rcTick
      let targetStore' : Eval.Store :=
        (machine.store.setBox location nextBox).rcTick
      have middleStoreEq : middleStore = sourceStore' := by
        simpa [sourceStore', nextBox] using congrArg Prod.fst outputEq
      have operationValueEq : operationValue = .loc location :=
        congrArg Prod.snd outputEq
      subst middleStore
      subst operationValue
      obtain ⟨_, targetStep, nextStores, nextState⟩ :=
        attached.simulate_traced_dup_retain_shared_state
          (sourceFuel := sourceFuel) (context := context)
          (interpretation := interpretation) functionMember descendant state
          stores sourceDeclarations sourceResolved sourceGet shared control
      have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore'
          (.loc location :: source) := by
        apply runtime.runOp
          (run := operationRun)
        simp [sourceStore', nextBox, IxIR1.Store.setBox, IxIR1.Store.rcTick]
      have nextOwnership : Lower.Sim.SourceOwnershipAt
          attached.target.artifact.trace.positions next sourceStore'
            (.loc location :: source) frameRoots :=
        Lower.Sim.SourceOwnershipAt.dup (checked := attached.target)
          functionMember descendant ownership sourceResolved operationRun
      let nextFrame : Eval.Frame :=
        { frame with
          pc := frame.pc + 1
          values := frame.values.push (.loc location) }
      let nextMachine : Eval.Machine :=
        { machine with
          store := targetStore'
          control := .running nextFrame stack }
      have nextControl : nextMachine.control =
          .running nextFrame stack := rfl
      have nextNoCredits : nextFrame.credits = #[] := by
        simpa [nextFrame] using noCredits
      have nextStores' :
          Lower.Sim.StoreRel sourceStore' nextMachine.store := by
        simpa [nextMachine, targetStore', sourceStore', nextBox] using nextStores
      have tail := worker (machine := nextMachine) (stack := stack)
        functionMember nextDescendant nextState nextStores' nextRuntime
          nextOwnership continuationRun resultWorld nextControl nextNoCredits
          middleImage finish
      refine BudgetedReachesPost.prependPreserving
        (before := machine) (middle := nextMachine) (prefixCount := 1) ?_ tail
      intro heapFuel
      let fundedMachine : Eval.Machine := { machine with heapFuel }
      have fundedStores :
          Lower.Sim.StoreRel sourceStore fundedMachine.store := by
        simpa [fundedMachine] using stores
      have fundedControl : fundedMachine.control = .running frame stack := by
        simpa [fundedMachine] using control
      obtain ⟨_, fundedStep, _, _⟩ :=
        attached.simulate_traced_dup_retain_shared_state
          (sourceFuel := sourceFuel) (context := context)
          (interpretation := interpretation) (machine := fundedMachine)
          functionMember descendant state fundedStores sourceDeclarations
          sourceResolved sourceGet shared fundedControl
      simpa [fundedMachine, nextMachine, nextFrame, targetStore', nextBox] using
        fundedStep.toSteps fundedControl

/-- Complete CPS composition for an HPT-certified constructor projection. -/
theorem CompiledAttachment.simulate_traced_fetch_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace} {sourceAtom : IxIR1.Atom}
    {targetAtom : Atom} {sourceField targetField : Nat}
    {targetCid : IxIR1.CtorId}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.fetch sourceAtom sourceField) index
        (.fetch targetAtom targetCid targetField) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.fetch sourceAtom sourceField) next.sourceCode) =
          .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation (sourceFuel + 1)) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  have middleImage : attached.SourceStoreImage middleStore :=
    attached.runOp_preservesSourceStoreImage sourceDeclarations functionMember
      descendant state image operationRun
  obtain ⟨location, box, identity, fields, value, sourceResolved, sourceGet,
      node, fieldAt, outputEq⟩ :=
    IxIR1.runOp_fetch_success operationRun
  have middleStoreEq : middleStore = sourceStore :=
    congrArg Prod.fst outputEq
  have operationValueEq : operationValue = value :=
    congrArg Prod.snd outputEq
  subst middleStore
  subst operationValue
  obtain ⟨_, targetStep, nextStores, nextState⟩ :=
    attached.simulate_traced_fetch_state_of_run_hpt
      (sourceFuel := sourceFuel) (context := context)
      (interpretation := interpretation) functionMember descendant state stores
      sourceDeclarations operationRun control
  have nextDescendant : functionTrace.root.Descendant next := by
    exact .step descendant (by simp [Lower.CodeTrace.children])
  have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore
      (value :: source) :=
    runtime.runOp rfl operationRun
  have nextOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions next sourceStore
        (value :: source) frameRoots :=
    Lower.Sim.SourceOwnershipAt.fetch (checked := attached.target)
      functionMember descendant ownership operationRun
  let nextFrame : Eval.Frame :=
    { frame with
      pc := frame.pc + 1
      values := frame.values.push value }
  let nextMachine : Eval.Machine :=
    { machine with control := .running nextFrame stack }
  have nextControl : nextMachine.control = .running nextFrame stack := rfl
  have nextNoCredits : nextFrame.credits = #[] := by
    simpa [nextFrame] using noCredits
  have tail := worker (machine := nextMachine) (stack := stack)
    functionMember nextDescendant nextState nextStores nextRuntime
      nextOwnership continuationRun resultWorld nextControl nextNoCredits
      middleImage finish
  refine BudgetedReachesPost.prependPreserving
    (before := machine) (middle := nextMachine) (prefixCount := 1) ?_ tail
  intro heapFuel
  let fundedMachine : Eval.Machine := { machine with heapFuel }
  have fundedStores :
      Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  obtain ⟨_, fundedStep, _, _⟩ :=
    attached.simulate_traced_fetch_state_of_run_hpt
      (sourceFuel := sourceFuel) (context := context)
      (interpretation := interpretation) (machine := fundedMachine)
      functionMember descendant state fundedStores sourceDeclarations
      operationRun fundedControl
  simpa [fundedMachine, nextMachine, nextFrame] using
    fundedStep.toSteps fundedControl

/-- Complete CPS composition for an HPT-certified scalar-leaf shallow free. -/
theorem CompiledAttachment.simulate_traced_free_freeUnique_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace} {sourceAtom : IxIR1.Atom}
    {targetAtom : Atom} {targetCid : IxIR1.CtorId}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.free sourceAtom) index (.freeUnique targetAtom targetCid) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.free sourceAtom) next.sourceCode) = .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation (sourceFuel + 1)) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  have middleImage : attached.SourceStoreImage middleStore :=
    attached.runOp_preservesSourceStoreImage sourceDeclarations functionMember
      descendant state image operationRun
  obtain ⟨location, box, sourceResolved, sourceGet, unique, outputEq⟩ :=
    IxIR1.runOp_free_success operationRun
  have middleStoreEq : middleStore = sourceStore.kill location :=
    congrArg Prod.fst outputEq
  have operationValueEq : operationValue = .erased :=
    congrArg Prod.snd outputEq
  subst middleStore
  subst operationValue
  obtain ⟨fact, selected⟩ :=
    attached.scalarLeafAt?_of_free_descendant functionMember descendant
  obtain ⟨exactBox, fields, exactGet, node, scalarFields⟩ :=
    attached.sidecars.scalarLeafAt?_runtime selected state.environment
      sourceResolved
  have boxEq : exactBox = box :=
    Option.some.inj (exactGet.symm.trans sourceGet)
  subst exactBox
  obtain ⟨_, targetStep, nextStores, nextTarget⟩ :=
    Lower.Sim.simulate_traced_free_freeUnique_state
      (sourceContext := sourceContext) (sourceCurrent := functionTrace.source)
      (sourceFuel := sourceFuel) (context := context)
      (interpretation := interpretation) descendant state.target stores
      sourceResolved sourceGet unique node scalarFields control
  have nextState := attached.traceState_next_of_member functionMember state
    descendant sourceDeclarations operationRun nextTarget
  have nextDescendant : functionTrace.root.Descendant next := by
    exact .step descendant (by simp [Lower.CodeTrace.children])
  have nextRuntime : Lower.Sim.SourceRuntimeInvariant
      (sourceStore.kill location) (.erased :: source) := by
    apply runtime.runOp
      (run := operationRun)
    simp [IxIR1.Store.kill]
  have nextOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions next
        (sourceStore.kill location) (.erased :: source) frameRoots :=
    Lower.Sim.SourceOwnershipAt.free (checked := attached.target)
      functionMember descendant ownership sourceResolved sourceGet unique node
        scalarFields operationRun
  let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
  let nextMachine : Eval.Machine :=
    { machine with
      store := machine.store.kill location
      control := .running nextFrame stack }
  have nextControl : nextMachine.control = .running nextFrame stack := rfl
  have nextNoCredits : nextFrame.credits = #[] := by
    simpa [nextFrame] using noCredits
  have nextStores' : Lower.Sim.StoreRel (sourceStore.kill location)
      nextMachine.store := by
    simpa [nextMachine] using nextStores
  have tail := worker (machine := nextMachine) (stack := stack)
    functionMember nextDescendant nextState nextStores' nextRuntime
      nextOwnership continuationRun resultWorld nextControl nextNoCredits
      middleImage finish
  refine BudgetedReachesPost.prependPreserving
    (before := machine) (middle := nextMachine) (prefixCount := 1) ?_ tail
  intro heapFuel
  let fundedMachine : Eval.Machine := { machine with heapFuel }
  have fundedStores :
      Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  obtain ⟨_, fundedStep, _, _⟩ :=
    Lower.Sim.simulate_traced_free_freeUnique_state
      (sourceContext := sourceContext) (sourceCurrent := functionTrace.source)
      (sourceFuel := sourceFuel) (context := context)
      (interpretation := interpretation) (machine := fundedMachine)
      descendant state.target fundedStores sourceResolved sourceGet unique node
      scalarFields fundedControl
  simpa [fundedMachine, nextMachine, nextFrame] using
    fundedStep.toSteps fundedControl

/-- Complete CPS composition for shared destruction.  Scalar releases reserve
one heap unit ahead of the continuation; recursive location releases use the
framed work-list plan to reserve exactly their local traversal cost plus the
continuation's independently selected budget. -/
theorem CompiledAttachment.simulate_traced_drop_release_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace} {sourceAtom : IxIR1.Atom}
    {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.drop sourceAtom) index (.releaseShared targetAtom) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.drop sourceAtom) next.sourceCode) = .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation (sourceFuel + 1)) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  have middleImage : attached.SourceStoreImage middleStore :=
    attached.runOp_preservesSourceStoreImage sourceDeclarations functionMember
      descendant state image operationRun
  obtain ⟨value, sourceResolved, operationOutput⟩ :=
    IxIR1.runOp_drop_success operationRun
  have nextDescendant : functionTrace.root.Descendant next := by
    exact .step descendant (by simp [Lower.CodeTrace.children])
  have scalarCase (selected : IxIR1.RVal)
      (selectedResolved :
        IxIR1.resolveAtom source sourceAtom = .ok selected)
      (scalar : Eval.RVal.isScalar selected = true)
      (outputEq : (middleStore, operationValue) =
        (sourceStore, .erased)) :
      BudgetedReachesPost context interpretation post outcome.1 outcome.2
        machine := by
    have middleStoreEq : middleStore = sourceStore :=
      congrArg Prod.fst outputEq
    have operationValueEq : operationValue = .erased :=
      congrArg Prod.snd outputEq
    subst middleStore
    subst operationValue
    let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
    let probeMachine : Eval.Machine := { machine with heapFuel := 1 }
    have probeStores : Lower.Sim.StoreRel sourceStore probeMachine.store := by
      simpa [probeMachine] using stores
    have probeControl : probeMachine.control = .running frame stack := by
      simpa [probeMachine] using control
    obtain ⟨_, _, nextStores, nextState⟩ :=
      attached.simulate_traced_drop_release_scalar_state
        (sourceFuel := sourceFuel) (targetHeapFuel := 0)
        (context := context) (interpretation := interpretation)
        (machine := probeMachine) functionMember descendant state probeStores
        sourceDeclarations selectedResolved scalar
        (heapFuel := by simp [probeMachine]) probeControl
    let nextMachine : Eval.Machine :=
      { machine with control := .running nextFrame stack }
    have nextStores' :
        Lower.Sim.StoreRel sourceStore nextMachine.store := by
      simpa [nextMachine, probeMachine] using nextStores
    have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore
        (.erased :: source) :=
      runtime.runOp rfl operationRun
    have nextOwnership : Lower.Sim.SourceOwnershipAt
        attached.target.artifact.trace.positions next sourceStore
          (.erased :: source) frameRoots :=
      Lower.Sim.SourceOwnershipAt.drop (checked := attached.target)
        functionMember descendant ownership operationRun
    have nextControl : nextMachine.control =
        .running nextFrame stack := rfl
    have nextNoCredits : nextFrame.credits = #[] := by
      simpa [nextFrame] using noCredits
    have tail := worker (machine := nextMachine) (stack := stack)
      functionMember nextDescendant nextState nextStores' nextRuntime
        nextOwnership continuationRun resultWorld nextControl nextNoCredits
        middleImage finish
    obtain ⟨tailHeapFuel, tail⟩ := tail
    let fundedMachine : Eval.Machine :=
      { machine with heapFuel := tailHeapFuel + 1 }
    have fundedStores :
        Lower.Sim.StoreRel sourceStore fundedMachine.store := by
      simpa [fundedMachine] using stores
    have fundedControl : fundedMachine.control = .running frame stack := by
      simpa [fundedMachine] using control
    obtain ⟨_, fundedStep, _, _⟩ :=
      attached.simulate_traced_drop_release_scalar_state
        (sourceFuel := sourceFuel) (targetHeapFuel := tailHeapFuel)
        (context := context) (interpretation := interpretation)
        (machine := fundedMachine) functionMember descendant state
        fundedStores sourceDeclarations selectedResolved scalar
        (heapFuel := by simp [fundedMachine]) fundedControl
    refine ⟨tailHeapFuel + 1, ?_⟩
    simpa [fundedMachine, nextMachine, nextFrame] using
      tail.prepend (fundedStep.toSteps fundedControl)
  cases value with
  | lit literal =>
      exact scalarCase (.lit literal) sourceResolved (by rfl) operationOutput
  | erased =>
      exact scalarCase .erased sourceResolved (by rfl) operationOutput
  | loc location =>
      obtain ⟨sourceStore', sourceDropped, outputEq⟩ := operationOutput
      have middleStoreEq : middleStore = sourceStore' :=
        congrArg Prod.fst outputEq
      have operationValueEq : operationValue = .erased :=
        congrArg Prod.snd outputEq
      subst middleStore
      subst operationValue
      have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore'
          (.erased :: source) :=
        runtime.runOp (IxIR1.NoReuse.dropVal_reuses sourceDropped)
          operationRun
      have nextOwnership : Lower.Sim.SourceOwnershipAt
          attached.target.artifact.trace.positions next sourceStore'
            (.erased :: source) frameRoots :=
        Lower.Sim.SourceOwnershipAt.drop (checked := attached.target)
          functionMember descendant ownership operationRun
      obtain ⟨localFuel, targetStore, _, _, stepForSuffix, nextStores,
          _, nextState⟩ :=
        attached.simulate_traced_drop_release_recursive_state_framed
          (sourceFuel := sourceFuel) (context := context)
          (interpretation := interpretation) functionMember descendant state
          runtime.positiveSharedRC stores sourceDeclarations sourceResolved
          sourceDropped control
      let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
      let nextMachine : Eval.Machine :=
        { store := targetStore
          heapFuel := 0
          control := .running nextFrame stack }
      have nextControl : nextMachine.control =
          .running nextFrame stack := rfl
      have nextNoCredits : nextFrame.credits = #[] := by
        simpa [nextFrame] using noCredits
      have tail := worker (machine := nextMachine) (stack := stack)
        functionMember nextDescendant nextState nextStores nextRuntime
          nextOwnership continuationRun resultWorld nextControl nextNoCredits
          middleImage finish
      obtain ⟨tailHeapFuel, tail⟩ := tail
      have prefixControl :
          ({ machine with heapFuel := localFuel + tailHeapFuel } :
            Eval.Machine).control = .running frame stack := by
        simpa using control
      refine ⟨localFuel + tailHeapFuel, ?_⟩
      simpa [nextMachine, nextFrame] using
        tail.prepend ((stepForSuffix tailHeapFuel).toSteps prefixControl)

/-- Complete CPS composition for unique destruction, with the same backward
heap-budget discipline as shared release. -/
theorem CompiledAttachment.simulate_traced_dropU_dropUnique_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace} {sourceAtom : IxIR1.Atom}
    {targetAtom : Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.dropU sourceAtom) index (.dropUnique targetAtom) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.dropU sourceAtom) next.sourceCode) = .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation (sourceFuel + 1)) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  have middleImage : attached.SourceStoreImage middleStore :=
    attached.runOp_preservesSourceStoreImage sourceDeclarations functionMember
      descendant state image operationRun
  obtain ⟨value, sourceResolved, operationOutput⟩ :=
    IxIR1.runOp_dropU_success operationRun
  have nextDescendant : functionTrace.root.Descendant next := by
    exact .step descendant (by simp [Lower.CodeTrace.children])
  have scalarCase (selected : IxIR1.RVal)
      (selectedResolved :
        IxIR1.resolveAtom source sourceAtom = .ok selected)
      (scalar : Eval.RVal.isScalar selected = true)
      (outputEq : (middleStore, operationValue) =
        (sourceStore, .erased)) :
      BudgetedReachesPost context interpretation post outcome.1 outcome.2
        machine := by
    have middleStoreEq : middleStore = sourceStore :=
      congrArg Prod.fst outputEq
    have operationValueEq : operationValue = .erased :=
      congrArg Prod.snd outputEq
    subst middleStore
    subst operationValue
    let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
    let probeMachine : Eval.Machine := { machine with heapFuel := 1 }
    have probeStores : Lower.Sim.StoreRel sourceStore probeMachine.store := by
      simpa [probeMachine] using stores
    have probeControl : probeMachine.control = .running frame stack := by
      simpa [probeMachine] using control
    obtain ⟨_, _, nextStores, nextState⟩ :=
      attached.simulate_traced_dropU_dropUnique_scalar_state
        (sourceFuel := sourceFuel) (targetHeapFuel := 0)
        (context := context) (interpretation := interpretation)
        (machine := probeMachine) functionMember descendant state probeStores
        sourceDeclarations selectedResolved scalar
        (heapFuel := by simp [probeMachine]) probeControl
    let nextMachine : Eval.Machine :=
      { machine with control := .running nextFrame stack }
    have nextStores' :
        Lower.Sim.StoreRel sourceStore nextMachine.store := by
      simpa [nextMachine, probeMachine] using nextStores
    have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore
        (.erased :: source) :=
      runtime.runOp rfl operationRun
    have nextOwnership : Lower.Sim.SourceOwnershipAt
        attached.target.artifact.trace.positions next sourceStore
          (.erased :: source) frameRoots :=
      Lower.Sim.SourceOwnershipAt.dropU (checked := attached.target)
        functionMember descendant ownership operationRun
    have nextControl : nextMachine.control =
        .running nextFrame stack := rfl
    have nextNoCredits : nextFrame.credits = #[] := by
      simpa [nextFrame] using noCredits
    have tail := worker (machine := nextMachine) (stack := stack)
      functionMember nextDescendant nextState nextStores' nextRuntime
        nextOwnership continuationRun resultWorld nextControl nextNoCredits
        middleImage finish
    obtain ⟨tailHeapFuel, tail⟩ := tail
    let fundedMachine : Eval.Machine :=
      { machine with heapFuel := tailHeapFuel + 1 }
    have fundedStores :
        Lower.Sim.StoreRel sourceStore fundedMachine.store := by
      simpa [fundedMachine] using stores
    have fundedControl : fundedMachine.control = .running frame stack := by
      simpa [fundedMachine] using control
    obtain ⟨_, fundedStep, _, _⟩ :=
      attached.simulate_traced_dropU_dropUnique_scalar_state
        (sourceFuel := sourceFuel) (targetHeapFuel := tailHeapFuel)
        (context := context) (interpretation := interpretation)
        (machine := fundedMachine) functionMember descendant state
        fundedStores sourceDeclarations selectedResolved scalar
        (heapFuel := by simp [fundedMachine]) fundedControl
    refine ⟨tailHeapFuel + 1, ?_⟩
    simpa [fundedMachine, nextMachine, nextFrame] using
      tail.prepend (fundedStep.toSteps fundedControl)
  cases value with
  | lit literal =>
      exact scalarCase (.lit literal) sourceResolved (by rfl) operationOutput
  | erased =>
      exact scalarCase .erased sourceResolved (by rfl) operationOutput
  | loc location =>
      obtain ⟨sourceStore', sourceDropped, outputEq⟩ := operationOutput
      have middleStoreEq : middleStore = sourceStore' :=
        congrArg Prod.fst outputEq
      have operationValueEq : operationValue = .erased :=
        congrArg Prod.snd outputEq
      subst middleStore
      subst operationValue
      have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore'
          (.erased :: source) :=
        runtime.runOp (IxIR1.NoReuse.dropUVal_reuses sourceDropped)
          operationRun
      have nextOwnership : Lower.Sim.SourceOwnershipAt
          attached.target.artifact.trace.positions next sourceStore'
            (.erased :: source) frameRoots :=
        Lower.Sim.SourceOwnershipAt.dropU (checked := attached.target)
          functionMember descendant ownership operationRun
      obtain ⟨localFuel, targetStore, _, _exactDrop, stepForSuffix, nextStores,
          nextState⟩ :=
        attached.simulate_traced_dropU_dropUnique_recursive_state_framed
          (sourceFuel := sourceFuel) (context := context)
          (interpretation := interpretation) functionMember descendant state
          stores sourceDeclarations sourceResolved sourceDropped control
      let nextFrame : Eval.Frame := { frame with pc := frame.pc + 1 }
      let nextMachine : Eval.Machine :=
        { store := targetStore
          heapFuel := 0
          control := .running nextFrame stack }
      have nextControl : nextMachine.control =
          .running nextFrame stack := rfl
      have nextNoCredits : nextFrame.credits = #[] := by
        simpa [nextFrame] using noCredits
      have tail := worker (machine := nextMachine) (stack := stack)
        functionMember nextDescendant nextState nextStores nextRuntime
          nextOwnership continuationRun resultWorld nextControl nextNoCredits
          middleImage finish
      obtain ⟨tailHeapFuel, tail⟩ := tail
      have prefixControl :
          ({ machine with heapFuel := localFuel + tailHeapFuel } :
            Eval.Machine).control = .running frame stack := by
        simpa using control
      refine ⟨localFuel + tailHeapFuel, ?_⟩
      simpa [nextMachine, nextFrame] using
        tail.prepend ((stepForSuffix tailHeapFuel).toSteps prefixControl)

/-- CPS composition for checked ordinary allocation.  The checked trace
recovers the exact uniform schema and producer capabilities; the trace-indexed
source ownership invariant justifies the target field worlds.  Allocation then
preserves the continuation's chosen heap budget. -/
theorem CompiledAttachment.simulate_traced_alloc_checked_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    (contextSchemas : context.schemas =
      attached.target.artifact.validationContext.schemas)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace} {sourceWorld targetWorld : Ixon.Owned}
    {sourceCid targetCid : IxIR1.CtorId}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.alloc sourceWorld sourceCid sourceArguments) index
        (.alloc targetWorld targetCid targetArguments) next)
      sourceStore source frameRoots)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.alloc sourceWorld sourceCid sourceArguments)
          next.sourceCode) = .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      .logical functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      .logical (sourceFuel + 1)) :
    BudgetedReachesPost context .logical post outcome.1 outcome.2
      machine := by
  obtain ⟨schema, checkedSchemaAt, _⟩ :=
    attached.target.allocationSchema functionMember descendant
  have schemaAt : context.schemas sourceWorld sourceCid = some schema := by
    rw [contextSchemas]
    exact checkedSchemaAt
  obtain ⟨values, sourceAllocation, targetAllocation, nextFrame,
      sourceAllocationEq, targetAllocationEq, sourceResolved,
      continuationRun, nextFrameEq, targetStep, nextStores, nextState⟩ :=
    attached.simulate_traced_alloc_checked_success_step
      (context := context) (machine := machine) functionMember contextSchemas
      descendant state stores sourceDeclarations sourceRun control schemaAt
      ownership
  subst sourceAllocation
  subst targetAllocation
  subst nextFrame
  let node : IxIR1.Node := .ctorN sourceCid values.toArray
  let sourceAllocation := sourceStore.allocNode sourceWorld node
  let targetAllocation := machine.store.allocNode sourceWorld node
  have nextDescendant : functionTrace.root.Descendant next := by
    exact .step descendant (by simp [Lower.CodeTrace.children])
  have operationRun : IxIR1.runOp sourceContext (sourceFuel + 1)
      functionTrace.source sourceStore source
        (.alloc sourceWorld sourceCid sourceArguments) =
        .ok (sourceAllocation.1, .loc sourceAllocation.2) := by
    unfold IxIR1.runOp
    simp only
    rw [sourceResolved]
    rfl
  have nextImage : attached.SourceStoreImage sourceAllocation.1 :=
    attached.runOp_preservesSourceStoreImage sourceDeclarations functionMember
      descendant state image operationRun
  have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceAllocation.1
      (.loc sourceAllocation.2 :: source) := by
    apply runtime.runOp (run := operationRun)
    simp [sourceAllocation, node, IxIR1.Store.allocNode]
  have nextOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions next sourceAllocation.1
        (.loc sourceAllocation.2 :: source) frameRoots :=
    Lower.Sim.SourceOwnershipAt.alloc (checked := attached.target)
      functionMember descendant ownership operationRun
  let nextFrame : Eval.Frame :=
    { frame with
      pc := frame.pc + 1
      values := frame.values.push (.loc sourceAllocation.2) }
  let nextMachine : Eval.Machine :=
    { machine with
      store := targetAllocation.1
      control := .running nextFrame stack }
  have nextControl : nextMachine.control = .running nextFrame stack := rfl
  have nextNoCredits : nextFrame.credits = #[] := by
    simpa [nextFrame] using noCredits
  have nextStores' : Lower.Sim.StoreRel sourceAllocation.1
      nextMachine.store := by
    simpa [nextMachine, targetAllocation, sourceAllocation, node] using
      nextStores
  have tail := worker (machine := nextMachine) (stack := stack)
    functionMember nextDescendant nextState nextStores' nextRuntime
      nextOwnership continuationRun resultWorld nextControl nextNoCredits
      nextImage finish
  refine BudgetedReachesPost.prependPreserving
    (before := machine) (middle := nextMachine) (prefixCount := 1) ?_ tail
  intro heapFuel
  let fundedMachine : Eval.Machine := { machine with heapFuel }
  have fundedStores :
      Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  obtain ⟨_, fundedStep, _, _⟩ :=
    attached.simulate_traced_alloc_checked_state
      (sourceFuel := sourceFuel) (context := context)
      (machine := fundedMachine) functionMember contextSchemas descendant
      state fundedStores sourceDeclarations sourceResolved fundedControl
      schemaAt ownership
  simpa [fundedMachine, nextMachine, nextFrame, targetAllocation,
    sourceAllocation, node] using fundedStep.toSteps fundedControl

/-- Complete CPS composition for strictly under-saturated function PAP
allocation.  Source success fixes the captured vector and fresh node; the
generated target allocation preserves the continuation's chosen heap budget. -/
theorem CompiledAttachment.simulate_traced_papp_fn_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace} {sourceAddress targetAddress : Ixon.Address}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.papp sourceAddress sourceArguments) index
        (.papp targetAddress targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.papp sourceAddress sourceArguments) index
        (.papp targetAddress targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.papp sourceAddress sourceArguments) index
        (.papp targetAddress targetArguments) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceDeclaration : sourceContext.decls sourceAddress =
      some (.fn sourceDefinition))
    (targetDeclaration : context.declarations sourceAddress =
      some (.fn targetDefinition))
    (arity : targetDefinition.signature.params.size = sourceDefinition.arity)
    (papSafe : targetDefinition.signature.papSafe = true)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.papp sourceAddress sourceArguments) next.sourceCode) =
          .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation (sourceFuel + 1)) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  have middleImage : attached.SourceStoreImage middleStore :=
    attached.runOp_preservesSourceStoreImage sourceDeclarations functionMember
      descendant state image operationRun
  obtain ⟨values, declaration, sourceResolved, declarationAt, under,
      operationOutput⟩ := IxIR1.runOp_papp_success operationRun
  have declarationEq : declaration = .fn sourceDefinition := by
    exact Option.some.inj (declarationAt.symm.trans sourceDeclaration)
  subst declaration
  have under' : values.length < sourceDefinition.arity := by
    simpa [IxIR1.declArity] using under
  let node : IxIR1.Node :=
    .papN sourceAddress sourceDefinition.arity values.toArray
  let sourceAllocation := sourceStore.allocNode .shared node
  let targetAllocation := machine.store.allocNode .shared node
  have middleStoreEq : middleStore = sourceAllocation.1 := by
    simpa [sourceAllocation, node, IxIR1.declArity] using
      congrArg Prod.fst operationOutput
  have operationValueEq : operationValue = .loc sourceAllocation.2 := by
    simpa [sourceAllocation, node, IxIR1.declArity] using
      congrArg Prod.snd operationOutput
  subst middleStore
  subst operationValue
  obtain ⟨_, targetStep, nextStores, nextState⟩ :=
    attached.simulate_traced_papp_fn_state
      (sourceFuel := sourceFuel) (context := context)
      (interpretation := interpretation) functionMember descendant state
      stores sourceDeclarations sourceResolved sourceDeclaration
      targetDeclaration arity papSafe under' noCredits control
  have nextDescendant : functionTrace.root.Descendant next := by
    exact .step descendant (by simp [Lower.CodeTrace.children])
  have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceAllocation.1
      (.loc sourceAllocation.2 :: source) := by
    apply runtime.runOp (run := operationRun)
    simp [sourceAllocation, node, IxIR1.Store.allocNode]
  have nextOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions next sourceAllocation.1
        (.loc sourceAllocation.2 :: source) frameRoots :=
    Lower.Sim.SourceOwnershipAt.papp (checked := attached.target)
      functionMember descendant ownership operationRun
  let nextFrame : Eval.Frame :=
    { frame with
      pc := frame.pc + 1
      values := frame.values.push (.loc sourceAllocation.2) }
  let nextMachine : Eval.Machine :=
    { machine with
      store := targetAllocation.1
      control := .running nextFrame stack }
  have nextControl : nextMachine.control = .running nextFrame stack := rfl
  have nextNoCredits : nextFrame.credits = #[] := by
    simpa [nextFrame] using noCredits
  have nextStores' : Lower.Sim.StoreRel sourceAllocation.1
      nextMachine.store := by
    simpa [nextMachine, targetAllocation, sourceAllocation, node] using
      nextStores
  have tail := worker (machine := nextMachine) (stack := stack)
    functionMember nextDescendant nextState nextStores' nextRuntime
      nextOwnership continuationRun resultWorld nextControl nextNoCredits
      middleImage finish
  refine BudgetedReachesPost.prependPreserving
    (before := machine) (middle := nextMachine) (prefixCount := 1) ?_ tail
  intro heapFuel
  let fundedMachine : Eval.Machine := { machine with heapFuel }
  have fundedStores :
      Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  obtain ⟨_, fundedStep, _, _⟩ :=
    attached.simulate_traced_papp_fn_state
      (sourceFuel := sourceFuel) (context := context)
      (interpretation := interpretation) (machine := fundedMachine)
      functionMember descendant state fundedStores sourceDeclarations
      sourceResolved sourceDeclaration targetDeclaration arity papSafe under'
      noCredits fundedControl
  simpa [fundedMachine, nextMachine, nextFrame, targetAllocation,
    sourceAllocation, node] using fundedStep.toSteps fundedControl

/-- Complete CPS composition for the erased dynamic-application branch.
Residual shared arguments are released with an exact locally framed heap
budget, after which the smaller-fuel caller worker runs on the erased result.
-/
theorem CompiledAttachment.simulate_traced_apply_erased_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {sourceStore sourceReleased : IxIR1.Store}
    {source values : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok .erased)
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceRelease : IxIR1.dropMany sourceContext sourceFuel sourceStore
      values = .ok sourceReleased)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 3)
      functionTrace.source sourceStore source
        (.letOp (.apply sourceFunction sourceArguments) next.sourceCode) =
          .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation (sourceFuel + 2)) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  have sourceOperation : IxIR1.runOp sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.apply sourceFunction sourceArguments) =
          .ok (sourceReleased, .erased) := by
    rw [IxIR1.runOp.eq_def]
    dsimp only
    rw [functionResolved]
    simp only [bind, Except.bind]
    rw [argumentsResolved]
    simp only
    rw [IxIR1.applyGo.eq_def]
    dsimp only
    rw [sourceRelease]
    rfl
  have nextImage : attached.SourceStoreImage sourceReleased :=
    attached.runOp_preservesSourceStoreImage sourceDeclarations functionMember
      descendant state image sourceOperation
  have operationOutput : (middleStore, operationValue) =
      (sourceReleased, .erased) :=
    Except.ok.inj (operationRun.symm.trans sourceOperation)
  have middleStoreEq : middleStore = sourceReleased :=
    congrArg Prod.fst operationOutput
  have operationValueEq : operationValue = .erased :=
    congrArg Prod.snd operationOutput
  subst middleStore
  subst operationValue
  obtain ⟨targetHeapFuel, targetReleased, targetRelease, nextStores,
      _⟩ :=
    Lower.Sim.dropMany_simulates_releaseSharedWork
      runtime.positiveSharedRC stores sourceRelease
  have nextDescendant : functionTrace.root.Descendant next := by
    exact .step descendant (by simp [Lower.CodeTrace.children])
  have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceReleased
      (.erased :: source) :=
    runtime.runOp (IxIR1.NoReuse.dropMany_reuses sourceRelease)
      sourceOperation
  have nextOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions next sourceReleased
        (.erased :: source) frameRoots :=
    Lower.Sim.SourceOwnershipAt.applyFrom (checked := attached.target)
      functionMember descendant ownership
        (attached.applyOwnershipPreservesFrom_sourceStoreImage_of_declarations
          sourceDeclarations image) sourceOperation
  let nextFrame : Eval.Frame :=
    { frame with
      pc := frame.pc + 1
      values := frame.values.push .erased }
  let nextMachine : Eval.Machine :=
    { store := targetReleased
      heapFuel := 0
      control := .running nextFrame stack }
  let exactMachine : Eval.Machine :=
    { machine with heapFuel := targetHeapFuel }
  have exactControl : exactMachine.control = .running frame stack := by
    simpa [exactMachine] using control
  have exactTransfer : Eval.ApplyTransfer context interpretation
      exactMachine.store exactMachine.heapFuel .erased values.toArray
      { frame with pc := frame.pc + 1 } stack nextMachine := by
    simpa [exactMachine, nextMachine, nextFrame] using
      (Eval.ApplyTransfer.erased
        (context := context) (interpretation := interpretation)
        (resume := { frame with pc := frame.pc + 1 }) (stack := stack)
        (by simpa using targetRelease))
  obtain ⟨_, nextState⟩ :=
    attached.simulate_traced_apply_transfer_state
      (machine := exactMachine) (target := nextMachine) functionMember
      descendant state sourceDeclarations functionResolved argumentsResolved
      sourceOperation noCredits exactControl exactTransfer
  have nextControl : nextMachine.control = .running nextFrame stack := rfl
  have nextNoCredits : nextFrame.credits = #[] := by
    simpa [nextFrame] using noCredits
  have tail := worker (machine := nextMachine) (stack := stack)
    functionMember nextDescendant nextState nextStores nextRuntime
      nextOwnership continuationRun resultWorld nextControl nextNoCredits
      nextImage finish
  refine BudgetedReachesPost.prependFramed
    (before := machine) (middle := nextMachine) (prefixCount := 1)
    (localFuel := targetHeapFuel) ?_ tail
  intro suffixFuel
  let fundedMachine : Eval.Machine :=
    { machine with heapFuel := targetHeapFuel + suffixFuel }
  let fundedNext : Eval.Machine :=
    { nextMachine with heapFuel := suffixFuel }
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  have fundedRelease := Lower.Sim.releaseSharedWork_add_suffix
    (suffix := suffixFuel) targetRelease
  have fundedTransfer : Eval.ApplyTransfer context interpretation
      fundedMachine.store fundedMachine.heapFuel .erased values.toArray
      { frame with pc := frame.pc + 1 } stack fundedNext := by
    simpa [fundedMachine, fundedNext, nextMachine, nextFrame] using
      (Eval.ApplyTransfer.erased
        (context := context) (interpretation := interpretation)
        (resume := { frame with pc := frame.pc + 1 }) (stack := stack)
        (by simpa using fundedRelease))
  obtain ⟨fundedStep, _⟩ :=
    attached.simulate_traced_apply_transfer_state
      (machine := fundedMachine) (target := fundedNext) functionMember
      descendant state sourceDeclarations functionResolved argumentsResolved
      sourceOperation noCredits fundedControl fundedTransfer
  simpa [fundedMachine, fundedNext] using
    fundedStep.toSteps fundedControl

/-- Complete CPS composition for under-saturated dynamic PAP application.
Captured values are retained, the old PAP is released, and the extended PAP
is allocated before the smaller-fuel caller worker resumes. -/
theorem CompiledAttachment.simulate_traced_apply_pap_under_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok (.loc location))
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext sourceFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalUnder : (captured.toList ++ values).length < arity)
    (sourceRun : IxIR1.runCode sourceContext (sourceFuel + 3)
      functionTrace.source sourceStore source
        (.letOp (.apply sourceFunction sourceArguments) next.sourceCode) =
          .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation (sourceFuel + 2)) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  let pap : IxIR1.Node :=
    .papN address arity (captured ++ values.toArray)
  let sourceAllocation := sourceReleased.allocNode .shared pap
  let targetPap : IxIR1.Node :=
    .papN address arity (captured ++ values.toArray)
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      retainedStores, targetRelease, releasedStores, sourceOperation, _,
      nextStores, nextState⟩ :=
    attached.simulate_traced_apply_pap_under_state
      (sourceFuel := sourceFuel) (context := context)
      (interpretation := interpretation) functionMember descendant state
      stores runtime.positiveSharedRC sourceDeclarations functionResolved
      argumentsResolved sourceGet shared node capturedUnder sourceRetain
      sourceRelease totalUnder noCredits control
  have operationRun' : IxIR1.runOp sourceContext (sourceFuel + 2)
      functionTrace.source sourceStore source
        (.apply sourceFunction sourceArguments) =
          .ok (sourceAllocation.1, .loc sourceAllocation.2) := by
    simpa [sourceAllocation, pap] using sourceOperation
  have nextImage : attached.SourceStoreImage sourceAllocation.1 :=
    attached.runOp_preservesSourceStoreImage sourceDeclarations functionMember
      descendant state image operationRun'
  have operationOutput : (middleStore, operationValue) =
      (sourceAllocation.1, .loc sourceAllocation.2) := by
    apply Except.ok.inj (operationRun.symm.trans ?_)
    simpa [sourceAllocation, pap] using sourceOperation
  have middleStoreEq : middleStore = sourceAllocation.1 :=
    congrArg Prod.fst operationOutput
  have operationValueEq : operationValue = .loc sourceAllocation.2 :=
    congrArg Prod.snd operationOutput
  subst middleStore
  subst operationValue
  have nextDescendant : functionTrace.root.Descendant next := by
    exact .step descendant (by simp [Lower.CodeTrace.children])
  have reuseEq : sourceAllocation.1.reuses = sourceStore.reuses := by
    change sourceReleased.reuses = sourceStore.reuses
    exact (IxIR1.NoReuse.dropVal_reuses sourceRelease).trans
      (IxIR1.NoReuse.dupVals_reuses sourceRetain)
  have nextRuntime : Lower.Sim.SourceRuntimeInvariant sourceAllocation.1
      (.loc sourceAllocation.2 :: source) :=
    runtime.runOp reuseEq operationRun'
  have nextOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions next sourceAllocation.1
        (.loc sourceAllocation.2 :: source) frameRoots :=
    Lower.Sim.SourceOwnershipAt.applyFrom (checked := attached.target)
      functionMember descendant ownership
        (attached.applyOwnershipPreservesFrom_sourceStoreImage_of_declarations
          sourceDeclarations image) operationRun'
  let targetAllocation := targetReleased.allocNode .shared targetPap
  let nextFrame : Eval.Frame :=
    { frame with
      pc := frame.pc + 1
      values := frame.values.push (.loc sourceAllocation.2) }
  let nextMachine : Eval.Machine :=
    { store := targetAllocation.1
      heapFuel := 0
      control := .running nextFrame stack }
  have nextControl : nextMachine.control = .running nextFrame stack := rfl
  have nextNoCredits : nextFrame.credits = #[] := by
    simpa [nextFrame] using noCredits
  have nextStores' : Lower.Sim.StoreRel sourceAllocation.1
      nextMachine.store := by
    simpa [nextMachine, targetAllocation, targetPap, sourceAllocation, pap]
      using nextStores
  have nextState' : attached.sidecars.TraceStateRel functionTrace next
      sourceAllocation.1 (.loc sourceAllocation.2 :: source) nextFrame := by
    simpa [sourceAllocation, pap, nextFrame] using nextState
  have tail := worker (machine := nextMachine) (stack := stack)
    functionMember nextDescendant nextState' nextStores' nextRuntime
      nextOwnership continuationRun resultWorld nextControl nextNoCredits
      nextImage finish
  refine BudgetedReachesPost.prependFramed
    (before := machine) (middle := nextMachine) (prefixCount := 1)
    (localFuel := targetHeapFuel) ?_ tail
  intro suffixFuel
  let fundedMachine : Eval.Machine :=
    { machine with heapFuel := targetHeapFuel + suffixFuel }
  let fundedNext : Eval.Machine :=
    { nextMachine with heapFuel := suffixFuel }
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  have targetGet : fundedMachine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have targetUnder : (captured ++ values.toArray).size < arity := by
    simpa using totalUnder
  have fundedRelease := Lower.Sim.releaseSharedWork_add_suffix
    (suffix := suffixFuel) targetRelease
  have locationEq : targetAllocation.2 = sourceAllocation.2 := by
    exact releasedStores.alloc_location .shared pap
  have fundedTransfer := Eval.ApplyTransfer.papUnder
    (context := context) (interpretation := interpretation)
    (resume := { frame with pc := frame.pc + 1 }) (stack := stack)
    targetGet shared node capturedUnder targetRetain fundedRelease targetUnder
  dsimp only at fundedTransfer
  rw [locationEq] at fundedTransfer
  have fundedTransfer' : Eval.ApplyTransfer context interpretation
      fundedMachine.store fundedMachine.heapFuel (.loc location) values.toArray
      { frame with pc := frame.pc + 1 } stack fundedNext := by
    simpa [fundedMachine, fundedNext, nextMachine, nextFrame,
      targetAllocation, targetPap, sourceAllocation, pap] using fundedTransfer
  obtain ⟨fundedStep, _⟩ :=
    attached.simulate_traced_apply_transfer_state
      (machine := fundedMachine) (target := fundedNext) functionMember
      descendant state sourceDeclarations functionResolved argumentsResolved
      (by simpa [sourceAllocation, pap] using sourceOperation) noCredits
      fundedControl fundedTransfer'
  simpa [fundedMachine, fundedNext] using
    fundedStep.toSteps fundedControl

/-- Complete CPS composition for exact dynamic PAP saturation.  The checked
apply capability transition constructs the all-shared callee entry and the
exact suspended caller roots; the callee worker returns through an ordinary
resume handler and the caller worker consumes the successful continuation. -/
theorem CompiledAttachment.simulate_traced_apply_pap_saturated_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    {applyFuel calleeFuel callerFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    (callerMember : callerTrace ∈ attached.target.artifact.trace.functions)
    (calleeMember : calleeTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : callerTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    {sourceStore sourceRetained sourceReleased outputStore finalStore :
      IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {value finalValue : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel callerTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok (.loc location))
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext applyFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalExact : (captured.toList ++ values).length = arity)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition))
    (sourceOperation : IxIR1.runOp sourceContext (applyFuel + 2)
      callerTrace.source sourceStore source
        (.apply sourceFunction sourceArguments) = .ok (outputStore, value))
    (calleeRun : IxIR1.runCode sourceContext calleeFuel sourceDefinition
      sourceReleased (captured.toList ++ values).reverse
        sourceDefinition.body = .ok (outputStore, value))
    (calleeResultWorld : IxIR1.Sim.HasWorld outputStore
      sourceDefinition.result value)
    (callerRuntime : Lower.Sim.SourceRuntimeInvariant outputStore
      (value :: source))
    (callerRun : IxIR1.runCode sourceContext callerFuel callerTrace.source
      outputStore (value :: source) next.sourceCode =
        .ok (finalStore, finalValue))
    (callerResultWorld : IxIR1.Sim.HasWorld finalStore
      callerTrace.source.result finalValue)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation callerTrace frameRoots stack
        (finalStore, finalValue) outcome post)
    (calleeWorker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation calleeFuel)
    (callerWorker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation callerFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  let sourceTotal := captured.toList ++ values
  let targetTotal := captured ++ values.toArray
  let resume : Eval.Frame := { frame with pc := frame.pc + 1 }
  let calleeFrame : Eval.Frame :=
    { definition := targetDefinition, values := targetTotal }
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      _, targetRelease, releasedStores, _, _, calleeState, _⟩ :=
    attached.simulate_traced_apply_pap_saturated_enter_state
      (sourceFuel := applyFuel) (context := context)
      (interpretation := interpretation) callerMember calleeMember
      descendant calleeMatch state stores runtime.positiveSharedRC
      sourceDeclarations functionResolved argumentsResolved sourceGet shared
      node capturedUnder sourceRetain sourceRelease totalExact papArity
      sourceDeclaration sourcePapSafe targetDeclaration noCredits control
  have papAt : sourceStore.get? location =
      some ⟨.shared, box.rc, .papN address arity captured⟩ := by
    simpa only [← shared, ← node] using sourceGet
  have calleePapSafe : calleeTrace.generated.signature.papSafe = true := by
    calc
      calleeTrace.generated.signature.papSafe =
          calleeTrace.source.papSafe := calleeTrace.sourcePapSafe
      _ = sourceDefinition.papSafe := congrArg IxIR1.FnDef.papSafe
        calleeMatch.source
      _ = true := sourcePapSafe
  have entryArity : sourceTotal.length =
      calleeTrace.generated.signature.params.size := by
    calc
      sourceTotal.length = arity := by simpa [sourceTotal] using totalExact
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
      _ = calleeTrace.generated.signature.params.size :=
        calleeTrace.sourceArity.symm
  obtain ⟨_, _, remaining, _, _, _, _, _, readyOwnership,
      entryOwnership⟩ :=
    Lower.Sim.SourceOwnershipAt.applyPapEntry
      (checked := attached.target) (sourceContext := sourceContext)
      (sourceFuel := applyFuel) (supplied := sourceTotal) (residual := [])
      callerMember calleeMember descendant ownership functionResolved
      argumentsResolved papAt sourceRetain sourceRelease
      (by simp [sourceTotal]) entryArity calleePapSafe
  let suspendedRoots : List IxIR1.Sim.Root :=
    Lower.Sim.rootsForCapabilities remaining.toList source ++ frameRoots
  have calleeOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions calleeTrace.root sourceReleased
        sourceTotal.reverse suspendedRoots := by
    simpa [suspendedRoots, IxIR1.Sim.rootsFor] using entryOwnership
  have calleeRuntime : Lower.Sim.SourceRuntimeInvariant sourceReleased
      sourceTotal.reverse :=
    Lower.Sim.SourceRuntimeInvariant.sharedEntry
      ((runtime.order.dupVals sourceRetain).dropVal sourceRelease)
      ((runtime.papsUnder.dupVals sourceRetain).dropVal sourceRelease)
      (by simpa [suspendedRoots, List.append_assoc] using readyOwnership)
  have retainedImage : attached.SourceStoreImage sourceRetained :=
    attached.dupVals_preservesSourceStoreImage image sourceRetain
  have calleeImage : attached.SourceStoreImage sourceReleased :=
    attached.dropVal_preservesSourceStoreImage sourceDeclarations retainedImage
      sourceRelease
  have calleeRun' : IxIR1.runCode sourceContext calleeFuel
      calleeTrace.source sourceReleased sourceTotal.reverse
        calleeTrace.root.sourceCode = .ok (outputStore, value) := by
    rw [calleeTrace.rootSourceCode, calleeMatch.source]
    simpa [sourceTotal] using calleeRun
  have calleeResultWorld' : IxIR1.Sim.HasWorld outputStore
      calleeTrace.source.result value := by
    simpa [calleeMatch.source] using calleeResultWorld
  have callerOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions next outputStore
        (value :: source) frameRoots :=
    Lower.Sim.SourceOwnershipAt.applyFrom (checked := attached.target)
      callerMember descendant ownership
        (attached.applyOwnershipPreservesFrom_sourceStoreImage_of_declarations
          sourceDeclarations image) sourceOperation
  let calleeMachine : Eval.Machine :=
    { store := targetReleased
      heapFuel := 0
      control := .running calleeFrame (.resume resume :: stack) }
  have calleeStores : Lower.Sim.StoreRel sourceReleased
      calleeMachine.store := by
    simpa [calleeMachine] using releasedStores
  have calleeState' : attached.sidecars.TraceStateRel calleeTrace
      calleeTrace.root sourceReleased sourceTotal.reverse calleeFrame := by
    simpa [sourceTotal, targetTotal, calleeFrame] using calleeState
  have calleeControl : calleeMachine.control =
      .running calleeFrame (.resume resume :: stack) := rfl
  have calleeNoCredits : calleeFrame.credits = #[] := rfl
  have returnHandler : SuccessfulReturnHandler attached sourceContext context
      interpretation calleeTrace suspendedRoots (.resume resume :: stack)
      (outputStore, value) outcome post := by
    intro returningTrace returnFuel returnSite returnBlock returnInput
      returnEntryValueCount returnAtom returnTarget returnGenerated returnStore
      returnSource returnFrame returnMachine returningMember returnDescendant
      returnState returnStores returnRuntime returnOwnership returnRun returnWorld
      returnControl returnNoCredits returnImage
    obtain ⟨returnedValue, _, returnOutputEq⟩ :=
      IxIR1.runCode_ret_success returnRun
    have returnStoreEq : returnStore = outputStore :=
      (congrArg Prod.fst returnOutputEq).symm
    have returnedValueEq : returnedValue = value :=
      (congrArg Prod.snd returnOutputEq).symm
    subst returnStore
    subst returnedValue
    have handler : SuccessfulReturnHandler attached sourceContext context
        interpretation returningTrace suspendedRoots
        (.resume { frame with pc := frame.pc + 1 } :: stack)
        (outputStore, value) outcome post :=
      resumeReturnHandlerWithOwnership attached
        (sourceContext := sourceContext) (callerFuel := callerFuel)
        (operationFuel := applyFuel + 2) (context := context)
        (interpretation := interpretation) (calleeTrace := returningTrace)
        (outcome := outcome) (post := post) callerMember descendant state
        (binder := by rfl) (delta := by rfl) sourceDeclarations
        sourceOperation callerRuntime callerOwnership callerRun
        callerResultWorld noCredits finish callerWorker
    apply handler returningMember returnDescendant returnState returnStores
      returnRuntime returnOwnership returnRun returnWorld
    · simpa [resume] using returnControl
    · exact returnNoCredits
    · exact returnImage
  have tail := calleeWorker (machine := calleeMachine)
    (stack := .resume resume :: stack) calleeMember
      Lower.CodeTrace.Descendant.refl calleeState' calleeStores calleeRuntime
      calleeOwnership calleeRun' calleeResultWorld' calleeControl
      calleeNoCredits calleeImage returnHandler
  refine BudgetedReachesPost.prependFramed
    (before := machine) (middle := calleeMachine) (prefixCount := 1)
    (localFuel := targetHeapFuel) ?_ tail
  intro suffixFuel
  let fundedMachine : Eval.Machine :=
    { machine with heapFuel := targetHeapFuel + suffixFuel }
  let fundedCallee : Eval.Machine :=
    { calleeMachine with heapFuel := suffixFuel }
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  have targetGet : fundedMachine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have fundedRelease := Lower.Sim.releaseSharedWork_add_suffix
    (suffix := suffixFuel) targetRelease
  have totalArrayEq : sourceTotal.toArray = targetTotal := by
    apply Array.toList_inj.mp
    simp [sourceTotal, targetTotal]
  have targetSize : targetTotal.size = arity := by
    simpa [sourceTotal, targetTotal] using totalExact
  have targetPapSafe : targetDefinition.signature.papSafe = true := by
    calc
      targetDefinition.signature.papSafe =
          calleeTrace.generated.signature.papSafe := by
            rw [calleeMatch.generated]
      _ = true := calleePapSafe
  have targetParamArity : targetDefinition.signature.params.size = arity := by
    calc
      targetDefinition.signature.params.size =
          calleeTrace.generated.signature.params.size := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.arity := calleeTrace.sourceArity
      _ = sourceDefinition.arity := congrArg IxIR1.FnDef.arity
        calleeMatch.source
      _ = arity := papArity.symm
  have suppliedEq : targetTotal.extract 0 arity = targetTotal := by
    rw [← targetSize]
    exact Array.extract_size
  have suppliedArity : (targetTotal.extract 0 arity).size =
      targetDefinition.signature.params.size := by
    rw [suppliedEq, targetSize, targetParamArity]
  have targetNonempty : targetDefinition.blocks.isEmpty = false := by
    simpa [calleeMatch.generated] using calleeTrace.generatedNonempty
  have fundedTransfer := Eval.ApplyTransfer.papFn
    (context := context) (interpretation := interpretation)
    (resume := resume) (stack := stack) targetGet shared node capturedUnder
      targetRetain fundedRelease
      (by simpa [targetTotal] using Nat.le_of_eq targetSize.symm)
      targetDeclaration targetPapSafe suppliedArity targetNonempty
  dsimp only at fundedTransfer
  have remainingEmpty :
      (targetTotal.extract arity targetTotal.size).isEmpty = true := by
    simp [Array.isEmpty, Array.size_extract]
    omega
  rw [suppliedEq, remainingEmpty] at fundedTransfer
  simp only [if_true] at fundedTransfer
  have fundedTransfer' : Eval.ApplyTransfer context interpretation
      fundedMachine.store fundedMachine.heapFuel (.loc location)
      values.toArray resume stack fundedCallee := by
    simpa [fundedMachine, fundedCallee, calleeMachine, calleeFrame,
      sourceTotal, targetTotal] using fundedTransfer
  obtain ⟨fundedStep, _⟩ :=
    attached.simulate_traced_apply_transfer_state
      (machine := fundedMachine) (target := fundedCallee) callerMember
      descendant state sourceDeclarations functionResolved argumentsResolved
      sourceOperation noCredits fundedControl fundedTransfer'
  simpa [fundedMachine, fundedCallee] using
    fundedStep.toSteps fundedControl

/-- Complete CPS composition for an erased return-time `applyMore` result.
Residual arguments are released with an exact local heap budget, and that
budget is framed over the already funded resumed-caller continuation. -/
theorem CompiledAttachment.simulate_traced_ret_apply_more_erased_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {returnFuel applyFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {returnFrame caller : Eval.Frame}
    {rest : List Eval.Continuation} {returningTrace : Lower.FunctionTrace}
    {returnSite : Lower.SourceSite} {returnBlock : BlockId}
    {returnInput : Lower.Sim.EnvMap} {returnEntryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {returnGenerated : Block}
    (returnDescendant : returningTrace.root.Descendant
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated))
    {sourceStore sourceReleased : IxIR1.Store}
    {source values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel returningTrace
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated) sourceStore source returnFrame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (resultWorld : IxIR1.Sim.HasWorld sourceStore
      returningTrace.source.result .erased)
    (sourceRun : IxIR1.runCode sourceContext (returnFuel + 1)
      returningTrace.source sourceStore source (.ret sourceAtom) =
        .ok (sourceStore, .erased))
    (control : machine.control =
      .running returnFrame (.applyMore values.toArray caller :: rest))
    (noCredits : returnFrame.credits = #[])
    (sourceRelease : IxIR1.dropMany sourceContext applyFuel sourceStore
      values = .ok sourceReleased)
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (continuation : SuccessfulResumeContinuation context interpretation
      caller rest (sourceReleased, .erased) outcome post) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨targetHeapFuel, targetReleased, targetRelease, nextStores, _⟩ :=
    Lower.Sim.dropMany_simulates_releaseSharedWork runtime.positiveSharedRC
      stores sourceRelease
  let nextMachine : Eval.Machine :=
    { store := targetReleased
      heapFuel := 0
      control := .running
        { caller with values := caller.values.push .erased } rest }
  have nextStores' : Lower.Sim.StoreRel sourceReleased
      nextMachine.store := by
    simpa [nextMachine] using nextStores
  have nextControl : nextMachine.control = .running
      { caller with values := caller.values.push .erased } rest := rfl
  have tail := continuation nextStores' nextControl
  refine BudgetedReachesPost.prependFramed
    (before := machine) (middle := nextMachine) (prefixCount := 1)
    (localFuel := targetHeapFuel) ?_ tail
  intro suffixFuel
  let fundedMachine : Eval.Machine :=
    { machine with heapFuel := targetHeapFuel + suffixFuel }
  let fundedNext : Eval.Machine :=
    { nextMachine with heapFuel := suffixFuel }
  have fundedStores : Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control =
      .running returnFrame (.applyMore values.toArray caller :: rest) := by
    simpa [fundedMachine] using control
  have fundedRelease := Lower.Sim.releaseSharedWork_add_suffix
    (suffix := suffixFuel) targetRelease
  have fundedTransfer : Eval.ApplyTransfer context interpretation
      fundedMachine.store fundedMachine.heapFuel .erased values.toArray caller
      rest fundedNext := by
    simpa [fundedMachine, fundedNext, nextMachine] using
      (Eval.ApplyTransfer.erased
        (context := context) (interpretation := interpretation)
        (resume := caller) (stack := rest) fundedRelease)
  obtain ⟨_, _, fundedSteps, _⟩ :=
    attached.simulate_traced_ret_apply_more_success
      (machine := fundedMachine) (target := fundedNext) returnDescendant state
      fundedStores sourceRun resultWorld fundedControl noCredits fundedTransfer
  simpa [fundedMachine, fundedNext] using fundedSteps

/-- Complete CPS composition for an under-saturated PAP returned to
`applyMore`.  The longer PAP allocation resumes the caller immediately, while
the old PAP's exact release cost is framed over the resumed continuation. -/
theorem CompiledAttachment.simulate_traced_ret_apply_more_pap_under_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {returnFuel applyFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {returnFrame caller : Eval.Frame}
    {rest : List Eval.Continuation} {returningTrace : Lower.FunctionTrace}
    {returnSite : Lower.SourceSite} {returnBlock : BlockId}
    {returnInput : Lower.Sim.EnvMap} {returnEntryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {returnGenerated : Block}
    (returnDescendant : returningTrace.root.Descendant
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated))
    {sourceStore sourceRetained sourceReleased : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel returningTrace
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated) sourceStore source returnFrame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (resultWorld : IxIR1.Sim.HasWorld sourceStore
      returningTrace.source.result (.loc location))
    (sourceRun : IxIR1.runCode sourceContext (returnFuel + 1)
      returningTrace.source sourceStore source (.ret sourceAtom) =
        .ok (sourceStore, .loc location))
    (control : machine.control =
      .running returnFrame (.applyMore values.toArray caller :: rest))
    (noCredits : returnFrame.credits = #[])
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext applyFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalUnder : (captured.toList ++ values).length < arity)
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (continuation : SuccessfulResumeContinuation context interpretation
      caller rest
      ((sourceReleased.allocNode .shared
          (.papN address arity (captured ++ values.toArray))).1,
        .loc (sourceReleased.allocNode .shared
          (.papN address arity (captured ++ values.toArray))).2)
      outcome post) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  let pap : IxIR1.Node :=
    .papN address arity (captured ++ values.toArray)
  let sourceAllocation := sourceReleased.allocNode .shared pap
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      _, targetRelease, releasedStores, _, _, _, nextStores⟩ :=
    attached.simulate_traced_ret_apply_more_pap_under_state
      (returnFuel := returnFuel) (applyFuel := applyFuel)
      (context := context) (interpretation := interpretation) returnDescendant
      state stores runtime.positiveSharedRC sourceResolved resultWorld control
      noCredits sourceGet shared node capturedUnder sourceRetain sourceRelease
      totalUnder
  let actualTargetAllocation := targetReleased.allocNode .shared pap
  have nextStores' : Lower.Sim.StoreRel sourceAllocation.1
      actualTargetAllocation.1 := by
    simpa [sourceAllocation, pap, actualTargetAllocation] using nextStores
  have locationEq : actualTargetAllocation.2 = sourceAllocation.2 :=
    releasedStores.alloc_location .shared pap
  let nextMachine : Eval.Machine :=
    { store := actualTargetAllocation.1
      heapFuel := 0
      control := .running
        { caller with values := caller.values.push (.loc sourceAllocation.2) }
        rest }
  have nextStores'' : Lower.Sim.StoreRel sourceAllocation.1
      nextMachine.store := by
    simpa [nextMachine] using nextStores'
  have nextControl : nextMachine.control = .running
      { caller with values := caller.values.push (.loc sourceAllocation.2) }
      rest := rfl
  have continuation' : SuccessfulResumeContinuation context interpretation
      caller rest (sourceAllocation.1, .loc sourceAllocation.2) outcome post := by
    change SuccessfulResumeContinuation context interpretation caller rest
      (sourceAllocation.1, .loc sourceAllocation.2) outcome post at continuation
    exact continuation
  have tail := continuation' nextStores'' nextControl
  refine BudgetedReachesPost.prependFramed
    (before := machine) (middle := nextMachine) (prefixCount := 1)
    (localFuel := targetHeapFuel) ?_ tail
  intro suffixFuel
  let fundedMachine : Eval.Machine :=
    { machine with heapFuel := targetHeapFuel + suffixFuel }
  let fundedNext : Eval.Machine :=
    { nextMachine with heapFuel := suffixFuel }
  have fundedStores : Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control =
      .running returnFrame (.applyMore values.toArray caller :: rest) := by
    simpa [fundedMachine] using control
  have targetGet : fundedMachine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have targetUnder : (captured ++ values.toArray).size < arity := by
    simpa using totalUnder
  have fundedRelease := Lower.Sim.releaseSharedWork_add_suffix
    (suffix := suffixFuel) targetRelease
  have fundedTransfer := Eval.ApplyTransfer.papUnder
    (context := context) (interpretation := interpretation)
    (resume := caller) (stack := rest) targetGet shared node capturedUnder
      targetRetain fundedRelease targetUnder
  dsimp only at fundedTransfer
  rw [locationEq] at fundedTransfer
  have fundedTransfer' : Eval.ApplyTransfer context interpretation
      fundedMachine.store fundedMachine.heapFuel (.loc location)
      values.toArray caller rest fundedNext := by
    simpa [fundedMachine, fundedNext, nextMachine, actualTargetAllocation,
      sourceAllocation, pap] using fundedTransfer
  obtain ⟨_, _, fundedSteps, _⟩ :=
    attached.simulate_traced_ret_apply_more_success
      (machine := fundedMachine) (target := fundedNext) returnDescendant state
      fundedStores sourceRun resultWorld fundedControl noCredits fundedTransfer'
  simpa [fundedMachine, fundedNext] using fundedSteps

/-- Complete CPS composition for an exactly saturated return-time `applyMore`
redispatch.  Terminal ownership is reworlded to the shared PAP root, the PAP
retain/release prefix constructs the next callee's canonical entry, and the
local heap cost is framed over that callee's ordinary resume handler. -/
theorem CompiledAttachment.simulate_traced_ret_apply_more_pap_saturated_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    {returnFuel applyFuel calleeFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {returnFrame caller : Eval.Frame}
    {rest : List Eval.Continuation}
    {returningTrace calleeTrace : Lower.FunctionTrace}
    (returningMember : returningTrace ∈
      attached.target.artifact.trace.functions)
    (calleeMember : calleeTrace ∈
      attached.target.artifact.trace.functions)
    {returnSite : Lower.SourceSite} {returnBlock : BlockId}
    {returnInput : Lower.Sim.EnvMap} {returnEntryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {returnGenerated : Block}
    (returnDescendant : returningTrace.root.Descendant
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    {sourceStore sourceRetained sourceReleased outputStore : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    {suspendedRoots : List IxIR1.Sim.Root}
    {value : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel returningTrace
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated) sourceStore source returnFrame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated)
      sourceStore source
        (IxIR1.Sim.rootsFor .shared values ++ suspendedRoots))
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (resultWorld : IxIR1.Sim.HasWorld sourceStore
      returningTrace.source.result (.loc location))
    (sourceRun : IxIR1.runCode sourceContext (returnFuel + 1)
      returningTrace.source sourceStore source (.ret sourceAtom) =
        .ok (sourceStore, .loc location))
    (control : machine.control =
      .running returnFrame (.applyMore values.toArray caller :: rest))
    (noCredits : returnFrame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext applyFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalExact : (captured.toList ++ values).length = arity)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition))
    (calleeRun : IxIR1.runCode sourceContext calleeFuel sourceDefinition
      sourceReleased (captured.toList ++ values).reverse
        sourceDefinition.body = .ok (outputStore, value))
    (calleeResultWorld : IxIR1.Sim.HasWorld outputStore
      sourceDefinition.result value)
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (nextHandler : SuccessfulReturnHandler attached sourceContext context
      interpretation calleeTrace suspendedRoots (.resume caller :: rest)
      (outputStore, value) outcome post)
    (calleeWorker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation calleeFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  let sourceTotal := captured.toList ++ values
  let targetTotal := captured ++ values.toArray
  let calleeFrame : Eval.Frame :=
    { definition := targetDefinition, values := targetTotal }
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      _, targetRelease, releasedStores, _, _, _, calleeState⟩ :=
    attached.simulate_traced_ret_apply_more_pap_saturated_enter_state
      (returnFuel := returnFuel) (applyFuel := applyFuel)
      (context := context) (interpretation := interpretation) calleeMember
      returnDescendant calleeMatch state stores runtime.positiveSharedRC
      sourceResolved resultWorld control noCredits sourceGet shared node
      capturedUnder sourceRetain sourceRelease totalExact papArity
      sourceDeclaration sourcePapSafe targetDeclaration
  have papAt : sourceStore.get? location =
      some ⟨.shared, box.rc, .papN address arity captured⟩ := by
    simpa only [← shared, ← node] using sourceGet
  have terminalOwnership := Lower.Sim.SourceOwnershipAt.returnRoot
    (checked := attached.target) returningMember returnDescendant ownership
      sourceResolved
  have sharedResult : IxIR1.Sim.HasWorld sourceStore .shared
      (.loc location) := ⟨box, sourceGet, shared⟩
  have returnedOwnership : IxIR1.Sim.RootOwnership sourceStore
      (⟨.shared, .loc location⟩ ::
        IxIR1.Sim.rootsFor .shared values ++ suspendedRoots) :=
    Lower.Sim.RootOwnership_reworldHead terminalOwnership sharedResult
  have readyOwnership : IxIR1.Sim.RootOwnership sourceReleased
      (IxIR1.Sim.rootsFor .shared sourceTotal ++ suspendedRoots) := by
    simpa [sourceTotal] using IxIR1.Sim.applyGo_preparePap_owned papAt
      returnedOwnership sourceRetain sourceRelease
  have calleePapSafe : calleeTrace.generated.signature.papSafe = true := by
    calc
      calleeTrace.generated.signature.papSafe =
          calleeTrace.source.papSafe := calleeTrace.sourcePapSafe
      _ = sourceDefinition.papSafe := congrArg IxIR1.FnDef.papSafe
        calleeMatch.source
      _ = true := sourcePapSafe
  have entryArity : sourceTotal.length =
      calleeTrace.generated.signature.params.size := by
    calc
      sourceTotal.length = arity := by simpa [sourceTotal] using totalExact
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
      _ = calleeTrace.generated.signature.params.size :=
        calleeTrace.sourceArity.symm
  have entryShape :
      Lower.entryCapabilities calleeTrace.generated.signature =
        Array.replicate sourceTotal.length (.owned .shared) := by
    simpa [entryArity] using
      attached.target.papSafeEntryCapabilities calleeMember calleePapSafe
  have calleeOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions calleeTrace.root sourceReleased
        sourceTotal.reverse suspendedRoots := by
    intro entry entryMember entryCoordinate
    rw [attached.target.entryCapabilities calleeMember entryMember
      entryCoordinate]
    exact Lower.Sim.SourceOwnershipInvariant.sharedEntry entryShape
      readyOwnership
  have calleeRuntime : Lower.Sim.SourceRuntimeInvariant sourceReleased
      sourceTotal.reverse :=
    Lower.Sim.SourceRuntimeInvariant.sharedEntry
      ((runtime.order.dupVals sourceRetain).dropVal sourceRelease)
      ((runtime.papsUnder.dupVals sourceRetain).dropVal sourceRelease)
      readyOwnership
  have retainedImage : attached.SourceStoreImage sourceRetained :=
    attached.dupVals_preservesSourceStoreImage image sourceRetain
  have calleeImage : attached.SourceStoreImage sourceReleased :=
    attached.dropVal_preservesSourceStoreImage sourceDeclarations retainedImage
      sourceRelease
  have calleeRun' : IxIR1.runCode sourceContext calleeFuel
      calleeTrace.source sourceReleased sourceTotal.reverse
        calleeTrace.root.sourceCode = .ok (outputStore, value) := by
    rw [calleeTrace.rootSourceCode, calleeMatch.source]
    simpa [sourceTotal] using calleeRun
  have calleeResultWorld' : IxIR1.Sim.HasWorld outputStore
      calleeTrace.source.result value := by
    simpa [calleeMatch.source] using calleeResultWorld
  let calleeMachine : Eval.Machine :=
    { store := targetReleased
      heapFuel := 0
      control := .running calleeFrame (.resume caller :: rest) }
  have calleeStores : Lower.Sim.StoreRel sourceReleased
      calleeMachine.store := by
    simpa [calleeMachine] using releasedStores
  have calleeState' : attached.sidecars.TraceStateRel calleeTrace
      calleeTrace.root sourceReleased sourceTotal.reverse calleeFrame := by
    simpa [sourceTotal, targetTotal, calleeFrame] using calleeState
  have calleeControl : calleeMachine.control =
      .running calleeFrame (.resume caller :: rest) := rfl
  have calleeNoCredits : calleeFrame.credits = #[] := rfl
  have tail := calleeWorker (machine := calleeMachine)
    (stack := .resume caller :: rest) calleeMember
      Lower.CodeTrace.Descendant.refl calleeState' calleeStores calleeRuntime
      calleeOwnership calleeRun' calleeResultWorld' calleeControl
      calleeNoCredits calleeImage nextHandler
  refine BudgetedReachesPost.prependFramed
    (before := machine) (middle := calleeMachine) (prefixCount := 1)
    (localFuel := targetHeapFuel) ?_ tail
  intro suffixFuel
  let fundedMachine : Eval.Machine :=
    { machine with heapFuel := targetHeapFuel + suffixFuel }
  let fundedCallee : Eval.Machine :=
    { calleeMachine with heapFuel := suffixFuel }
  have fundedStores : Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control =
      .running returnFrame (.applyMore values.toArray caller :: rest) := by
    simpa [fundedMachine] using control
  have targetGet : fundedMachine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have fundedRelease := Lower.Sim.releaseSharedWork_add_suffix
    (suffix := suffixFuel) targetRelease
  have targetSize : targetTotal.size = arity := by
    simpa [sourceTotal, targetTotal] using totalExact
  have targetPapSafe : targetDefinition.signature.papSafe = true := by
    calc
      targetDefinition.signature.papSafe =
          calleeTrace.generated.signature.papSafe := by
            rw [calleeMatch.generated]
      _ = true := calleePapSafe
  have targetParamArity :
      targetDefinition.signature.params.size = arity := by
    calc
      targetDefinition.signature.params.size =
          calleeTrace.generated.signature.params.size := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.arity := calleeTrace.sourceArity
      _ = sourceDefinition.arity := congrArg IxIR1.FnDef.arity
        calleeMatch.source
      _ = arity := papArity.symm
  have suppliedEq : targetTotal.extract 0 arity = targetTotal := by
    rw [← targetSize]
    exact Array.extract_size
  have suppliedArity : (targetTotal.extract 0 arity).size =
      targetDefinition.signature.params.size := by
    rw [suppliedEq, targetSize, targetParamArity]
  have targetNonempty : targetDefinition.blocks.isEmpty = false := by
    simpa [calleeMatch.generated] using calleeTrace.generatedNonempty
  have fundedTransfer := Eval.ApplyTransfer.papFn
    (context := context) (interpretation := interpretation)
    (resume := caller) (stack := rest) targetGet shared node capturedUnder
      targetRetain fundedRelease
      (by simpa [targetTotal] using Nat.le_of_eq targetSize.symm)
      targetDeclaration targetPapSafe suppliedArity targetNonempty
  dsimp only at fundedTransfer
  have remainingEmpty :
      (targetTotal.extract arity targetTotal.size).isEmpty = true := by
    simp [Array.isEmpty, Array.size_extract]
    omega
  rw [suppliedEq, remainingEmpty] at fundedTransfer
  simp only [if_true] at fundedTransfer
  have fundedTransfer' : Eval.ApplyTransfer context interpretation
      fundedMachine.store fundedMachine.heapFuel (.loc location)
      values.toArray caller rest fundedCallee := by
    simpa [fundedMachine, fundedCallee, calleeMachine, calleeFrame,
      sourceTotal, targetTotal] using fundedTransfer
  obtain ⟨_, _, fundedSteps, _⟩ :=
    attached.simulate_traced_ret_apply_more_success
      (machine := fundedMachine) (target := fundedCallee) returnDescendant
      state fundedStores sourceRun resultWorld fundedControl noCredits
      fundedTransfer'
  simpa [fundedMachine, fundedCallee] using fundedSteps

/-- Complete CPS composition for an over-saturated return-time `applyMore`
redispatch.  The returning callee's terminal ownership exposes the shared PAP
and residual arguments, the PAP preparation splits the next callee's supplied
and residual roots, and the local retain/release cost is framed over the next
callee worker and its recursive `applyMore` handler. -/
theorem CompiledAttachment.simulate_traced_ret_apply_more_pap_over_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    {returnFuel applyFuel calleeFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {returnFrame caller : Eval.Frame}
    {rest : List Eval.Continuation}
    {returningTrace calleeTrace : Lower.FunctionTrace}
    (returningMember : returningTrace ∈
      attached.target.artifact.trace.functions)
    (calleeMember : calleeTrace ∈
      attached.target.artifact.trace.functions)
    {returnSite : Lower.SourceSite} {returnBlock : BlockId}
    {returnInput : Lower.Sim.EnvMap} {returnEntryValueCount : Nat}
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {returnGenerated : Block}
    (returnDescendant : returningTrace.root.Descendant
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    {sourceStore sourceRetained sourceReleased outputStore : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    {suspendedRoots : List IxIR1.Sim.Root}
    {value : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel returningTrace
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated) sourceStore source returnFrame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.ret returnSite returnBlock returnInput returnEntryValueCount sourceAtom
        targetAtom returnGenerated)
      sourceStore source
        (IxIR1.Sim.rootsFor .shared values ++ suspendedRoots))
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (resultWorld : IxIR1.Sim.HasWorld sourceStore
      returningTrace.source.result (.loc location))
    (sourceRun : IxIR1.runCode sourceContext (returnFuel + 1)
      returningTrace.source sourceStore source (.ret sourceAtom) =
        .ok (sourceStore, .loc location))
    (control : machine.control =
      .running returnFrame (.applyMore values.toArray caller :: rest))
    (noCredits : returnFrame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext applyFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalOver : arity < (captured.toList ++ values).length)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition))
    (calleeRun : IxIR1.runCode sourceContext calleeFuel sourceDefinition
      sourceReleased ((captured.toList ++ values).take arity).reverse
        sourceDefinition.body = .ok (outputStore, value))
    (calleeResultWorld : IxIR1.Sim.HasWorld outputStore
      sourceDefinition.result value)
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (nextHandler : SuccessfulReturnHandler attached sourceContext context
      interpretation calleeTrace
      (IxIR1.Sim.rootsFor .shared
          ((captured.toList ++ values).drop arity) ++ suspendedRoots)
      (.applyMore
          ((captured ++ values.toArray).extract arity
            (captured ++ values.toArray).size)
          caller :: rest)
      (outputStore, value) outcome post)
    (calleeWorker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation calleeFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  let sourceTotal := captured.toList ++ values
  let sourceSupplied := sourceTotal.take arity
  let sourceRemaining := sourceTotal.drop arity
  let targetTotal := captured ++ values.toArray
  let targetSupplied := targetTotal.extract 0 arity
  let targetRemaining := targetTotal.extract arity targetTotal.size
  let calleeFrame : Eval.Frame :=
    { definition := targetDefinition, values := targetSupplied }
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      _, targetRelease, releasedStores, _, _, _, remainingEq, calleeState⟩ :=
    attached.simulate_traced_ret_apply_more_pap_over_enter_state
      (returnFuel := returnFuel) (applyFuel := applyFuel)
      (context := context) (interpretation := interpretation) calleeMember
      returnDescendant calleeMatch state stores runtime.positiveSharedRC
      sourceResolved resultWorld control noCredits sourceGet shared node
      capturedUnder sourceRetain sourceRelease totalOver papArity
      sourceDeclaration sourcePapSafe targetDeclaration
  have papAt : sourceStore.get? location =
      some ⟨.shared, box.rc, .papN address arity captured⟩ := by
    simpa only [← shared, ← node] using sourceGet
  have terminalOwnership := Lower.Sim.SourceOwnershipAt.returnRoot
    (checked := attached.target) returningMember returnDescendant ownership
      sourceResolved
  have sharedResult : IxIR1.Sim.HasWorld sourceStore .shared
      (.loc location) := ⟨box, sourceGet, shared⟩
  have returnedOwnership : IxIR1.Sim.RootOwnership sourceStore
      (⟨.shared, .loc location⟩ ::
        IxIR1.Sim.rootsFor .shared values ++ suspendedRoots) :=
    Lower.Sim.RootOwnership_reworldHead terminalOwnership sharedResult
  have preparedOwnership := IxIR1.Sim.applyGo_preparePap_owned papAt
    returnedOwnership sourceRetain sourceRelease
  have readyOwnership : IxIR1.Sim.RootOwnership sourceReleased
      (IxIR1.Sim.rootsFor .shared sourceSupplied ++
        IxIR1.Sim.rootsFor .shared sourceRemaining ++ suspendedRoots) := by
    simpa [sourceTotal, sourceSupplied, sourceRemaining,
      IxIR1.Sim.rootsFor, List.append_assoc] using preparedOwnership
  have calleePapSafe : calleeTrace.generated.signature.papSafe = true := by
    calc
      calleeTrace.generated.signature.papSafe =
          calleeTrace.source.papSafe := calleeTrace.sourcePapSafe
      _ = sourceDefinition.papSafe := congrArg IxIR1.FnDef.papSafe
        calleeMatch.source
      _ = true := sourcePapSafe
  have suppliedArity : sourceSupplied.length =
      calleeTrace.generated.signature.params.size := by
    have sourceOver : arity < sourceTotal.length := by
      simpa [sourceTotal] using totalOver
    calc
      sourceSupplied.length = arity := by
        simp [sourceSupplied, Nat.min_eq_left (Nat.le_of_lt sourceOver)]
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
      _ = calleeTrace.generated.signature.params.size :=
        calleeTrace.sourceArity.symm
  have entryShape :
      Lower.entryCapabilities calleeTrace.generated.signature =
        Array.replicate sourceSupplied.length (.owned .shared) := by
    simpa [suppliedArity] using
      attached.target.papSafeEntryCapabilities calleeMember calleePapSafe
  have calleeOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions calleeTrace.root sourceReleased
        sourceSupplied.reverse
        (IxIR1.Sim.rootsFor .shared sourceRemaining ++ suspendedRoots) := by
    intro entry entryMember entryCoordinate
    rw [attached.target.entryCapabilities calleeMember entryMember
      entryCoordinate]
    exact Lower.Sim.SourceOwnershipInvariant.sharedEntry entryShape
      (by simpa [List.append_assoc] using readyOwnership)
  have calleeRuntime : Lower.Sim.SourceRuntimeInvariant sourceReleased
      sourceSupplied.reverse :=
    Lower.Sim.SourceRuntimeInvariant.sharedEntry
      ((runtime.order.dupVals sourceRetain).dropVal sourceRelease)
      ((runtime.papsUnder.dupVals sourceRetain).dropVal sourceRelease)
      (by simpa [List.append_assoc] using readyOwnership)
  have retainedImage : attached.SourceStoreImage sourceRetained :=
    attached.dupVals_preservesSourceStoreImage image sourceRetain
  have calleeImage : attached.SourceStoreImage sourceReleased :=
    attached.dropVal_preservesSourceStoreImage sourceDeclarations retainedImage
      sourceRelease
  have calleeRun' : IxIR1.runCode sourceContext calleeFuel
      calleeTrace.source sourceReleased sourceSupplied.reverse
        calleeTrace.root.sourceCode = .ok (outputStore, value) := by
    rw [calleeTrace.rootSourceCode, calleeMatch.source]
    simpa [sourceTotal, sourceSupplied] using calleeRun
  have calleeResultWorld' : IxIR1.Sim.HasWorld outputStore
      calleeTrace.source.result value := by
    simpa [calleeMatch.source] using calleeResultWorld
  let calleeMachine : Eval.Machine :=
    { store := targetReleased
      heapFuel := 0
      control := .running calleeFrame
        (.applyMore targetRemaining caller :: rest) }
  have calleeStores : Lower.Sim.StoreRel sourceReleased
      calleeMachine.store := by
    simpa [calleeMachine] using releasedStores
  have calleeState' : attached.sidecars.TraceStateRel calleeTrace
      calleeTrace.root sourceReleased sourceSupplied.reverse calleeFrame := by
    simpa [sourceTotal, sourceSupplied, targetTotal, targetSupplied,
      calleeFrame] using calleeState
  have calleeControl : calleeMachine.control =
      .running calleeFrame (.applyMore targetRemaining caller :: rest) := rfl
  have calleeNoCredits : calleeFrame.credits = #[] := rfl
  have nextHandler' : SuccessfulReturnHandler attached sourceContext context
      interpretation calleeTrace
      (IxIR1.Sim.rootsFor .shared sourceRemaining ++ suspendedRoots)
      (.applyMore targetRemaining caller :: rest)
      (outputStore, value) outcome post := by
    change SuccessfulReturnHandler attached sourceContext context
      interpretation calleeTrace
      (IxIR1.Sim.rootsFor .shared sourceRemaining ++ suspendedRoots)
      (.applyMore targetRemaining caller :: rest)
      (outputStore, value) outcome post at nextHandler
    exact nextHandler
  have tail := calleeWorker (machine := calleeMachine)
    (stack := .applyMore targetRemaining caller :: rest) calleeMember
      Lower.CodeTrace.Descendant.refl calleeState' calleeStores calleeRuntime
      calleeOwnership calleeRun' calleeResultWorld' calleeControl
      calleeNoCredits calleeImage nextHandler'
  refine BudgetedReachesPost.prependFramed
    (before := machine) (middle := calleeMachine) (prefixCount := 1)
    (localFuel := targetHeapFuel) ?_ tail
  intro suffixFuel
  let fundedMachine : Eval.Machine :=
    { machine with heapFuel := targetHeapFuel + suffixFuel }
  let fundedCallee : Eval.Machine :=
    { calleeMachine with heapFuel := suffixFuel }
  have fundedStores : Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control =
      .running returnFrame (.applyMore values.toArray caller :: rest) := by
    simpa [fundedMachine] using control
  have targetGet : fundedMachine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have fundedRelease := Lower.Sim.releaseSharedWork_add_suffix
    (suffix := suffixFuel) targetRelease
  have targetOver : arity < targetTotal.size := by
    simpa [sourceTotal, targetTotal] using totalOver
  have targetPapSafe : targetDefinition.signature.papSafe = true := by
    calc
      targetDefinition.signature.papSafe =
          calleeTrace.generated.signature.papSafe := by
            rw [calleeMatch.generated]
      _ = true := calleePapSafe
  have targetParamArity :
      targetDefinition.signature.params.size = arity := by
    calc
      targetDefinition.signature.params.size =
          calleeTrace.generated.signature.params.size := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.arity := calleeTrace.sourceArity
      _ = sourceDefinition.arity := congrArg IxIR1.FnDef.arity
        calleeMatch.source
      _ = arity := papArity.symm
  have targetSuppliedSize : targetSupplied.size = arity := by
    simp [targetSupplied, Array.size_extract]
    omega
  have targetSuppliedArity : targetSupplied.size =
      targetDefinition.signature.params.size := by
    rw [targetSuppliedSize, targetParamArity]
  have targetNonempty : targetDefinition.blocks.isEmpty = false := by
    simpa [calleeMatch.generated] using calleeTrace.generatedNonempty
  have fundedTransfer := Eval.ApplyTransfer.papFn
    (context := context) (interpretation := interpretation)
    (resume := caller) (stack := rest) targetGet shared node capturedUnder
      targetRetain fundedRelease (Nat.le_of_lt targetOver) targetDeclaration
      targetPapSafe targetSuppliedArity targetNonempty
  dsimp only at fundedTransfer
  have remainingNonempty : targetRemaining.isEmpty = false := by
    simp [targetRemaining, Array.isEmpty, Array.size_extract]
    omega
  rw [remainingNonempty] at fundedTransfer
  have fundedTransfer' : Eval.ApplyTransfer context interpretation
      fundedMachine.store fundedMachine.heapFuel (.loc location)
      values.toArray caller rest fundedCallee := by
    simpa [fundedMachine, fundedCallee, calleeMachine, calleeFrame,
      targetTotal, targetSupplied, targetRemaining] using fundedTransfer
  obtain ⟨_, _, fundedSteps, _⟩ :=
    attached.simulate_traced_ret_apply_more_success
      (machine := fundedMachine) (target := fundedCallee) returnDescendant
      state fundedStores sourceRun resultWorld fundedControl noCredits
      fundedTransfer'
  simpa [fundedMachine, fundedCallee] using fundedSteps

/-- Complete CPS composition for an over-saturated dynamic PAP application.
The checked apply transition partitions the source roots between the first
callee and its residual `applyMore` continuation; the first callee worker then
runs under the supplied recursively constructed return handler. -/
theorem CompiledAttachment.simulate_traced_apply_pap_over_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    {applyFuel calleeFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    (callerMember : callerTrace ∈ attached.target.artifact.trace.functions)
    (calleeMember : calleeTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceFunction : IxIR1.Atom} {targetFunction : Atom}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : callerTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    {sourceStore sourceRetained sourceReleased outputStore : IxIR1.Store}
    {source : List IxIR1.RVal} {location : Nat} {box : IxIR1.NodeBox}
    {address : Ixon.Address} {arity : Nat}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {captured : Array IxIR1.RVal} {values : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {value : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel callerTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (functionResolved :
      IxIR1.resolveAtom source sourceFunction = .ok (.loc location))
    (argumentsResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (sourceRetain :
      IxIR1.dupVals sourceStore captured.toList = .ok sourceRetained)
    (sourceRelease : IxIR1.dropVal sourceContext applyFuel sourceRetained
      (.loc location) = .ok sourceReleased)
    (totalOver : arity < (captured.toList ++ values).length)
    (papArity : arity = sourceDefinition.arity)
    (sourceDeclaration :
      sourceContext.decls address = some (.fn sourceDefinition))
    (sourcePapSafe : sourceDefinition.papSafe = true)
    (targetDeclaration :
      context.declarations address = some (.fn targetDefinition))
    (calleeRun : IxIR1.runCode sourceContext calleeFuel sourceDefinition
      sourceReleased ((captured.toList ++ values).take arity).reverse
        sourceDefinition.body = .ok (outputStore, value))
    (calleeResultWorld : IxIR1.Sim.HasWorld outputStore
      sourceDefinition.result value)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (nextHandler : ∀ remaining : Array Lower.BindingCap,
      SuccessfulReturnHandler attached sourceContext context interpretation
        calleeTrace
        (IxIR1.Sim.rootsFor .shared
            ((captured.toList ++ values).drop arity) ++
          Lower.Sim.rootsForCapabilities remaining.toList source ++ frameRoots)
        (.applyMore
            ((captured ++ values.toArray).extract arity
              (captured ++ values.toArray).size)
            { frame with pc := frame.pc + 1 } :: stack)
        (outputStore, value) outcome post)
    (calleeWorker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation calleeFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  let sourceTotal := captured.toList ++ values
  let sourceSupplied := sourceTotal.take arity
  let sourceRemaining := sourceTotal.drop arity
  let targetTotal := captured ++ values.toArray
  let targetSupplied := targetTotal.extract 0 arity
  let targetRemaining := targetTotal.extract arity targetTotal.size
  let resume : Eval.Frame := { frame with pc := frame.pc + 1 }
  let calleeFrame : Eval.Frame :=
    { definition := targetDefinition, values := targetSupplied }
  obtain ⟨targetRetained, targetReleased, targetHeapFuel, targetRetain,
      _, targetRelease, releasedStores, _, _, _, calleeState, _⟩ :=
    attached.simulate_traced_apply_pap_over_enter_state
      (sourceFuel := applyFuel) (context := context)
      (interpretation := interpretation) callerMember calleeMember descendant
      calleeMatch state stores runtime.positiveSharedRC sourceDeclarations
      functionResolved argumentsResolved sourceGet shared node capturedUnder
      sourceRetain sourceRelease totalOver papArity sourceDeclaration
      sourcePapSafe targetDeclaration noCredits control
  have papAt : sourceStore.get? location =
      some ⟨.shared, box.rc, .papN address arity captured⟩ := by
    simpa only [← shared, ← node] using sourceGet
  have calleePapSafe : calleeTrace.generated.signature.papSafe = true := by
    calc
      calleeTrace.generated.signature.papSafe =
          calleeTrace.source.papSafe := calleeTrace.sourcePapSafe
      _ = sourceDefinition.papSafe := congrArg IxIR1.FnDef.papSafe
        calleeMatch.source
      _ = true := sourcePapSafe
  have suppliedArity : sourceSupplied.length =
      calleeTrace.generated.signature.params.size := by
    have sourceOver : arity < sourceTotal.length := by
      simpa [sourceTotal] using totalOver
    calc
      sourceSupplied.length = arity := by
        simp [sourceSupplied, Nat.min_eq_left (Nat.le_of_lt sourceOver)]
      _ = sourceDefinition.arity := papArity
      _ = calleeTrace.source.arity := by rw [calleeMatch.source]
      _ = calleeTrace.generated.signature.params.size :=
        calleeTrace.sourceArity.symm
  obtain ⟨_, _, remaining, _, _, _, _, _, readyOwnership,
      entryOwnership⟩ :=
    Lower.Sim.SourceOwnershipAt.applyPapEntry
      (checked := attached.target) (sourceContext := sourceContext)
      (sourceFuel := applyFuel) (supplied := sourceSupplied)
      (residual := sourceRemaining) callerMember calleeMember descendant
      ownership functionResolved argumentsResolved papAt sourceRetain
      sourceRelease (by
        exact (List.take_append_drop arity sourceTotal).symm)
      suppliedArity calleePapSafe
  let suspendedRoots : List IxIR1.Sim.Root :=
    Lower.Sim.rootsForCapabilities remaining.toList source ++ frameRoots
  have calleeOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions calleeTrace.root sourceReleased
        sourceSupplied.reverse
        (IxIR1.Sim.rootsFor .shared sourceRemaining ++ suspendedRoots) := by
    simpa [suspendedRoots] using entryOwnership
  have calleeRuntime : Lower.Sim.SourceRuntimeInvariant sourceReleased
      sourceSupplied.reverse :=
    Lower.Sim.SourceRuntimeInvariant.sharedEntry
      ((runtime.order.dupVals sourceRetain).dropVal sourceRelease)
      ((runtime.papsUnder.dupVals sourceRetain).dropVal sourceRelease)
      (by simpa [suspendedRoots, List.append_assoc] using readyOwnership)
  have retainedImage : attached.SourceStoreImage sourceRetained :=
    attached.dupVals_preservesSourceStoreImage image sourceRetain
  have calleeImage : attached.SourceStoreImage sourceReleased :=
    attached.dropVal_preservesSourceStoreImage sourceDeclarations retainedImage
      sourceRelease
  have calleeRun' : IxIR1.runCode sourceContext calleeFuel
      calleeTrace.source sourceReleased sourceSupplied.reverse
        calleeTrace.root.sourceCode = .ok (outputStore, value) := by
    rw [calleeTrace.rootSourceCode, calleeMatch.source]
    simpa [sourceTotal, sourceSupplied] using calleeRun
  have calleeResultWorld' : IxIR1.Sim.HasWorld outputStore
      calleeTrace.source.result value := by
    simpa [calleeMatch.source] using calleeResultWorld
  let calleeMachine : Eval.Machine :=
    { store := targetReleased
      heapFuel := 0
      control := .running calleeFrame
        (.applyMore targetRemaining resume :: stack) }
  have calleeStores : Lower.Sim.StoreRel sourceReleased
      calleeMachine.store := by
    simpa [calleeMachine] using releasedStores
  have calleeState' : attached.sidecars.TraceStateRel calleeTrace
      calleeTrace.root sourceReleased sourceSupplied.reverse calleeFrame := by
    simpa [sourceTotal, sourceSupplied, targetTotal, targetSupplied,
      calleeFrame] using calleeState
  have calleeControl : calleeMachine.control =
      .running calleeFrame (.applyMore targetRemaining resume :: stack) := rfl
  have calleeNoCredits : calleeFrame.credits = #[] := rfl
  have nextHandler' : SuccessfulReturnHandler attached sourceContext context
      interpretation calleeTrace
      (IxIR1.Sim.rootsFor .shared sourceRemaining ++ suspendedRoots)
      (.applyMore targetRemaining resume :: stack)
      (outputStore, value) outcome post := by
    intro returningTrace returnFuel returnSite returnBlock returnInput
      returnEntryValueCount returnAtom returnTarget returnGenerated returnStore
      returnSource returnFrame returnMachine returningMember returnDescendant
      returnState returnStores returnRuntime returnOwnership returnRun returnWorld
      returnControl returnNoCredits returnImage
    exact nextHandler remaining returningMember returnDescendant returnState
      returnStores returnRuntime
      (by simpa [sourceTotal, sourceRemaining, suspendedRoots,
          List.append_assoc] using returnOwnership)
      returnRun returnWorld
      (by simpa [targetTotal, targetRemaining, resume] using returnControl)
      returnNoCredits returnImage
  have tail := calleeWorker (machine := calleeMachine)
    (stack := .applyMore targetRemaining resume :: stack) calleeMember
      Lower.CodeTrace.Descendant.refl calleeState' calleeStores calleeRuntime
      calleeOwnership calleeRun' calleeResultWorld' calleeControl
      calleeNoCredits calleeImage nextHandler'
  refine BudgetedReachesPost.prependFramed
    (before := machine) (middle := calleeMachine) (prefixCount := 1)
    (localFuel := targetHeapFuel) ?_ tail
  intro suffixFuel
  let fundedMachine : Eval.Machine :=
    { machine with heapFuel := targetHeapFuel + suffixFuel }
  let fundedCallee : Eval.Machine :=
    { calleeMachine with heapFuel := suffixFuel }
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  have targetGet : fundedMachine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have fundedRelease := Lower.Sim.releaseSharedWork_add_suffix
    (suffix := suffixFuel) targetRelease
  have targetOver : arity < targetTotal.size := by
    simpa [sourceTotal, targetTotal] using totalOver
  have targetPapSafe : targetDefinition.signature.papSafe = true := by
    calc
      targetDefinition.signature.papSafe =
          calleeTrace.generated.signature.papSafe := by
            rw [calleeMatch.generated]
      _ = true := calleePapSafe
  have targetParamArity :
      targetDefinition.signature.params.size = arity := by
    calc
      targetDefinition.signature.params.size =
          calleeTrace.generated.signature.params.size := by
            rw [calleeMatch.generated]
      _ = calleeTrace.source.arity := calleeTrace.sourceArity
      _ = sourceDefinition.arity := congrArg IxIR1.FnDef.arity
        calleeMatch.source
      _ = arity := papArity.symm
  have targetSuppliedSize : targetSupplied.size = arity := by
    simp [targetSupplied, Array.size_extract]
    omega
  have targetSuppliedArity : targetSupplied.size =
      targetDefinition.signature.params.size := by
    rw [targetSuppliedSize, targetParamArity]
  have targetNonempty : targetDefinition.blocks.isEmpty = false := by
    simpa [calleeMatch.generated] using calleeTrace.generatedNonempty
  have fundedTransfer := Eval.ApplyTransfer.papFn
    (context := context) (interpretation := interpretation)
    (resume := resume) (stack := stack) targetGet shared node capturedUnder
      targetRetain fundedRelease (Nat.le_of_lt targetOver) targetDeclaration
      targetPapSafe targetSuppliedArity targetNonempty
  dsimp only at fundedTransfer
  have remainingNonempty : targetRemaining.isEmpty = false := by
    simp [targetRemaining, Array.isEmpty, Array.size_extract]
    omega
  rw [remainingNonempty] at fundedTransfer
  have fundedTransfer' : Eval.ApplyTransfer context interpretation
      fundedMachine.store fundedMachine.heapFuel (.loc location)
      values.toArray resume stack fundedCallee := by
    simpa [fundedMachine, fundedCallee, calleeMachine, calleeFrame,
      targetTotal, targetSupplied, targetRemaining] using fundedTransfer
  obtain ⟨fundedStep, _⟩ :=
    Lower.Sim.simulate_traced_apply_transfer_state
      (machine := fundedMachine) (target := fundedCallee) descendant
      state.target functionResolved argumentsResolved noCredits fundedControl
      fundedTransfer'
  simpa [fundedMachine, fundedCallee] using
    fundedStep.toSteps fundedControl

/-- Interpret an aligned successful `applyGo` plan as the universal
`applyMore` return handler required by the trace worker.  Recursion follows
the plan's residual over-application edge, while every invoked function body
uses the corresponding strictly smaller source-fuel worker. -/
theorem CompiledAttachment.applyMoreReturnHandler_of_plan
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    {applyFuel : Nat} {sourceStore outputStore : IxIR1.Store}
    {function outputValue : IxIR1.RVal} {values : List IxIR1.RVal}
    (plan : ApplyMorePlan attached sourceContext context applyFuel sourceStore
      function values outputStore outputValue)
    (workers : ∀ fuel, fuel < applyFuel →
      SuccessfulTraceSimulationAt attached sourceContext context
        interpretation fuel)
    {caller : Eval.Frame} {rest : List Eval.Continuation}
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (continuation : SuccessfulResumeContinuation context interpretation
      caller rest (outputStore, outputValue) outcome post)
    (functionTrace : Lower.FunctionTrace)
    (suspendedRoots : List IxIR1.Sim.Root) :
    SuccessfulReturnHandler attached sourceContext context interpretation
      functionTrace (IxIR1.Sim.rootsFor .shared values ++ suspendedRoots)
      (.applyMore values.toArray caller :: rest) (sourceStore, function)
      outcome post := by
  induction plan generalizing functionTrace suspendedRoots caller rest outcome
      post with
  | @erased fuel planStore planReleased planValues sourceRelease =>
      intro returningTrace returnFuel site blockId input entryValueCount
        sourceAtom targetAtom generated returnStore source returnFrame machine
        returningMember descendant state stores runtime ownership returnRun
        resultWorld control noCredits image
      obtain ⟨returnedValue, sourceResolved, outputEq⟩ :=
        IxIR1.runCode_ret_success returnRun
      have storeEq : returnStore = planStore := by
        simpa using (congrArg Prod.fst outputEq).symm
      have valueEq : returnedValue = IxIR1.RVal.erased :=
        (congrArg Prod.snd outputEq).symm
      subst returnStore
      subst returnedValue
      exact attached.simulate_traced_ret_apply_more_erased_cps
        (sourceContext := sourceContext) (applyFuel := fuel) descendant state
        stores runtime resultWorld returnRun control noCredits sourceRelease
        continuation
  | @papUnder fuel planStore retainedStore releasedStore location box address
      arity captured planValues sourceGet node sourceRetain sourceRelease
      totalUnder =>
      intro returningTrace returnFuel site blockId input entryValueCount
        sourceAtom targetAtom generated returnStore source returnFrame machine
        returningMember descendant state stores runtime ownership returnRun
        resultWorld control noCredits image
      obtain ⟨returnedValue, sourceResolved, outputEq⟩ :=
        IxIR1.runCode_ret_success returnRun
      have storeEq : returnStore = planStore := by
        simpa using (congrArg Prod.fst outputEq).symm
      have valueEq : returnedValue = IxIR1.RVal.loc location :=
        (congrArg Prod.snd outputEq).symm
      subst returnStore
      subst returnedValue
      obtain ⟨shared, capturedUnder⟩ := attached.livePapFacts returningMember
        descendant runtime ownership sourceGet node
      exact attached.simulate_traced_ret_apply_more_pap_under_cps
        (sourceContext := sourceContext) (applyFuel := fuel) descendant state
        stores runtime sourceResolved resultWorld returnRun control noCredits
        sourceGet shared node capturedUnder sourceRetain sourceRelease totalUnder
        continuation
  | @papSaturatedFn fuel calleeFuel planStore retainedStore releasedStore
      planOutputStore location box address arity captured planValues
      sourceDefinition targetDefinition calleeTrace planOutputValue calleeMember
      calleeMatch sourceGet node sourceRetain sourceRelease
      totalExact papArity sourceDeclaration sourcePapSafe targetDeclaration
      calleeRun calleeResultWorld calleeSmaller =>
      intro returningTrace returnFuel site blockId input entryValueCount
        sourceAtom targetAtom generated returnStore source returnFrame machine
        returningMember descendant state stores runtime ownership returnRun
        resultWorld control noCredits image
      obtain ⟨returnedValue, sourceResolved, outputEq⟩ :=
        IxIR1.runCode_ret_success returnRun
      have storeEq : returnStore = planStore := by
        simpa using (congrArg Prod.fst outputEq).symm
      have valueEq : returnedValue = IxIR1.RVal.loc location :=
        (congrArg Prod.snd outputEq).symm
      subst returnStore
      subst returnedValue
      obtain ⟨shared, capturedUnder⟩ := attached.livePapFacts returningMember
        descendant runtime ownership sourceGet node
      have nextHandler : SuccessfulReturnHandler attached sourceContext context
          interpretation calleeTrace suspendedRoots (.resume caller :: rest)
          (planOutputStore, planOutputValue) outcome post :=
        resumeReturnHandlerOfContinuation attached calleeTrace suspendedRoots
          caller rest (planOutputStore, planOutputValue) outcome post
          continuation
      exact attached.simulate_traced_ret_apply_more_pap_saturated_cps
        (sourceContext := sourceContext) (applyFuel := fuel)
        (calleeFuel := calleeFuel)
        returningMember calleeMember descendant calleeMatch state stores runtime
        ownership sourceDeclarations sourceResolved resultWorld returnRun control
        noCredits image
        sourceGet shared node capturedUnder sourceRetain sourceRelease totalExact
        papArity sourceDeclaration sourcePapSafe targetDeclaration calleeRun
        calleeResultWorld nextHandler (workers calleeFuel calleeSmaller)
  | @papOverFn fuel calleeFuel planStore retainedStore releasedStore calledStore
      planOutputStore location box address arity captured planValues
      sourceDefinition targetDefinition calleeTrace calledValue planOutputValue
      calleeMember calleeMatch sourceGet node sourceRetain sourceRelease
      totalOver papArity sourceDeclaration sourcePapSafe
      targetDeclaration calleeRun calleeResultWorld calleeSmaller residual ih =>
      intro returningTrace returnFuel site blockId input entryValueCount
        sourceAtom targetAtom generated returnStore source returnFrame machine
        returningMember descendant state stores runtime ownership returnRun
        resultWorld control noCredits image
      obtain ⟨returnedValue, sourceResolved, outputEq⟩ :=
        IxIR1.runCode_ret_success returnRun
      have storeEq : returnStore = planStore := by
        simpa using (congrArg Prod.fst outputEq).symm
      have valueEq : returnedValue = IxIR1.RVal.loc location :=
        (congrArg Prod.snd outputEq).symm
      subst returnStore
      subst returnedValue
      obtain ⟨shared, capturedUnder⟩ := attached.livePapFacts returningMember
        descendant runtime ownership sourceGet node
      have residualWorkers : ∀ recursiveFuel, recursiveFuel < fuel →
          SuccessfulTraceSimulationAt attached sourceContext context
            interpretation recursiveFuel := by
        intro recursiveFuel smaller
        exact workers recursiveFuel (Nat.lt_trans smaller (Nat.lt_succ_self fuel))
      have residualHandler : SuccessfulReturnHandler attached sourceContext
          context interpretation calleeTrace
          (IxIR1.Sim.rootsFor .shared
              ((captured.toList ++ planValues).drop arity) ++ suspendedRoots)
          (.applyMore
              ((captured ++ planValues.toArray).extract arity
                (captured ++ planValues.toArray).size)
              caller :: rest)
          (calledStore, calledValue) outcome post := by
        have handler : SuccessfulReturnHandler attached sourceContext context
            interpretation calleeTrace
            (IxIR1.Sim.rootsFor .shared
                ((captured.toList ++ planValues).drop arity) ++
              suspendedRoots)
            (.applyMore
                ((captured.toList ++ planValues).drop arity).toArray caller ::
              rest)
            (calledStore, calledValue) outcome post :=
          ih residualWorkers continuation calleeTrace suspendedRoots
        intro recursiveTrace recursiveReturnFuel recursiveSite recursiveBlock
          recursiveInput recursiveEntryValueCount recursiveAtom recursiveTarget
          recursiveGenerated recursiveStore recursiveSource recursiveFrame
          recursiveMachine recursiveMember recursiveDescendant recursiveState
          recursiveStores recursiveRuntime recursiveOwnership recursiveRun
          recursiveWorld recursiveControl recursiveNoCredits recursiveImage
        apply handler recursiveMember recursiveDescendant recursiveState
          recursiveStores recursiveRuntime recursiveOwnership recursiveRun
          recursiveWorld ?_ recursiveNoCredits recursiveImage
        have remainingArrayEq :
            ((captured ++ planValues.toArray).extract arity
              (captured ++ planValues.toArray).size) =
              ((captured.toList ++ planValues).drop arity).toArray := by
          rw [show captured ++ planValues.toArray =
              (captured.toList ++ planValues).toArray by
            apply Array.toList_inj.mp
            simp]
          exact List.toArray_drop.symm
        rw [← remainingArrayEq]
        exact recursiveControl
      exact attached.simulate_traced_ret_apply_more_pap_over_cps
        (sourceContext := sourceContext) (applyFuel := fuel)
        (calleeFuel := calleeFuel)
        returningMember calleeMember descendant calleeMatch state stores runtime
        ownership sourceDeclarations sourceResolved resultWorld returnRun control
        noCredits image
        sourceGet shared node capturedUnder sourceRetain sourceRelease totalOver
        papArity sourceDeclaration sourcePapSafe targetDeclaration calleeRun
        calleeResultWorld residualHandler (workers calleeFuel calleeSmaller)

/-- Direct worker-facing form of `applyMoreReturnHandler_of_plan`: successful
source evaluation selects its exhaustive plan internally, so callers need
only the two installed declaration environments and the usual smaller-fuel
workers. -/
theorem CompiledAttachment.applyMoreReturnHandler_of_applyGo
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (targetDeclarations : context.declarations =
      (Eval.Context.ofProgram attached.target.artifact.program
        attached.target.artifact.validationContext.schemas).declarations)
    {applyFuel : Nat} {sourceStore outputStore : IxIR1.Store}
    {function outputValue : IxIR1.RVal} {values : List IxIR1.RVal}
    (run : IxIR1.applyGo sourceContext applyFuel sourceStore function values =
      .ok (outputStore, outputValue))
    (workers : ∀ fuel, fuel < applyFuel →
      SuccessfulTraceSimulationAt attached sourceContext context
        interpretation fuel)
    {caller : Eval.Frame} {rest : List Eval.Continuation}
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (continuation : SuccessfulResumeContinuation context interpretation
      caller rest (outputStore, outputValue) outcome post)
    (functionTrace : Lower.FunctionTrace)
    (suspendedRoots : List IxIR1.Sim.Root) :
    SuccessfulReturnHandler attached sourceContext context interpretation
      functionTrace (IxIR1.Sim.rootsFor .shared values ++ suspendedRoots)
      (.applyMore values.toArray caller :: rest) (sourceStore, function)
      outcome post := by
  exact attached.applyMoreReturnHandler_of_plan
    sourceDeclarations
    (attached.applyMorePlan_of_applyGo sourceDeclarations targetDeclarations
      run)
    workers continuation functionTrace suspendedRoots

/-- Complete CPS composition for an addressed ordinary function call.  The
target enters the retained callee root in one step, the smaller-fuel callee
worker runs under an exact `.resume` handler, and that handler restores and
runs the caller's successful continuation. -/
theorem CompiledAttachment.simulate_traced_call_fn_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {callFuel calleeFuel callerFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    (callerMember : callerTrace ∈ attached.target.artifact.trace.functions)
    (calleeMember : calleeTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace} {sourceAddress targetAddress : Ixon.Address}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : callerTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration sourceAddress) sourceDefinition targetDefinition)
    {sourceStore outputStore finalStore : IxIR1.Store}
    {source : List IxIR1.RVal} {values : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {value finalValue : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel callerTrace
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : sourceDefinition.arity = values.length)
    (sourceOperation : IxIR1.runOp sourceContext (callFuel + 1)
      callerTrace.source sourceStore source
        (.call sourceAddress sourceArguments) = .ok (outputStore, value))
    (calleeRun : IxIR1.runCode sourceContext calleeFuel sourceDefinition
      sourceStore values.reverse sourceDefinition.body =
        .ok (outputStore, value))
    (calleeResultWorld : IxIR1.Sim.HasWorld outputStore
      sourceDefinition.result value)
    (callerRuntime : Lower.Sim.SourceRuntimeInvariant outputStore
      (value :: source))
    (callerRun : IxIR1.runCode sourceContext callerFuel callerTrace.source
      outputStore (value :: source) next.sourceCode =
        .ok (finalStore, finalValue))
    (callerResultWorld : IxIR1.Sim.HasWorld finalStore
      callerTrace.source.result finalValue)
    (targetDeclaration : context.declarations sourceAddress =
      some (.fn targetDefinition))
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation callerTrace frameRoots stack
        (finalStore, finalValue) outcome post)
    (calleeWorker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation calleeFuel)
    (callerWorker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation callerFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  let resume : Eval.Frame := { frame with pc := frame.pc + 1 }
  let calleeFrame : Eval.Frame :=
    { definition := targetDefinition, values := values.toArray }
  let calleeMachine : Eval.Machine :=
    { machine with
      control := .running calleeFrame (.resume resume :: stack) }
  obtain ⟨_, _, entryStores, calleeState⟩ :=
    attached.simulate_traced_call_fn_enter_state
      (sourceContext := sourceContext) (sourceFuel := callFuel)
      (context := context) (interpretation := interpretation)
      calleeMember descendant
      calleeMatch state stores sourceResolved argumentArity targetDeclaration
      noCredits control
  have signatureAt := attached.target.targetSignature calleeMember
    calleeMatch.owner
  obtain ⟨callPosition, remaining, callPositionMember,
      callPositionCoordinate, consumed, _, entryOwnership⟩ :=
    Lower.Sim.SourceOwnershipAt.callEntry (checked := attached.target)
      callerMember calleeMember descendant signatureAt ownership sourceResolved
  let suspendedRoots : List IxIR1.Sim.Root :=
    Lower.Sim.rootsForCapabilities remaining.toList source ++ frameRoots
  have calleeOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions calleeTrace.root sourceStore
        values.reverse suspendedRoots := by
    simpa [suspendedRoots] using entryOwnership
  have calleeRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore
      values.reverse := runtime.resolveAtomsReverse sourceResolved
  have calleeRun' : IxIR1.runCode sourceContext calleeFuel calleeTrace.source
      sourceStore values.reverse calleeTrace.root.sourceCode =
        .ok (outputStore, value) := by
    rw [calleeTrace.rootSourceCode, calleeMatch.source]
    exact calleeRun
  have calleeResultWorld' : IxIR1.Sim.HasWorld outputStore
      calleeTrace.source.result value := by
    simpa [calleeMatch.source] using calleeResultWorld
  have calleeControl : calleeMachine.control =
      .running calleeFrame (.resume resume :: stack) := rfl
  have calleeNoCredits : calleeFrame.credits = #[] := rfl
  have returnHandler : SuccessfulReturnHandler attached sourceContext context
      interpretation calleeTrace suspendedRoots (.resume resume :: stack)
      (outputStore, value) outcome post := by
    intro returningTrace returnFuel returnSite returnBlock returnInput
      returnEntryValueCount returnAtom returnTarget returnGenerated returnStore
      returnSource returnFrame returnMachine returningMember returnDescendant
      returnState returnStores returnRuntime returnOwnership returnRun returnWorld
      returnControl returnNoCredits returnImage
    obtain ⟨returnedValue, returnResolved, returnOutputEq⟩ :=
      IxIR1.runCode_ret_success returnRun
    have returnStoreEq : returnStore = outputStore :=
      (congrArg Prod.fst returnOutputEq).symm
    have returnedValueEq : returnedValue = value :=
      (congrArg Prod.snd returnOutputEq).symm
    subst returnStore
    subst returnedValue
    have terminalOwnership := Lower.Sim.SourceOwnershipAt.returnRoot
      (checked := attached.target) returningMember returnDescendant
        returnOwnership returnResolved
    have calleeResultWorld'' : IxIR1.Sim.HasWorld outputStore
        calleeTrace.generated.signature.result value := by
      simpa [calleeTrace.sourceOrder.result] using calleeResultWorld'
    have returnedOwnership : IxIR1.Sim.RootOwnership outputStore
        (⟨calleeTrace.generated.signature.result, value⟩ :: suspendedRoots) :=
      Lower.Sim.RootOwnership_reworldHead terminalOwnership calleeResultWorld''
    have callerOwnership := Lower.Sim.SourceOwnershipAt.callResult
      (checked := attached.target) callerMember signatureAt descendant
      callPositionMember callPositionCoordinate ownership sourceResolved
      consumed (by simpa [suspendedRoots] using returnedOwnership)
    have handler : SuccessfulReturnHandler attached sourceContext context
        interpretation returningTrace suspendedRoots
        (.resume { frame with pc := frame.pc + 1 } :: stack)
        (outputStore, value) outcome post :=
      resumeReturnHandlerWithOwnership attached
        (sourceContext := sourceContext) (callerFuel := callerFuel)
        (operationFuel := callFuel + 1) (context := context)
        (interpretation := interpretation) (calleeTrace := returningTrace)
        (outcome := outcome) (post := post) callerMember descendant state
        (binder := by rfl) (delta := by rfl) sourceDeclarations
        sourceOperation callerRuntime callerOwnership callerRun
        callerResultWorld noCredits finish callerWorker
    apply handler returningMember returnDescendant returnState returnStores
      returnRuntime returnOwnership returnRun returnWorld
    · simpa [resume] using returnControl
    · exact returnNoCredits
    · exact returnImage
  have tail := calleeWorker (machine := calleeMachine)
    (stack := .resume resume :: stack) calleeMember
      Lower.CodeTrace.Descendant.refl
      calleeState entryStores calleeRuntime calleeOwnership calleeRun'
      calleeResultWorld' calleeControl calleeNoCredits image returnHandler
  obtain ⟨tailHeapFuel, tail⟩ := tail
  let fundedMachine : Eval.Machine := { machine with heapFuel := tailHeapFuel }
  have fundedStores : Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  obtain ⟨_, fundedStep, _, _⟩ :=
    attached.simulate_traced_call_fn_enter_state
      (sourceContext := sourceContext) (sourceFuel := callFuel)
      (context := context) (interpretation := interpretation)
      (machine := fundedMachine) calleeMember descendant calleeMatch state
      fundedStores sourceResolved argumentArity targetDeclaration noCredits
      fundedControl
  refine ⟨tailHeapFuel, ?_⟩
  simpa [fundedMachine, calleeMachine, calleeFrame, resume] using
    tail.prepend (fundedStep.toSteps fundedControl)

/-- Complete CPS composition for a recursive self-call.  The target enters
the same retained function root, the smaller-fuel worker executes that root
under an exact `.resume` handler, and the handler restores the caller's
successful continuation. -/
theorem CompiledAttachment.simulate_traced_call_self_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {callFuel calleeFuel callerFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next))
    {sourceStore outputStore finalStore : IxIR1.Store}
    {source : List IxIR1.RVal} {values : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {value finalValue : IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next)
      sourceStore source frameRoots)
    (sourceDeclarations : sourceContext.decls =
      IxIR1.HPT.programDeclEnv attached.source.lowering.result.artifacts)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : functionTrace.source.arity = values.length)
    (sourceOperation : IxIR1.runOp sourceContext (callFuel + 1)
      functionTrace.source sourceStore source (.callSelf sourceArguments) =
        .ok (outputStore, value))
    (calleeRun : IxIR1.runCode sourceContext calleeFuel
      functionTrace.source sourceStore values.reverse
        functionTrace.source.body = .ok (outputStore, value))
    (calleeResultWorld : IxIR1.Sim.HasWorld outputStore
      functionTrace.source.result value)
    (callerRuntime : Lower.Sim.SourceRuntimeInvariant outputStore
      (value :: source))
    (callerRun : IxIR1.runCode sourceContext callerFuel functionTrace.source
      outputStore (value :: source) next.sourceCode =
        .ok (finalStore, finalValue))
    (callerResultWorld : IxIR1.Sim.HasWorld finalStore
      functionTrace.source.result finalValue)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack
        (finalStore, finalValue) outcome post)
    (calleeWorker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation calleeFuel)
    (callerWorker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation callerFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  let resume : Eval.Frame := { frame with pc := frame.pc + 1 }
  let calleeFrame : Eval.Frame :=
    { definition := frame.definition, values := values.toArray }
  let calleeMachine : Eval.Machine :=
    { machine with
      control := .running calleeFrame (.resume resume :: stack) }
  obtain ⟨_, _, entryStores, calleeState⟩ :=
    attached.simulate_traced_call_self_enter_state
      (sourceContext := sourceContext) (sourceFuel := callFuel)
      (context := context) (interpretation := interpretation)
      functionMember descendant state stores sourceResolved argumentArity
      noCredits control
  obtain ⟨callPosition, remaining, callPositionMember,
      callPositionCoordinate, consumed, _, entryOwnership⟩ :=
    Lower.Sim.SourceOwnershipAt.callSelfEntry (checked := attached.target)
      functionMember descendant ownership sourceResolved
  let suspendedRoots : List IxIR1.Sim.Root :=
    Lower.Sim.rootsForCapabilities remaining.toList source ++ frameRoots
  have calleeOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions functionTrace.root sourceStore
        values.reverse suspendedRoots := by
    simpa [suspendedRoots] using entryOwnership
  have calleeRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore
      values.reverse := runtime.resolveAtomsReverse sourceResolved
  have calleeRun' : IxIR1.runCode sourceContext calleeFuel
      functionTrace.source sourceStore values.reverse
        functionTrace.root.sourceCode = .ok (outputStore, value) := by
    rw [functionTrace.rootSourceCode]
    exact calleeRun
  have calleeControl : calleeMachine.control =
      .running calleeFrame (.resume resume :: stack) := rfl
  have calleeNoCredits : calleeFrame.credits = #[] := rfl
  have returnHandler : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace suspendedRoots (.resume resume :: stack)
      (outputStore, value) outcome post := by
    intro returningTrace returnFuel returnSite returnBlock returnInput
      returnEntryValueCount returnAtom returnTarget returnGenerated returnStore
      returnSource returnFrame returnMachine returningMember returnDescendant
      returnState returnStores returnRuntime returnOwnership returnRun returnWorld
      returnControl returnNoCredits returnImage
    obtain ⟨returnedValue, returnResolved, returnOutputEq⟩ :=
      IxIR1.runCode_ret_success returnRun
    have returnStoreEq : returnStore = outputStore :=
      (congrArg Prod.fst returnOutputEq).symm
    have returnedValueEq : returnedValue = value :=
      (congrArg Prod.snd returnOutputEq).symm
    subst returnStore
    subst returnedValue
    have terminalOwnership := Lower.Sim.SourceOwnershipAt.returnRoot
      (checked := attached.target) returningMember returnDescendant
        returnOwnership returnResolved
    have calleeResultWorld' : IxIR1.Sim.HasWorld outputStore
        functionTrace.generated.signature.result value := by
      simpa [functionTrace.sourceOrder.result] using calleeResultWorld
    have returnedOwnership : IxIR1.Sim.RootOwnership outputStore
        (⟨functionTrace.generated.signature.result, value⟩ :: suspendedRoots) :=
      Lower.Sim.RootOwnership_reworldHead terminalOwnership calleeResultWorld'
    have callerOwnership := Lower.Sim.SourceOwnershipAt.callSelfResult
      (checked := attached.target) functionMember descendant
      callPositionMember callPositionCoordinate ownership sourceResolved
      consumed (by simpa [suspendedRoots] using returnedOwnership)
    have handler : SuccessfulReturnHandler attached sourceContext context
        interpretation returningTrace suspendedRoots
        (.resume { frame with pc := frame.pc + 1 } :: stack)
        (outputStore, value) outcome post :=
      resumeReturnHandlerWithOwnership attached
        (sourceContext := sourceContext) (callerFuel := callerFuel)
        (operationFuel := callFuel + 1) (context := context)
        (interpretation := interpretation) (calleeTrace := returningTrace)
        (outcome := outcome) (post := post) functionMember descendant state
        (binder := by rfl) (delta := by rfl) sourceDeclarations
        sourceOperation callerRuntime callerOwnership callerRun
        callerResultWorld noCredits finish callerWorker
    apply handler returningMember returnDescendant returnState returnStores
      returnRuntime returnOwnership returnRun returnWorld
    · simpa [resume] using returnControl
    · exact returnNoCredits
    · exact returnImage
  have tail := calleeWorker (machine := calleeMachine)
    (stack := .resume resume :: stack) functionMember
      Lower.CodeTrace.Descendant.refl calleeState entryStores calleeRuntime
      calleeOwnership calleeRun' calleeResultWorld calleeControl
      calleeNoCredits image returnHandler
  obtain ⟨tailHeapFuel, tail⟩ := tail
  let fundedMachine : Eval.Machine := { machine with heapFuel := tailHeapFuel }
  have fundedStores : Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  obtain ⟨_, fundedStep, _, _⟩ :=
    attached.simulate_traced_call_self_enter_state
      (sourceContext := sourceContext) (sourceFuel := callFuel)
      (context := context) (interpretation := interpretation)
      (machine := fundedMachine) functionMember descendant state fundedStores
      sourceResolved argumentArity noCredits fundedControl
  refine ⟨tailHeapFuel, ?_⟩
  simpa [fundedMachine, calleeMachine, calleeFrame, resume] using
    tail.prepend (fundedStep.toSteps fundedControl)

/-- Complete CPS composition for an addressed tail call.  Because the target
keeps the continuation stack unchanged, the stack-generic return handler is
passed directly to the retained callee worker. -/
theorem CompiledAttachment.simulate_traced_tail_call_fn_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {callFuel calleeFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation}
    {callerTrace calleeTrace : Lower.FunctionTrace}
    (callerMember : callerTrace ∈ attached.target.artifact.trace.functions)
    (calleeMember : calleeTrace ∈ attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {address : Ixon.Address} {sourceArguments : Array IxIR1.Atom}
    {generated : Block}
    (descendant : callerTrace.root.Descendant
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated))
    {sourceDefinition : IxIR1.FnDef} {targetDefinition : Function}
    (calleeMatch : Lower.FunctionTraceMatch calleeTrace
      (.declaration address) sourceDefinition targetDefinition)
    {sourceStore outputStore : IxIR1.Store}
    {source values : List IxIR1.RVal} {value : IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (state : attached.sidecars.TraceStateRel callerTrace
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated) sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated) sourceStore source frameRoots)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : sourceDefinition.arity = values.length)
    (sourceRun : IxIR1.runCode sourceContext (callFuel + 2)
      callerTrace.source sourceStore source
        (.letOp (.call address sourceArguments) (.ret (.var 0))) =
          .ok (outputStore, value))
    (calleeRun : IxIR1.runCode sourceContext calleeFuel sourceDefinition
      sourceStore values.reverse sourceDefinition.body =
        .ok (outputStore, value))
    (calleeResultWorld : IxIR1.Sim.HasWorld outputStore
      sourceDefinition.result value)
    (targetDeclaration : context.declarations address =
      some (.fn targetDefinition))
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation callerTrace frameRoots stack
        (outputStore, value) outcome post)
    (calleeWorker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation calleeFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  let calleeFrame : Eval.Frame :=
    { definition := targetDefinition, values := values.toArray }
  let calleeMachine : Eval.Machine :=
    { machine with control := .running calleeFrame stack }
  obtain ⟨sourceEquation, targetStep, entryStores, calleeState⟩ :=
    attached.simulate_traced_tail_call_fn_enter_state
      (sourceContext := sourceContext) (sourceFuel := callFuel)
      (context := context) (interpretation := interpretation) calleeMember
      descendant calleeMatch state stores sourceResolved argumentArity
      targetDeclaration noCredits control
  have signatureAt := attached.target.targetSignature calleeMember
    calleeMatch.owner
  have calleeOwnership := Lower.Sim.SourceOwnershipAt.tailCallEntry
    (checked := attached.target) callerMember calleeMember descendant
      signatureAt ownership sourceResolved
  have invokeRun : IxIR1.invoke sourceContext callFuel address values
      sourceStore = .ok (outputStore, value) := by
    rw [← sourceEquation]
    exact sourceRun
  have calleeRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore
      values.reverse := runtime.resolveAtomsReverse sourceResolved
  have calleeRun' : IxIR1.runCode sourceContext calleeFuel calleeTrace.source
      sourceStore values.reverse calleeTrace.root.sourceCode =
        .ok (outputStore, value) := by
    rw [calleeTrace.rootSourceCode, calleeMatch.source]
    exact calleeRun
  have calleeResultWorld' : IxIR1.Sim.HasWorld outputStore
      calleeTrace.source.result value := by
    simpa [calleeMatch.source] using calleeResultWorld
  have calleeControl : calleeMachine.control =
      .running calleeFrame stack := rfl
  have calleeNoCredits : calleeFrame.credits = #[] := rfl
  have tail := calleeWorker (machine := calleeMachine) (stack := stack)
    calleeMember Lower.CodeTrace.Descendant.refl calleeState entryStores
      calleeRuntime calleeOwnership calleeRun' calleeResultWorld' calleeControl
      calleeNoCredits image finish
  obtain ⟨tailHeapFuel, tail⟩ := tail
  let fundedMachine : Eval.Machine := { machine with heapFuel := tailHeapFuel }
  have fundedStores : Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  obtain ⟨_, fundedStep, _, _⟩ :=
    attached.simulate_traced_tail_call_fn_enter_state
      (sourceContext := sourceContext) (sourceFuel := callFuel)
      (context := context) (interpretation := interpretation)
      (machine := fundedMachine) calleeMember descendant calleeMatch state
      fundedStores sourceResolved argumentArity targetDeclaration noCredits
      fundedControl
  refine ⟨tailHeapFuel, ?_⟩
  simpa [fundedMachine, calleeMachine, calleeFrame] using
    tail.prepend (fundedStep.toSteps fundedControl)

/-- Complete CPS composition for a recursive self tail call.  The same trace
root is re-entered with the existing continuation stack and return handler. -/
theorem CompiledAttachment.simulate_traced_tail_call_self_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {callFuel calleeFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceArguments : Array IxIR1.Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated))
    {sourceStore outputStore : IxIR1.Store}
    {source values : List IxIR1.RVal} {value : IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated) sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated) sourceStore source frameRoots)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (argumentArity : functionTrace.source.arity = values.length)
    (sourceRun : IxIR1.runCode sourceContext (callFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.callSelf sourceArguments) (.ret (.var 0))) =
          .ok (outputStore, value))
    (calleeRun : IxIR1.runCode sourceContext calleeFuel
      functionTrace.source sourceStore values.reverse
        functionTrace.source.body = .ok (outputStore, value))
    (calleeResultWorld : IxIR1.Sim.HasWorld outputStore
      functionTrace.source.result value)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {outcome : IxIR1.Store × IxIR1.RVal} {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack
        (outputStore, value) outcome post)
    (calleeWorker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation calleeFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  let calleeFrame : Eval.Frame :=
    { definition := frame.definition, values := values.toArray }
  let calleeMachine : Eval.Machine :=
    { machine with control := .running calleeFrame stack }
  obtain ⟨sourceEquation, targetStep, entryStores, calleeState⟩ :=
    attached.simulate_traced_tail_call_self_enter_state
      (sourceContext := sourceContext) (sourceFuel := callFuel)
      (context := context) (interpretation := interpretation) functionMember
      descendant state stores sourceResolved argumentArity noCredits control
  have calleeOwnership := Lower.Sim.SourceOwnershipAt.tailCallSelfEntry
    (checked := attached.target) functionMember descendant ownership
      sourceResolved
  have sourceEquationRun : (do
      let out ← IxIR1.runCode sourceContext callFuel functionTrace.source
        sourceStore values.reverse functionTrace.source.body
      IxIR1.checkResultWorld functionTrace.source.result out) =
        .ok (outputStore, value) := by
    rw [← sourceEquation]
    exact sourceRun
  have calleeRuntime : Lower.Sim.SourceRuntimeInvariant sourceStore
      values.reverse := runtime.resolveAtomsReverse sourceResolved
  have calleeRun' : IxIR1.runCode sourceContext calleeFuel
      functionTrace.source sourceStore values.reverse
        functionTrace.root.sourceCode = .ok (outputStore, value) := by
    rw [functionTrace.rootSourceCode]
    exact calleeRun
  have calleeControl : calleeMachine.control =
      .running calleeFrame stack := rfl
  have calleeNoCredits : calleeFrame.credits = #[] := rfl
  have tail := calleeWorker (machine := calleeMachine) (stack := stack)
    functionMember Lower.CodeTrace.Descendant.refl calleeState entryStores
      calleeRuntime calleeOwnership calleeRun' calleeResultWorld calleeControl
      calleeNoCredits image finish
  obtain ⟨tailHeapFuel, tail⟩ := tail
  let fundedMachine : Eval.Machine := { machine with heapFuel := tailHeapFuel }
  have fundedStores : Lower.Sim.StoreRel sourceStore fundedMachine.store := by
    simpa [fundedMachine] using stores
  have fundedControl : fundedMachine.control = .running frame stack := by
    simpa [fundedMachine] using control
  obtain ⟨_, fundedStep, _, _⟩ :=
    attached.simulate_traced_tail_call_self_enter_state
      (sourceContext := sourceContext) (sourceFuel := callFuel)
      (context := context) (interpretation := interpretation)
      (machine := fundedMachine) functionMember descendant state fundedStores
      sourceResolved argumentArity noCredits fundedControl
  refine ⟨tailHeapFuel, ?_⟩
  simpa [fundedMachine, calleeMachine, calleeFrame] using
    tail.prepend (fundedStep.toSteps fundedControl)

/-- Worker-facing addressed tail-call rule.  Successful source evaluation is
inverted here to recover the retained callee, its smaller body fuel, and its
checked result world; the exhaustive induction only supplies workers below
the current outer fuel. -/
theorem CompiledAttachment.simulate_traced_tail_call_cps_of_run
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {callFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    (contracts : SuccessfulSimulationContracts attached sourceContext context)
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {address : Ixon.Address} {sourceArguments : Array IxIR1.Atom}
    {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated) sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.tailCall site blockId input entryValueCount address sourceArguments
        generated) sourceStore source frameRoots)
    (sourceRun : IxIR1.runCode sourceContext (callFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.call address sourceArguments) (.ret (.var 0))) =
          .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (workers : ∀ fuel, fuel < callFuel + 2 →
      SuccessfulTraceSimulationAt attached sourceContext context
        interpretation fuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  obtain ⟨values, sourceResolved, invokeRun⟩ :=
    IxIR1.runOp_call_success operationRun
  obtain ⟨calleeFuel, callFuelEq, invoked⟩ :=
    IxIR1.invoke_success invokeRun
  obtain ⟨returnedValue, returnedResolved, sourceOutputEq⟩ :=
    IxIR1.runCode_ret_success continuationRun
  have returnedValueEq : returnedValue = operationValue := by
    simpa [IxIR1.resolveAtom] using returnedResolved.symm
  subst returnedValue
  subst sourceOutput
  cases invoked with
  | @fn sourceDefinition bodyOutput sourceDeclaration argumentArity calleeRun
      resultRun =>
      obtain ⟨bodyOutputEq, calleeResultWorld⟩ :=
        IxIR1.Sim.checkResultWorld_ok resultRun
      cases bodyOutputEq
      obtain ⟨targetDefinition, calleeTrace, calleeMember, calleeMatch,
          targetDeclaration⟩ :=
        attached.functionTrace_of_source_declaration
          contracts.sourceDeclarations contracts.targetDeclarations
            sourceDeclaration
      exact attached.simulate_traced_tail_call_fn_cps functionMember
        calleeMember descendant calleeMatch state stores runtime ownership
          sourceResolved argumentArity.symm sourceRun calleeRun
          calleeResultWorld targetDeclaration control noCredits image finish
          (workers calleeFuel (by omega))
  | @extern arity value sourceDeclaration _ _ _ =>
      exact False.elim (attached.sourceDeclaration_not_extern
        contracts.sourceDeclarations sourceDeclaration)

/-- Worker-facing self-tail-call rule, with evaluator inversion and result
checking discharged before entering the existing CPS adapter. -/
theorem CompiledAttachment.simulate_traced_tail_call_self_cps_of_run
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {callFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceArguments : Array IxIR1.Atom} {generated : Block}
    (descendant : functionTrace.root.Descendant
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated) sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.tailCallSelf site blockId input entryValueCount sourceArguments
        generated) sourceStore source frameRoots)
    (sourceRun : IxIR1.runCode sourceContext (callFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.callSelf sourceArguments) (.ret (.var 0))) =
          .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (workers : ∀ fuel, fuel < callFuel + 2 →
      SuccessfulTraceSimulationAt attached sourceContext context
        interpretation fuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  obtain ⟨values, bodyOutput, sourceResolved, argumentArity, calleeRun,
      resultRun⟩ := IxIR1.runOp_callSelf_success operationRun
  obtain ⟨returnedValue, returnedResolved, sourceOutputEq⟩ :=
    IxIR1.runCode_ret_success continuationRun
  have returnedValueEq : returnedValue = operationValue := by
    simpa [IxIR1.resolveAtom] using returnedResolved.symm
  subst returnedValue
  subst sourceOutput
  obtain ⟨bodyOutputEq, calleeResultWorld⟩ :=
    IxIR1.Sim.checkResultWorld_ok resultRun
  cases bodyOutputEq
  exact attached.simulate_traced_tail_call_self_cps functionMember descendant
    state stores runtime ownership sourceResolved argumentArity.symm sourceRun
      calleeRun calleeResultWorld control noCredits image finish
      (workers callFuel (by omega))

/-- Worker-facing addressed call rule for an ordinary `letOp`.  Source
evaluation determines the retained callee and both recursive fuels; the
shared no-reuse contract transports the caller runtime across invocation. -/
theorem CompiledAttachment.simulate_traced_call_cps_of_run
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {callFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    (contracts : SuccessfulSimulationContracts attached sourceContext context)
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace} {sourceAddress targetAddress : Ixon.Address}
    {sourceArguments : Array IxIR1.Atom} {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.call sourceAddress sourceArguments) index
        (.call targetAddress targetArguments) next)
      sourceStore source frameRoots)
    (sourceRun : IxIR1.runCode sourceContext (callFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.call sourceAddress sourceArguments) next.sourceCode) =
          .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (workers : ∀ fuel, fuel < callFuel + 2 →
      SuccessfulTraceSimulationAt attached sourceContext context
        interpretation fuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  obtain ⟨values, sourceResolved, invokeRun⟩ :=
    IxIR1.runOp_call_success operationRun
  obtain ⟨calleeFuel, callFuelEq, invoked⟩ :=
    IxIR1.invoke_success invokeRun
  cases invoked with
  | @fn sourceDefinition bodyOutput sourceDeclaration argumentArity calleeRun
      resultRun =>
      obtain ⟨bodyOutputEq, calleeResultWorld⟩ :=
        IxIR1.Sim.checkResultWorld_ok resultRun
      cases bodyOutputEq
      obtain ⟨targetDefinition, calleeTrace, calleeMember, calleeMatch,
          targetDeclaration⟩ :=
        attached.functionTrace_of_source_declaration
          contracts.sourceDeclarations contracts.targetDeclarations
            sourceDeclaration
      have callerRuntime : Lower.Sim.SourceRuntimeInvariant middleStore
          (operationValue :: source) :=
        runtime.runOp
          (IxIR1.NoReuse.invoke_reuses_eq
            (attached.sourceContextNoReuse contracts.sourceDeclarations)
            invokeRun)
          operationRun
      exact attached.simulate_traced_call_fn_cps functionMember calleeMember
        descendant calleeMatch state stores runtime ownership
          contracts.sourceDeclarations sourceResolved argumentArity.symm
          operationRun calleeRun calleeResultWorld callerRuntime
          continuationRun resultWorld targetDeclaration control noCredits
          image finish (workers calleeFuel (by omega))
          (workers (callFuel + 1) (by omega))
  | @extern arity value sourceDeclaration _ _ _ =>
      exact False.elim (attached.sourceDeclaration_not_extern
        contracts.sourceDeclarations sourceDeclaration)

/-- Worker-facing recursive self-call rule for an ordinary `letOp`.  The
function-level no-reuse certificate supplies the caller runtime invariant
after the checked callee result is returned. -/
theorem CompiledAttachment.simulate_traced_call_self_cps_of_run
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {callFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    (contracts : SuccessfulSimulationContracts attached sourceContext context)
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace}
    {sourceArguments : Array IxIR1.Atom} {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.callSelf sourceArguments) index (.callSelf targetArguments) next)
      sourceStore source frameRoots)
    (sourceRun : IxIR1.runCode sourceContext (callFuel + 2)
      functionTrace.source sourceStore source
        (.letOp (.callSelf sourceArguments) next.sourceCode) = .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (workers : ∀ fuel, fuel < callFuel + 2 →
      SuccessfulTraceSimulationAt attached sourceContext context
        interpretation fuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  obtain ⟨values, bodyOutput, sourceResolved, argumentArity, calleeRun,
      resultRun⟩ := IxIR1.runOp_callSelf_success operationRun
  obtain ⟨bodyOutputEq, calleeResultWorld⟩ :=
    IxIR1.Sim.checkResultWorld_ok resultRun
  cases bodyOutputEq
  have callerRuntime : Lower.Sim.SourceRuntimeInvariant middleStore
      (operationValue :: source) :=
    runtime.runOp
      (IxIR1.NoReuse.runOp_reuses_eq
        (attached.sourceContextNoReuse contracts.sourceDeclarations)
        (attached.functionTraceNoReuse functionMember) (by trivial)
        operationRun)
      operationRun
  exact attached.simulate_traced_call_self_cps functionMember descendant state
    stores runtime ownership contracts.sourceDeclarations sourceResolved
      argumentArity.symm operationRun calleeRun calleeResultWorld callerRuntime
      continuationRun resultWorld control noCredits image finish
      (workers callFuel (by omega)) (workers (callFuel + 1) (by omega))

/-- Worker-facing dynamic-application rule.  The successful evaluator run is
decomposed into the erased, under-saturated, exactly saturated, or
over-saturated PAP plan; each plan constructor feeds the corresponding CPS
adapter, including the recursive `applyMore` return handler. -/
theorem CompiledAttachment.simulate_traced_apply_cps_of_run
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {applyFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    (contracts : SuccessfulSimulationContracts attached sourceContext context)
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {next : Lower.CodeTrace} {sourceFunction : IxIR1.Atom}
    {targetFunction : Atom} {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount
        (.apply sourceFunction sourceArguments) index
        (.apply targetFunction targetArguments) next)
      sourceStore source frameRoots)
    (sourceRun : IxIR1.runCode sourceContext (applyFuel + 3)
      functionTrace.source sourceStore source
        (.letOp (.apply sourceFunction sourceArguments) next.sourceCode) =
          .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (workers : ∀ fuel, fuel < applyFuel + 3 →
      SuccessfulTraceSimulationAt attached sourceContext context
        interpretation fuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
    IxIR1.runCode_letOp_success sourceRun
  have middleImage : attached.SourceStoreImage middleStore :=
    attached.runOp_preservesSourceStoreImage contracts.sourceDeclarations
      functionMember descendant state image operationRun
  obtain ⟨functionValue, values, functionResolved, argumentsResolved,
      applyRun⟩ := IxIR1.runOp_apply_success operationRun
  have plan := attached.applyMorePlan_of_applyGo
    contracts.sourceDeclarations contracts.targetDeclarations applyRun
  have callerRuntime : Lower.Sim.SourceRuntimeInvariant middleStore
      (operationValue :: source) :=
    runtime.runOp
      (IxIR1.NoReuse.applyGo_reuses_eq
        (attached.sourceContextNoReuse contracts.sourceDeclarations)
        applyRun)
      operationRun
  have callerOwnership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions next middleStore
        (operationValue :: source) frameRoots :=
    Lower.Sim.SourceOwnershipAt.applyFrom (checked := attached.target)
      functionMember descendant ownership
        (attached.applyOwnershipPreservesFrom_sourceStoreImage_of_declarations
          contracts.sourceDeclarations image) operationRun
  have nextDescendant : functionTrace.root.Descendant next := by
    exact .step descendant (by simp [Lower.CodeTrace.children])
  cases plan with
  | @erased fuel planStore planReleased planValues sourceRelease =>
      exact attached.simulate_traced_apply_erased_cps functionMember descendant
        state stores runtime ownership contracts.sourceDeclarations
          functionResolved argumentsResolved sourceRelease
          sourceRun resultWorld control noCredits image finish
          (workers (applyFuel + 2) (by omega))
  | @papUnder fuel planStore retainedStore releasedStore location box address
      arity captured planValues sourceGet node sourceRetain sourceRelease
      totalUnder =>
      obtain ⟨shared, capturedUnder⟩ := attached.livePapFacts functionMember
        descendant runtime ownership sourceGet node
      exact attached.simulate_traced_apply_pap_under_cps functionMember
        descendant state stores runtime ownership contracts.sourceDeclarations
          functionResolved argumentsResolved sourceGet shared node capturedUnder
          sourceRetain sourceRelease totalUnder sourceRun resultWorld control
          noCredits image finish
          (workers (applyFuel + 2) (by omega))
  | @papSaturatedFn fuel calleeFuel planStore retainedStore releasedStore
      planOutputStore location box address arity captured planValues
      sourceDefinition targetDefinition calleeTrace planOutputValue calleeMember
      calleeMatch sourceGet node sourceRetain sourceRelease totalExact papArity
      sourceDeclaration sourcePapSafe targetDeclaration calleeRun
      calleeResultWorld calleeSmaller =>
      obtain ⟨shared, capturedUnder⟩ := attached.livePapFacts functionMember
        descendant runtime ownership sourceGet node
      exact attached.simulate_traced_apply_pap_saturated_cps functionMember
        calleeMember descendant calleeMatch state stores runtime ownership
          contracts.sourceDeclarations functionResolved argumentsResolved
          sourceGet shared node capturedUnder sourceRetain sourceRelease
          totalExact papArity sourceDeclaration sourcePapSafe targetDeclaration
          operationRun calleeRun calleeResultWorld callerRuntime continuationRun
          resultWorld control noCredits image finish
          (workers calleeFuel (by omega))
          (workers (applyFuel + 2) (by omega))
  | @papOverFn fuel calleeFuel planStore retainedStore releasedStore calledStore
      planOutputStore location box address arity captured planValues
      sourceDefinition targetDefinition calleeTrace calledValue planOutputValue
      calleeMember calleeMatch sourceGet node sourceRetain sourceRelease
      totalOver papArity sourceDeclaration sourcePapSafe targetDeclaration
      calleeRun calleeResultWorld calleeSmaller residual =>
      obtain ⟨shared, capturedUnder⟩ := attached.livePapFacts functionMember
        descendant runtime ownership sourceGet node
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, callerTargets⟩ :=
        attached.simulate_traced_apply_pap_over_enter_state
          (context := context) (interpretation := interpretation)
          functionMember calleeMember descendant calleeMatch state stores
          runtime.positiveSharedRC contracts.sourceDeclarations
          functionResolved argumentsResolved sourceGet shared node
          capturedUnder sourceRetain sourceRelease totalOver papArity
          sourceDeclaration sourcePapSafe targetDeclaration noCredits control
      let resume : Eval.Frame := { frame with pc := frame.pc + 1 }
      let nextFrame : Eval.Frame :=
        { frame with
          pc := frame.pc + 1
          values := frame.values.push operationValue }
      have nextState : attached.sidecars.TraceStateRel functionTrace next
          middleStore (operationValue :: source) nextFrame := by
        simpa [nextFrame] using
          (callerTargets middleStore operationValue operationRun)
      have nextNoCredits : nextFrame.credits = #[] := by
        simpa [nextFrame] using noCredits
      have continuation : SuccessfulResumeContinuation context interpretation
        resume stack (middleStore, operationValue) outcome post :=
        resumeContinuationOfWorker attached functionMember nextDescendant
          (by rfl) nextState callerRuntime middleImage callerOwnership continuationRun
          resultWorld nextNoCredits finish
          (workers (applyFuel + 2) (by omega))
      have nextHandler : ∀ remaining : Array Lower.BindingCap,
          SuccessfulReturnHandler attached sourceContext context interpretation
            calleeTrace
            (IxIR1.Sim.rootsFor .shared
                ((captured.toList ++ values).drop arity) ++
              Lower.Sim.rootsForCapabilities remaining.toList source ++
                frameRoots)
            (.applyMore
                ((captured ++ values.toArray).extract arity
                  (captured ++ values.toArray).size)
                { frame with pc := frame.pc + 1 } :: stack)
            (calledStore, calledValue) outcome post := by
        intro remaining
        have handler : SuccessfulReturnHandler attached sourceContext context
            interpretation calleeTrace
            (IxIR1.Sim.rootsFor .shared
                ((captured.toList ++ values).drop arity) ++
              (Lower.Sim.rootsForCapabilities remaining.toList source ++
                frameRoots))
            (.applyMore ((captured.toList ++ values).drop arity).toArray
              resume :: stack)
          (calledStore, calledValue) outcome post :=
          attached.applyMoreReturnHandler_of_plan contracts.sourceDeclarations
            residual
            (fun recursiveFuel smaller =>
              workers recursiveFuel (by omega))
            continuation calleeTrace
            (Lower.Sim.rootsForCapabilities remaining.toList source ++
              frameRoots)
        intro returningTrace returnFuel returnSite returnBlock returnInput
          returnEntryValueCount returnAtom returnTarget returnGenerated
          returnStore returnSource returnFrame returnMachine returningMember
          returnDescendant returnState returnStores returnRuntime
          returnOwnership returnRun returnWorld returnControl returnNoCredits
          returnImage
        apply handler returningMember returnDescendant returnState returnStores
          returnRuntime
        · simpa [List.append_assoc] using returnOwnership
        · exact returnRun
        · exact returnWorld
        · have remainingArrayEq :
              ((captured ++ values.toArray).extract arity
                (captured ++ values.toArray).size) =
                ((captured.toList ++ values).drop arity).toArray := by
            rw [show captured ++ values.toArray =
                (captured.toList ++ values).toArray by
              apply Array.toList_inj.mp
              simp]
            exact List.toArray_drop.symm
          rw [← remainingArrayEq]
          simpa [resume] using returnControl
        · exact returnNoCredits
        · exact returnImage
      exact attached.simulate_traced_apply_pap_over_cps functionMember
        calleeMember descendant calleeMatch state stores runtime ownership
          contracts.sourceDeclarations functionResolved argumentsResolved
          sourceGet shared node capturedUnder sourceRetain sourceRelease
          totalOver papArity sourceDeclaration sourcePapSafe targetDeclaration
          calleeRun calleeResultWorld control noCredits image nextHandler
          (workers calleeFuel (by omega))

/-- Exhaustive worker-facing rule for a traced source operation.  Checked
operation syntax leaves exactly one target instruction in every executable
case.  Reuse has no legal IxIR₂ syntax, retained extern operations are ruled
out by attachment, and dynamic apply consumes one additional evaluator fuel
constructor before entering its complete PAP plan. -/
theorem CompiledAttachment.simulate_traced_letOp_cps_of_run
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {operationFuel : Nat}
    {context : Eval.Context}
    (contracts : SuccessfulSimulationContracts attached sourceContext context)
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input nextInput : Lower.Sim.EnvMap} {entryValueCount index : Nat}
    {operation : IxIR1.Op} {instruction : Instr} {next : Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.letOp site blockId input nextInput entryValueCount operation index
        instruction next) sourceStore source frameRoots)
    (sourceRun : IxIR1.runCode sourceContext (operationFuel + 2)
      functionTrace.source sourceStore source
        (.letOp operation next.sourceCode) = .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context .logical
      functionTrace frameRoots stack sourceOutput outcome post)
    (workers : ∀ fuel, fuel < operationFuel + 2 →
      SuccessfulTraceSimulationAt attached sourceContext context .logical fuel) :
    BudgetedReachesPost context .logical post outcome.1 outcome.2 machine := by
  have operationSyntax :=
    functionTrace.descendantOperationSyntax descendant
  cases operation with
  | pure sourceAtom =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
      case move targetAtom =>
        exact attached.simulate_traced_pure_move_cps functionMember descendant
          state stores runtime ownership contracts.sourceDeclarations sourceRun
          resultWorld control noCredits image finish
          (workers (operationFuel + 1) (by omega))
  | alloc sourceWorld sourceCid sourceArguments =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
      case alloc targetWorld targetCid targetArguments =>
        exact attached.simulate_traced_alloc_checked_cps functionMember
          contracts.targetSchemas descendant state stores runtime
          contracts.sourceDeclarations ownership sourceRun resultWorld control
          noCredits image finish (workers (operationFuel + 1) (by omega))
  | reuse sourceTarget sourceCid sourceArguments =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
  | free sourceAtom =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
      case freeUnique targetAtom targetCid =>
        exact attached.simulate_traced_free_freeUnique_cps functionMember
          descendant state stores runtime ownership
          contracts.sourceDeclarations sourceRun resultWorld control noCredits
          image finish (workers (operationFuel + 1) (by omega))
  | dup sourceAtom =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
      case retainShared targetAtom =>
        exact attached.simulate_traced_dup_retain_cps functionMember descendant
          state stores runtime ownership contracts.sourceDeclarations sourceRun
          resultWorld control noCredits image finish
          (workers (operationFuel + 1) (by omega))
  | drop sourceAtom =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
      case releaseShared targetAtom =>
        exact attached.simulate_traced_drop_release_cps functionMember
          descendant state stores runtime ownership
          contracts.sourceDeclarations sourceRun resultWorld control noCredits
          image finish (workers (operationFuel + 1) (by omega))
  | dropU sourceAtom =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
      case dropUnique targetAtom =>
        exact attached.simulate_traced_dropU_dropUnique_cps functionMember
          descendant state stores runtime ownership
          contracts.sourceDeclarations sourceRun resultWorld control noCredits
          image finish (workers (operationFuel + 1) (by omega))
  | fetch sourceAtom sourceField =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
      case fetch targetAtom targetCid targetField =>
        exact attached.simulate_traced_fetch_cps functionMember descendant state
          stores runtime ownership contracts.sourceDeclarations sourceRun
          resultWorld control noCredits image finish
          (workers (operationFuel + 1) (by omega))
  | call sourceAddress sourceArguments =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
      case call targetAddress targetArguments =>
        exact attached.simulate_traced_call_cps_of_run contracts functionMember
          descendant state stores runtime ownership sourceRun resultWorld
          control noCredits image finish workers
  | callSelf sourceArguments =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
      case callSelf targetArguments =>
        exact attached.simulate_traced_call_self_cps_of_run contracts
          functionMember descendant state stores runtime ownership sourceRun
          resultWorld control noCredits image finish workers
  | papp sourceAddress sourceArguments =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
      case papp targetAddress targetArguments =>
        obtain ⟨middleStore, operationValue, operationRun, continuationRun⟩ :=
          IxIR1.runCode_letOp_success sourceRun
        obtain ⟨values, declaration, sourceResolved, sourceDeclaration,
            under, operationOutput⟩ :=
          IxIR1.runOp_papp_success operationRun
        cases declaration with
        | extern arity =>
            exact False.elim (attached.sourceDeclaration_not_extern
              contracts.sourceDeclarations sourceDeclaration)
        | fn sourceDefinition =>
            obtain ⟨targetDefinition, calleeTrace, calleeMember, calleeMatch,
                targetDeclaration⟩ :=
              attached.functionTrace_of_source_declaration
                contracts.sourceDeclarations contracts.targetDeclarations
                  sourceDeclaration
            have sourcePapSafe : sourceDefinition.papSafe = true :=
              attached.pappSafe contracts.sourceDeclarations functionMember
                descendant sourceDeclaration
            have targetArity : targetDefinition.signature.params.size =
                sourceDefinition.arity := by
              calc
                targetDefinition.signature.params.size =
                    calleeTrace.generated.signature.params.size := by
                  rw [calleeMatch.generated]
                _ = calleeTrace.source.arity := calleeTrace.sourceArity
                _ = sourceDefinition.arity := congrArg IxIR1.FnDef.arity
                  calleeMatch.source
            have targetPapSafe : targetDefinition.signature.papSafe = true := by
              calc
                targetDefinition.signature.papSafe =
                    calleeTrace.generated.signature.papSafe := by
                  rw [calleeMatch.generated]
                _ = calleeTrace.source.papSafe := calleeTrace.sourcePapSafe
                _ = sourceDefinition.papSafe := congrArg IxIR1.FnDef.papSafe
                  calleeMatch.source
                _ = true := sourcePapSafe
            exact attached.simulate_traced_papp_fn_cps functionMember
              descendant state stores runtime ownership
                contracts.sourceDeclarations sourceDeclaration
                targetDeclaration targetArity targetPapSafe sourceRun
                resultWorld control noCredits image finish
                (workers (operationFuel + 1) (by omega))
  | apply sourceFunction sourceArguments =>
      cases instruction <;>
        simp only [Lower.OperationSyntax] at operationSyntax
      case apply targetFunction targetArguments =>
        cases operationFuel with
        | zero =>
            obtain ⟨middleStore, operationValue, operationRun,
                continuationRun⟩ := IxIR1.runCode_letOp_success sourceRun
            obtain ⟨functionValue, values, functionResolved,
                argumentsResolved, applyRun⟩ :=
              IxIR1.runOp_apply_success operationRun
            have impossible := attached.applyMorePlan_of_applyGo
              contracts.sourceDeclarations contracts.targetDeclarations
                applyRun
            cases impossible
        | succ applyFuel =>
            exact attached.simulate_traced_apply_cps_of_run contracts
              functionMember descendant state stores runtime ownership
              sourceRun resultWorld control noCredits image finish
              (fun fuel smaller => workers fuel (by omega))
  | extern sourceAddress sourceArguments =>
      exact False.elim
        (attached.sourceExtern_impossible functionMember descendant)

/-- Complete CPS composition for a literal-zero switch branch. The checked
branch certificate supplies both the exact recursive child and a target step
that preserves the continuation's chosen heap budget. -/
theorem CompiledAttachment.simulate_traced_switch_nat_zero_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List Lower.EdgeTrace} {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frameRoots)
    {alternativeIndex : Nat} {body : IxIR1.Code}
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.lit (.nat 0)))
    (sourceAlternative : Lower.sourceAlternativeAtTag? alternatives 0 =
      some (.mk 0 0 body, alternativeIndex))
    (branchRun : IxIR1.runCode sourceContext sourceFuel functionTrace.source
      sourceStore source body = .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation sourceFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨constructors, peel, branches, childFrame, terminator, edgeMember,
      childMember, selected, childSource, childCode, targetStep,
      targetPreserving, childNoCredits, childTarget⟩ :=
    Lower.Sim.simulate_traced_switch_nat_zero_state descendant state.target
      sourceResolved control noCredits
  have selectedEq :
      (IxIR1.Alt.mk 0 0 branches.zero.body,
          branches.zero.alternativeIndex) =
        (.mk 0 0 body, alternativeIndex) :=
    Option.some.inj (selected.symm.trans sourceAlternative)
  have bodyEq : branches.zero.body = body :=
    congrArg (fun pair : IxIR1.Alt × Nat =>
      match pair.1 with | .mk _ _ code => code) selectedEq
  have childRun : IxIR1.runCode sourceContext sourceFuel
      functionTrace.source sourceStore source
        branches.zeroChild.sourceCode = .ok sourceOutput := by
    rw [childCode, bodyEq]
    exact branchRun
  have childState := state.natZeroChild selected childSource childCode
    childTarget
  have childDescendant :
      functionTrace.root.Descendant branches.zeroChild :=
    .step descendant childMember
  have parentEnvironments : Lower.Sim.EnvRel source frame.values input := by
    simpa [Lower.CodeTrace.sourceInputMap] using state.target.environments
  have childOwnership := Lower.Sim.SourceOwnershipAt.switchNatZero
    attached.target functionMember descendant terminator branches ownership
      parentEnvironments
  let childMachine : Eval.Machine :=
    { machine with control := .running childFrame stack }
  have childStores : Lower.Sim.StoreRel sourceStore childMachine.store := by
    simpa [childMachine] using stores
  have childControl : childMachine.control =
      .running childFrame stack := rfl
  have tail := worker (machine := childMachine) (stack := stack)
    functionMember childDescendant childState childStores runtime childOwnership
      childRun resultWorld childControl childNoCredits image finish
  refine BudgetedReachesPost.prependPreserving
    (before := machine) (middle := childMachine) (prefixCount := 1) ?_ tail
  intro heapFuel
  have fundedControl : ({ machine with heapFuel } : Eval.Machine).control =
      .running frame stack := by
    simpa using control
  simpa [childMachine] using
    (targetPreserving heapFuel).toSteps fundedControl

/-- Complete CPS composition for a literal-successor switch branch. The
peeled predecessor becomes the child's scalar head and ownership lenders are
shifted in lockstep with the target parameter prefix. -/
theorem CompiledAttachment.simulate_traced_switch_nat_succ_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {alternatives : Array IxIR1.Alt}
    {targetScrutinee : Atom} {generated : Block}
    {outgoing : List Lower.EdgeTrace} {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {predecessor : Nat} {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.switchValue site blockId input entryValueCount sourceScrutinee true
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frameRoots)
    {alternativeIndex : Nat} {body : IxIR1.Code}
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.lit (.nat (predecessor + 1))))
    (sourceAlternative : Lower.sourceAlternativeAtTag? alternatives 1 =
      some (.mk 1 1 body, alternativeIndex))
    (branchRun : IxIR1.runCode sourceContext sourceFuel functionTrace.source
      sourceStore (.lit (.nat predecessor) :: source) body =
        .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation sourceFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨constructors, peel, branches, childFrame, terminator, edgeMember,
      childMember, selected, childSource, childCode, targetStep,
      targetPreserving, childNoCredits, childTarget⟩ :=
    Lower.Sim.simulate_traced_switch_nat_succ_state descendant state.target
      sourceResolved control noCredits
  have selectedEq :
      (IxIR1.Alt.mk 1 1 branches.succ.body,
          branches.succ.alternativeIndex) =
        (.mk 1 1 body, alternativeIndex) :=
    Option.some.inj (selected.symm.trans sourceAlternative)
  have bodyEq : branches.succ.body = body :=
    congrArg (fun pair : IxIR1.Alt × Nat =>
      match pair.1 with | .mk _ _ code => code) selectedEq
  have childRun : IxIR1.runCode sourceContext sourceFuel
      functionTrace.source sourceStore
        (.lit (.nat predecessor) :: source)
        branches.succChild.sourceCode = .ok sourceOutput := by
    rw [childCode, bodyEq]
    exact branchRun
  have childState := state.natSuccChild selected childSource childCode
    sourceResolved childTarget
  have childDescendant :
      functionTrace.root.Descendant branches.succChild :=
    .step descendant childMember
  have parentEnvironments : Lower.Sim.EnvRel source frame.values input := by
    simpa [Lower.CodeTrace.sourceInputMap] using state.target.environments
  have childOwnership := Lower.Sim.SourceOwnershipAt.switchNatSucc
    attached.target functionMember descendant terminator branches ownership
      parentEnvironments (predecessor := predecessor)
  have childRuntime := runtime.natSuccessor predecessor
  let childMachine : Eval.Machine :=
    { machine with control := .running childFrame stack }
  have childStores : Lower.Sim.StoreRel sourceStore childMachine.store := by
    simpa [childMachine] using stores
  have childControl : childMachine.control =
      .running childFrame stack := rfl
  have tail := worker (machine := childMachine) (stack := stack)
    functionMember childDescendant childState childStores childRuntime
      childOwnership childRun resultWorld childControl childNoCredits image finish
  refine BudgetedReachesPost.prependPreserving
    (before := machine) (middle := childMachine) (prefixCount := 1) ?_ tail
  intro heapFuel
  have fundedControl : ({ machine with heapFuel } : Eval.Machine).control =
      .running frame stack := by
    simpa using control
  simpa [childMachine] using
    (targetPreserving heapFuel).toSteps fundedControl

/-- Complete CPS composition for a constructor switch branch. The target
dispatch and certified fetch prologue enter the exact recursive child, while
the attached schema invariant turns every fetched field into a borrow from
the selected constructor root. -/
theorem CompiledAttachment.simulate_traced_switch_ctor_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {location : Nat} {box : IxIR1.NodeBox} {cid : CtorId}
    {fields : Array IxIR1.RVal} {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frameRoots)
    (sourceResolved : IxIR1.resolveAtom source sourceScrutinee =
      .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN cid fields)
    {tag fieldCount alternativeIndex : Nat} {body : IxIR1.Code}
    (sourceAlternative : Lower.sourceAlternativeAtTag? alternatives cid.cidx =
      some (.mk tag fieldCount body, alternativeIndex))
    (fieldArity : fields.size = fieldCount)
    {constructors : Array CtorAlt} {targetPeel : Option NatPeel}
    {index : Nat} {target : CtorAlt} {edge : Lower.EdgeTrace}
    {child : Lower.CodeTrace}
    (terminator : generated.terminator =
      .switchValue targetScrutinee constructors targetPeel)
    (targetAt : constructors[index]? = some target)
    (targetAlternative : constructors.find? (fun candidate =>
      candidate.cid == cid) = some target)
    (edgeAt : outgoing[index]? = some edge)
    (childAt : children[index]? = some child)
    (branchRun : IxIR1.runCode sourceContext sourceFuel functionTrace.source
      sourceStore (fields.toList.reverse ++ source) body = .ok sourceOutput)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation sourceFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  obtain ⟨childFrame, _edgeFrame, _childScrutinee, childSource, childCode,
      targetSteps, targetPreserving, childNoCredits, nextStores, childTarget,
      _parentBlockAt, _parentPc, _targetResolved, _targetGet, _transferred,
      _switchStep, _childBlockAt, _childPc, _childResolved, _prologue⟩ :=
    Lower.Sim.simulate_traced_switch_ctor_state descendant state.target stores
      sourceResolved sourceGet node sourceAlternative fieldArity terminator
      targetAt targetAlternative edgeAt childAt control noCredits
  have recursiveMatched :=
    functionTrace.descendantSwitchBranchesMatch descendant
  have localMatched :=
    Lower.CodeTrace.switchNodeBranchesMatch_of_match recursiveMatched
  have branch := Lower.constructorBranchMatchAt_of_switch_match
    localMatched terminator targetAt edgeAt childAt
  have targetCid : target.cid = cid := by
    have matched : (target.cid == cid) = true := Array.find?_some
      (p := fun candidate : CtorAlt => candidate.cid == cid)
      (a := target) (xs := constructors) targetAlternative
    exact beq_iff_eq.mp matched
  have branchAlternative := branch.sourceAlternative
  rw [targetCid, sourceAlternative] at branchAlternative
  have alternativeEqual := Option.some.inj branchAlternative
  have sourceFieldCount : branch.fieldCount = fieldCount := by
    exact (congrArg (fun alternative : IxIR1.Alt × Nat =>
      match alternative.1 with | .mk _ fields _ => fields)
        alternativeEqual).symm
  have branchFieldArity : fields.size = branch.fieldCount := by
    rw [sourceFieldCount]
    exact fieldArity
  have childRun : IxIR1.runCode sourceContext sourceFuel
      functionTrace.source sourceStore (fields.toList.reverse ++ source)
        child.sourceCode = .ok sourceOutput := by
    rw [childCode]
    exact branchRun
  have childState := state.constructorChild sourceAlternative childSource
    childCode sourceResolved sourceGet node fieldArity childTarget
  have childMember : child ∈ children := List.mem_of_getElem? childAt
  have childDescendant : functionTrace.root.Descendant child :=
    .step descendant childMember
  have parentEnvironments : Lower.Sim.EnvRel source frame.values input := by
    simpa [Lower.CodeTrace.sourceInputMap] using state.target.environments
  have schemaFields : ∀ {world schema},
      attached.target.artifact.validationContext.schemas world cid =
        some schema →
      ∃ count, schema.fields = Array.replicate count world := by
    intro world schema found
    rw [attached.targetSchemasProduced] at found
    exact attached.schema_fields_replicate found
  have childOwnership := Lower.Sim.SourceOwnershipAt.switchCtor
    attached.target functionMember descendant terminator targetAt childAt
      branch ownership parentEnvironments sourceResolved sourceGet node
      targetCid branchFieldArity schemaFields
  have childRuntime := runtime.constructorBranch sourceGet node
  let childMachine : Eval.Machine :=
    { machine with control := .running childFrame stack }
  have childStores : Lower.Sim.StoreRel sourceStore childMachine.store := by
    simpa [childMachine] using nextStores
  have childControl : childMachine.control =
      .running childFrame stack := rfl
  have tail := worker (machine := childMachine) (stack := stack)
    functionMember childDescendant childState childStores childRuntime
      childOwnership childRun resultWorld childControl childNoCredits image finish
  refine BudgetedReachesPost.prependPreserving
    (before := machine) (middle := childMachine)
      (prefixCount := 1 + fields.size) ?_ tail
  intro heapFuel
  simpa [childMachine] using targetPreserving heapFuel

/-- Exhaustive CPS composition for a successful source `case`.  The source
evaluator has already reduced the dispatch to one indexed constructor,
literal-zero, or literal-successor branch.  Nat branches are selected wholly
from the retained lowering certificate.  Constructor dispatch consumes one
focused witness for the corresponding emitted target; establishing that
witness from the attached source typing/constructor universe is deliberately
kept separate from the trace/fuel induction. -/
theorem CompiledAttachment.simulate_traced_switch_cps
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    {sourceContext : IxIR1.Ctx} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {functionTrace : Lower.FunctionTrace}
    (functionMember : functionTrace ∈
      attached.target.artifact.trace.functions)
    {site : Lower.SourceSite} {blockId : BlockId}
    {input : Lower.Sim.EnvMap} {entryValueCount : Nat}
    {sourceScrutinee : IxIR1.Atom} {peelNat : Bool}
    {alternatives : Array IxIR1.Alt} {targetScrutinee : Atom}
    {generated : Block} {outgoing : List Lower.EdgeTrace}
    {children : List Lower.CodeTrace}
    (descendant : functionTrace.root.Descendant
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children))
    {sourceStore : IxIR1.Store} {source : List IxIR1.RVal}
    {frameRoots : List IxIR1.Sim.Root}
    {sourceOutput outcome : IxIR1.Store × IxIR1.RVal}
    (state : attached.sidecars.TraceStateRel functionTrace
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frame)
    (stores : Lower.Sim.StoreRel sourceStore machine.store)
    (runtime : Lower.Sim.SourceRuntimeInvariant sourceStore source)
    (ownership : Lower.Sim.SourceOwnershipAt
      attached.target.artifact.trace.positions
      (.switchValue site blockId input entryValueCount sourceScrutinee peelNat
        alternatives targetScrutinee generated outgoing children)
      sourceStore source frameRoots)
    (selected : IndexedCaseSuccess sourceContext sourceFuel
      functionTrace.source sourceStore source sourceScrutinee peelNat
        alternatives sourceOutput)
    (constructorSelection :
      ∀ {location : Nat} {box : IxIR1.NodeBox} {cid : CtorId}
          {fields : Array IxIR1.RVal} {fieldCount alternativeIndex : Nat}
          {body : IxIR1.Code},
        IxIR1.resolveAtom source sourceScrutinee = .ok (.loc location) →
        sourceStore.get? location = some box →
        box.node = .ctorN cid fields →
        Lower.sourceAlternativeAtTag? alternatives cid.cidx =
          some (.mk cid.cidx fieldCount body, alternativeIndex) →
        fields.size = fieldCount →
        ConstructorSwitchSelection targetScrutinee generated outgoing children
          cid)
    (resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      functionTrace.source.result sourceOutput.2)
    (control : machine.control = .running frame stack)
    (noCredits : frame.credits = #[])
    (image : attached.SourceStoreImage sourceStore)
    {post : SourceMachinePost}
    (finish : SuccessfulReturnHandler attached sourceContext context
      interpretation functionTrace frameRoots stack sourceOutput outcome post)
    (worker : SuccessfulTraceSimulationAt attached sourceContext context
      interpretation sourceFuel) :
    BudgetedReachesPost context interpretation post outcome.1 outcome.2
      machine := by
  cases selected with
  | ctorBranch resolved found node sourceAlternative fieldArity branchRun =>
      let target := constructorSelection resolved found node sourceAlternative
        fieldArity
      exact attached.simulate_traced_switch_ctor_cps functionMember descendant
        state stores runtime ownership resolved found node sourceAlternative
          fieldArity target.terminator target.targetAt target.targetAlternative
          target.edgeAt target.childAt branchRun resultWorld control noCredits
          image finish worker
  | natZero peels resolved sourceAlternative branchRun =>
      subst peelNat
      exact attached.simulate_traced_switch_nat_zero_cps functionMember
        descendant state stores runtime ownership resolved sourceAlternative
          branchRun resultWorld control noCredits image finish worker
  | natSucc peels resolved sourceAlternative branchRun =>
      subst peelNat
      exact attached.simulate_traced_switch_nat_succ_cps functionMember
        descendant state stores runtime ownership resolved sourceAlternative
          branchRun resultWorld control noCredits image finish worker

/-- Every successful retained source trace is simulated by the checked IxIR₂
machine under logical extern interpretation.  Strong induction is solely on
source evaluator fuel: local operations and switches recurse at the immediate
predecessor, calls recurse into both the strictly smaller callee and caller
continuation, and over-application follows its strictly descending plan. -/
theorem CompiledAttachment.successfulTraceSimulation
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    (sourceContext : IxIR1.Ctx) (context : Eval.Context)
    (contracts : SuccessfulSimulationContracts attached sourceContext context) :
    ∀ fuel, SuccessfulTraceSimulationAt attached sourceContext context
      .logical fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel smallerWorkers =>
      cases fuel with
      | zero =>
          exact successfulTraceSimulationAt_zero attached sourceContext context
            .logical
      | succ sourceFuel =>
          intro functionTrace trace sourceStore source frameRoots sourceOutput
            outcome frame machine stack post functionMember descendant state
            stores runtime ownership sourceRun resultWorld control noCredits
            image finish
          cases trace with
          | ret site blockId input entryValueCount sourceAtom targetAtom
              generated =>
              exact finish functionMember descendant state stores runtime
                ownership sourceRun resultWorld control noCredits image
          | tailCall site blockId input entryValueCount address sourceArguments
              generated =>
              cases sourceFuel with
              | zero =>
                  obtain ⟨middleStore, operationValue, operationRun,
                      continuationRun⟩ :=
                    IxIR1.runCode_letOp_success sourceRun
                  rw [IxIR1.runOp.eq_def] at operationRun
                  contradiction
              | succ callFuel =>
                  exact attached.simulate_traced_tail_call_cps_of_run contracts
                    functionMember descendant state stores runtime ownership
                    sourceRun resultWorld control noCredits image finish
                    (fun recursiveFuel smaller =>
                      smallerWorkers recursiveFuel (by omega))
          | tailCallSelf site blockId input entryValueCount sourceArguments
              generated =>
              cases sourceFuel with
              | zero =>
                  obtain ⟨middleStore, operationValue, operationRun,
                      continuationRun⟩ :=
                    IxIR1.runCode_letOp_success sourceRun
                  rw [IxIR1.runOp.eq_def] at operationRun
                  contradiction
              | succ callFuel =>
                  exact attached.simulate_traced_tail_call_self_cps_of_run
                    functionMember descendant state stores runtime ownership
                    sourceRun resultWorld control noCredits image finish
                    (fun recursiveFuel smaller =>
                      smallerWorkers recursiveFuel (by omega))
          | letOp site blockId input nextInput entryValueCount operation index
              instruction next =>
              cases sourceFuel with
              | zero =>
                  obtain ⟨middleStore, operationValue, operationRun,
                      continuationRun⟩ :=
                    IxIR1.runCode_letOp_success sourceRun
                  rw [IxIR1.runOp.eq_def] at operationRun
                  contradiction
              | succ operationFuel =>
                  exact attached.simulate_traced_letOp_cps_of_run contracts
                    functionMember descendant state stores runtime ownership
                    sourceRun resultWorld control noCredits image finish
                    (fun recursiveFuel smaller =>
                      smallerWorkers recursiveFuel (by omega))
          | switchValue site blockId input entryValueCount sourceScrutinee
              peelNat alternatives targetScrutinee generated outgoing
              children =>
              have selected := indexedCaseSuccess_of_run sourceRun
              exact attached.simulate_traced_switch_cps functionMember
                descendant state stores runtime ownership selected
                (fun resolved found node sourceAlternative fieldArity =>
                  match exactEq : attached.sidecars.exactConstructorAt?
                      site sourceScrutinee with
                  | none =>
                      attached.constructorSwitchSelection_of_residual
                        functionMember descendant exactEq image found node
                        sourceAlternative fieldArity
                  | some (fact, identity) =>
                      attached.constructorSwitchSelection_of_exactHPT_runtime
                        functionMember descendant state exactEq resolved found
                        node)
                resultWorld control noCredits image finish
                (smallerWorkers sourceFuel (Nat.lt_succ_self sourceFuel))

/-- Public whole-main successful-run preservation for an attached baseline
lowering.  The source and target budgets are intentionally independent: the
trace worker selects sufficient heap fuel backwards from recursive
destruction, while its finite step witness supplies the exact control fuel
accepted by `runMain`. -/
theorem CompiledAttachment.successfulMainSimulation
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel)
    (sourceContext : IxIR1.Ctx) (context : Eval.Context)
    (contracts : SuccessfulSimulationContracts attached sourceContext context) :
    Lower.Sim.SuccessfulMainSimulation sourceContext context
      attached.target.artifact.source.main
      attached.target.artifact.source.mainResult
      attached.target.artifact.program := by
  intro sourceFuel sourceOutput sourceRun
  obtain ⟨mainBodyRun, mainResultWorld⟩ :=
    IxIR1.Sim.runOwnedMain_ok sourceRun
  have mainRun : IxIR1.runCode sourceContext sourceFuel
      attached.target.artifact.mainTrace.source ({} : IxIR1.Store) []
        attached.target.artifact.mainTrace.root.sourceCode = .ok sourceOutput := by
    rw [attached.target.artifact.mainSource,
      attached.target.artifact.mainRootSourceCode]
    exact mainBodyRun
  have resultWorld : IxIR1.Sim.HasWorld sourceOutput.1
      attached.target.artifact.mainTrace.source.result sourceOutput.2 := by
    rw [attached.target.artifact.mainSource]
    exact mainResultWorld
  let frame := Lower.Sim.initialMainFrame attached.target.artifact
  let machine := Lower.Sim.initialMainMachine attached.target.artifact 0
  have state : attached.sidecars.TraceStateRel
      attached.target.artifact.mainTrace
      attached.target.artifact.mainTrace.root ({} : IxIR1.Store) [] frame := by
    simpa [frame] using attached.initialMainTraceState
  have stores : Lower.Sim.StoreRel ({} : IxIR1.Store) machine.store := by
    simpa [machine, Lower.Sim.initialMainMachine] using
      Lower.Sim.StoreRel.initial
  have control : machine.control = .running frame [] := by
    rfl
  have noCredits : frame.credits = #[] := by
    rfl
  have reached :=
    (attached.successfulTraceSimulation sourceContext context contracts
      sourceFuel)
      attached.target.artifact.mainTraceMember
      Lower.CodeTrace.Descendant.refl state stores
      Lower.Sim.SourceRuntimeInvariant.empty
      attached.initialMainSourceOwnership mainRun resultWorld control noCredits
      attached.sourceStoreImage_empty
      (attached.haltReturnHandler sourceContext context .logical
        attached.target.artifact.mainTrace sourceOutput)
  obtain ⟨heapFuel, controlFuel, final, steps, halted, finalStores⟩ := reached
  cases final with
  | mk targetStore heapRemaining finalControl =>
      dsimp only at halted
      subst finalControl
      let targetOutput : Eval.Result :=
        { store := targetStore
          value := sourceOutput.2
          controlRemaining := 0
          heapRemaining }
      refine ⟨controlFuel, heapFuel, targetOutput, ?_, ?_⟩
      · rw [Lower.Sim.runMain_eq_initialMainMachine]
        have targetRun := steps.runMachine_halted
        simpa [machine, targetOutput, Lower.Sim.initialMainMachine,
          Eval.initialMachine] using targetRun
      · exact { finalStores with value := rfl }

/-- Canonical end-to-end entry point: the checked attachment alone simulates
every successful owned main run in its exact emitted evaluator contexts. -/
theorem CompiledAttachment.successfulCanonicalMainSimulation
    {mainWorld : Ixon.Owned} {lowerFuel : Nat}
    (attached : CompiledAttachment mainWorld lowerFuel) :
    Lower.Sim.SuccessfulMainSimulation attached.simulationSourceContext
      attached.simulationTargetContext attached.target.artifact.source.main
      attached.target.artifact.source.mainResult
      attached.target.artifact.program :=
  attached.successfulMainSimulation attached.simulationSourceContext
    attached.simulationTargetContext
    attached.successfulSimulationContracts


/-! Existing theorem names remain available for direct application. -/
namespace Attached
export CompiledAttachment (
  declarationFunctionEntryTraceState
  mainFunctionEntryTraceState
  functionEntryTraceState
  initialMainTraceState
  initialMainSourceOwnership
  traceState_next
  traceState_next_of_member
  mainTraceState_next
  simulate_traced_pure_move_state
  simulate_traced_pure_move_success_step
  simulate_traced_alloc_checked_state
  simulate_traced_alloc_checked_success_step
  simulate_traced_dup_retain_scalar_state
  simulate_traced_dup_retain_shared_state
  simulate_traced_drop_release_scalar_state
  simulate_traced_dropU_dropUnique_scalar_state
  simulate_traced_dropU_dropUnique_recursive_state
  simulate_traced_dropU_dropUnique_recursive_state_framed
  simulate_traced_drop_release_recursive_state
  simulate_traced_drop_release_recursive_state_framed
  simulate_traced_papp_fn_state
  simulate_traced_apply_transfer_state
  simulate_traced_apply_erased_state
  simulate_traced_apply_pap_under_state
  simulate_traced_apply_pap_saturated_enter_state
  simulate_traced_apply_pap_over_enter_state
  simulate_traced_call_fn_enter_state
  simulate_traced_call_self_enter_state
  simulate_traced_tail_call_fn_enter_state
  simulate_traced_tail_call_self_enter_state
  simulate_traced_ret_apply_more_success
  simulate_traced_ret_apply_more_pap_saturated_enter_state
  simulate_traced_ret_apply_more_pap_over_enter_state
  simulate_traced_ret_apply_more_pap_under_state
  simulate_traced_ret_apply_more_erased_state
  simulate_traced_return_to_letOp_state
  simulate_traced_ret_halt_success
  constructorSwitchSelection_of_exactHPT_nonempty
  constructorSwitchSelection_of_exactHPT
  constructorSwitchSelection_of_exactHPT_runtime
  simulate_traced_fetch_state_of_run_hpt
  simulate_traced_free_freeUnique_state_of_run_hpt
  functionCodeConstructorsKnown
  functionTraceConstructorsKnown
  descendantOperationConstructorsKnown
  sourceContextConstructorsKnown
  SourceStoreImage
  simulationSourceContext
  simulationSourceContext_eq_addressedCtx
  sourceRebuildSemanticAudit
  sourceContextRenames
  sourceContextRenamesOfDeclarations
  sourceCodeAddressImage
  functionSourceAddressImage
  letOpAddressImages
  rawApplyOwnership
  sourceStoreImage_empty
  runOp_preservesSourceStoreImage
  dupVals_preservesSourceStoreImage
  dropVal_preservesSourceStoreImage
  dropMany_preservesSourceStoreImage
  applyGo_exactImage
  applyGo_owned_of_sourceStoreImage
  applyGo_owned_of_sourceStoreImage_of_declarations
  applyOwnershipPreservesFrom_sourceStoreImage_of_declarations
  applyOwnershipPreservesFrom_sourceStoreImage
  constructorSwitchSelection_of_residual_nonempty
  constructorSwitchSelection_of_residual
  simulationTargetContext
  successfulSimulationContracts
  haltReturnHandler
  functionTrace_of_source_declaration
  functionTrace_of_target_declaration
  sourceDeclaration_not_extern
  targetDeclaration_not_extern
  applyMorePlan_of_applyGo
  simulate_traced_pure_move_cps
  simulate_traced_dup_retain_cps
  simulate_traced_fetch_cps
  simulate_traced_free_freeUnique_cps
  simulate_traced_drop_release_cps
  simulate_traced_dropU_dropUnique_cps
  simulate_traced_alloc_checked_cps
  simulate_traced_papp_fn_cps
  simulate_traced_apply_erased_cps
  simulate_traced_apply_pap_under_cps
  simulate_traced_apply_pap_saturated_cps
  simulate_traced_ret_apply_more_erased_cps
  simulate_traced_ret_apply_more_pap_under_cps
  simulate_traced_ret_apply_more_pap_saturated_cps
  simulate_traced_ret_apply_more_pap_over_cps
  simulate_traced_apply_pap_over_cps
  applyMoreReturnHandler_of_plan
  applyMoreReturnHandler_of_applyGo
  simulate_traced_call_fn_cps
  simulate_traced_call_self_cps
  simulate_traced_tail_call_fn_cps
  simulate_traced_tail_call_self_cps
  simulate_traced_tail_call_cps_of_run
  simulate_traced_tail_call_self_cps_of_run
  simulate_traced_call_cps_of_run
  simulate_traced_call_self_cps_of_run
  simulate_traced_apply_cps_of_run
  simulate_traced_letOp_cps_of_run
  simulate_traced_switch_nat_zero_cps
  simulate_traced_switch_nat_succ_cps
  simulate_traced_switch_ctor_cps
  simulate_traced_switch_cps
  successfulTraceSimulation
  successfulMainSimulation
  successfulCanonicalMainSimulation)
end Attached

end Ix.Compiler.IxIR2.Pipeline
