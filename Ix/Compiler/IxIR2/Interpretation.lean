import Ix.Compiler.IxIR2.CreditFree
import Ix.Compiler.IxIR2.Eval

/-! Exact interpretation independence for programs without credit operations.
Calls, recursive calls, edges, and residual PAP application preserve the
inventory of function bodies. No heap or fuel observation is weakened. -/

namespace Ix.Compiler.IxIR2.Eval

theorem ApplyTransfer.interpretation {context : Context}
    {first second : Interpretation} {store : Store} {heapFuel : Nat}
    {function : RVal} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {target : Machine}
    (transferred : ApplyTransfer context first store heapFuel function
      arguments resume stack target) :
    ApplyTransfer context second store heapFuel function arguments resume
      stack target := transferred

theorem InstructionTransfer.interpretation {context : Context}
    {first second : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {instruction : Instr}
    {target : Machine} (free : CreditFree.instruction instruction = true)
    (transferred : InstructionTransfer context first store heapFuel frame
      stack instruction target) :
    InstructionTransfer context second store heapFuel frame stack
      instruction target := by
  cases instruction <;> first | exact transferred | contradiction

theorem TerminatorTransfer.interpretation {context : Context}
    {first second : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {terminator : Terminator}
    {target : Machine}
    (transferred : TerminatorTransfer context first store heapFuel frame
      stack terminator target) :
    TerminatorTransfer context second store heapFuel frame stack
      terminator target := transferred

private theorem instructionCaseInterpretation {context : Context}
    {first second : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {instruction : Instr}
    {target : Machine} (free : CreditFree.instruction instruction = true)
    (classified : InstructionTransferCase context first store heapFuel frame
      stack instruction target) :
    InstructionTransferCase context second store heapFuel frame stack
      instruction target := by
  cases classified <;> try contradiction
  all_goals first
    | (constructor <;> assumption)
    | (apply InstructionTransferCase.apply <;> first
        | assumption
        | (apply ApplyTransfer.interpretation; assumption))

private theorem terminatorCaseInterpretation {context : Context}
    {first second : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation} {terminator : Terminator}
    {target : Machine}
    (classified : TerminatorTransferCase context first store heapFuel frame
      stack terminator target) :
    TerminatorTransferCase context second store heapFuel frame stack
      terminator target := by
  cases classified with
  | jump h => exact .jump h
  | switchCtor a b c d e => exact .switchCtor a b c d e
  | switchNatZero a b => exact .switchNatZero a b
  | switchNatSucc a b => exact .switchNatSucc a b
  | branchPresent a b c => exact .branchPresent a b c
  | branchAbsent a b c => exact .branchAbsent a b c
  | retResume a b c => exact .retResume a b c
  | retHalt a b c => exact .retHalt a b c
  | retApplyMore a b c d => exact .retApplyMore a b c d.interpretation
  | tailCallFn a b c d e => exact .tailCallFn a b c d e
  | tailCallSelf a b c d => exact .tailCallSelf a b c d

private def continuationFunction : Continuation → Function
  | .resume frame | .applyMore _ frame => frame.definition

private def stackFunctions (predicate : Function → Prop)
    (stack : List Continuation) : Prop :=
  ∀ continuation ∈ stack, predicate (continuationFunction continuation)

private def machineFunctions (predicate : Function → Prop)
    (machine : Machine) : Prop :=
  match machine.control with
  | .halted _ => True
  | .running frame stack => predicate frame.definition ∧ stackFunctions predicate stack

private theorem applyFunctions {predicate : Function → Prop}
    {context : Context} {interpretation : Interpretation}
    (declarations : ∀ address definition,
      context.declarations address = some (.fn definition) → predicate definition)
    {store : Store} {heapFuel : Nat} {function : RVal}
    {arguments : Array RVal} {resume : Frame} {stack : List Continuation}
    {target : Machine} (caller : predicate resume.definition)
    (saved : stackFunctions predicate stack)
    (transferred : ApplyTransfer context interpretation store heapFuel
      function arguments resume stack target) : machineFunctions predicate target := by
  cases transferred.classify with
  | erased | papUnder | papExtern => exact ⟨caller, saved⟩
  | papFn _ _ _ _ _ _ _ declaration _ _ _ =>
      refine ⟨declarations _ _ declaration, ?_⟩
      intro continuation member
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst continuation
        split <;> exact caller
      · exact saved _ member

private theorem instructionFunctions {predicate : Function → Prop}
    {context : Context} {interpretation : Interpretation}
    (declarations : ∀ address definition,
      context.declarations address = some (.fn definition) → predicate definition)
    {store : Store} {heapFuel : Nat} {frame : Frame}
    {stack : List Continuation} {instruction : Instr} {target : Machine}
    (current : predicate frame.definition) (saved : stackFunctions predicate stack)
    (free : CreditFree.instruction instruction = true)
    (transferred : InstructionTransferCase context interpretation store heapFuel
      frame stack instruction target) : machineFunctions predicate target := by
  cases transferred <;> try contradiction
  case apply transferred =>
    exact applyFunctions declarations
      (resume := { frame with pc := frame.pc + 1 }) current saved transferred
  all_goals first
    | exact ⟨current, saved⟩
    | (refine ⟨?_, ?_⟩
       · first | exact current | exact declarations _ _ (by assumption)
       · intro continuation member
         rcases List.mem_cons.mp member with equal | member
         · subst continuation; exact current
         · exact saved _ member)

private theorem terminatorFunctions {predicate : Function → Prop}
    {context : Context} {interpretation : Interpretation}
    (declarations : ∀ address definition,
      context.declarations address = some (.fn definition) → predicate definition)
    {store : Store} {heapFuel : Nat} {frame : Frame}
    {stack : List Continuation} {terminator : Terminator} {target : Machine}
    (current : predicate frame.definition) (saved : stackFunctions predicate stack)
    (transferred : TerminatorTransferCase context interpretation store heapFuel
      frame stack terminator target) : machineFunctions predicate target := by
  cases transferred with
  | jump edge | switchCtor _ _ _ _ edge | switchNatZero _ edge
  | switchNatSucc _ edge | branchPresent _ _ edge | branchAbsent _ _ edge =>
      exact ⟨edge.definition.symm ▸ current, saved⟩
  | retResume =>
      exact ⟨saved _ (List.mem_cons_self), fun continuation member =>
        saved continuation (List.mem_cons_of_mem _ member)⟩
  | retHalt => trivial
  | retApplyMore _ _ _ transferred =>
      exact applyFunctions declarations (saved _ List.mem_cons_self)
        (fun continuation member => saved continuation (List.mem_cons_of_mem _ member))
        transferred
  | tailCallFn _ _ declaration _ _ => exact ⟨declarations _ _ declaration, saved⟩
  | tailCallSelf => exact ⟨current, saved⟩

private theorem stepInterpretation {context : Context}
    {first second : Interpretation}
    (declarations : ∀ address definition,
      context.declarations address = some (.fn definition) →
        CreditFree.function definition = true)
    {before after : Machine}
    (free : machineFunctions (fun definition => CreditFree.function definition = true) before)
    (stepped : Step context first before after) :
    Step context second before after ∧
      machineFunctions (fun definition => CreditFree.function definition = true) after := by
  cases stepped.classify with
  | halted => exact ⟨rfl, trivial⟩
  | instruction blockAt pc instructionAt classified =>
      have instructionFree := CreditFree.instructionAt free.1 blockAt pc
      rw [instructionAt] at instructionFree
      refine ⟨?_, instructionFunctions declarations free.1 free.2 instructionFree classified⟩
      exact (instructionCaseInterpretation instructionFree classified).step
        blockAt pc instructionAt
  | terminator blockAt pc terminatorAt classified =>
      refine ⟨?_, terminatorFunctions declarations free.1 free.2 classified⟩
      exact (terminatorCaseInterpretation classified).step blockAt pc terminatorAt

private theorem stepsInterpretation {context : Context}
    {first second : Interpretation}
    (declarations : ∀ address definition,
      context.declarations address = some (.fn definition) →
        CreditFree.function definition = true)
    {count : Nat} {before after : Machine}
    (free : machineFunctions (fun definition => CreditFree.function definition = true) before)
    (steps : Steps context first count before after) :
    Steps context second count before after := by
  induction steps with
  | refl => exact .refl _
  | cons running head tail ih =>
      obtain ⟨head, nextFree⟩ := stepInterpretation declarations free head
      exact .cons running head (ih nextFree)

/-- Change credit interpretation without changing any successful runner
observation, including both remaining budgets and every heap counter. -/
theorem runMachine_creditFree {context : Context} {first second : Interpretation}
    (declarations : ∀ address definition,
      context.declarations address = some (.fn definition) →
        CreditFree.function definition = true)
    {definition : Function} (free : CreditFree.function definition = true)
    {arguments : Array RVal} {store : Store}
    {controlFuel heapFuel : Nat} {result : Result}
    (run : runMachine context first controlFuel
      (initialMachine definition arguments heapFuel store) = .ok result) :
    runMachine context second controlFuel
      (initialMachine definition arguments heapFuel store) = .ok result := by
  obtain ⟨count, budget, steps⟩ := runMachine_steps run
  have transported : Steps context second count
      (initialMachine definition arguments heapFuel store)
      { store := result.store, heapFuel := result.heapRemaining,
        control := .halted result.value } :=
    stepsInterpretation declarations ⟨free, by simp [stackFunctions]⟩ steps
  rw [budget, transported.runMachine]
  cases result with
  | mk store value controlRemaining heapRemaining =>
      cases controlRemaining <;> rfl

private theorem programDeclarations {source : Program}
    (free : CreditFree.program source = true)
    {schemas : Ixon.Owned → CtorId → Option CtorSchema}
    {oracle : Ixon.Address → List RVal → Option RVal}
    (address : Ixon.Address) (definition : Function)
    (found : (Context.ofProgram source schemas oracle).declarations address =
      some (.fn definition)) : CreditFree.function definition = true := by
  obtain ⟨entry, member, value⟩ := Option.map_eq_some_iff.mp found
  simp only [CreditFree.program, Bool.and_eq_true] at free
  have entryFree := List.all_eq_true.mp free.2 entry (List.mem_of_find?_eq_some member)
  rw [value] at entryFree
  exact entryFree

/-- Declared runtime functions inherit the complete baseline interpretation
boundary, for arbitrary arguments and initial heaps. -/
theorem runFunction_creditFree {source : Program}
    (free : CreditFree.program source = true)
    {schemas : Ixon.Owned → CtorId → Option CtorSchema}
    {oracle : Ixon.Address → List RVal → Option RVal}
    {address : Ixon.Address} {definition : Function}
    (declared : (Context.ofProgram source schemas oracle).declarations address = some (.fn definition))
    {arguments : Array RVal} {store : Store}
    {first second : Interpretation} {controlFuel heapFuel : Nat} {result : Result}
    (arity : arguments.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false)
    (run : runFunction (Context.ofProgram source schemas oracle) first definition
      arguments controlFuel heapFuel store = .ok result) :
    runFunction (Context.ofProgram source schemas oracle) second definition
      arguments controlFuel heapFuel store = .ok result := by
  rw [runFunction_eq_runMachine arity nonempty] at run ⊢
  exact runMachine_creditFree (programDeclarations free) (programDeclarations free address definition declared) run

/-- The complete credit-free main boundary. The same schemas and scalar
oracle are used on both sides; the validated compiler additionally closes
the extern boundary. -/
theorem runMain_creditFree {source : Program}
    (free : CreditFree.program source = true)
    {schemas : Ixon.Owned → CtorId → Option CtorSchema}
    {oracle : Ixon.Address → List RVal → Option RVal}
    {first second : Interpretation} {controlFuel heapFuel : Nat}
    {result : Result}
    (arity : source.main.signature.params.size = 0)
    (nonempty : source.main.blocks.isEmpty = false)
    (run : runMain (Context.ofProgram source schemas oracle) first source
      controlFuel heapFuel = .ok result) :
    runMain (Context.ofProgram source schemas oracle) second source
      controlFuel heapFuel = .ok result := by
  rw [runMain_eq_runMachine arity nonempty] at run ⊢
  have mainFree : CreditFree.function source.main = true := by
    simp only [CreditFree.program, Bool.and_eq_true] at free
    exact free.1
  exact runMachine_creditFree (programDeclarations free)
    mainFree run

end Ix.Compiler.IxIR2.Eval
