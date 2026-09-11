import Ix.Compiler.IxIR2.Eval

/-!
# Execution with continuation-owned credits

The v1 dispatcher changes only direct non-tail calls. It saves the complete
caller frame once and enters the callee with no credits. All other instructions
and every terminator use the original evaluator, including its checks against
abandoning a credit on return or transferring it across a forbidden boundary.
The v0 runner is extensionally equal to the original runner.
-/

namespace Ix.Compiler.IxIR2.Eval.Policy

open Ix.Compiler.Ixon (Address)

inductive DirectCall where
  | function (address : Address) (arguments : Array Atom)
  | self (arguments : Array Atom)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def DirectCall.instruction : DirectCall → Instr
  | .function address arguments => .call address arguments
  | .self arguments => .callSelf arguments

def DirectCall.ofInstruction? : Instr → Option DirectCall
  | .call address arguments => some (.function address arguments)
  | .callSelf arguments => some (.self arguments)
  | _ => none

def DirectCall.arguments : DirectCall → Array Atom
  | .function _ arguments | .self arguments => arguments

def DirectCall.definition (context : Context) (frame : Frame) :
    DirectCall → Except Error Function
  | .self _ => .ok frame.definition
  | .function address _ =>
      match context.declarations address with
      | some (.fn definition) => .ok definition
      | some (.extern _) => .error (.stuck "call must not target an extern")
      | none => .error (.unknownRef address)

/-- Inspect exactly the current instruction, without interpreting a missing
block, a terminator, or an invalid program counter as a call. -/
def directCall? (frame : Frame) : Option DirectCall := do
  let block ← frame.definition.blocks[frame.block]?
  DirectCall.ofInstruction? (← block.instructions[frame.pc]?)

def suspendCall (context : Context) (machine : Machine) (frame : Frame)
    (stack : List Continuation) (call : DirectCall) : Except Error Machine := do
  let values ← resolveAtoms frame.values call.arguments
  let definition ← call.definition context frame
  let callee ← enterFunction definition values
  let caller : Frame := { frame with pc := frame.pc + 1 }
  return { machine with control := .running callee (.resume caller :: stack) }

def step (policy : CreditPolicy) (context : Context)
    (interpretation : Interpretation) (machine : Machine) : Except Error Machine :=
  match policy, machine.control with
  | .suspendedCallsV1, .running frame stack =>
      match directCall? frame with
      | some call => suspendCall context machine frame stack call
      | none => Eval.step context interpretation machine
  | _, _ => Eval.step context interpretation machine

def Step (policy : CreditPolicy) (context : Context)
    (interpretation : Interpretation) (before after : Machine) : Prop :=
  step policy context interpretation before = .ok after

@[simp] theorem step_v0 (context : Context) (interpretation : Interpretation)
    (machine : Machine) :
    step .callLocalV0 context interpretation machine =
      Eval.step context interpretation machine := rfl

theorem step_of_noCall {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame : Frame} {stack : List Continuation}
    (running : machine.control = .running frame stack)
    (noCall : directCall? frame = none) :
    step .suspendedCallsV1 context interpretation machine =
      Eval.step context interpretation machine := by
  simp [step, running, noCall]

theorem step_of_call {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame : Frame} {stack : List Continuation}
    {call : DirectCall} (running : machine.control = .running frame stack)
    (atCall : directCall? frame = some call) :
    step .suspendedCallsV1 context interpretation machine =
      suspendCall context machine frame stack call := by
  simp [step, running, atCall]

inductive Steps (policy : CreditPolicy) (context : Context)
    (interpretation : Interpretation) : Nat → Machine → Machine → Prop where
  | refl (machine : Machine) : Steps policy context interpretation 0 machine machine
  | cons {count : Nat} {before middle after : Machine}
      {frame : Frame} {stack : List Continuation}
      (running : before.control = .running frame stack)
      (head : Step policy context interpretation before middle)
      (tail : Steps policy context interpretation count middle after) :
      Steps policy context interpretation (count + 1) before after

theorem Step.deterministic {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {before left right : Machine}
    (leftStep : Step policy context interpretation before left)
    (rightStep : Step policy context interpretation before right) : left = right :=
  Except.ok.inj (leftStep.symm.trans rightStep)

theorem Steps.trans {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {firstCount secondCount : Nat}
    {before middle after : Machine}
    (first : Steps policy context interpretation firstCount before middle)
    (second : Steps policy context interpretation secondCount middle after) :
    Steps policy context interpretation (firstCount + secondCount) before after := by
  induction first with
  | refl => simpa using second
  | cons running head tail ih =>
      simpa only [Nat.succ_add] using Steps.cons running head (ih second)

def runMachine (policy : CreditPolicy) (context : Context)
    (interpretation : Interpretation) : Nat → Machine → Except Error Result
  | controlFuel, { store, heapFuel, control := .halted value } =>
      .ok { store, value, controlRemaining := controlFuel, heapRemaining := heapFuel }
  | 0, { control := .running .., .. } => .error .controlFuel
  | controlFuel + 1, machine@{ control := .running .., .. } => do
      let next ← step policy context interpretation machine
      runMachine policy context interpretation controlFuel next

def runFunction (policy : CreditPolicy) (context : Context)
    (interpretation : Interpretation) (definition : Function)
    (arguments : Array RVal) (controlFuel heapFuel : Nat) (store : Store := {}) :
    Except Error Result := do
  let _ ← enterFunction definition arguments
  runMachine policy context interpretation controlFuel
    (initialMachine definition arguments heapFuel store)

def runMain (policy : CreditPolicy) (context : Context)
    (interpretation : Interpretation) (program : Program)
    (controlFuel : Nat := 100000) (heapFuel : Nat := 100000) : Except Error Result :=
  runFunction policy context interpretation program.main #[] controlFuel heapFuel

theorem runMachine_v0 (context : Context) (interpretation : Interpretation)
    (controlFuel : Nat) (machine : Machine) :
    runMachine .callLocalV0 context interpretation controlFuel machine =
      Eval.runMachine context interpretation controlFuel machine := by
  induction controlFuel generalizing machine with
  | zero => cases machine with | mk store heapFuel control => cases control <;> rfl
  | succ fuel ih =>
      cases machine with
      | mk store heapFuel control =>
          cases control with
          | halted value => rfl
          | running frame stack =>
              simp only [runMachine, Eval.runMachine, step_v0]
              cases Eval.step context interpretation
                  { store, heapFuel, control := .running frame stack } <;>
                simp only [bind, Except.bind, ih]

theorem runFunction_v0 (context : Context) (interpretation : Interpretation)
    (definition : Function) (arguments : Array RVal) (controlFuel heapFuel : Nat)
    (store : Store) :
    runFunction .callLocalV0 context interpretation definition arguments
        controlFuel heapFuel store =
      Eval.runFunction context interpretation definition arguments
        controlFuel heapFuel store := by
  unfold runFunction Eval.runFunction enterFunction
  split
  · rfl
  · split
    · rfl
    · simpa only [bind, Except.bind, pure, Except.pure, initialMachine] using
        runMachine_v0 context interpretation controlFuel
          (initialMachine definition arguments heapFuel store)

theorem runMain_v0 (context : Context) (interpretation : Interpretation)
    (program : Program) (controlFuel heapFuel : Nat) :
    runMain .callLocalV0 context interpretation program controlFuel heapFuel =
      Eval.runMain context interpretation program controlFuel heapFuel :=
  runFunction_v0 ..

theorem runMachine_steps {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {controlFuel : Nat} {machine : Machine}
    {result : Result}
    (run : runMachine policy context interpretation controlFuel machine = .ok result) :
    ∃ count, controlFuel = count + result.controlRemaining ∧
      Steps policy context interpretation count machine
        { store := result.store, heapFuel := result.heapRemaining,
          control := .halted result.value } := by
  induction controlFuel generalizing machine with
  | zero =>
      rcases machine with ⟨store, heapFuel, control⟩
      cases control with
      | halted value =>
          simp only [runMachine, Except.ok.injEq] at run
          subst result
          exact ⟨0, by simp, .refl _⟩
      | running frame stack => cases run
  | succ controlFuel ih =>
      rcases machine with ⟨store, heapFuel, control⟩
      cases control with
      | halted value =>
          simp only [runMachine, Except.ok.injEq] at run
          subst result
          exact ⟨0, by simp, .refl _⟩
      | running frame stack =>
          simp only [runMachine] at run
          cases stepped : step policy context interpretation
              { store, heapFuel, control := .running frame stack } with
          | error error => simp [stepped, bind, Except.bind] at run
          | ok next =>
              simp only [stepped, bind, Except.bind] at run
              obtain ⟨count, budget, steps⟩ := ih run
              exact ⟨count + 1, by omega, .cons rfl stepped steps⟩

theorem Steps.runMachine {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {count controlFuel : Nat}
    {before after : Machine}
    (steps : Steps policy context interpretation count before after) :
    Policy.runMachine policy context interpretation (count + controlFuel) before =
      Policy.runMachine policy context interpretation controlFuel after := by
  induction steps with
  | refl => simp only [Nat.zero_add]
  | @cons count before middle after frame stack running head tail ih =>
      rw [Nat.succ_add]
      cases before with
      | mk store heapFuel control =>
          simp only at running
          subst control
          simp only [Policy.runMachine]
          rw [head]
          simp only [bind, Except.bind]
          exact ih

/-- The executable call has one saved caller and a callee with empty credits.
The heap and remaining heap budget stay unchanged at the call transition. -/
theorem suspendCall_iff {context : Context} {machine target : Machine}
    {frame : Frame} {stack : List Continuation} {call : DirectCall} :
    suspendCall context machine frame stack call = .ok target ↔
      ∃ values definition,
        resolveAtoms frame.values call.arguments = .ok values ∧
        call.definition context frame = .ok definition ∧
        values.size = definition.signature.params.size ∧
        definition.blocks.isEmpty = false ∧
        target = { machine with
          control := .running { definition, values }
            (.resume { frame with pc := frame.pc + 1 } :: stack) } := by
  unfold suspendCall
  cases resolved : resolveAtoms frame.values call.arguments with
  | error error => simp [bind, Except.bind]
  | ok values =>
      cases found : call.definition context frame with
      | error error => simp [bind, Except.bind]
      | ok definition =>
          by_cases arity : values.size = definition.signature.params.size
          · cases empty : definition.blocks.isEmpty with
            | true => simp_all [enterFunction, bind, Except.bind]
            | false =>
                simp_all [enterFunction, bind, Except.bind, pure, Except.pure]
                exact eq_comm
          · simp [enterFunction, arity, bind, Except.bind]

theorem Step.classify {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {before after : Machine}
    (stepped : Step policy context interpretation before after) :
    Eval.Step context interpretation before after ∨
      ∃ frame stack call,
        policy = .suspendedCallsV1 ∧ before.control = .running frame stack ∧
        directCall? frame = some call ∧
        suspendCall context before frame stack call = .ok after := by
  cases policy with
  | callLocalV0 => exact .inl stepped
  | suspendedCallsV1 =>
      cases control : before.control with
      | halted value => exact .inl (by simpa [Step, Eval.Step, step, control] using stepped)
      | running frame stack =>
          cases atCall : directCall? frame with
          | none => exact .inl (by simpa [Step, Eval.Step, step, control, atCall] using stepped)
          | some call =>
              exact .inr ⟨frame, stack, call, rfl, rfl, atCall,
                by simpa [Step, step, control, atCall] using stepped⟩

theorem directCall?_atInstruction {frame : Frame} {block : Block}
    {instruction : Instr} (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instructionAt : block.instructions[frame.pc] = instruction) :
    directCall? frame = DirectCall.ofInstruction? instruction := by
  simp [directCall?, blockAt, Array.getElem?_eq_getElem pc, instructionAt]

theorem directCall?_atTerminator {frame : Frame} {block : Block}
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size) : directCall? frame = none := by
  simp [directCall?, blockAt, pc]

/-- Every successful old step is also a successful v1 step with exactly the
same machine. Thus the new policy preserves all existing accepted executions. -/
theorem of_originalStep {context : Context} {interpretation : Interpretation}
    {before after : Machine} (original : Eval.Step context interpretation before after) :
    Step .suspendedCallsV1 context interpretation before after := by
  cases original.classify with
  | halted => rfl
  | instruction blockAt pc instructionAt classified =>
      have original := classified.step blockAt pc instructionAt
      have atCall := directCall?_atInstruction blockAt pc instructionAt
      cases classified <;>
        try { simpa only [Step, Eval.Step, step, atCall,
          DirectCall.ofInstruction?] using original }
      all_goals simp_all [Step, step, DirectCall.ofInstruction?, suspendCall,
        DirectCall.arguments, DirectCall.definition, enterFunction,
        bind, Except.bind, pure, Except.pure]
  | terminator blockAt pc terminatorAt classified =>
      have original := classified.step blockAt pc terminatorAt
      have noCall := directCall?_atTerminator blockAt pc
      simpa only [Step, Eval.Step, step, noCall] using original

theorem of_originalSteps {context : Context} {interpretation : Interpretation}
    {count : Nat} {before after : Machine}
    (original : Eval.Steps context interpretation count before after) :
    Steps .suspendedCallsV1 context interpretation count before after := by
  induction original with
  | refl => exact .refl _
  | cons running head tail ih => exact .cons running (of_originalStep head) ih

theorem of_originalRun {context : Context} {interpretation : Interpretation}
    {controlFuel : Nat} {machine : Machine} {result : Result}
    (original : Eval.runMachine context interpretation controlFuel machine = .ok result) :
    runMachine .suspendedCallsV1 context interpretation controlFuel machine = .ok result := by
  obtain ⟨count, budget, steps⟩ := Eval.runMachine_steps original
  rw [budget, (of_originalSteps steps).runMachine]
  simp only [runMachine]

theorem runFunction_eq_runMachine {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {definition : Function}
    {arguments : Array RVal} {controlFuel heapFuel : Nat} {store : Store}
    (arity : arguments.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    runFunction policy context interpretation definition arguments controlFuel heapFuel store =
      runMachine policy context interpretation controlFuel
        (initialMachine definition arguments heapFuel store) := by
  simp [runFunction, enterFunction, arity, nonempty, bind, Except.bind]

theorem runMain_eq_runMachine {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {program : Program} {controlFuel heapFuel : Nat}
    (arity : program.main.signature.params.size = 0)
    (nonempty : program.main.blocks.isEmpty = false) :
    runMain policy context interpretation program controlFuel heapFuel =
      runMachine policy context interpretation controlFuel
        (initialMachine program.main #[] heapFuel) := by
  apply runFunction_eq_runMachine
  · simpa using arity.symm
  · exact nonempty

theorem Steps.cancelPrefixToHalted {policy : CreditPolicy} {context : Context}
    {interpretation : Interpretation} {prefixCount totalCount : Nat}
    {before middle final : Machine} {store : Store} {heapFuel : Nat} {value : RVal}
    (prefixSteps : Steps policy context interpretation prefixCount before middle)
    (total : Steps policy context interpretation totalCount before final)
    (halted : final = { store, heapFuel, control := .halted value }) :
    ∃ suffixCount, totalCount = prefixCount + suffixCount ∧
      Steps policy context interpretation suffixCount middle final := by
  induction prefixSteps generalizing totalCount final with
  | refl => exact ⟨totalCount, by simp, total⟩
  | @cons prefixCount before prefixMiddle middle frame stack running head tail ih =>
      cases total with
      | refl =>
          have controls : Control.running frame stack = .halted value := by
            rw [← running]
            exact congrArg Machine.control halted
          contradiction
      | cons totalRunning totalHead totalTail =>
          have middleEq := head.deterministic totalHead
          subst middleEq
          obtain ⟨suffixCount, countEq, suffix⟩ := ih totalTail halted
          exact ⟨suffixCount, by omega, suffix⟩

end Ix.Compiler.IxIR2.Eval.Policy
