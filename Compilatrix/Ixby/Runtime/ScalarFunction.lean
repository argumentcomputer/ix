import Compilatrix.Ixby.Runtime.ScalarLaws

/-! Execution contracts for scalar functions in an actual program. Acceptance
checks exact code, entry, arity, and constructor declarations. No theorem about
a separately assembled example is substituted for the accepted function. -/

namespace Compilatrix.Ixby.Runtime.ScalarFunction

open Ix.Ixby

def direct (arity : Nat) (operation : Primitive) : Function := {
  arity
  blocks := #[
    { locals := arity, instruction := .letOp
        (.primitive operation ((List.range arity).map Operand.local)) 1 },
    { locals := arity + 1, instruction := .ret (.local arity) }] }

def projection (operation : Primitive) (box : Constructor) : Function := {
  arity := 1
  blocks := #[
    { locals := 1, instruction := .letOp (.primitive operation [.local 0]) 1 },
    { locals := 2, instruction := .letOp (.construct box [.local 1]) 2 },
    { locals := 3, instruction := .ret (.local 2) }] }

structure Checked (program : Program) (id : FunctionId) (expected : Function) : Type where
  code : program.getFunction id = .ok expected

private theorem function_eq {a b : Function}
    (arity : a.arity = b.arity) (entry : a.entry = b.entry) (blocks : a.blocks = b.blocks) :
    a = b := by
  cases a; cases b; simp_all

/-- Successful matching retains propositional equality evidence. The checker
does not trust derived Boolean equality or a digest of the function body. -/
def check (program : Program) (id : FunctionId) (expected : Function) :
    Except String (Checked program id expected) := do
  match found : program.getFunction id with
  | .error _ => throw s!"missing scalar runtime function {id}"
  | .ok actual =>
    if arity : actual.arity = expected.arity then
      if entry : actual.entry = expected.entry then
        if blocks : actual.blocks = expected.blocks then
          return ⟨(function_eq arity entry blocks) ▸ found⟩
        else throw s!"scalar runtime blocks differ: {id}"
      else throw s!"scalar runtime entry differs: {id}"
    else throw s!"scalar runtime arity differs: {id}"

def start (id : FunctionId) (args : Array Value) : State :=
  { control := .eval { function := id, block := 0, locals := args } }

theorem Checked.unary {program : Program} {id : FunctionId} {operation : Primitive}
    (checked : Checked program id (direct 1 operation))
    (limits : Limits) (room : 2 ≤ limits.locals) (arg result : Value)
    (primitive : operation.eval limits [arg] = .ok result) :
    run limits program 3 (start id #[arg]) = .ok result := by
  simp [run, step, stepEval, Frame.check, checked.code, direct, start,
    evalOp, Frame.readOperands, Frame.read, Frame.transfer, primitive,
    List.range_succ, Nat.not_lt.mpr room, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem Checked.binary {program : Program} {id : FunctionId} {operation : Primitive}
    (checked : Checked program id (direct 2 operation))
    (limits : Limits) (room : 3 ≤ limits.locals) (a b result : Value)
    (primitive : operation.eval limits [a, b] = .ok result) :
    run limits program 3 (start id #[a, b]) = .ok result := by
  simp [run, step, stepEval, Frame.check, checked.code, direct, start,
    evalOp, Frame.readOperands, Frame.read, Frame.transfer, primitive,
    List.range_succ, Nat.not_lt.mpr room, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem Checked.project {program : Program} {id : FunctionId} {operation : Primitive}
    {box : Constructor} (checked : Checked program id (projection operation box))
    (limits : Limits) (room : 3 ≤ limits.locals) (arg result : Value) (layout : CtorId)
    (constructor : program.getConstructor box = .ok { id := layout, fields := 1 })
    (primitive : operation.eval limits [arg] = .ok result) :
    run limits program 4 (start id #[arg]) = .ok (.ctor layout #[result]) := by
  simp [run, step, stepEval, Frame.check, checked.code, projection, start,
    evalOp, Frame.readOperands, Frame.read, Frame.transfer, primitive, constructor,
    Nat.not_lt.mpr room, show ¬limits.locals < 1 by omega,
    show ¬limits.locals < 2 by omega, bind, Except.bind, pure, Except.pure]

/-- A checked whole-program initial state connects these local contracts to
authenticated execution. Admission and input validation are not bypassed. -/
theorem evaluates_of_initial {limits : Limits} {program : Program} {input : Array Value}
    {result : Value} {fuel : Nat}
    (initial : initialState limits program input = .ok (start program.entry input))
    (execution : run limits program fuel (start program.entry input) = .ok result) :
    Evaluates limits program input result := by
  exact ⟨fuel, by simpa [execute, initial] using execution⟩

theorem Checked.unary_evaluates {program : Program} {id : FunctionId} {operation : Primitive}
    (checked : Checked program id (direct 1 operation))
    (limits : Limits) (room : 2 ≤ limits.locals) (arg result : Value)
    (entry : program.entry = id) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [arg] = .ok ())
    (primitive : operation.eval limits [arg] = .ok result) :
    Evaluates limits program #[arg] result := by
  apply evaluates_of_initial (fuel := 3)
  · simp [initialState, admitted, enter, entry, checked.code, direct, Frame.check, inputs,
      start, show ¬limits.locals < 1 by omega, bind, Except.bind, pure, Except.pure]
  · simpa [entry] using checked.unary limits room arg result primitive

theorem Checked.binary_evaluates {program : Program} {id : FunctionId} {operation : Primitive}
    (checked : Checked program id (direct 2 operation))
    (limits : Limits) (room : 3 ≤ limits.locals) (a b result : Value)
    (entry : program.entry = id) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [a, b] = .ok ())
    (primitive : operation.eval limits [a, b] = .ok result) :
    Evaluates limits program #[a, b] result := by
  apply evaluates_of_initial (fuel := 3)
  · simp [initialState, admitted, enter, entry, checked.code, direct, Frame.check, inputs,
      start, show ¬limits.locals < 2 by omega, bind, Except.bind, pure, Except.pure]
  · simpa [entry] using checked.binary limits room a b result primitive

theorem Checked.project_evaluates {program : Program} {id : FunctionId} {operation : Primitive}
    {box : Constructor} (checked : Checked program id (projection operation box))
    (limits : Limits) (room : 3 ≤ limits.locals) (arg result : Value) (layout : CtorId)
    (constructor : program.getConstructor box = .ok { id := layout, fields := 1 })
    (entry : program.entry = id) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [arg] = .ok ())
    (primitive : operation.eval limits [arg] = .ok result) :
    Evaluates limits program #[arg] (.ctor layout #[result]) := by
  apply evaluates_of_initial (fuel := 4)
  · simp [initialState, admitted, enter, entry, checked.code, projection, Frame.check, inputs,
      start, show ¬limits.locals < 1 by omega, bind, Except.bind, pure, Except.pure]
  · simpa [entry] using checked.project limits room arg result layout constructor primitive

end Compilatrix.Ixby.Runtime.ScalarFunction
