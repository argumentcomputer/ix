import Compilatrix.Ixby.Runtime.Execute

/-! Finite paths through the unchanged reference machine. A helper contract
stops at its return control, preserving the caller's continuation. This makes
nested calls compositional without treating intermediate states as admitted
whole-program executions. -/

namespace Compilatrix.Ixby.Runtime.Execution

open Ix.Ixby

inductive Reaches (limits : Limits) (program : Program) : State → State → Prop
  | refl (state) : Reaches limits program state state
  | cons {start next stop} (first : step limits program start = .ok (.next next))
      (rest : Reaches limits program next stop) : Reaches limits program start stop

theorem Reaches.trans {limits : Limits} {program : Program} {a b c : State}
    (left : Reaches limits program a b) (right : Reaches limits program b c) :
    Reaches limits program a c := by
  induction left with
  | refl => exact right
  | cons first _ ih => exact .cons first (ih right)

theorem Reaches.of_step {limits : Limits} {program : Program} {a b : State}
    (one : step limits program a = .ok (.next b)) : Reaches limits program a b :=
  .cons one (.refl b)

theorem reaches_of_chunk {limits : Limits} {program : Program} {fuel count : Nat}
    {start stop : State}
    (execution : runChunk limits program fuel start count = .ok (.inr stop, count + fuel)) :
    Reaches limits program start stop := by
  induction fuel generalizing start count with
  | zero =>
    simp only [runChunk, Except.ok.injEq, Prod.mk.injEq, Sum.inr.injEq] at execution
    exact execution.1 ▸ .refl start
  | succ fuel ih =>
    cases first : step limits program start with
    | error error => simp [runChunk, first, bind, Except.bind] at execution
    | ok transition =>
      cases transition with
      | halted value => simp [runChunk, first, bind, Except.bind, pure, Except.pure] at execution
      | next next =>
        apply Reaches.cons first
        apply ih (count := count + 1)
        simpa [runChunk, first, bind, Except.bind, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using execution

/-- Every finite path composes with the ordinary fuelled evaluator. -/
theorem Reaches.run {limits : Limits} {program : Program} {start stop : State}
    (path : Reaches limits program start stop) {value : Value} {fuel : Nat}
    (rest : run limits program fuel stop = .ok value) :
    ∃ total, run limits program total start = .ok value := by
  induction path with
  | refl => exact ⟨fuel, rest⟩
  | cons first _ ih =>
    obtain ⟨total, accepted⟩ := ih rest
    exact ⟨total + 1, by simpa [Ix.Ixby.run, first] using accepted⟩

def frameState (id : FunctionId) (block : BlockId) (locals : Array Value)
    (continuation : Array Continuation) : State :=
  { control := .eval { function := id, block, locals }, continuation }

def returned (value : Value) (continuation : Array Continuation) : State :=
  { control := .ret value, continuation }

theorem Reaches.halts {limits : Limits} {program : Program} {start : State} {value : Value}
    (path : Reaches limits program start (returned value #[])) :
    ∃ fuel, Ix.Ixby.run limits program fuel start = .ok value :=
  path.run (fuel := 1) (by rfl)

/-- Whole-program execution requires the evaluator's own validated initial
state, in addition to the compositional path through helper code. -/
theorem Reaches.evaluates {limits : Limits} {program : Program} {input : Array Value}
    {start : State} {value : Value}
    (path : Reaches limits program start (returned value #[]))
    (initial : initialState limits program input = .ok start) :
    Evaluates limits program input value := by
  obtain ⟨fuel, execution⟩ := path.halts
  exact ⟨fuel, by simpa [execute, initial] using execution⟩

/-- Returning to an existing caller restores its saved frame and appends the
result. The ordinary transfer check still checks the resumed block and locals. -/
theorem resume {limits : Limits} {program : Program} (value : Value)
    (continuation : Array Continuation) (saved resumed : Frame)
    (transfer : saved.transfer limits program saved.block #[value] = .ok resumed) :
    Reaches limits program (returned value (continuation.push (.resume saved)))
      { control := .eval resumed, continuation } := by
  apply Reaches.of_step
  simp [step, returned, transfer, bind, Except.bind, pure, Except.pure]

end Compilatrix.Ixby.Runtime.Execution
