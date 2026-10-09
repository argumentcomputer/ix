import Compilatrix.Cfg.Rc.Proof.Native.ReturnedObservation
import Compilatrix.Lir.Proof.Run

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec
open Compilatrix.Rt.Rc.Procs

/-- A concrete evaluator result retains the complete physical return witness,
including its heap, source denotation, exact memory, and complete-tree
readback interface. -/
def ReturnedOutput (P : Program) (pairs : List (Nat × Cfg.Fun)) (lp : Lir.Program)
    (origin : Own.Heap) (addresses : AddressMap) (external : Nat → Nat)
    (context base limit : Lir.Word) (regionBytes : Nat) (logical : Fir.Val)
    (output : List Lir.Word × X86.Memory) : Prop :=
  ∃ returned : Returned P pairs lp origin addresses external context base limit regionBytes logical,
    output = ([returned.word], returned.memory)

variable {P : Program} {pairs : List (Nat × Cfg.Fun)} {lp : Lir.Program}
  {origin : Own.Heap} {addresses : AddressMap} {external : Nat → Nat}
  {context base limit : Lir.Word} {regionBytes : Nat}
  {words : List Lir.Word} {memory : X86.Memory} {initial : Lir.State}

theorem ResultAt.eval_forward
    (initialized : Lir.State.initial lp words memory context = some initial)
    {clock : Nat} {result : Sem.Result Fir.Val}
    (execution : ResultAt P pairs lp origin addresses external context base limit regionBytes
      clock initial [] result) (regular : result ≠ .timeout) :
    ∃ targetClock, Sem.Result.Refines
      (ReturnedOutput P pairs lp origin addresses external context base limit regionBytes)
      result (Lir.eval lp targetClock words memory context) := by
  have runs := Lir.runs_eval initialized
  have failed : Sem.Fails (Lir.semStep lp) initial →
      ∃ targetClock, Sem.Result.Refines
        (ReturnedOutput P pairs lp origin addresses external context base limit regionBytes)
        result (Lir.eval lp targetClock words memory context) := by
    intro failure
    obtain ⟨targetClock, resource, reached⟩ := Sem.Forward.reaches_of_fails failure
    refine ⟨targetClock, ?_⟩
    rw [runs.eq reached]
    exact .resource resource
  cases result with
  | ok logical =>
    rcases execution with ⟨returned, cost, trace⟩ | failure
    · refine ⟨cost, ?_⟩
      rw [runs.eq (returned.finish trace)]
      exact .ok ⟨returned, rfl⟩
    · exact failed failure
  | timeout => exact False.elim (regular rfl)
  | resource resource => exact failed execution
  | trap =>
    rcases execution with ⟨cost, final, trace, trapped⟩ | failure
    · have finalStep := Lir.semStep_trap.2 trapped
      have reached : Sem.Reaches (Lir.semStep lp) initial cost .trap :=
        .of_final trace (finalStep ▸ .trap) (Nat.le_refl _)
      refine ⟨cost, ?_⟩
      rw [runs.eq reached]
      exact .trap
    · exact failed failure
  | stuck => exact ⟨0, .stuck⟩

theorem ResultAt.eval_timeout
    (initialized : Lir.State.initial lp words memory context = some initial)
    {clock : Nat}
    (execution : ResultAt P pairs lp origin addresses external context base limit regionBytes
      clock initial [] .timeout) :
    Lir.eval lp clock words memory context = .timeout ∨
      ∃ resource, Lir.eval lp clock words memory context = .resource resource := by
  rcases execution with timeout | ⟨resource, failure⟩
  · exact .inl ((Lir.runs_eval initialized).eq timeout)
  · exact .inr ⟨resource, (Lir.runs_eval initialized).eq failure⟩

/-- Actual entry charges the source once before its body; native initial
binding is free. The resulting clock map is successor, and the executable
Lir evaluator retains the complete returned physical witness. -/
theorem resultAt_eval_sim_succ {source : Nat → Sem.Result Fir.Val}
    (zero : source 0 = .timeout)
    (physical : ∀ clock, ∃ initial,
      Lir.State.initial lp words memory context = some initial ∧
      ResultAt P pairs lp origin addresses external context base limit regionBytes
        clock initial [] (source (clock + 1))) :
    Sem.Sim (ReturnedOutput P pairs lp origin addresses external context base limit regionBytes)
      Nat.succ source (fun clock => Lir.eval lp clock words memory context) where
  forward clock regular := by
    cases clock with
    | zero => exact False.elim (regular zero)
    | succ clock =>
      obtain ⟨initial, initialized, execution⟩ := physical clock
      exact ResultAt.eval_forward initialized execution regular
  timeout clock timedOut := by
    obtain ⟨initial, initialized, execution⟩ := physical clock
    rw [timedOut] at execution
    exact ResultAt.eval_timeout initialized execution




end Compilatrix.Cfg.Rc.Native.Spec
