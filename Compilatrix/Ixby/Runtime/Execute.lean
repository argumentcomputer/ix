import Ix.Ixby

/-! Resumable reference execution for long native tests. Chunking changes only
when the host can report progress; `runChunk_run` equates it with the upstream
reference evaluator for the same total fuel. -/

namespace Compilatrix.Ixby.Runtime

open Ix.Ixby

def runChunk (limits : Limits) (program : Program) :
    Nat → State → Nat → Except Error (Sum Value State × Nat)
  | 0, state, count => .ok (.inr state, count)
  | fuel + 1, state, count => do
    match ← step limits program state with
    | .halted value => return (.inl value, count + 1)
    | .next state => runChunk limits program fuel state (count + 1)

theorem runChunk_run (limits : Limits) (program : Program) (fuel extra : Nat)
    (state : State) (count : Nat) :
    ((runChunk limits program fuel state count).bind fun (result, _) =>
      match result with
      | .inl value => .ok value
      | .inr next => run limits program extra next) =
      run limits program (fuel + extra) state := by
  induction fuel generalizing state count with
  | zero => simp [runChunk, Except.bind]
  | succ fuel ih =>
    cases hs : step limits program state with
    | error error => simp [runChunk, run, hs, Nat.succ_add, bind, Except.bind]
    | ok transition =>
      cases transition with
      | halted value => simp [runChunk, run, hs, Nat.succ_add, bind, Except.bind, pure, Except.pure]
      | next next => simpa [runChunk, run, hs, Nat.succ_add, bind, Except.bind] using ih next (count + 1)

end Compilatrix.Ixby.Runtime
