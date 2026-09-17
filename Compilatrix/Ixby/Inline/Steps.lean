import Compilatrix.Ixby.Inline.Syntax

/-! Exact logical step counts, independent of the host executor. A path contains
only successful nonterminal transitions, so it cannot hide fuel exhaustion. -/

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

inductive Steps (limits : Limits) (program : Program) : Nat → State → State → Prop
  | refl (state) : Steps limits program 0 state state
  | cons {count start next stop}
      (first : step limits program start = .ok (.next next))
      (rest : Steps limits program count next stop) : Steps limits program (count + 1) start stop

theorem Steps.run {limits program count start stop}
    (path : Steps limits program count start stop) (fuel : Nat) :
    run limits program (count + fuel) start = run limits program fuel stop := by
  induction path with
  | refl => simp
  | cons first rest ih => simpa only [Nat.succ_add, Ix.Ixby.run, first] using ih

theorem Steps.trans {limits program first second a b c}
    (left : Steps limits program first a b) (right : Steps limits program second b c) :
    Steps limits program (first + second) a c := by
  induction left with
  | refl => simpa using right
  | cons step rest ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.cons step (ih right)

theorem run_after_step {limits program state next output fuel}
    (first : step limits program state = .ok (.next next))
    (accepted : run limits program fuel state = .ok output) :
    ∃ rest, fuel = rest + 1 ∧ run limits program rest next = .ok output := by
  cases fuel with
  | zero => simp [run] at accepted
  | succ rest => exact ⟨rest, rfl, by simpa [run, first] using accepted⟩

theorem run_after_steps {limits program count state next output fuel}
    (path : Steps limits program count state next)
    (accepted : run limits program fuel state = .ok output) :
    ∃ rest, fuel = count + rest ∧ run limits program rest next = .ok output := by
  induction path generalizing fuel with
  | refl => exact ⟨fuel, by omega, accepted⟩
  | cons first path ih =>
    obtain ⟨remaining, total, afterFirst⟩ := run_after_step first accepted
    obtain ⟨rest, count, afterRest⟩ := ih afterFirst
    exact ⟨rest, by omega, afterRest⟩

end Compilatrix.Ixby.Inline
