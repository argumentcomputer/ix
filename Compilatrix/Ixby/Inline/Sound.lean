import Compilatrix.Ixby.Inline.Reflect
import Compilatrix.Ixby.Inline.Initial
import Compilatrix.Ixby.Inline.Optimize

/-! Public successful-execution contracts for the exact checked and selected
images. The unchanged upstream initial state validates every complete input.
These are Ixby-to-Ixby results, independent of the frontend's source boundary. -/

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

theorem Certificate.execute_forward {limits source target protectedPrefix}
    (certificate : Certificate limits source target protectedPrefix)
    {input : Array Value} {fuel : Nat} {output : Value}
    (accepted : execute limits source input fuel = .ok output) :
    execute limits target input fuel = .ok output := by
  cases initialized : initialState limits source input with
  | error error => simp [execute, initialized] at accepted
  | ok state =>
    have candidate : initialState limits target input = .ok state :=
      (certificate.initialState_eq input).symm.trans initialized
    have originalRun : run limits source fuel state = .ok output := by
      simpa [execute, initialized] using accepted
    simpa [execute, candidate] using certificate.relation.run_forward originalRun

theorem Certificate.evaluates_forward {limits source target protectedPrefix}
    (certificate : Certificate limits source target protectedPrefix)
    {input : Array Value} {output : Value} (accepted : Evaluates limits source input output) :
    Evaluates limits target input output := by
  obtain ⟨fuel, accepted⟩ := accepted
  exact ⟨fuel, certificate.execute_forward accepted⟩

theorem Certificate.execute_reflect {limits source target protectedPrefix}
    (certificate : Certificate limits source target protectedPrefix)
    {input : Array Value} {fuel : Nat} {output : Value}
    (accepted : execute limits target input fuel = .ok output) :
    execute (extraStack limits) source input (4 * fuel) = .ok output := by
  cases initialized : initialState limits target input with
  | error error => simp [execute, initialized] at accepted
  | ok state =>
    have original : initialState (extraStack limits) source input = .ok state := by
      rw [initialState_extraStack, certificate.initialState_eq]
      exact initialized
    have within : state.continuation.size ≤ limits.continuations := by
      rw [initialState_continuation initialized]
      simp
    have candidateRun : run limits target fuel state = .ok output := by
      simpa [execute, initialized] using accepted
    simpa [execute, original] using certificate.relation.run_reflect within candidateRun

theorem Certificate.evaluates_reflect {limits source target protectedPrefix}
    (certificate : Certificate limits source target protectedPrefix)
    {input : Array Value} {output : Value} (accepted : Evaluates limits target input output) :
    Evaluates (extraStack limits) source input output := by
  obtain ⟨fuel, accepted⟩ := accepted
  exact ⟨4 * fuel, certificate.execute_reflect accepted⟩

/-- An existing successful baseline specification fixes every successful
optimized result under the original resource profile. -/
theorem Certificate.result_eq {limits source target protectedPrefix}
    (certificate : Certificate limits source target protectedPrefix)
    {input : Array Value} {expected actual : Value}
    (baseline : Evaluates limits source input expected)
    (optimized : Evaluates limits target input actual) : actual = expected :=
  evaluates_deterministic optimized (certificate.evaluates_forward baseline)

theorem Outcome.execute_forward {limits source protectedPrefix}
    (selected : Outcome limits source protectedPrefix)
    {input : Array Value} {fuel : Nat} {output : Value}
    (accepted : execute limits source input fuel = .ok output) :
    execute limits selected.program input fuel = .ok output :=
  selected.certificate.execute_forward accepted

theorem Outcome.execute_reflect {limits source protectedPrefix}
    (selected : Outcome limits source protectedPrefix)
    {input : Array Value} {fuel : Nat} {output : Value}
    (accepted : execute limits selected.program input fuel = .ok output) :
    execute (extraStack limits) source input (4 * fuel) = .ok output :=
  selected.certificate.execute_reflect accepted

end Compilatrix.Ixby.Inline
