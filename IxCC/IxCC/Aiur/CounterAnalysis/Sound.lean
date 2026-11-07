import IxCC.Aiur.CounterAnalysis.Search
import IxCC.Aiur.Static.CounterProofs

/-! Universal soundness of the pinned unit-counter analyzer for the exact
local replay relation. This does not assume an honest advice oracle and does
not identify local replay with satisfying keyed AIR rows. -/

namespace IxCC.Aiur.CounterAnalysis

open _root_.IxCC.Vendor.Aiur (G)
open _root_.IxCC.Vendor.Aiur.Bytecode
open OracleEval (Values)

theorem find_runFunction {toplevel : Toplevel} {self : Nat} {function : Function}
    {candidate : UnitCounter.Certificate} {inputs : Values} {replies : List Values}
    {limits : OracleEval.Limits} {result : OracleEval.Result}
    (lookup : toplevel.functions[self]? = some function)
    (found : UnitCounter.find? self function = some candidate)
    (success : OracleEval.runFunction toplevel limits self inputs replies = .ok result) :
    CounterRelation self candidate inputs result.outputs result.demands := by
  have valid := find_spec found
  exact check_runFunction lookup valid.checked valid.inputColumn success

/-- A candidate returned by the pinned analyzer governs every constrained
self-call in every successful body, for all inputs, outputs, and advice. -/
theorem find_body {toplevel : Toplevel} {self : Nat} {function : Function}
    {candidate : UnitCounter.Certificate} {inputs outputs : Values} {demands : List Message}
    {advice : List OracleEval.AdviceObservation}
    (lookup : toplevel.functions[self]? = some function)
    (found : UnitCounter.find? self function = some candidate)
    (body : OracleEval.Body toplevel self inputs outputs demands advice) :
    CounterRelation self candidate inputs outputs demands := by
  have valid := find_spec found
  exact check_body lookup valid.checked valid.inputColumn body

theorem find_body_normalized {toplevel : Toplevel} {self : Nat} {function : Function}
    {candidate : UnitCounter.Certificate} {inputs outputs childInputs childOutputs : Values} {demands : List Message}
    {advice : List OracleEval.AdviceObservation}
    (lookup : toplevel.functions[self]? = some function)
    (found : UnitCounter.find? self function = some candidate)
    (body : OracleEval.Body toplevel self inputs outputs demands advice)
    (demanded : .function self childInputs childOutputs ∈ demands) :
    Static.normalizedCounter candidate childInputs childOutputs =
      Static.normalizedCounter candidate inputs outputs + 1 := by
  obtain ⟨parent, child, parentRead, childRead, step⟩ := find_body lookup found body _ _ demanded
  exact Static.normalizedCounter_step candidate inputs outputs childInputs childOutputs parent child
    parentRead childRead (find_spec found).unit step

/-- A demanded self-call with the same selected counter observation cannot
occur in an analyzed body, even if its other inputs or outputs differ. -/
theorem find_body_counter_ne {toplevel : Toplevel} {self : Nat} {function : Function}
    {candidate : UnitCounter.Certificate} {inputs outputs childInputs childOutputs : Values} {demands : List Message}
    {advice : List OracleEval.AdviceObservation}
    (lookup : toplevel.functions[self]? = some function)
    (found : UnitCounter.find? self function = some candidate)
    (body : OracleEval.Body toplevel self inputs outputs demands advice)
    (demanded : .function self childInputs childOutputs ∈ demands) :
    Static.normalizedCounter candidate childInputs childOutputs ≠ Static.normalizedCounter candidate inputs outputs := by
  have step := find_body_normalized lookup found body demanded
  intro equal
  have unchanged : (Static.normalizedCounter candidate inputs outputs).n =
      ((Static.normalizedCounter candidate inputs outputs).n + 1) % _root_.IxCC.Vendor.Aiur.gSize.toNat := by
    have := congrArg G.n (equal.symm.trans step)
    simpa only [G.add_one_n] using this
  exact UnitCounter.Proofs.add_mod_ne_self (Field.value_lt _) (by decide) (by decide) unchanged.symm

/-- A nonempty chain of actual analyzed bodies cannot return to the same
inputs and outputs in fewer steps than the field characteristic. -/
theorem find_body_no_short_cycle {toplevel : Toplevel} {self : Nat} {function : Function}
    {candidate : UnitCounter.Certificate} {length : Nat}
    (lookup : toplevel.functions[self]? = some function)
    (found : UnitCounter.find? self function = some candidate)
    (inputs outputs : Nat → Values) (demands : Nat → List Message)
    (advice : Nat → List OracleEval.AdviceObservation)
    (bodies : ∀ index, index < length → OracleEval.Body toplevel self (inputs index) (outputs index) (demands index) (advice index))
    (edges : ∀ index, index < length → .function self (inputs (index + 1)) (outputs (index + 1)) ∈ demands index)
    (positive : 0 < length) (short : length < _root_.IxCC.Vendor.Aiur.gSize.toNat)
    (sameInputs : inputs length = inputs 0) (sameOutputs : outputs length = outputs 0) : False := by
  let value := fun index => Static.normalizedCounter candidate (inputs index) (outputs index)
  have advances : ∀ index, index < length → value (index + 1) = value index + 1 :=
    fun index bounded => find_body_normalized lookup found (bodies index bounded) (edges index bounded)
  exact UnitCounter.Proofs.no_short_field_cycle value positive short advances
    (by simp only [value, sameInputs, sameOutputs])

end IxCC.Aiur.CounterAnalysis
