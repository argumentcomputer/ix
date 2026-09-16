import CompilatrixTests.Aiur.CounterAnalysis.Fixtures
import Compilatrix.Aiur.CounterAnalysis

/-! Kernel regressions for inferred choices and arbitrary-input consequences.
No native decision procedure is used to certify analyzer behavior. -/

namespace CompilatrixTests.Aiur.CounterAnalysis

open Compilatrix.Aiur
open Compilatrix.Aiur.CounterAnalysis
open Compilatrix.Aiur.Static (counterObservation CounterStep)
open _root_.Aiur (G)
open _root_.Aiur.Bytecode
open OracleEval (Values)
open CompilatrixTests.Aiur.Execution (mkFunction)

private theorem input_found (increasing : Bool) :
    UnitCounter.find? 0 (mkFunction 1 (Static.inputBody 0 increasing)) =
      some ⟨.input, 0, if increasing then 1 else 0 - 1⟩ := by
  cases increasing <;> cbv

private theorem output_found (increasing : Bool) :
    UnitCounter.find? 0 (mkFunction 1 (Static.outputBody 0 increasing)) =
      some ⟨.output, 0, if increasing then 1 else 0 - 1⟩ := by
  cases increasing <;> cbv

private theorem input_step (increasing : Bool) (parent child : G) {outputs childOutputs : Values}
    {demands : List Message} {advice : List OracleEval.AdviceObservation}
    (body : OracleEval.Body (Static.inputProgram increasing) 0 [parent] outputs demands advice)
    (demanded : .function 0 [child] childOutputs ∈ demands) :
    child = parent + (if increasing then 1 else 0 - 1) := by
  have relation := find_body (by rfl) (input_found increasing) body [child] childOutputs demanded
  simpa [counterObservation, CounterStep] using relation

private theorem output_step (increasing : Bool) (parent child : G) {inputs childInputs : Values}
    {demands : List Message} {advice : List OracleEval.AdviceObservation}
    (body : OracleEval.Body (Static.outputProgram increasing) 0 inputs [parent] demands advice)
    (demanded : .function 0 childInputs [child] ∈ demands) :
    parent = child + (if increasing then 1 else 0 - 1) := by
  have relation := find_body (by rfl) (output_found increasing) body childInputs [child] demanded
  simpa [counterObservation, CounterStep] using relation

theorem input_increment (parent child : G) {outputs childOutputs : Values}
    {demands : List Message} {advice : List OracleEval.AdviceObservation}
    (body : OracleEval.Body (Static.inputProgram true) 0 [parent] outputs demands advice)
    (demanded : .function 0 [child] childOutputs ∈ demands) : child = parent + 1 :=
  input_step true parent child body demanded

theorem input_decrement (parent child : G) {outputs childOutputs : Values}
    {demands : List Message} {advice : List OracleEval.AdviceObservation}
    (body : OracleEval.Body (Static.inputProgram false) 0 [parent] outputs demands advice)
    (demanded : .function 0 [child] childOutputs ∈ demands) : child = parent - 1 := by
  simpa only [Bool.false_eq_true, ↓reduceIte, G.add_neg_one_eq_sub] using input_step false parent child body demanded

theorem output_increment (parent child : G) {inputs childInputs : Values}
    {demands : List Message} {advice : List OracleEval.AdviceObservation}
    (body : OracleEval.Body (Static.outputProgram true) 0 inputs [parent] demands advice)
    (demanded : .function 0 childInputs [child] ∈ demands) : parent = child + 1 :=
  output_step true parent child body demanded

theorem output_decrement (parent child : G) {inputs childInputs : Values}
    {demands : List Message} {advice : List OracleEval.AdviceObservation}
    (body : OracleEval.Body (Static.outputProgram false) 0 inputs [parent] demands advice)
    (demanded : .function 0 childInputs [child] ∈ demands) : parent = child - 1 := by
  simpa only [Bool.false_eq_true, ↓reduceIte, G.add_neg_one_eq_sub] using output_step false parent child body demanded

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
theorem algebra_found : UnitCounter.find? 0 algebraFunction = some ⟨.input, 1, 1⟩ := by cbv

theorem algebra_all_self_calls {inputs outputs childInputs childOutputs : Values}
    {demands : List Message} {advice : List OracleEval.AdviceObservation}
    (body : OracleEval.Body algebraProgram 0 inputs outputs demands advice)
    (demanded : .function 0 childInputs childOutputs ∈ demands) :
    ∃ parent child, inputs[1]? = some parent ∧ childInputs[1]? = some child ∧ child = parent + 1 := by
  simpa [counterObservation, CounterStep] using find_body (by rfl) algebra_found body _ _ demanded

theorem marker_found : UnitCounter.find? 0 markerFunction = some ⟨.output, 1, 1⟩ := by cbv

theorem marker_all_self_calls {inputs outputs childInputs childOutputs : Values}
    {demands : List Message} {advice : List OracleEval.AdviceObservation}
    (body : OracleEval.Body markerProgram 0 inputs outputs demands advice)
    (demanded : .function 0 childInputs childOutputs ∈ demands) :
    ∃ parent child, outputs[1]? = some parent ∧ childOutputs[1]? = some child ∧ parent = child + 1 := by
  simpa [counterObservation, CounterStep] using find_body (by rfl) marker_found body _ _ demanded

theorem short_leaf_found : UnitCounter.find? 0 shortLeafFunction = some ⟨.output, 1, 1⟩ := by cbv

theorem short_leaf_body : OracleEval.Body shortLeafProgram 0 [7] [0] []
    [⟨.gInverse 7, [1]⟩] := by
  refine ⟨{}, [[1]], ⟨.returned 2 [0], [], [⟨.gInverse 7, [1]⟩]⟩, ?_, rfl, rfl, rfl⟩
  cbv

theorem hints_rejected : UnitCounter.find? 0 hintFunction = none := by cbv
theorem nonlinear_rejected : UnitCounter.find? 0 nonlinearFunction = none := by cbv
theorem repeated_outputs_rejected : UnitCounter.find? 0 repeatedOutputFunction = none := by cbv
theorem missing_argument_rejected : UnitCounter.find? 0 missingArgumentFunction = none := by cbv
theorem missing_register_rejected : UnitCounter.find? 0 missingRegisterFunction = none := by cbv
theorem no_outputs_rejected : UnitCounter.find? 0 noOutputsFunction = none := by cbv
theorem bad_branch_rejected : UnitCounter.find? 0 badBranchFunction = none := by cbv
theorem yield_rejected : UnitCounter.find? 0 yieldFunction = none := by cbv
theorem continuation_rejected : UnitCounter.find? 0 continuationFunction = none := by cbv

end CompilatrixTests.Aiur.CounterAnalysis
