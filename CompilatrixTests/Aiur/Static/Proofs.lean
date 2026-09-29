import CompilatrixTests.Aiur.Static.Fixtures
import CompilatrixTests.Aiur.Execution.Proofs

/-! Public executions constructed from ordinary rank/replay data, with no
handwritten static certificate. Concrete acceptance uses kernel reduction. -/

namespace CompilatrixTests.Aiur.Static

open Compilatrix.Aiur
open OracleEval (unrestrictedAdvice)
open _root_.Aiur.Bytecode (Toplevel)

private def accepted {toplevel : Toplevel} {oracle : OracleEval.AdviceOracle} {trace : Trace}
    (result : Except Static.Error (Static.CheckedTrace toplevel oracle trace))
    (success : result.isOk = true) : Static.CheckedTrace toplevel oracle trace :=
  match checked : result with
  | .ok value => value
  | .error _ => by simp [Except.isOk, Except.toBool] at success

private theorem input_inferred (increasing : Bool) :
    Static.inferPlans (inputProgram increasing) = .ok #[
      ⟨⟨0, false⟩, true, 1, some ⟨.input, 0, if increasing then 1 else 0 - 1⟩⟩] := by
  cases increasing <;> cbv

private theorem output_inferred (increasing : Bool) :
    Static.inferPlans (outputProgram increasing) = .ok #[
      ⟨⟨0, false⟩, true, 1, some ⟨.output, 0, if increasing then 1 else 0 - 1⟩⟩] := by
  cases increasing <;> cbv

-- Lean v4.34.0 `cbv` builds an ill-typed `ite_true` proof for a literal `if True`;
-- rewriting it first keeps `cbv` on its well-typed path.
private theorem input_accepted (increasing : Bool) :
    (certify (inputProgram increasing) (inputTrace increasing) #[0, 0, 0] inputReplies).isOk = true := by
  cases increasing <;>
    (unfold certify Static.validate Static.prepare
     simp only [Static.prepareChecked_ok ({} : Wire.CheckLimits) _ _ (by cbv) _ (input_inferred _),
       ite_true]
     cbv)

private theorem output_accepted (increasing : Bool) :
    (certify (outputProgram increasing) (outputTrace increasing) #[0, 0, 0]
      (outputReplies increasing)).isOk = true := by
  cases increasing <;>
    (unfold certify Static.validate Static.prepare
     simp only [Static.prepareChecked_ok ({} : Wire.CheckLimits) _ _ (by cbv) _ (output_inferred _),
       ite_true]
     cbv)

private theorem mixed_accepted : (certify mixedProgram mixedTrace mixedRanks mixedReplies).isOk = true := by
  have plans : Static.inferPlans mixedProgram = .ok #[
    ⟨⟨0, true⟩, true, 1, none⟩,
    ⟨⟨0, false⟩, true, 1, some ⟨.input, 0, 0 - 1⟩⟩] := by cbv
  unfold certify Static.validate Static.prepare
  simp only [Static.prepareChecked_ok ({} : Wire.CheckLimits) _ _ (by cbv) _ plans]
  cbv

theorem input_decrement_exec :
    BytecodeEvalW (inputProgram false) (Memory.heap (Memory.cells (inputTrace false)))
      unrestrictedAdvice 0 [2] [0] :=
  (accepted (certify (inputProgram false) (inputTrace false) #[0, 0, 0] inputReplies) (input_accepted false)).public_bytecode
    (by decide)

theorem input_increment_exec :
    BytecodeEvalW (inputProgram true) (Memory.heap (Memory.cells (inputTrace true)))
      unrestrictedAdvice 0 [0 - 2] [0] :=
  (accepted (certify (inputProgram true) (inputTrace true) #[0, 0, 0] inputReplies) (input_accepted true)).public_bytecode
    (by decide)

theorem output_increment_exec :
    BytecodeEvalW (outputProgram true) (Memory.heap (Memory.cells (outputTrace true)))
      unrestrictedAdvice 0 [7] [2] :=
  (accepted (certify (outputProgram true) (outputTrace true) #[0, 0, 0] (outputReplies true)) (output_accepted true)).public_bytecode
    (by decide)

theorem output_decrement_exec :
    BytecodeEvalW (outputProgram false) (Memory.heap (Memory.cells (outputTrace false)))
      unrestrictedAdvice 0 [7] [0 - 2] :=
  (accepted (certify (outputProgram false) (outputTrace false) #[0, 0, 0] (outputReplies false)) (output_accepted false)).public_bytecode
    (by decide)

theorem mixed_ranked_exec : BytecodeEvalW mixedProgram (Memory.heap (Memory.cells mixedTrace))
    unrestrictedAdvice 0 [2] [0] :=
  (accepted (certify mixedProgram mixedTrace mixedRanks mixedReplies) mixed_accepted).public_bytecode (by decide)

theorem mixed_counter_exec : BytecodeEvalW mixedProgram (Memory.heap (Memory.cells mixedTrace))
    unrestrictedAdvice 1 [2] [0] :=
  (accepted (certify mixedProgram mixedTrace mixedRanks mixedReplies) mixed_accepted).public_bytecode (by decide)

theorem duplicate_providers_exec : BytecodeEvalW fallbackProgram (Memory.heap (Memory.cells duplicateTrace))
    unrestrictedAdvice 0 [2] [0] :=
  (accepted (certify fallbackProgram duplicateTrace #[0, 1, 1, 2] duplicateReplies) (by cbv)).public_bytecode
    (by decide)

theorem zero_weight_parent_exec : BytecodeEvalW (inputProgram false) (Memory.heap (Memory.cells zeroJunkTrace))
    unrestrictedAdvice 0 [2] [0] :=
  (accepted (certify (inputProgram false) zeroJunkTrace #[0, 0, 0, 0] zeroJunkReplies) (by
    unfold certify Static.validate Static.prepare
    simp only [Static.prepareChecked_ok ({} : Wire.CheckLimits) _ _ (by cbv) _ (input_inferred false)]
    cbv)).public_bytecode
    (by decide)

theorem ranked_mutual_exec : BytecodeEvalW Execution.rankedProgram
    (Memory.heap (Memory.cells Execution.rankedTrace)) unrestrictedAdvice 0 [2] [0] :=
  (accepted (certify Execution.rankedProgram Execution.rankedTrace #[0, 1, 2] inputReplies) (by cbv)).public_bytecode
    (by decide)

theorem ordered_call_exec : BytecodeEvalW orderedProgram (Memory.heap (Memory.cells (Execution.callTrace 42)))
    unrestrictedAdvice 0 [20, 22] [42] :=
  (accepted (certify orderedProgram (Execution.callTrace 42) #[0, 0] #[[[42]], []]) (by
    have plans : Static.inferPlans orderedProgram = .ok #[
      ⟨⟨0, false⟩, true, 2, none⟩, ⟨⟨1, false⟩, true, 2, none⟩] := by cbv
    unfold certify Static.validate Static.prepare
    simp only [Static.prepareChecked_ok ({} : Wire.CheckLimits) _ _ (by cbv) _ plans]
    cbv)).public_bytecode
    (by decide)

theorem pointer_seven_exec : BytecodeEvalW Execution.storeProgram
    (Memory.heap (Memory.cells Execution.storeTrace)) unrestrictedAdvice 0 [42] [7] :=
  (accepted (certify Execution.storeProgram Execution.storeTrace #[0, 0] #[[[7]], []]) (by cbv)).public_bytecode
    (by decide)

theorem self_loop_no_checked (toplevel : Toplevel) (oracle : OracleEval.AdviceOracle)
    (checked : Static.CheckedTrace toplevel oracle Execution.selfLoopTrace) : False :=
  Execution.self_loop_no_static checked.assignment.certificate

theorem mutual_loop_no_checked (toplevel : Toplevel) (oracle : OracleEval.AdviceOracle)
    (checked : Static.CheckedTrace toplevel oracle Execution.mutualLoopTrace) : False :=
  Execution.mutual_loop_no_static checked.assignment.certificate

theorem self_loop_rejected (toplevel : Toplevel) (oracle : OracleEval.AdviceOracle) (limits : Static.Limits)
    (ranks : Array Nat) (replies : Array (List OracleEval.Values)) :
    (Static.validate toplevel oracle Execution.selfLoopTrace limits ranks replies).isOk = false := by
  cases result : Static.validate toplevel oracle Execution.selfLoopTrace limits ranks replies with
  | error _ => rfl
  | ok checked => exact False.elim (self_loop_no_checked toplevel oracle checked)

theorem mutual_loop_rejected (toplevel : Toplevel) (oracle : OracleEval.AdviceOracle) (limits : Static.Limits)
    (ranks : Array Nat) (replies : Array (List OracleEval.Values)) :
    (Static.validate toplevel oracle Execution.mutualLoopTrace limits ranks replies).isOk = false := by
  cases result : Static.validate toplevel oracle Execution.mutualLoopTrace limits ranks replies with
  | error _ => rfl
  | ok checked => exact False.elim (mutual_loop_no_checked toplevel oracle checked)

end CompilatrixTests.Aiur.Static
