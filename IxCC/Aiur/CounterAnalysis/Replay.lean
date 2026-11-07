import IxCC.Aiur.CounterAnalysis.ReplayHelpers

/-! Every successful real opcode has the register/call effect used by the
abstract interpreter. Arbitrary replies are retained as arbitrary values. -/

namespace IxCC.Aiur.CounterAnalysis

open _root_.Aiur (G)
open _root_.Aiur.Bytecode
open OracleEval (Values State)

theorem evalOp_effect {toplevel : Toplevel} {maxValues : Nat} {op : Op} {before after : State}
    (success : OracleEval.evalOp toplevel maxValues op before = .ok after) : Effect op before after := by
  cases op <;> simp only [OracleEval.evalOp] at success
  case const value =>
    have ⟨values, demands⟩ := appendValues_spec success
    exact ⟨[value], values, rfl, congrArg calls demands⟩
  case add left right =>
    obtain ⟨a, b, leftRead, rightRead, values, demands⟩ := fieldBinary_spec success
    exact ⟨[a + b], values, ⟨a, b, leftRead, rightRead, rfl⟩, congrArg calls demands⟩
  case sub left right =>
    obtain ⟨a, b, leftRead, rightRead, values, demands⟩ := fieldBinary_spec success
    exact ⟨[a - b], values, ⟨a, b, leftRead, rightRead, rfl⟩, congrArg calls demands⟩
  case mul left right =>
    obtain ⟨a, b, leftRead, rightRead, values, demands⟩ := fieldBinary_spec success
    exact ⟨[a * b], values, ⟨a, b, leftRead, rightRead, rfl⟩, congrArg calls demands⟩
  case eqZero index =>
    obtain ⟨value, _, success⟩ := bind_success success
    have ⟨values, demands⟩ := appendValues_spec success
    exact ⟨[G.eqZero value], values, rfl, congrArg calls demands⟩
  case call function indices size unconstrained =>
    cases reads : OracleEval.readMany maxValues before indices with
    | error error => rw [reads] at success; cases success
    | ok inputs =>
      rw [reads] at success
      simp only [bind, Except.bind] at success
      cases found : toplevel.functions[function]? with
      | none => rw [found] at success; cases success
      | some callee =>
        rw [found] at success
        by_cases bad : (inputs.length != callee.layout.inputSize) = true
        · simp [bad] at success
        · simp only [bad] at success
          cases unconstrained with
          | true =>
            simp only [↓reduceIte] at success
            obtain ⟨outputs, arity, values, demands⟩ := hint_spec success
            exact ⟨outputs, values, arity, congrArg calls demands⟩
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at success
            obtain ⟨⟨outputs, replied⟩, reply, success⟩ := bind_success success
            obtain ⟨demanded, demand, success⟩ := bind_success success
            have ⟨arity, values₁, demands₁⟩ := takeReply_spec reply
            have ⟨values₂, demands₂⟩ := demand_spec demand
            have ⟨values₃, demands₃⟩ := appendValues_spec success
            refine ⟨outputs, by rw [values₃, values₂, values₁], arity, inputs, readMany_spec reads, ?_⟩
            rw [demands₃, demands₂, demands₁]
            rfl
  case store indices =>
    obtain ⟨inputs, _, success⟩ := bind_success success
    obtain ⟨⟨answer, replied⟩, reply, success⟩ := bind_success success
    have ⟨_, values₁, demands₁⟩ := takeReply_spec reply
    split at success
    next pointer equal =>
      obtain ⟨demanded, demand, success⟩ := bind_success success
      have ⟨values₂, demands₂⟩ := demand_spec demand
      have ⟨values₃, demands₃⟩ := appendValues_spec success
      refine ⟨[pointer], by rw [values₃, values₂, values₁], rfl, ?_⟩
      change calls after.demandsRev = calls before.demandsRev
      rw [demands₃, demands₂, demands₁]
      rfl
    next => cases success
  case load size index =>
    obtain ⟨pointer, _, success⟩ := bind_success success
    obtain ⟨⟨outputs, replied⟩, reply, success⟩ := bind_success success
    obtain ⟨demanded, demand, success⟩ := bind_success success
    have ⟨arity, values₁, demands₁⟩ := takeReply_spec reply
    have ⟨values₂, demands₂⟩ := demand_spec demand
    have ⟨values₃, demands₃⟩ := appendValues_spec success
    refine ⟨outputs, by rw [values₃, values₂, values₁], arity, ?_⟩
    change calls after.demandsRev = calls before.demandsRev
    rw [demands₃, demands₂, demands₁]
    rfl
  case assertEq left right information =>
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨_, _, success⟩ := bind_success success
    split at success
    · cases success
      exact ⟨[], by simp, rfl, rfl⟩
    · cases success
  case ioGetInfo channel key =>
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨outputs, arity, values, demands⟩ := hint_spec success
    exact ⟨outputs, values, arity, congrArg calls demands⟩
  case ioRead channel index size =>
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨outputs, arity, values, demands⟩ := hint_spec success
    exact ⟨outputs, values, arity, congrArg calls demands⟩
  case ioSetInfo | ioWrite | debug =>
    cases success
    exact ⟨[], by simp, rfl, rfl⟩
  case unconstrainedBigUintDivMod =>
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨outputs, arity, values, demands⟩ := hint_spec success
    exact ⟨outputs, values, arity, congrArg calls demands⟩
  case unconstrainedGToBytes | unconstrainedGInverse =>
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨outputs, arity, values, demands⟩ := hint_spec success
    exact ⟨outputs, values, arity, congrArg calls demands⟩
  case unconstrainedU32Add =>
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨outputs, arity, values, demands⟩ := u32Hint_spec success
    exact ⟨outputs, values, arity, congrArg calls demands⟩
  case unconstrainedU32Add3 =>
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨outputs, arity, values, demands⟩ := u32Hint_spec success
    exact ⟨outputs, values, arity, congrArg calls demands⟩
  case u32ToField =>
    obtain ⟨bytes, _, success⟩ := bind_success success
    have ⟨values, demands⟩ := appendValues_spec success
    exact ⟨[OracleEval.packBytes bytes], values, rfl, congrArg calls demands⟩
  all_goals first
    | obtain ⟨outputs, arity, values, sameCalls⟩ := unaryGadget_spec success
      exact ⟨outputs, values, arity, sameCalls⟩
    | obtain ⟨outputs, arity, values, sameCalls⟩ := binaryGadget_spec success
      exact ⟨outputs, values, arity, sameCalls⟩

end IxCC.Aiur.CounterAnalysis
