import Compilatrix.Aiur.BytecodeSound
import CompilatrixTests.Aiur.Execution.TraceFixtures

/-! Kernel-checked complete executions. Concrete checker computations use
ordinary reduction; no native reflection theorem is added. -/

namespace CompilatrixTests.Aiur.Execution

open Compilatrix.Aiur
open Compilatrix.Aiur.OracleEval

private def acceptedTrace (trace : Trace) (success : trace.validate.isOk = true) : Trace.Validated trace :=
  match checked : trace.validate with
  | .ok result => result
  | .error _ => by simp [checked, Except.isOk, Except.toBool] at success

theorem counter_exec : BytecodeEvalW counterProgram (Memory.heap (Memory.cells counterTrace))
    unrestrictedAdvice 0 [2] [0] :=
  (acceptedTrace counterTrace (by decide)).public_bytecode
    (checkRows_sound _ _ _ {} counterReplies (by decide)) counterStatic (by decide)

theorem ranked_mutual_exec : BytecodeEvalW rankedProgram (Memory.heap (Memory.cells rankedTrace))
    unrestrictedAdvice 0 [2] [0] :=
  (acceptedTrace rankedTrace (by decide)).public_bytecode
    (checkRows_sound _ _ _ {} counterReplies (by decide)) rankedStatic (by decide)

theorem store_at_seven_exec : BytecodeEvalW storeProgram (Memory.heap (Memory.cells storeTrace))
    unrestrictedAdvice 0 [42] [7] :=
  (acceptedTrace storeTrace (by decide)).public_bytecode
    (checkRows_sound _ _ _ {} #[[[7]], []] (by decide)) storeStatic (by decide)

theorem load_without_store_exec : BytecodeEvalW loadProgram (Memory.heap (Memory.cells loadTrace))
    unrestrictedAdvice 0 [7] [42] :=
  (acceptedTrace loadTrace (by decide)).public_bytecode
    (checkRows_sound _ _ _ {} #[[[42]], []] (by decide)) loadStatic (by decide)

theorem self_pointer_exec : BytecodeEvalW loadProgram (Memory.heap (Memory.cells selfPointerTrace))
    unrestrictedAdvice 0 [7] [7] :=
  (acceptedTrace selfPointerTrace (by decide)).public_bytecode
    (checkRows_sound _ _ _ {} #[[[7]], []] (by decide)) selfPointerStatic (by decide)

theorem distinct_store_pointers_exec : BytecodeEvalW doubleStoreProgram (Memory.heap (Memory.cells doubleStoreTrace))
    unrestrictedAdvice 0 [42] [7, 9] :=
  (acceptedTrace doubleStoreTrace (by decide)).public_bytecode
    (checkRows_sound _ _ _ {} #[[[7], [9]], [], []] (by decide)) doubleStoreStatic (by decide)

theorem gadget_exec : BytecodeEvalW xorProgram (Memory.heap (Memory.cells xorTrace))
    unrestrictedAdvice 0 [1, 2] [3] :=
  (acceptedTrace xorTrace (by decide)).public_bytecode
    (checkRows_sound _ _ _ {} #[[[3]], []] (by decide)) xorStatic (by decide)

theorem constrained_call_exec : BytecodeEvalW callProgram (Memory.heap (Memory.cells (callTrace 42)))
    unrestrictedAdvice 0 [20, 22] [42] :=
  (acceptedTrace (callTrace 42) (by decide)).public_bytecode
    (checkRows_sound _ _ _ {} #[[[42]], []] (by decide)) callStatic (by decide)

theorem unconstrained_call_exec : BytecodeEvalW hintCallProgram (Memory.heap (Memory.cells hintCallTrace))
    unrestrictedAdvice 0 [] [99] :=
  (acceptedTrace hintCallTrace (by decide)).public_bytecode
    (checkRows_sound _ _ _ {} #[[[99]]] (by decide)) hintCallStatic (by decide)

theorem repeated_advice_exec : BytecodeEvalW repeatedAdvice (Memory.heap (Memory.cells repeatedAdviceTrace))
    unrestrictedAdvice 0 [0] [7, 9] :=
  (acceptedTrace repeatedAdviceTrace (by decide)).public_bytecode
    (checkRows_sound _ _ _ {} #[[[7], [9]]] (by decide)) repeatedAdviceStatic (by decide)

theorem continuation_scope_body : Body continuationScope 0 [0, 10] [17] [] [] :=
  ⟨{ maxSteps := 64 }, [], ⟨.returned 6 [17], [], []⟩, by rfl, rfl, rfl, rfl⟩

theorem nested_return_body : Body nestedEarlyReturn 0 [0] [7, 8] [] [] :=
  ⟨{ maxSteps := 64 }, [], ⟨.returned 2 [7, 8], [], []⟩, by rfl, rfl, rfl, rfl⟩

theorem continuation_scope_exec (heap : Memory.Heap) (oracle : AdviceOracle) :
    BytecodeEvalW continuationScope heap oracle 0 [0, 10] [17] :=
  .function continuation_scope_body (by simp [AdviceAllowed]) (by simp)

theorem nested_return_exec (heap : Memory.Heap) (oracle : AdviceOracle) :
    BytecodeEvalW nestedEarlyReturn heap oracle 0 [0] [7, 8] :=
  .function nested_return_body (by simp [AdviceAllowed]) (by simp)

/-- Bytecode replay itself does not certify well-foundedness. This actual
self-calling body passes every local row check, but no static certificate
can justify the balanced cyclic trace. -/
theorem self_loop_rows : Rows selfLoopProgram unrestrictedAdvice selfLoopTrace :=
  checkRows_sound _ _ _ {} #[[[99]]] (by decide)

theorem self_loop_no_static (certificate : StaticCertificate selfLoopTrace.RowId selfLoopTrace.Requires) : False :=
  certificate.noShortCycle (fun _ => ⟨0, by decide⟩) 1 (by decide) (by decide)
    ⟨fun _ _ => by dsimp only; decide, rfl⟩

theorem mutual_loop_rows : Rows mutualLoopProgram unrestrictedAdvice mutualLoopTrace :=
  checkRows_sound _ _ _ {} #[[[99]], [[99]]] (by decide)

theorem mutual_loop_no_static (certificate : StaticCertificate mutualLoopTrace.RowId mutualLoopTrace.Requires) : False := by
  let walk : Nat → mutualLoopTrace.RowId := fun index => ⟨index % 2, Nat.mod_lt _ (by decide)⟩
  apply certificate.noShortCycle walk 2 (by decide) (by decide)
  constructor
  · intro index bounded
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> decide
  · decide

theorem false_gadget_has_no_meaning (toplevel : _root_.Aiur.Bytecode.Toplevel)
    (heap : Memory.Heap) (oracle : AdviceOracle) :
    ¬ MessageEval toplevel heap oracle (.gadget 3 [1, 2, 9]) := by
  intro execution
  have invalid := MessageEval.gadget_iff.mp execution
  exact (by decide : Gadget.check 3 [1, 2, 9] ≠ true) invalid

end CompilatrixTests.Aiur.Execution
