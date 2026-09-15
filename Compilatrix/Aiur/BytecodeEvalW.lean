import Compilatrix.Aiur.OracleEval.Local
import Compilatrix.Aiur.Memory

/-! Finite bytecode execution against one witness heap and allowed advice.
Each function executes its actual pinned body. Constrained callees execute
recursively; memory and gadget messages have concrete leaf meanings.
No allocation order, prior store, or determinism of advice is assumed. -/

namespace Compilatrix.Aiur

open _root_.Aiur.Bytecode (Toplevel)
open OracleEval (Values AdviceOracle AdviceAllowed)

inductive MessageEval (toplevel : Toplevel) (heap : Memory.Heap) (oracle : AdviceOracle) :
    Message → Prop where
  | function {function : Nat} {inputs outputs : Values} {demands : List Message}
      {advice : List OracleEval.AdviceObservation}
      (body : OracleEval.Body toplevel function inputs outputs demands advice)
      (allowed : AdviceAllowed oracle advice)
      (children : ∀ message ∈ demands, MessageEval toplevel heap oracle message) :
      MessageEval toplevel heap oracle (.function function inputs outputs)
  | memory {bucket : Nat} {pointer : _root_.Aiur.G} {values : Values}
      (observed : heap bucket pointer = some values) (width : values.length = bucket) :
      MessageEval toplevel heap oracle (.memory bucket pointer values)
  | gadget {channel : Nat} {payload : Values} (valid : OracleEval.Gadget.check channel payload = true) :
      MessageEval toplevel heap oracle (.gadget channel payload)

abbrev BytecodeEvalW (toplevel : Toplevel) (heap : Memory.Heap) (oracle : AdviceOracle)
    (function : Nat) (inputs outputs : Values) : Prop :=
  MessageEval toplevel heap oracle (.function function inputs outputs)

theorem OracleEval.Checked.sound {toplevel : Toplevel} {function : Nat} {inputs : Values}
    (checked : OracleEval.Checked toplevel function inputs) (heap : Memory.Heap) (oracle : AdviceOracle)
    (allowed : AdviceAllowed oracle checked.result.advice)
    (children : ∀ message ∈ checked.result.demands, MessageEval toplevel heap oracle message) :
    BytecodeEvalW toplevel heap oracle function inputs checked.result.outputs :=
  .function checked.body allowed children

theorem MessageEval.memory_iff {toplevel : Toplevel} {heap : Memory.Heap} {oracle : AdviceOracle}
    {bucket : Nat} {pointer : _root_.Aiur.G} {values : Values} :
    MessageEval toplevel heap oracle (.memory bucket pointer values) ↔
      heap bucket pointer = some values ∧ values.length = bucket := by
  constructor
  · intro execution
    cases execution with | memory observed width => exact ⟨observed, width⟩
  · rintro ⟨observed, width⟩
    exact .memory observed width

theorem MessageEval.gadget_iff {toplevel : Toplevel} {heap : Memory.Heap} {oracle : AdviceOracle}
    {channel : Nat} {payload : Values} :
    MessageEval toplevel heap oracle (.gadget channel payload) ↔
      OracleEval.Gadget.check channel payload = true := by
  constructor
  · intro execution
    cases execution with | gadget valid => exact valid
  · exact .gadget

theorem BytecodeEvalW.body {toplevel : Toplevel} {heap : Memory.Heap} {oracle : AdviceOracle}
    {function : Nat} {inputs outputs : Values} (execution : BytecodeEvalW toplevel heap oracle function inputs outputs) :
    ∃ demands advice, OracleEval.Body toplevel function inputs outputs demands advice ∧
      AdviceAllowed oracle advice ∧ ∀ message ∈ demands, MessageEval toplevel heap oracle message := by
  cases execution with
  | function body allowed children => exact ⟨_, _, body, allowed, children⟩

theorem MessageEval.advice_mono {toplevel : Toplevel} {heap : Memory.Heap} {left right : AdviceOracle}
    (admits : ∀ request answer, left request answer = true → right request answer = true)
    {message : Message} (execution : MessageEval toplevel heap left message) :
    MessageEval toplevel heap right message := by
  induction execution with
  | function body allowed children ih =>
      exact .function body (OracleEval.adviceAllowed_mono admits allowed) ih
  | memory observed width => exact .memory observed width
  | gadget valid => exact .gadget valid

theorem MessageEval.heap_congr {toplevel : Toplevel} {left right : Memory.Heap} {oracle : AdviceOracle}
    (same : ∀ bucket pointer, left bucket pointer = right bucket pointer)
    {message : Message} (execution : MessageEval toplevel left oracle message) :
    MessageEval toplevel right oracle message := by
  induction execution with
  | function body allowed children ih => exact .function body allowed ih
  | memory observed width => exact .memory ((same _ _).symm.trans observed) width
  | gadget valid => exact .gadget valid

end Compilatrix.Aiur
