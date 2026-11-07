import IxCC.Aiur.BytecodeEvalW
import IxCC.Aiur.OracleEval.Rows
import IxCC.Aiur.Certificate

/-! Discharge the generic derivation rule with concrete bytecode replay.
The premises name the remaining AIR extraction and static-row obligations;
neither follows merely from addressed bytecode/component ingress. -/

namespace IxCC.Aiur

open _root_.Aiur.Bytecode (Toplevel)
open OracleEval (Values AdviceOracle)

theorem Trace.Derivation.bytecode {toplevel : Toplevel} {oracle : AdviceOracle} {trace : Trace}
    (checked : Trace.Validated trace) (rows : OracleEval.Rows toplevel oracle trace)
    {message : Message} (derivation : trace.Derivation message) :
    MessageEval toplevel (Memory.heap (Memory.cells trace)) oracle message := by
  apply derivation.sound (MessageEval toplevel (Memory.heap (Memory.cells trace)) oracle)
  intro id active nonzero children
  have facts := rows id active nonzero
  cases provided : (trace.row id).provides with
  | function function inputs outputs =>
      simp only [OracleEval.RowFact, provided] at facts
      obtain ⟨advice, body, allowed⟩ := facts
      exact .function body allowed children
  | memory bucket pointer values =>
      simp only [OracleEval.RowFact, provided] at facts
      exact .memory (Memory.row_agrees trace checked.memory id active provided) facts.1
  | gadget channel payload =>
      simp only [OracleEval.RowFact, provided] at facts
      exact .gadget facts.1

/-- A checked trace, concrete bytecode rows, and static row facts establish
an execution of every public function claim against the same extracted heap. -/
theorem Trace.Validated.public_bytecode {toplevel : Toplevel} {oracle : AdviceOracle} {trace : Trace}
    (checked : Trace.Validated trace) (rows : OracleEval.Rows toplevel oracle trace)
    (static : StaticCertificate trace.RowId trace.Requires)
    {function : Nat} {inputs outputs : Values}
    (claim : Message.function function inputs outputs ∈ trace.publicClaims) :
    BytecodeEvalW toplevel (Memory.heap (Memory.cells trace)) oracle function inputs outputs :=
  (checked.public_derivation static claim).bytecode checked rows

theorem OracleEval.CheckedRows.public_bytecode {toplevel : Toplevel} {oracle : AdviceOracle} {trace : Trace}
    (rows : OracleEval.CheckedRows toplevel oracle trace) (checked : Trace.Validated trace)
    (static : StaticCertificate trace.RowId trace.Requires)
    {function : Nat} {inputs outputs : Values}
    (claim : Message.function function inputs outputs ∈ trace.publicClaims) :
    BytecodeEvalW toplevel (Memory.heap (Memory.cells trace)) oracle function inputs outputs :=
  checked.public_bytecode rows.rows static claim

end IxCC.Aiur
