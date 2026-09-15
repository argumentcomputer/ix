import Compilatrix.Aiur.Static.Check
import Compilatrix.Aiur.BytecodeSound

namespace Compilatrix.Aiur.Static

open _root_.Aiur.Bytecode (Toplevel)
open OracleEval (AdviceOracle Values)

theorem CheckedTrace.public_message {toplevel : Toplevel} {oracle : AdviceOracle} {trace : Trace}
    (checked : CheckedTrace toplevel oracle trace) {message : Message}
    (claim : message ∈ trace.publicClaims) :
    MessageEval toplevel (Memory.heap (Memory.cells trace)) oracle message :=
  (checked.validated.public_derivation checked.assignment.certificate claim).bytecode
    checked.validated checked.rows.rows

theorem CheckedTrace.public_bytecode {toplevel : Toplevel} {oracle : AdviceOracle} {trace : Trace}
    (checked : CheckedTrace toplevel oracle trace) {function : Nat} {inputs outputs : Values}
    (claim : Message.function function inputs outputs ∈ trace.publicClaims) :
    BytecodeEvalW toplevel (Memory.heap (Memory.cells trace)) oracle function inputs outputs :=
  checked.public_message claim

theorem CheckedTrace.wellFounded {toplevel : Toplevel} {oracle : AdviceOracle} {trace : Trace}
    (checked : CheckedTrace toplevel oracle trace) : WellFounded trace.Requires :=
  checked.assignment.wellFounded checked.validated.bound

theorem CheckedTrace.noShortCycle {toplevel : Toplevel} {oracle : AdviceOracle} {trace : Trace}
    (checked : CheckedTrace toplevel oracle trace) (walk : Nat → trace.RowId) (length : Nat)
    (positive : 0 < length) (short : length < _root_.Aiur.gSize.toNat)
    (edges : ∀ i, i < length → trace.Requires (walk (i + 1)) (walk i))
    (closed : walk length = walk 0) : False :=
  checked.assignment.certificate.noShortCycle walk length positive short ⟨edges, closed⟩

end Compilatrix.Aiur.Static
