import Compilatrix.Aiur.Static.Assignment
import Compilatrix.Aiur.OracleEval.Rows

/-! One checked endpoint for supplied logical traces. Inputs are plain
bytecode, rows, ranks, and replay tapes; the result retains all proof objects. -/

namespace Compilatrix.Aiur.Static

open _root_.Aiur.Bytecode (Toplevel)
open OracleEval (AdviceOracle Values)

structure TraceLimits where
  trace : Trace.Limits := {}
  assignment : AssignmentLimits := {}
  replay : OracleEval.Limits := {}
  deriving Repr

structure Limits extends TraceLimits where
  components : Wire.CheckLimits := {}
  deriving Repr

inductive Error where
  | program (error : ProgramError)
  | trace (error : Trace.Error)
  | assignment (error : AssignmentError)
  | replay (error : OracleEval.Error)
  deriving DecidableEq, Repr

structure CheckedTrace (toplevel : Toplevel) (oracle : AdviceOracle) (trace : Trace) : Type where
  program : Program toplevel
  validated : Trace.Validated trace
  assignment : Assignment program trace
  rows : OracleEval.CheckedRows toplevel oracle trace

def validatePrepared {toplevel : Toplevel} (program : Program toplevel)
    (oracle : AdviceOracle) (trace : Trace) (limits : TraceLimits)
    (ranks : Array Nat) (replies : Array (List Values)) :
    Except Error (CheckedTrace toplevel oracle trace) := do
  let validated ← match trace.validate limits.trace with
    | .ok checked => pure checked
    | .error error => throw (.trace error)
  let assignment ← match checkAssignment program trace limits.trace limits.assignment ranks with
    | .ok checked => pure checked
    | .error error => throw (.assignment error)
  let rows ← match OracleEval.validateRows toplevel oracle trace limits.replay replies with
    | .ok checked => pure checked
    | .error error => throw (.replay error)
  return ⟨program, validated, assignment, rows⟩

def validate (toplevel : Toplevel) (oracle : AdviceOracle) (trace : Trace) (limits : Limits)
    (ranks : Array Nat) (replies : Array (List Values)) :
    Except Error (CheckedTrace toplevel oracle trace) := do
  let program ← match prepare limits.components toplevel with
    | .ok checked => pure checked
    | .error error => throw (.program error)
  validatePrepared program oracle trace limits.toTraceLimits ranks replies

end Compilatrix.Aiur.Static
