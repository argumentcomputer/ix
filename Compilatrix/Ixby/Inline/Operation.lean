import Compilatrix.Ixby.Inline.Substitution
import Compilatrix.Ixby.Inline.Layout

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

theorem PureOp.eval_toOp (operation : PureOp) (limits : Limits) (program : Program) (frame : Frame) :
    evalOp limits program frame operation.toOp = (operation.eval limits program frame).map Action.value := by
  cases operation with
  | copy operand =>
    cases found : frame.read operand <;> simp [PureOp.toOp, PureOp.eval, evalOp, found, Except.map, bind, Except.bind]
  | primitive operation operands =>
    cases found : frame.readOperands operands with
    | error error => simp [PureOp.toOp, PureOp.eval, evalOp, found, Except.map, bind, Except.bind]
    | ok args =>
      cases evaluated : operation.eval limits args <;>
        simp [PureOp.toOp, PureOp.eval, evalOp, found, evaluated, Except.map, bind, Except.bind]
  | construct ctor operands =>
    cases declaration : program.getConstructor ctor with
    | error error => simp [PureOp.toOp, PureOp.eval, evalOp, declaration, Except.map, bind, Except.bind]
    | ok decl =>
      cases found : frame.readOperands operands with
      | error error => simp [PureOp.toOp, PureOp.eval, evalOp, declaration, found, Except.map, bind, Except.bind]
      | ok fields =>
        by_cases arity : fields.length = decl.fields <;>
          simp [PureOp.toOp, PureOp.eval, evalOp, declaration, found, arity, Except.map, bind, Except.bind]
  | project operand field =>
    cases found : frame.read operand with
    | error error => simp [PureOp.toOp, PureOp.eval, evalOp, found, Except.map, bind, Except.bind]
    | ok object =>
      cases object <;> try rfl
      case ctor id fields =>
        cases projected : fields[field]? <;>
          simp [PureOp.toOp, PureOp.eval, evalOp, found, projected, Except.map, bind, Except.bind]
      all_goals simp [PureOp.toOp, PureOp.eval, evalOp, found, Except.map, bind, Except.bind]

theorem PureOp.eval_sameLayout {source target} (same : SameLayout source target)
    (operation : PureOp) (limits : Limits) (frame : Frame) :
    operation.eval limits source frame = operation.eval limits target frame := by
  cases operation with
  | construct ctor args => simp only [PureOp.eval, same.getConstructor]
  | _ => rfl

theorem PureOp.step_value {limits : Limits} {program : Program} {frame : Frame} {locals : Nat}
    {next : BlockId} {operation : PureOp} {value : Value} {resumed : Frame} {continuation : Array Continuation}
    (code : frame.check limits program = .ok ⟨locals, .letOp operation.toOp next⟩)
    (evaluated : operation.eval limits program frame = .ok value)
    (transfer : frame.transfer limits program next #[value] = .ok resumed) :
    step limits program ⟨.eval frame, continuation⟩ = .ok (.next ⟨.eval resumed, continuation⟩) := by
  simp [step, stepEval, code, PureOp.eval_toOp, evaluated, Except.map, transfer,
    bind, Except.bind, pure, Except.pure]

end Compilatrix.Ixby.Inline
