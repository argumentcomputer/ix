import Compilatrix.Ixby.Inline.Syntax

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

theorem readOperands_length {frame : Frame} {args : List Operand} {values : List Value}
    (read : frame.readOperands args = .ok values) : values.length = args.length := by
  induction args generalizing values with
  | nil => simpa [Frame.readOperands] using read
  | cons arg args ih =>
    cases first : frame.read arg with
    | error error => simp [Frame.readOperands, first, bind, Except.bind] at read
    | ok value =>
      cases rest : frame.readOperands args with
      | error error => simp [Frame.readOperands, first, rest, bind, Except.bind] at read
      | ok values' =>
        have same : values = value :: values' := by
          simpa [Frame.readOperands, first, rest, bind, Except.bind, pure, Except.pure] using read.symm
        subst values
        simp [ih rest]

theorem readOperands_index {frame : Frame} {args : List Operand} {values : List Value}
    (read : frame.readOperands args = .ok values) {index : Nat} {operand : Operand}
    (found : args[index]? = some operand) :
    ∃ value, values[index]? = some value ∧ frame.read operand = .ok value := by
  induction args generalizing values index with
  | nil => simp at found
  | cons arg args ih =>
    cases first : frame.read arg with
    | error error => simp [Frame.readOperands, first, bind, Except.bind] at read
    | ok value =>
      cases rest : frame.readOperands args with
      | error error => simp [Frame.readOperands, first, rest, bind, Except.bind] at read
      | ok values' =>
        have same : values = value :: values' := by
          simpa [Frame.readOperands, first, rest, bind, Except.bind, pure, Except.pure] using read.symm
        subst values
        cases index with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst operand
          exact ⟨value, rfl, first⟩
        | succ index =>
          exact ih rest (by simpa using found)

theorem substituteOperand_sound {frame : Frame} {args : List Operand} {values : List Value}
    (read : frame.readOperands args = .ok values) {operand replacement : Operand}
    (substituted : substituteOperand args operand = some replacement)
    (callee : FunctionId) (block : BlockId) :
    ({ function := callee, block, locals := values.toArray } : Frame).read operand =
      frame.read replacement := by
  cases operand with
  | «local» index =>
    obtain ⟨value, found, readValue⟩ := readOperands_index read substituted
    rw [readValue]
    simp [Frame.read, found]
  | literal scalar =>
    simp only [substituteOperand, Option.some.injEq] at substituted
    subst replacement
    rfl
  | erased =>
    simp only [substituteOperand, Option.some.injEq] at substituted
    subst replacement
    rfl

theorem substituteOperands_sound {frame : Frame} {args : List Operand} {values : List Value}
    (read : frame.readOperands args = .ok values) {operands replacements : List Operand}
    (substituted : substituteOperands args operands = some replacements)
    (callee : FunctionId) (block : BlockId) :
    ({ function := callee, block, locals := values.toArray } : Frame).readOperands operands =
      frame.readOperands replacements := by
  induction operands generalizing replacements with
  | nil =>
    simp only [substituteOperands, Option.some.injEq] at substituted
    subst replacements
    rfl
  | cons operand operands ih =>
    cases first : substituteOperand args operand with
    | none => simp [substituteOperands, first] at substituted
    | some replacement =>
      cases rest : substituteOperands args operands with
      | none => simp [substituteOperands, first, rest] at substituted
      | some replacements' =>
        have same : replacements = replacement :: replacements' := by
          simpa [substituteOperands, first, rest] using substituted.symm
        subst replacements
        simp only [Frame.readOperands, substituteOperand_sound read first callee block,
          ih rest]

theorem PureOp.substitute_sound {frame : Frame} {args : List Operand} {values : List Value}
    (read : frame.readOperands args = .ok values) {operation replacement : PureOp}
    (substituted : operation.substitute args = some replacement)
    (limits : Limits) (program : Program) (callee : FunctionId) (block : BlockId) :
    operation.eval limits program { function := callee, block, locals := values.toArray } =
      replacement.eval limits program frame := by
  cases operation with
  | copy operand =>
    cases found : substituteOperand args operand with
    | none => simp [PureOp.substitute, found] at substituted
    | some value =>
      have same : replacement = .copy value := by simpa [PureOp.substitute, found] using substituted.symm
      subst replacement
      exact substituteOperand_sound read found callee block
  | primitive primitive operands =>
    cases found : substituteOperands args operands with
    | none => simp [PureOp.substitute, found] at substituted
    | some replacements =>
      have same : replacement = .primitive primitive replacements := by
        simpa [PureOp.substitute, found] using substituted.symm
      subst replacement
      simp only [PureOp.eval, substituteOperands_sound read found callee block]
  | construct ctor operands =>
    cases found : substituteOperands args operands with
    | none => simp [PureOp.substitute, found] at substituted
    | some replacements =>
      have same : replacement = .construct ctor replacements := by
        simpa [PureOp.substitute, found] using substituted.symm
      subst replacement
      simp only [PureOp.eval, substituteOperands_sound read found callee block]
  | project operand field =>
    cases found : substituteOperand args operand with
    | none => simp [PureOp.substitute, found] at substituted
    | some value =>
      have same : replacement = .project value field := by
        simpa [PureOp.substitute, found] using substituted.symm
      subst replacement
      simp only [PureOp.eval, substituteOperand_sound read found callee block]

theorem read_of_bound (frame : Frame) {operand : Operand}
    (bound : operandBound frame.locals.size operand) : ∃ value, frame.read operand = .ok value := by
  cases operand with
  | «local» index =>
    exact ⟨frame.locals[index]'bound, by simp [Frame.read, Array.getElem?_eq_getElem bound]⟩
  | literal scalar => exact ⟨.scalar scalar, rfl⟩
  | erased => exact ⟨.erased, rfl⟩

theorem readOperands_of_bound (frame : Frame) {args : List Operand}
    (bound : operandsBound frame.locals.size args) : ∃ values, frame.readOperands args = .ok values := by
  induction args with
  | nil => exact ⟨[], rfl⟩
  | cons arg args ih =>
    obtain ⟨value, first⟩ := read_of_bound frame (bound arg (by simp))
    obtain ⟨values, rest⟩ := ih (fun operand member => bound operand (by simp [member]))
    exact ⟨value :: values, by simp [Frame.readOperands, first, rest, bind, Except.bind, pure, Except.pure]⟩

end Compilatrix.Ixby.Inline
