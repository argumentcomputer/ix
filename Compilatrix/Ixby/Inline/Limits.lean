import Compilatrix.Ixby.Inline.Operation

/-! Reintroducing an eliminated ordinary leaf call uses one temporary
continuation. All other capacities, scalar checks, and admission conditions
remain identical. These lemmas make that resource relation explicit. -/

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

def extraStack (limits : Limits) : Limits := { limits with continuations := limits.continuations + 1 }

theorem scalar_extraStack (limits : Limits) (value : Scalar) :
    value.validate (extraStack limits) = value.validate limits := by cases value <;> rfl

theorem primitive_extraStack (limits : Limits) (operation : Primitive) (args : List Value) :
    operation.eval (extraStack limits) args = operation.eval limits args := by
  simp only [Primitive.eval, scalar_extraStack]
  rfl

theorem check_extraStack (limits : Limits) (program : Program) (frame : Frame) :
    frame.check (extraStack limits) program = frame.check limits program := rfl

theorem transfer_extraStack (limits : Limits) (program : Program) (frame : Frame)
    (target : BlockId) (extra : Array Value) :
    frame.transfer (extraStack limits) program target extra = frame.transfer limits program target extra := rfl

theorem enter_extraStack (limits : Limits) (program : Program) (callee : FunctionId) (args : Array Value) :
    enter (extraStack limits) program callee args = enter limits program callee args := rfl

theorem evalOp_extraStack (limits : Limits) (program : Program) (frame : Frame) (operation : Op) :
    evalOp (extraStack limits) program frame operation = evalOp limits program frame operation := by
  cases operation with
  | primitive operation args => simp only [evalOp, primitive_extraStack]
  | _ => rfl

theorem pureOp_extraStack (limits : Limits) (program : Program) (frame : Frame) (operation : PureOp) :
    operation.eval (extraStack limits) program frame = operation.eval limits program frame := by
  cases operation with
  | primitive operation args => simp only [PureOp.eval, primitive_extraStack]
  | _ => rfl

theorem operand_extraStack (limits : Limits) (locals : Nat) (operand : Operand) :
    operand.valid (extraStack limits) locals = operand.valid limits locals := by
  cases operand <;> simp only [Operand.valid, scalar_extraStack]

theorem operands_extraStack (limits : Limits) (locals : Nat) (args : List Operand) :
    operandsValid (extraStack limits) locals args = operandsValid limits locals args := by
  simp only [operandsValid, operand_extraStack]
  rfl

theorem directCall_extraStack (limits : Limits) (program : Program) (locals : Nat)
    (callee : FunctionId) (args : List Operand) :
    directCallValid (extraStack limits) program locals callee args = directCallValid limits program locals callee args := by
  simp only [directCallValid, operands_extraStack]

theorem opValid_extraStack (limits : Limits) (program : Program) (self : FunctionId)
    (locals : Nat) (operation : Op) :
    operation.valid (extraStack limits) program self locals = operation.valid limits program self locals := by
  cases operation <;> simp only [Op.valid, operand_extraStack, operands_extraStack, directCall_extraStack]

theorem blockValid_extraStack (limits : Limits) (program : Program) (self : FunctionId)
    (function : Function) (block : Block) :
    block.valid (extraStack limits) program self function = block.valid limits program self function := by
  cases block.instruction <;>
    simp only [Block.valid, opValid_extraStack, operand_extraStack, operands_extraStack, directCall_extraStack] <;> rfl

theorem validateConstructors_extraStack (limits : Limits) (seen : List CtorId) (constructors : List CtorDecl) :
    validateConstructors (extraStack limits) seen constructors = validateConstructors limits seen constructors := by
  induction constructors generalizing seen with
  | nil => rfl
  | cons ctor constructors ih => simp only [validateConstructors, ih]; rfl

theorem validateBlocks_extraStack (limits : Limits) (program : Program) (self : FunctionId)
    (function : Function) (index : Nat) (blocks : List Block) :
    validateBlocks (extraStack limits) program self function index blocks =
      validateBlocks limits program self function index blocks := by
  induction blocks generalizing index with
  | nil => rfl
  | cons block blocks ih => simp only [validateBlocks, blockValid_extraStack, ih]

theorem validateFunctions_extraStack (limits : Limits) (program : Program)
    (index : Nat) (functions : List Function) :
    validateFunctions (extraStack limits) program index functions = validateFunctions limits program index functions := by
  induction functions generalizing index with
  | nil => rfl
  | cons function functions ih => simp only [validateFunctions, validateBlocks_extraStack, ih]; rfl

theorem validateProgram_extraStack (limits : Limits) (program : Program) :
    validateProgram (extraStack limits) program = validateProgram limits program := by
  simp only [validateProgram, validateConstructors_extraStack, validateFunctions_extraStack]
  rfl

theorem validateInputValues_extraStack (limits : Limits) (program : Program) (fuel : Nat) (values : List Value) :
    validateInputValues (extraStack limits) program fuel values = validateInputValues limits program fuel values := by
  induction fuel generalizing values with
  | zero => cases values <;> rfl
  | succ fuel ih =>
    cases values with
    | nil => rfl
    | cons value values => cases value <;> simp only [validateInputValues, scalar_extraStack, ih]

theorem initialState_extraStack (limits : Limits) (program : Program) (input : Array Value) :
    initialState (extraStack limits) program input = initialState limits program input := by
  simp only [initialState, validateProgram_extraStack, enter_extraStack,
    validateInputValues_extraStack]
  rfl

end Compilatrix.Ixby.Inline
