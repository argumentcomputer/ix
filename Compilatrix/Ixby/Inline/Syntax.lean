import Ix.Ixby.Eval

/-! The certified inlining fragment has one value-producing operation followed
by its return. Calls, closures, and control flow are excluded from that operation.
Substitution retains literal and erased operands and checks every local index. -/

namespace Compilatrix.Ixby.Inline

open Ix.Ixby

@[simp] theorem except_throw (error : Error) : (throw error : Except Error α) = .error error := rfl
@[simp] theorem except_pure (value : α) : (pure value : Except Error α) = .ok value := rfl

inductive PureOp where
  | copy (value : Operand)
  | primitive (operation : Primitive) (args : List Operand)
  | construct (ctor : Constructor) (args : List Operand)
  | project (value : Operand) (field : Nat)
  deriving BEq, DecidableEq, Repr, Inhabited

def PureOp.toOp : PureOp → Op
  | .copy value => .copy value
  | .primitive operation args => .primitive operation args
  | .construct ctor args => .construct ctor args
  | .project value field => .project value field

def PureOp.ofOp : Op → Option PureOp
  | .copy value => some (.copy value)
  | .primitive operation args => some (.primitive operation args)
  | .construct ctor args => some (.construct ctor args)
  | .project value field => some (.project value field)
  | _ => none

def substituteOperand (args : List Operand) : Operand → Option Operand
  | .local index => args[index]?
  | operand => some operand

def substituteOperands (args : List Operand) : List Operand → Option (List Operand)
  | [] => some []
  | operand :: rest => do
    return (← substituteOperand args operand) :: (← substituteOperands args rest)

def PureOp.substitute (args : List Operand) : PureOp → Option PureOp
  | .copy value => return .copy (← substituteOperand args value)
  | .primitive operation operands => return .primitive operation (← substituteOperands args operands)
  | .construct ctor operands => return .construct ctor (← substituteOperands args operands)
  | .project value field => return .project (← substituteOperand args value) field

def operandBound (locals : Nat) : Operand → Prop
  | .local index => index < locals
  | _ => True

instance (locals : Nat) (operand : Operand) : Decidable (operandBound locals operand) := by
  cases operand <;> unfold operandBound <;> infer_instance

def operandsBound (locals : Nat) (args : List Operand) : Prop :=
  ∀ operand ∈ args, operandBound locals operand

instance (locals : Nat) (args : List Operand) : Decidable (operandsBound locals args) :=
  inferInstanceAs (Decidable (∀ operand ∈ args, operandBound locals operand))

structure Leaf where
  arity : Nat
  operation : PureOp
  deriving BEq, DecidableEq, Repr, Inhabited

def Leaf.function (leaf : Leaf) : Function := {
  arity := leaf.arity
  blocks := #[
    ⟨leaf.arity, .letOp leaf.operation.toOp 1⟩,
    ⟨leaf.arity + 1, .ret (.local leaf.arity)⟩] }

/-- A recognizer proposes a leaf; the independent checker compares its entire
function, including entry, arity, and both blocks, using propositional equality. -/
def recognize (program : Program) (id : FunctionId) : Option Leaf := do
  let function ← program.functions[id]?
  let block ← function.blocks[0]?
  let .letOp operation 1 := block.instruction | none
  let operation ← PureOp.ofOp operation
  let leaf := { arity := function.arity, operation : Leaf }
  if function == leaf.function then some leaf else none

/-- Value semantics of precisely the four allowed operation forms. The soundness
module relates this definition to the unchanged Ixby operation evaluator. -/
def PureOp.eval (limits : Limits) (program : Program) (frame : Frame) : PureOp → Except Error Value
  | .copy value => frame.read value
  | .primitive operation args => do operation.eval limits (← frame.readOperands args)
  | .construct ctor args => do
    let decl ← program.getConstructor ctor
    let fields ← frame.readOperands args
    if fields.length != decl.fields then throw (.arityMismatch decl.fields fields.length)
    return .ctor decl.id fields.toArray
  | .project operand field => do
    match ← frame.read operand with
    | .ctor _ fields =>
      let some value := fields[field]? | throw (.invalidProjection field)
      return value
    | .erased => return .erased
    | _ => throw .notConstructor

end Compilatrix.Ixby.Inline
