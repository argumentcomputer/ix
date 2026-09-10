import Compilatrix.IxIR2.Validate
import Compilatrix.X86.Basic

/-! A bounded structural selector for closed unary-Nat computations. Known,
capture-free PAP arguments specialize a function's call interface. Nat values
remain expressions: successor emits ADD, and calls remain direct CALLs.
The closed translation validator is separate in NatCallsCheck. -/
namespace Compilatrix.X86.NatCalls
open Compilatrix Ixon

structure Schema where
  zero : IxIR2.CtorId
  succ : IxIR2.CtorId
  deriving BEq, Repr

inductive Expr where
  | argument
  | constant (value : Word)
  | successor (value : Expr)
  | call (function : Nat) (argument : Expr)
  deriving BEq, Repr, Inhabited

inductive Value where
  | nat (expression : Expr)
  | closure (function : Address)
  | erased
  deriving BEq, Repr, Inhabited

inductive Param where
  | nat
  | closure (function : Address)
  | erased
  deriving BEq, Repr, Inhabited

structure Function where
  origin : Option Address
  parameters : Array Param
  body : Expr
  deriving BEq, Repr, Inhabited

structure Residual where
  functions : Array Function
  entry : Nat
  deriving BEq, Repr, Inhabited

inductive Error where
  | budget
  | openMain
  | controlFlow
  | ownership
  | unknownRegister
  | wordOverflow
  | notNat
  | unknownFunction
  | callArity
  | multipleNatArguments
  | capturedPap
  | unknownClosure
  | constructor
  | instruction
  | returnValue
  deriving BEq, Repr

structure Limits where
  depth : Nat := 32
  functions : Nat := 64
  instructions : Nat := 1024
  deriving BEq, Repr

def value (registers : Array Value) : IxIR2.Atom → Except Error Value
  | .reg register => match registers[register]? with
      | some value => .ok value
      | none => .error .unknownRegister
  | .lit (.nat number) =>
      if number < UInt64.size then .ok (.nat (.constant number.toUInt64)) else .error .wordOverflow
  | .erased => .ok .erased
  | _ => .error .notNat

def natValue : Value → Except Error Expr
  | .nat expression => .ok expression
  | _ => .error .notNat

def parameter : Value → Param
  | .nat _ => .nat
  | .closure function => .closure function
  | .erased => .erased

def parameterValue : Param → Value
  | .nat => .nat .argument
  | .closure function => .closure function
  | .erased => .erased

def shared (function : IxIR2.Function) : Bool :=
  function.signature.result == .shared &&
  function.signature.params.all (fun param => param.world == .shared && param.passing == .owned)

mutual
  def lowerFunction (program : IxIR2.Program) (schema : Schema) (limits : Limits) :
      Nat → Array Function → Option Address → IxIR2.Function → Array Param →
      Except Error (Array Function × Nat)
    | 0, _, _, _, _ => .error .budget
    | fuel + 1, functions, origin, function, parameters => do
      if !shared function then throw .ownership
      if function.signature.params.size != parameters.size then throw .callArity
      let #[block] := function.blocks | throw .controlFlow
      if !block.creditParams.isEmpty then throw .ownership
      if block.instructions.size > limits.instructions || functions.size >= limits.functions then throw .budget
      let mut functions := functions
      let mut registers := parameters.map parameterValue
      for instruction in block.instructions do
        match instruction with
        | .move atom | .retainShared atom => registers := registers.push (← value registers atom)
        | .releaseShared _ => pure ()
        | .alloc .shared cid args =>
            let values ← args.mapM (value registers)
            if cid == schema.zero && values.isEmpty then
              registers := registers.push (.nat (.constant 0))
            else if cid == schema.succ then
              let #[argument] := values | throw .constructor
              registers := registers.push (.nat (.successor (← natValue argument)))
            else throw .constructor
        | .papp address captures =>
            if !captures.isEmpty then throw .capturedPap
            registers := registers.push (.closure address)
        | .call address atoms =>
            let (next, expression) ← lowerCall program schema limits fuel functions address (← atoms.mapM (value registers))
            functions := next
            registers := registers.push (.nat expression)
        | .apply closure atoms =>
            let .closure address ← value registers closure | throw .unknownClosure
            let (next, expression) ← lowerCall program schema limits fuel functions address (← atoms.mapM (value registers))
            functions := next
            registers := registers.push (.nat expression)
        | _ => throw .instruction
      let (nextFunctions, body) ← (match block.terminator with
        | .ret atom => do return (functions, ← natValue (← value registers atom))
        | .tailCall address atoms => do lowerCall program schema limits fuel functions address (← atoms.mapM (value registers))
        | _ => throw .controlFlow : Except Error (Array Function × Expr))
      if nextFunctions.size >= limits.functions then throw .budget
      return (nextFunctions.push { origin, parameters, body }, nextFunctions.size)

  def lowerCall (program : IxIR2.Program) (schema : Schema) (limits : Limits) :
      Nat → Array Function → Address → Array Value → Except Error (Array Function × Expr)
    | 0, _, _, _ => .error .budget
    | fuel + 1, functions, address, values => do
      let parameters := values.map parameter
      let numbers := values.filterMap fun | .nat expression => some expression | _ => none
      if numbers.size > 1 then throw .multipleNatArguments
      let inputExpr := numbers[0]?.getD (.constant 0)
      if let some index := functions.findIdx? (fun function => function.origin == some address && function.parameters == parameters) then
        return (functions, .call index inputExpr)
      let some (_, .fn function) := program.declarations.find? (·.1 == address) | throw .unknownFunction
      let (next, index) ← lowerFunction program schema limits fuel functions (some address) function parameters
      return (next, .call index inputExpr)
end

def lower (program : IxIR2.Program) (schema : Schema) (limits : Limits := {}) : Except Error Residual := do
  if !program.main.signature.params.isEmpty then throw .openMain
  let (functions, entry) ← lowerFunction program schema limits limits.depth #[] none program.main #[]
  return { functions, entry }

def Expr.instructions : Expr → List X86.Instr
  | .argument => [.mov .w64 .rax (.reg .rdi)]
  | .constant value => [.mov .w64 .rax (.imm value)]
  | .successor value => value.instructions ++ [.alu .add .w64 .rax (.imm 1)]
  | .call function inputExpr => inputExpr.instructions ++
      [.mov .w64 .rdi (.reg .rax), .push .rbp, .call function.toUInt32, .pop .rbp]

def Residual.target (residual : Residual) : X86.Program := {
  entry := residual.entry.toUInt32
  blocks := residual.functions.map fun function => {
    instructions := function.body.instructions.toArray
    terminator := .ret } }

/-- Mathematical Nat evaluation checks every intermediate bound; a wrapping
Word calculation is never used to justify an exact Nat result. -/
def evaluate (functions : Array Function) : Nat → Expr → Nat → Except Error Nat
  | 0, _, _ => .error .budget
  | fuel + 1, expression, argument => do
      let result ← match expression with
        | .argument => pure argument
        | .constant value => pure value.toNat
        | .successor expression => do pure ((← evaluate functions fuel expression argument) + 1)
        | .call function expression =>
            let some body := functions[function]? | throw .unknownFunction
            let argument ← evaluate functions fuel expression argument
            evaluate functions fuel body.body argument
      if result >= UInt64.size then throw .wordOverflow
      return result

def Residual.evaluate (residual : Residual) (fuel : Nat := 1024) : Except Error Nat := do
  let some main := residual.functions[residual.entry]? | throw .unknownFunction
  NatCalls.evaluate residual.functions fuel main.body 0

end Compilatrix.X86.NatCalls
