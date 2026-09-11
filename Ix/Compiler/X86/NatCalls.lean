import Ix.Compiler.X86.NatCallsCapture

/-! A bounded structural selector for closed unary-Nat computations. Known
PAP arguments specialize a function's call interface; a separate mode admits
one checked static Nat capture. Nat values
remain expressions: successor emits ADD, and calls remain direct CALLs.
The closed translation validator is separate in NatCallsCheck. -/
namespace Ix.Compiler.X86.NatCalls
open Ix.Compiler Ixon

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
  | .staticNat expression => .ok expression
  | _ => .error .notNat

def parameter : Value → Param
  | .nat _ => .nat
  | .closure function capture => .closure function capture
  | .staticNat expression => .staticNat expression
  | .erased => .erased

def parameterValue : Param → Value
  | .nat => .nat .argument
  | .closure function capture => .closure function capture
  | .staticNat expression => .staticNat expression
  | .erased => .erased

def shared (function : IxIR2.Function) : Bool :=
  function.signature.result == .shared &&
  function.signature.params.all (fun param => param.world == .shared && param.passing == .owned)

mutual
  def lowerFunction (program : IxIR2.Program) (schema : Schema) (limits : Limits) (mode : CaptureMode) :
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
            if captures.isEmpty then registers := registers.push (.closure address none)
            else
              if mode == .captureFree then throw .capturedPap
              let #[atom] := captures | throw .capturedPap
              let expression ← natValue (← value registers atom)
              let _ ← checkCapture functions expression limits.captureFuel
              registers := registers.push (.closure address (some expression))
        | .call address atoms =>
            let (next, expression) ← lowerCall program schema limits mode fuel functions address (← atoms.mapM (value registers))
            functions := next
            registers := registers.push (.nat expression)
        | .apply closure atoms =>
            let .closure address capture ← value registers closure | throw .unknownClosure
            let values := capture.toArray.map Value.staticNat ++ (← atoms.mapM (value registers))
            let (next, expression) ← lowerCall program schema limits mode fuel functions address values
            functions := next
            registers := registers.push (.nat expression)
        | _ => throw .instruction
      let (nextFunctions, body) ← (match block.terminator with
        | .ret atom => do return (functions, ← natValue (← value registers atom))
        | .tailCall address atoms => do lowerCall program schema limits mode fuel functions address (← atoms.mapM (value registers))
        | _ => throw .controlFlow : Except Error (Array Function × Expr))
      if nextFunctions.size >= limits.functions then throw .budget
      return (nextFunctions.push { origin, parameters, body }, nextFunctions.size)

  def lowerCall (program : IxIR2.Program) (schema : Schema) (limits : Limits) (mode : CaptureMode) :
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
      let (next, index) ← lowerFunction program schema limits mode fuel functions (some address) function parameters
      return (next, .call index inputExpr)
end

def lower (program : IxIR2.Program) (schema : Schema) (limits : Limits := {})
    (mode : CaptureMode := .captureFree) : Except Error Residual := do
  if !program.main.signature.params.isEmpty then throw .openMain
  let (functions, entry) ← lowerFunction program schema limits mode limits.depth #[] none program.main #[]
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

end Ix.Compiler.X86.NatCalls
