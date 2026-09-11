import Ix.Compiler.IxIR2.Validate
import Ix.Compiler.X86.Basic

namespace Ix.Compiler.X86.NatCalls
open Ix.Compiler Ixon

inductive CaptureMode where
  | captureFree
  | staticNat
  deriving BEq, Repr

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
  | closure (function : Address) (capture : Option Expr := none)
  | staticNat (expression : Expr)
  | erased
  deriving BEq, Repr, Inhabited

inductive Param where
  | nat
  | closure (function : Address) (capture : Option Expr := none)
  | staticNat (expression : Expr)
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
  | dynamicCapture
  | unknownClosure
  | constructor
  | instruction
  | returnValue
  deriving BEq, Repr

structure Limits where
  depth : Nat := 32
  functions : Nat := 64
  instructions : Nat := 1024
  captureFuel : Nat := 1024
  deriving BEq, Repr

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

end Ix.Compiler.X86.NatCalls
