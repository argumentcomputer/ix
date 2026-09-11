import Ix.Compiler.X86.ExactNat

/-! The first compositional scalar fragment. Values are exact unsigned
64-bit naturals. Local slots are immutable bindings; a let adds one slot.
Branches return a value to the enclosing continuation, giving explicit
joins. Calls have at most two scalar arguments and target earlier functions.
The executable semantics reports arithmetic overflow without wrapping. -/

namespace Ix.Compiler.X86.Scalar

def maxLocals : Nat := 32
def maxFunctions : Nat := 32
def maxNodes : Nat := 4096

inductive Atom where
  | var (index : Nat)
  | constant (value : Word)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Atom.eval (values : Array Word) : Atom → Option Word
  | .var index => values[index]?
  | .constant value => some value

def Atom.valid (locals : Nat) : Atom → Bool
  | .var index => index < locals
  | .constant _ => true

inductive Expr where
  | atom (value : Atom)
  | add (left right : Atom)
  | sub (left right : Atom)
  | letE (value body : Expr)
  | branch (scrutinee : Atom) (zero successor : Expr)
  | call (function : Nat) (arguments : Array Atom)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Function where
  parameters : Nat
  body : Expr
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Program where
  functions : Array Function
  entry : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Expr.nodes : Expr → Nat
  | .letE value body => 1 + value.nodes + body.nodes
  | .branch _ zero successor => 1 + zero.nodes + successor.nodes
  | _ => 1

def Expr.valid (functions : Array Function) (current : Nat) : Nat → Expr → Bool
  | locals, .atom value => value.valid locals
  | locals, .add left right | locals, .sub left right => left.valid locals && right.valid locals
  | locals, .letE value body =>
      locals < maxLocals && value.valid functions current locals && body.valid functions current (locals + 1)
  | locals, .branch scrutinee zero successor =>
      scrutinee.valid locals && zero.valid functions current locals && successor.valid functions current locals
  | locals, .call function arguments =>
      function < current && arguments.size ≤ 2 && arguments.all (·.valid locals) &&
        match functions[function]? with
        | some callee => arguments.size == callee.parameters
        | none => false

def Program.valid (program : Program) : Bool :=
  program.entry < program.functions.size && program.functions.size ≤ maxFunctions &&
    program.functions.toList.zipIdx.all fun (function, index) =>
      function.parameters ≤ 2 && function.body.nodes ≤ maxNodes &&
        function.body.valid program.functions index function.parameters

structure Checked where
  program : Program
  valid : program.valid = true

def check (program : Program) : Option Checked :=
  if valid : program.valid = true then some ⟨program, valid⟩ else none

inductive Error where
  | fuel
  | local
  | function
  | arity
  | overflow
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

def atom (values : Array Word) (value : Atom) : Except Error Word :=
  match value.eval values with
  | some value => .ok value
  | none => .error .local

def evaluate (functions : Array Function) : Nat → Expr → Array Word → Except Error Word
  | 0, _, _ => .error .fuel
  | fuel + 1, expression, values => do
      match expression with
      | .atom value => atom values value
      | .add left right =>
          let left ← atom values left
          let right ← atom values right
          match ExactNat.add left right with
          | some value => pure value
          | none => throw .overflow
      | .sub left right => return ExactNat.sub (← atom values left) (← atom values right)
      | .letE value body =>
          let value ← evaluate functions fuel value values
          evaluate functions fuel body (values.push value)
      | .branch scrutinee zero successor =>
          if (← atom values scrutinee) == 0 then evaluate functions fuel zero values
          else evaluate functions fuel successor values
      | .call function arguments =>
          let some callee := functions[function]? | throw .function
          let supplied ← arguments.mapM (atom values)
          if supplied.size != callee.parameters then throw .arity
          evaluate functions fuel callee.body supplied

/-- A finite semantic derivation is independent of interpreter fuel. In
particular, a native proof consumes this compositional relation rather than
an execution certificate specialized to one set of runtime arguments. -/
inductive Evaluates (functions : Array Function) : Expr → Array Word → Option Word → Prop where
  | atom {values : Array Word} {source : Atom} {value : Word}
      (found : source.eval values = some value) : Evaluates functions (.atom source) values (some value)
  | add {values : Array Word} {left right : Atom} {a b : Word}
      (leftValue : left.eval values = some a) (rightValue : right.eval values = some b) :
      Evaluates functions (.add left right) values (ExactNat.add a b)
  | sub {values : Array Word} {left right : Atom} {a b : Word}
      (leftValue : left.eval values = some a) (rightValue : right.eval values = some b) :
      Evaluates functions (.sub left right) values (some (ExactNat.sub a b))
  | letE {values : Array Word} {value body : Expr} {bound : Word} {result : Option Word}
      (first : Evaluates functions value values (some bound))
      (rest : Evaluates functions body (values.push bound) result) :
      Evaluates functions (.letE value body) values result
  | letOverflow {values : Array Word} {value body : Expr}
      (first : Evaluates functions value values none) :
      Evaluates functions (.letE value body) values none
  | zero {values : Array Word} {scrutinee : Atom} {zero successor : Expr} {result : Option Word}
      (scrutineeValue : scrutinee.eval values = some 0)
      (taken : Evaluates functions zero values result) :
      Evaluates functions (.branch scrutinee zero successor) values result
  | successor {values : Array Word} {scrutinee : Atom} {zero successor : Expr}
      {value : Word} {result : Option Word}
      (scrutineeValue : scrutinee.eval values = some value) (positive : value ≠ 0)
      (taken : Evaluates functions successor values result) :
      Evaluates functions (.branch scrutinee zero successor) values result
  | call {values supplied : Array Word} {function : Nat} {arguments : Array Atom}
      {callee : Function} {result : Option Word}
      (found : functions[function]? = some callee)
      (argumentsAt : arguments.mapM (Atom.eval values) = some supplied)
      (arity : supplied.size = callee.parameters)
      (evaluated : Evaluates functions callee.body supplied result) :
      Evaluates functions (.call function arguments) values result

end Ix.Compiler.X86.Scalar
