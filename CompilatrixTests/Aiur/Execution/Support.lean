import Compilatrix.Aiur.OracleEval.Rows

namespace CompilatrixTests.Aiur.Execution

open Compilatrix.Aiur
open Compilatrix.Aiur.OracleEval
open _root_.Aiur.Bytecode (Block Function Toplevel Op)

def mkFunction (inputSize : Nat) (body : Block) : Function :=
  ⟨body, ⟨inputSize, 8, 32, 16⟩, true, true⟩

def program (inputSize : Nat) (body : Block) : Toplevel :=
  ⟨#[mkFunction inputSize body], #[1, 2, 10], #[], #[]⟩

def opsProgram (inputSize : Nat) (ops : Array Op) (outputs : Array Nat) : Toplevel :=
  program inputSize ⟨ops, .return 0 outputs⟩

def need (count : IO.Ref Nat) (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"Aiur execution regression failed: {label}")
  count.modify (· + 1)

def succeeded (result : Except Error Result) (outputs : Values) : Bool :=
  match result with
  | .ok result => decide (result.outputs = outputs)
  | .error _ => false

def exactResult (result : Except Error Result) (expected : Result) : Bool :=
  match result with
  | .ok actual => decide (actual = expected)
  | .error _ => false

def sameResults (left right : Except Error Result) : Bool :=
  match left, right with
  | .ok left, .ok right => decide (left = right)
  | .error left, .error right => decide (left = right)
  | _, _ => false

def failed {α : Type} (result : Except Error α) (error : Error) : Bool :=
  match result with
  | .error actual => decide (actual = error)
  | .ok _ => false

def replay (toplevel : Toplevel) (inputs : Values := []) (replies : List Values := [])
    (limits : Limits := {}) : Except Error Result :=
  runFunction toplevel limits 0 inputs replies

end CompilatrixTests.Aiur.Execution
