import Compilatrix.Ixby.Inline.Image
import Compilatrix.Ixby.Binary
import Compilatrix.Ixby.Runtime.Chunked.Execute
import Compilatrix.Tools.Check

namespace CompilatrixTests.Ixby.Inline

open Ix.Ixby Compilatrix.Ixby.Inline Compilatrix.Tools.Check

def natural (n : Nat) : Value := .scalar (.nat n)
def literal (n : Nat) : Operand := .literal (.nat n)

def same [BEq α] [BEq β] : Except α β → Except α β → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

def wrapper (arity callee : Nat) (args : List Operand) : Function := {
  arity, blocks := #[⟨arity, .letOp (.call callee args) 1⟩,
    ⟨arity + 1, .ret (.local arity)⟩] }

def fixture (leaf : Leaf) (args : List Operand) (arity : Nat := 2) : Program := {
  functions := #[wrapper arity 1 args, leaf.function]
  constructors := #[⟨{ block := 1 }, 2⟩] }

def add : Program := fixture ⟨2, .primitive .natAdd [.local 0, .local 1]⟩ [.local 0, .local 1]

def compare (label : String) (program : Program) (input : Array Value)
    (expected : Except Error Value) (limits : Limits := {}) : IO Unit := do
  let selected ← checked (optimize limits program)
  need (selected.status != .unchanged) s!"{label}: no rewrite exercised"
  for (name, code) in [("original", program), ("optimized", selected.program)] do
    let reference := execute limits code input 10000
    need (same reference expected) s!"{label} {name}: expected {reprStr expected}, got {reprStr reference}"
    let chunked := Compilatrix.Ixby.Runtime.Chunked.execute limits code input 10000
    need (same reference chunked) s!"{label} {name}: chunked evaluator differs"

def rejected (label : String) (source target : Program) (protectedPrefix : Nat := 0) : IO Unit := do
  match check {} source target protectedPrefix with
  | .ok _ => throw (IO.userError s!"inline mutation accepted: {label}")
  | .error _ => pure ()

def instruction (program : Program) (function block : Nat) (value : Instr) : Program :=
  { program with functions := program.functions.modify function fun fn =>
    { fn with blocks := fn.blocks.modify block fun b => { b with instruction := value } } }

end CompilatrixTests.Ixby.Inline
