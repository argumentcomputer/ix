import Ix.Compiler.X86.ScalarObject

namespace Ix.Compiler.X86.Scalar

/-- Existing scalar derivations survive extension of the function table. -/
theorem Evaluates.withFunctions {functions extended : Array Function} {expression values result}
    (evaluated : Evaluates functions expression values result)
    (preserved : ∀ (index : Nat) (function : Function), functions[index]? = some function → extended[index]? = some function) :
    Evaluates extended expression values result := by
  induction evaluated with
  | atom found => exact .atom found
  | add left right => exact .add left right
  | sub left right => exact .sub left right
  | letE _ _ first rest => exact .letE first rest
  | letOverflow _ first => exact .letOverflow first
  | zero found _ taken => exact .zero found taken
  | successor found positive _ taken => exact .successor found positive taken
  | call found arguments arity _ called => exact .call (preserved _ _ found) arguments arity called

def bindFunction (entry : Nat) (captured : Word) : Function :=
  { parameters := 1, body := .call entry #[.constant captured, .var 0] }

def bindProgram (source : Program) (captured : Word) : Program :=
  { functions := source.functions.push (bindFunction source.entry captured), entry := source.functions.size }

/-- A checked unary ABI wrapper binds the first parameter of the original
binary entry. The original functions and their call indices are retained. -/
structure Bound (source : Checked) (captured : Word) where
  function : Function
  found : source.program.functions[source.program.entry]? = some function
  binary : function.parameters = 2
  checked : Checked
  same : checked.program = bindProgram source.program captured

def bind (source : Checked) (captured : Word) : Except String (Bound source captured) := do
  match found : source.program.functions[source.program.entry]? with
  | none => throw "captured scalar source entry is missing"
  | some function =>
      if binary : function.parameters = 2 then
        if valid : (bindProgram source.program captured).valid = true then
          return { function, found, binary, checked := ⟨bindProgram source.program captured, valid⟩, same := rfl }
        else throw "captured scalar wrapper exceeds the scalar function or code limits"
      else throw "captured scalar source entry must have two parameters"

theorem Bound.preserves {source captured} (bound : Bound source captured)
    {index : Nat} {function : Function} (found : source.program.functions[index]? = some function) :
    bound.checked.program.functions[index]? = some function := by
  have small := (Array.getElem?_eq_some_iff.mp found).1
  simpa [bound.same, bindProgram, Array.getElem?_push, small, Nat.ne_of_lt small] using found

theorem Bound.entry {source captured} (bound : Bound source captured) :
    bound.checked.program.functions[bound.checked.program.entry]? = some (bindFunction source.program.entry captured) := by
  simp [bound.same, bindProgram]

theorem Bound.evaluates {source captured} (bound : Bound source captured) (argument : Word) {result}
    (evaluated : Evaluates source.program.functions bound.function.body #[captured, argument] result) :
    Evaluates bound.checked.program.functions (bindFunction source.program.entry captured).body #[argument] result := by
  exact .call (supplied := #[captured, argument]) (bound.preserves bound.found)
    (by simp [Array.mapM_eq_mapM_toList, Atom.eval]) (by simp [bound.binary])
    (evaluated.withFunctions (fun _ _ found => bound.preserves found))

end Ix.Compiler.X86.Scalar
