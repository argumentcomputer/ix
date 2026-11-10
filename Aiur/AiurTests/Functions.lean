import Aiur.Modules.Function
import Aiur.Modules.Link
import Aiur.Modules.Emit
import Aiur.Library.U32.Goldilocks
import AiurTests.FunctionDeclarations

namespace AiurFunctionTests
open Aiur

def declarations : Modules.Definitions Nat := aiur_decls⟦
module Data {
  enum Cell<T> { Mk(T) }
  type Word = Field;
}
⟧

def identity : Generic.Function Nat := aiur_fn⟦
  inline fn identity<T>(x: T) -> T { x }
⟧

def read : Generic.Function Nat := aiur_fn (in declarations)⟦
  fn read(c: Cell<Word>) -> Word {
    let Cell::Mk(x) = c;
    identity(x)
  }
⟧

def even : Generic.Function Nat := aiur_fn⟦
  fn even(n: Field) -> Field {
    match n { 0 => { 1 }, _ => { odd(n - 1) } }
  }
⟧

def odd : Generic.Function Nat := aiur_fn⟦
  fn odd(n: Field) -> Field {
    match n { 0 => { 0 }, _ => { even(n - 1) } }
  }
⟧

def assembled := Modules.ofFunctions "Data" [identity, read, even, odd] declarations

def original : Modules.Program Nat := aiur⟦
module Data {
  enum Cell<T> { Mk(T) }
  type Word = Field;
  inline fn identity<T>(x: T) -> T { x }
  fn read(c: Cell<Word>) -> Word {
    let Cell::Mk(x) = c;
    identity(x)
  }
  fn even(n: Field) -> Field {
    match n { 0 => { 1 }, _ => { odd(n - 1) } }
  }
  fn odd(n: Field) -> Field {
    match n { 0 => { 0 }, _ => { even(n - 1) } }
  }
}
⟧

-- Individual quotations are transparent AST values. Assembly preserves the
-- whole module, including parameter metadata, forward calls, and recursion.
example : identity.body = .var "x" := rfl
example : assembled = original := rfl
#guard (Modules.checkTemplates assembled).isOk

/-- error: function quotations require named parameters; destructure with `let` in the body -/
#guard_msgs in
def badParameter : Generic.Function Nat := aiur_fn⟦
  fn bad((x, y): (Field, Field)) -> Field { x + y }
⟧

/-- error: expected declarations without functions, module parameters, or a signature -/
#guard_msgs in
def badDeclarations : Modules.Definitions Nat := aiur_decls⟦
module Data { fn ignored() -> Field { 0 } }
⟧

/-- error: invalid source identifier 'bad-name' -/
#guard_msgs in
def badName : Generic.Function Nat := aiur_fn⟦
  fn «bad-name»() -> Field { 0 }
⟧

end AiurFunctionTests

namespace FunctionModuleTests
open Lean Elab Command Aiur

aiur_module Other where
def odd := aiur_fn⟦
  fn odd(n: Field) -> Field {
    match n { 0 => { 0 }, _ => { Data::even(n - 1) } }
  }
⟧
def constants := aiur_fn⟦
  fn constants() -> (Field, Field, Field) { (0, 1, 256) }
⟧
end

abbrev F := Library.U32.Goldilocks.F

run_cmd Modules.Frontend.uncounted do
  -- Importing declarations has not created a second set of raw functions.
  if (← getEnv).contains `FunctionModuleTests.Data.identity then
    throwError "function emitted before program assembly"
  let input ← ofExcept (Modules.declaredModules (← getEnv)
    [`FunctionModuleTests.Data, `FunctionModuleTests.Other])
  let prepared ← ofExcept (Modules.prepare (input.toField F) ["Data::even"])
  let name := fun symbol => (symbol.splitOn "::").foldl Name.str `FunctionModuleTests
  let quoter ← liftTermElabM (Modules.numeralQuoter (mkConst ``F) (fun x : F => x.val))
  letI := quoter
  Modules.emitProgram (mkConst ``F) `FunctionModuleTests name
    prepared.environment.source.program (toExpr ([] : List (Generic.Table F)))

-- These are the original declarations, fully resolved and kernel-reducible.
example : Data.identity.body = .var "x" := by simp [Data.identity]
example : Data.read.params = [("c", .named "Data::Cell" [.field])] := rfl
example : program.functions = [Data.identity, Data.read, Data.even, Other.odd, Other.constants] := rfl
example : Data.even.name = "Data::even" := rfl
example : Other.odd.name = "Other::odd" := rfl
example : Other.constants.body = .tuple [.literal 0, .literal 1, .literal 256] := by
  simp [Other.constants]

/-- error: duplicate Aiur module: FunctionModuleTests.Data -/
#guard_msgs in
aiur_module Data where end

/-- error: declaration name must match Aiur function name actual -/
#guard_msgs in
aiur_module Mismatch where
def declared := aiur_fn⟦fn actual() -> Field { 0 }⟧
end

/-- error: duplicate Aiur function: repeated -/
#guard_msgs in
aiur_module Duplicate where
def repeated := aiur_fn⟦fn repeated() -> Field { 0 }⟧
def repeated := aiur_fn⟦fn repeated() -> Field { 1 }⟧
end

end FunctionModuleTests
