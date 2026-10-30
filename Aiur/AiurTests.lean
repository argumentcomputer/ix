import Aiur.Scalar
import AiurTests.Circuit
import AiurTests.Semantics
import AiurTests.Memo
import AiurTests.TupleRuntime
import AiurTests.Enums
import AiurTests.EnumEncoding
import AiurTests.Tagless
import AiurTests.EnumProofs
import AiurTests.Pointers
import AiurTests.WidthROM
import AiurTests.Tuples
import AiurTests.Tables
import AiurTests.RefutableLets
import AiurTests.InputTypes
import AiurTests.Hints
import AiurTests.Accumulators
import AiurTests.Generics
import AiurTests.Aliases
import AiurTests.PointerPatterns
import AiurTests.Consts
import AiurTests.Arrays
import AiurTests.SourceEvaluation
import AiurTests.Control
import AiurTests.Structs
import AiurTests.Updates
import AiurTests.Diagnostics
import AiurTests.Assertions
import AiurTests.OrPatterns
import AiurTests.Modules
import AiurTests.Opacity
import AiurTests.Execution
import AiurTests.Trace
import AiurTests.Inlining
import AiurTests.CircuitStats
import AiurTests.Optimized
import AiurTests.Propagation
import AiurTests.CompilerIndex
import AiurTests.Carry
import AiurTests.Blake3
import AiurTests.U8
import AiurTests.U64
import AiurTests.U32
import AiurTests.LibraryInterfaces
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

open Aiur.Scalar

namespace AiurTests

def identity : Program Nat := scalar_aiur% "fn identity(x) { x }"

/-- Elaboration produces ordinary AST constructors, reducible by the kernel. -/
example : identity = ⟨[⟨"identity", ["x"], .var "x"⟩]⟩ := rfl
example : typecheck identity = .ok () := by decide +kernel
example : eval (identity.toField Rat) "identity" [42] = .ok 42 := by decide +kernel

def sample : Program Nat := scalar_aiur% "
// The same definitions will be evaluated in two fields.
fn arithmetic(x: Field, y: Field) -> Field { (x + y) * (x - y) / y }
fn negation(x) { -x * 2 + 1 }
fn adjacent(x) { x--1 + x/-2 }
fn tabs(x) {\t x\t/\t2\r\n}
fn precedence() { 2 + 3 * 4 - 8 / 2 }
fn left_assoc() { 12 / 3 / 2 - 2 - 1 }
fn sum3(x, y, z,) { x + y + z }
fn forward(x) { sum3(x, 2, 3,) }
fn even(n) {
  match n {
    0 => 1,
    _ => odd(n - 1),
  }
}
fn odd(n) {
  match n {
    0 => 0,
    _ => even(n - 1),
  }
}
fn divide(x, y) { x / y }
fn lazy_match(x) { match x { 0 => 9, _ => 1 / 0 } }
fn ordered(x) { match x { 7 => 10, 0 => 20, _ => 30 } }
fn wildcard_first(x) { match x { _ => 11, 0 => 22 } }
fn partial_match(x) { match x { 1 => 4 } }
fn nested(x, y) { match x { 0 => { match y { 1 => 2, _ => 3 } }, _ => 4 } }
fn forever(x) { forever(x) }
fn eager() { sum3(1 / 0, 2, 3) }
fn large() { 123456789012345678901234567890 }
fn literal() { /* outer /* nested */ comment */ 8 } // trailing comment
"

def rationals : Program Rat := sample.toField Rat

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
def modSeven : Program (ZMod 7) := sample.toField (ZMod 7)

def rationalTests : List (String × Except EvalError Rat × Except EvalError Rat) := [
  ("arithmetic", eval rationals "arithmetic" [5, 2], .ok (21 / 2)),
  ("unary minus", eval rationals "negation" [3], .ok (-5)),
  ("adjacent operators", eval rationals "adjacent" [6], .ok 4),
  ("tabs and CRLF", eval rationals "tabs" [6], .ok 3),
  ("operator precedence", eval rationals "precedence" [], .ok 10),
  ("left associativity", eval rationals "left_assoc" [], .ok (-1)),
  ("many arguments", eval rationals "sum3" [4, 5, 6], .ok 15),
  ("forward call", eval rationals "forward" [4], .ok 9),
  ("mutual recursion, even", eval rationals "even" [10], .ok 1),
  ("mutual recursion, odd", eval rationals "even" [9], .ok 0),
  ("mutual recursion, other entry", eval rationals "odd" [9], .ok 1),
  ("division by zero", eval rationals "divide" [1, 0], .error .divisionByZero),
  ("unselected arm is lazy", eval rationals "lazy_match" [0], .ok 9),
  ("selected arm can fail", eval rationals "lazy_match" [1], .error .divisionByZero),
  ("pattern before specialization", eval rationals "ordered" [0], .ok 20),
  ("first matching arm", eval rationals "wildcard_first" [0], .ok 11),
  ("missing arm", eval rationals "partial_match" [0], .error .noMatchingArm),
  ("nested matches", eval rationals "nested" [0, 1], .ok 2),
  ("recursion limit", eval rationals "forever" [1] 20, .error .outOfFuel),
  ("zero fuel", eval rationals "literal" [] 0, .error .outOfFuel),
  ("single literal fuel", eval rationals "literal" [] 1, .ok 8),
  ("eager call arguments", eval rationals "eager" [], .error .divisionByZero),
  ("entry lookup", eval rationals "missing" [], .error (.unknownFunction "missing")),
  ("entry arity", eval rationals "sum3" [1], .error (.arityMismatch "sum3" 3 1)),
  ("large natural", eval rationals "large" [], .ok 123456789012345678901234567890)
]

def finiteFieldTests : List (String × Except EvalError (ZMod 7) × Except EvalError (ZMod 7)) := [
  ("literal reduction", eval modSeven "literal" [], .ok 1),
  ("field division", eval modSeven "divide" [1, 2], .ok 4),
  ("field negation", eval modSeven "negation" [3], .ok 2),
  ("patterns specialized too", eval modSeven "ordered" [0], .ok 3),
  ("zero after reduction", eval modSeven "divide" [1, 7], .error .divisionByZero)
]

def invalidPrograms : List (Program Nat × CheckError) := [
  (⟨[⟨"f", [], .literal 0⟩, ⟨"f", [], .literal 1⟩]⟩, .duplicateFunction "f"),
  (⟨[⟨"f", ["x", "x"], .var "x"⟩]⟩, .duplicateParameter "f" "x"),
  (⟨[⟨"f", [], .var "x"⟩]⟩, .unboundVariable "f" "x"),
  (⟨[⟨"f", [], .call "g" []⟩]⟩, .unknownFunction "f" "g"),
  (⟨[⟨"f", ["x"], .call "f" []⟩]⟩, .arityMismatch "f" "f" 1 0),
  (⟨[⟨"f", [], .matchValue (.literal 0) []⟩]⟩, .emptyMatch "f"),
  (⟨[⟨"f", [], .matchValue (.literal 0)
      [(.wildcard, .literal 1), (.literal 0, .var "unreachable")]⟩]⟩,
    .unboundVariable "f" "unreachable")
]

-- The string elaborator runs the checker rather than merely constructing syntax.
/-- error: function 'f' calls 'f' with 0 arguments; expected 1 -/
#guard_msgs in
#check (scalar_aiur% "fn f(x) { f() }" : Program Nat)

/-- error: duplicate function 'f' -/
#guard_msgs in
#check (scalar_aiur% "fn f() { 0 } fn f() { 1 }" : Program Nat)

/-- error: unbound variable 'y' in function 'f' -/
#guard_msgs in
#check (scalar_aiur% "fn f(x) { y }" : Program Nat)

-- These exercise parser failures without coupling tests to parser error formatting.
run_cmd do
  let env ← Lean.getEnv
  for source in [
    "fn f() { 1 } trailing",
    "fn f() { match 0 { } }",
    "fn f() { match 0 { x => 1 } }",
    "fn f(x: Nat) { x }",
    "fn f() -> Nat { 0 }",
    "fn f() { (1, 2) }",
    "fn f() { 1 + }",
    "fn f() { 1 /* comment */ 2 }",
    "fn f() { 1 } /* unterminated",
    "fn f() { 1 } -- not a Rust comment"
  ] do
    match Frontend.ofString env source with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted invalid source: {source}"

private def checkEqual [DecidableEq α] [Repr α] (label : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

def run : IO Unit := do
  for (label, actual, expected) in rationalTests do
    checkEqual label actual expected
  for (label, actual, expected) in finiteFieldTests do
    checkEqual label actual expected
  for (program, error) in invalidPrograms do
    checkEqual "checker error" (typecheck program) (.error error)
    checkEqual "checked evaluation" (eval (program.toField Rat) "f" [])
      (.error (.invalidProgram error))
  IO.println s!"Passed {rationalTests.length + finiteFieldTests.length + 2 * invalidPrograms.length} runtime checks."

end AiurTests

def main : IO Unit := do
  AiurTests.run
  AiurCircuitTests.run
  AiurTupleTests.run
  AiurPointerTests.run
  AiurTupleRuntimeTests.run
  AiurEnumTests.run
  AiurEnumEncodingTests.run
  AiurTaglessTests.run
  AiurTableTests.run
  AiurRefutableLetTests.run
  AiurInputTypeTests.run
  AiurHintTests.run
  AiurAccumulatorTests.run
  AiurGenericTests.run
  AiurAliasTests.run
  AiurPointerPatternTests.run
  AiurConstTests.run
  AiurArrayTests.run
  AiurControlTests.run
  AiurStructTests.run
  AiurUpdateTests.run
  AiurDiagnosticTests.run
  AiurAssertionTests.run
  AiurOrPatternTests.run
  AiurModuleTests.run
  AiurOpacityTests.run
  AiurExecutionTests.run
  AiurTraceTests.run
  AiurTraceTests.runSmallField
  AiurInlineTests.run
  AiurCircuitStatsTests.run
  AiurPropagationTests.run
  AiurCompilerIndexTests.run
  AiurCarryTests.run
  AiurU8Tests.run
  AiurU64Tests.run
  AiurU32Tests.run
  AiurOptimizedTests.run
