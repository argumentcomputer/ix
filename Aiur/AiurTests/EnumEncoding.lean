import Aiur.Frontend
import Aiur.Circuit.Compile
import Aiur.WireBoundary
import Mathlib.Algebra.Field.Rat

open Aiur

namespace AiurEnumEncodingTests

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def program : Program Nat := aiur% r#"
enum Maybe { None, Some(Field) }
enum Inner { A, B }
enum Outer { Raw(Field), Nested(Inner) }
enum Box { Empty, Full(&Field) }
enum Product { A(Field, Field), B((Field, Field)) }
fn identity(x: Maybe) -> Maybe { x }
"#

private def checks : List (String × Bool) := [
  ("canonical nullary encoding",
    decide ((Value.construct "Maybe" "None" [] : Value Rat).encode program.enums =
      some ⟨.enum "Maybe", [0, 0]⟩)),
  ("payload encoding",
    decide ((Value.construct "Maybe" "Some" [7] : Value Rat).encode program.enums =
      some ⟨.enum "Maybe", [1, 7]⟩)),
  ("invalid tag rejected", decide ((⟨.enum "Maybe", [2, 0]⟩ : WireValue Rat).decode program.enums = none)),
  ("nonzero padding rejected", decide ((⟨.enum "Maybe", [0, 7]⟩ : WireValue Rat).decode program.enums = none)),
  ("wrong width rejected", decide ((⟨.enum "Maybe", [0]⟩ : WireValue Rat).decode program.enums = none)),
  ("inactive variant does not restrict raw payload",
    decide ((⟨.enum "Outer", [0, 7]⟩ : WireValue Rat).decode program.enums =
      some (.construct "Outer" "Raw" [7]))),
  ("nested tags decoded",
    decide ((⟨.enum "Outer", [1, 1]⟩ : WireValue Rat).decode program.enums =
      some (.construct "Outer" "Nested" [.construct "Inner" "B" []]))),
  ("invalid active nested tag rejected",
    decide ((⟨.enum "Outer", [1, 7]⟩ : WireValue Rat).decode program.enums = none)),
  ("malformed constructor rejected",
    decide ((Value.construct "Maybe" "None" [7] : Value Rat).encode program.enums = none)),
  ("pointer payload retains its target type",
    decide ((⟨.enum "Box", [1, 9]⟩ : WireValue Rat).decode program.enums =
      some (.construct "Box" "Full" [.ptr .field 9]))),
  ("constructor arguments and tuple arguments remain distinct",
    decide ((⟨.enum "Product", [1, 3, 4]⟩ : WireValue Rat).decode program.enums =
      some (.construct "Product" "B" [.tuple [3, 4]])))
]

/-- Check actual generated polynomial equations with explicit auxiliary columns. -/
private def constraintsHold (name : String) (enable : Rat) (words witness : List Rat) : Bool :=
  match program.enums.layout (.enum name) with
  | .error _ => false
  | .ok layout =>
      match Circuit.Compiler.validate layout (.const enable) (words.map Circuit.ArithExpr.const) {} with
      | .error _ => false
      | .ok (_, state) => decide (state.nextVar = witness.length) &&
          state.constraints.toList.all (fun polynomial =>
            decide (polynomial.denote (fun id => witness.getD id 0) = 0))

private def constraintsChecks : List (String × Bool) := [
  ("valid tag and zero padding", constraintsHold "Maybe" 1 [0, 0] [1, 0, 0, -1]),
  ("padding constrained", !constraintsHold "Maybe" 1 [0, 7] [1, 0, 0, -1]),
  ("invalid tag constrained", !constraintsHold "Maybe" 1 [2, 0] [0, 1/2, 0, 1]),
  ("inactive value may be noncanonical", constraintsHold "Maybe" 0 [2, 7] [0, 1/2, 0, 1]),
  ("unselected nested enum does not restrict raw field", constraintsHold "Outer" 1 [0, 7]
    [1, 0, 0, -1, 0, 1/7, 0, 1/6]),
  ("selected nested enum is constrained", !constraintsHold "Outer" 1 [1, 7]
    [0, 1, 1, 0, 0, 1/7, 0, 1/6]),
  ("selected nested enum accepts valid tag", constraintsHold "Outer" 1 [1, 0]
    [0, 1, 1, 0, 1, 0, 0, -1])
]

private def system : Circuit.System Rat :=
  (Circuit.compile (program.toField Rat)).toOption.getD { chips := [], enums := program.enums }

private def rootChecks : List (String × Bool) := [
  ("invalid root argument tag", decide (system.check ⟨[]⟩
    ⟨"identity", [⟨.enum "Maybe", [2, 0]⟩], ⟨.enum "Maybe", [0, 0]⟩⟩ [] = .error .malformedEntry)),
  ("noncanonical root argument padding", decide (system.check ⟨[]⟩
    ⟨"identity", [⟨.enum "Maybe", [0, 7]⟩], ⟨.enum "Maybe", [0, 0]⟩⟩ [] = .error .malformedEntry)),
  ("invalid root result tag", decide (system.check ⟨[]⟩
    ⟨"identity", [⟨.enum "Maybe", [0, 0]⟩], ⟨.enum "Maybe", [2, 0]⟩⟩ [] = .error .malformedEntry)),
  ("well-formed root still requires proof", decide (system.check ⟨[]⟩
    ⟨"identity", [⟨.enum "Maybe", [0, 0]⟩], ⟨.enum "Maybe", [1, 7]⟩⟩ [] = .error .unbalancedMessages)),
  ("pointer in an unselected root variant", decide (system.check ⟨[]⟩
    ⟨"identity", [⟨.enum "Box", [0, 0]⟩], ⟨.enum "Maybe", [0, 0]⟩⟩ [] = .error .pointerEntryArgument)),
  ("pointer-bearing root variant rejected", decide (system.check ⟨[]⟩
    ⟨"identity", [⟨.enum "Box", [1, 99]⟩], ⟨.enum "Maybe", [0, 0]⟩⟩ [] = .error .pointerEntryArgument))
]

def run : IO Unit := do
  for (label, passed) in checks ++ constraintsChecks ++ rootChecks do
    unless passed do throw (IO.userError s!"enum encoding check failed: {label}")
  IO.println s!"Passed {checks.length + constraintsChecks.length + rootChecks.length} enum encoding and polynomial checks."

end AiurEnumEncodingTests
