module
public import Ix.Ixon
public import Ix.Sharing

public section

namespace Tests.IxonV3
open Ixon

structure ExprCase where
  name : String
  expr : Expr
  bytes : ByteArray

def lambdaTelescope : Expr :=
  .lam .many (.sort 0) (.lam .many (.sort 0) (.lam .many (.sort 0) (.var 0)))

def fixtures : List (String × Expr) := [
  ("app", .app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)),
  ("lam", lambdaTelescope),
  ("lam_local_unique", .lam ⟨.linear, .localUnique⟩ (.sort 0) (.var 0)),
  ("lam_affine_local", .lam ⟨.affine, .localShared⟩ (.sort 0) (.var 0)),
  ("all", .all ⟨.linear, .localUnique⟩ .localUnique (.sort 0)
    (.all .many .shared (.sort 0) (.var 0))),
  ("ordinary_let", .letE ⟨true, .value, ⟨.erased, .unique⟩⟩ (.sort 0) (.nat 1) (.var 0)),
  ("local_unique_let", .letE ⟨false, .value, ⟨.affine, .localUnique⟩⟩ (.sort 0) (.var 1) (.var 0)),
  ("borrow", .letE (.borrow false .affine) (.sort 0) (.prj 2 1 (.var 1)) (.var 0)),
  ("borrow_nondep", .letE (.borrow true .many) (.sort 0) (.var 1) (.var 0)),
  ("reference", .ref 0 #[]),
  ("recursion", .recur 2 #[0, 1])
]

def valueContracts : Array ValueContract := #[.unique, .shared, .localUnique, .localShared]
def usages : Array Uses := #[.erased, .linear, .affine, .many]

/-- Every representable combination. Resource validity is checked separately
from these representation tests, including for borrow-let contracts. -/
def modeCases : List ExprCase := Id.run do
  let mut cases := #[]
  for v in [:4] do
    for u in [:4] do
      let contract : BinderContract := ⟨usages[u]!, valueContracts[v]!⟩
      let code := (u + 4 * v).toUInt8
      cases := cases.push ⟨s!"lambda-{u}-{v}", .lam contract (.sort 0) (.var 0),
        ByteArray.mk #[0x81, code, 0x00, 0x10]⟩
      for r in [:4] do
        cases := cases.push ⟨s!"forall-{u}-{v}-{r}",
          .all contract valueContracts[r]! (.sort 0) (.var 0),
          ByteArray.mk #[0x91, code + 16 * r.toUInt8, 0x00, 0x10]⟩
      for flags in [:4] do
        let lc : LetContract := {
          nonDep := flags % 2 == 1
          kind := if flags / 2 == 1 then .borrowShared else .value
          binder := contract
        }
        cases := cases.push ⟨s!"let-{u}-{v}-{flags}", .letE lc (.sort 0) (.var 1) (.var 0),
          ByteArray.mk #[0xA0 + flags.toUInt8, code, 0x00, 0x11, 0x10]⟩
  return cases.toList

/-- Load independent golden bytes once for the Lean, Rust FFI, and VM suites. -/
def readExprCases : IO (List ExprCase) := do
  let file ← IO.FS.readFile "Tests/Fixtures/ixon-v3/expressions.txt"
  let lines := file.splitOn "\n"
  let golden : List ExprCase ← fixtures.mapM fun (name, expr) => do
    let some line := lines.find? (·.startsWith (name ++ " "))
      | throw <| IO.userError s!"missing fixture {name}"
    let [_, hex] := line.splitOn " "
      | throw <| IO.userError s!"invalid fixture row: {line}"
    let some bytes := bytesOfHex hex
      | throw <| IO.userError s!"invalid fixture hex: {name}"
    return { name, expr, bytes }
  return golden ++ modeCases

def checkBytes (name : String) (expr : Expr) (expected : ByteArray) : IO Nat := do
  let actual := runPut (putExpr expr)
  unless actual == expected do
    throw <| IO.userError s!"{name}: bytes {hexOfBytes actual} != {hexOfBytes expected}"
  match runGetExact getExpr expected with
  | .ok decoded => unless decoded == expr do
      throw <| IO.userError s!"{name}: decoded expression differs"
  | .error e => throw <| IO.userError s!"{name}: {e}"
  if (runGetExact getExpr (expected.push 0)).toOption.isSome then
    throw <| IO.userError s!"{name}: accepted trailing byte"
  for n in [0:expected.size] do
    if (runGetExact getExpr (expected.extract 0 n)).toOption.isSome then
      throw <| IO.userError s!"{name}: accepted truncation at {n}"
  return expected.size + 3

def malformedCases : Array (String × ByteArray) := #[
  ("empty-app", .mk #[0x70]),
  ("empty-lambda", .mk #[0x80]),
  ("empty-forall", .mk #[0x90]),
  ("split-app-telescope", .mk #[0x71, 0x71, 0x10, 0x11, 0x12]),
  ("split-lambda-telescope", .mk #[0x81, 0x07, 0x00, 0x81, 0x07, 0x00, 0x10]),
  ("split-forall-telescope", .mk #[0x91, 0x17, 0x00, 0x91, 0x17, 0x00, 0x10]),
  ("reserved-let-flags", .mk #[0xA4, 0x07, 0x00, 0x10, 0x10]),
  ("nonminimal-variable", .mk #[0x18, 0x00]),
  ("nonminimal-reference-count", .mk #[0x28, 0x07, 0x00]),
  ("nonminimal-reference-index", .mk #[0x20, 0x80, 0x00]),
  ("truncated-lambda-telescope", .mk #[0x87, 0x07, 0x00, 0x10]),
  ("truncated-app-telescope", .mk #[0x77, 0x10])
]

/-- Shared raw rejection cases for the native Lean decoder and VM. -/
def rejectedExprCases : Array (String × ByteArray) := Id.run do
  let mut cases := malformedCases
  for code in [16:256] do
    cases := cases.push (s!"lambda-reserved-binder-{code}", .mk #[0x81, code.toUInt8, 0x00, 0x10])
    cases := cases.push (s!"let-reserved-binder-{code}", .mk #[0xA0, code.toUInt8, 0x00, 0x10, 0x10])
  for code in [64:256] do
    cases := cases.push (s!"forall-reserved-bits-{code}", .mk #[0x91, code.toUInt8, 0x00, 0x10])
  return cases

def runGolden (cases : List ExprCase) : IO Nat := do
  let mut checks := 0
  for test in cases do
    checks := checks + (← checkBytes test.name test.expr test.bytes)
  for (name, bytes) in rejectedExprCases do
    if (runGetExact getExpr bytes).toOption.isSome then
      throw <| IO.userError s!"{name}: accepted noncanonical bytes {hexOfBytes bytes}"
    checks := checks + 1
  return checks

end Tests.IxonV3
