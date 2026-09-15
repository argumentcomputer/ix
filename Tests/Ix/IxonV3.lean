module
public import Ix.Ixon
public import Ix.Sharing

public section

namespace Tests.IxonV3
open Ixon

def fixtures : List (String × Expr) := [
  ("app", .app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)),
  ("lam", .lam .many (.sort 0) (.lam .many (.sort 0) (.lam .many (.sort 0) (.var 0)))),
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
def modeCases : List (String × Expr × ByteArray) := Id.run do
  let mut cases := #[]
  for v in [:4] do
    for u in [:4] do
      let contract : BinderContract := ⟨usages[u]!, valueContracts[v]!⟩
      let code := (u + 4 * v).toUInt8
      cases := cases.push (s!"lambda-{u}-{v}", .lam contract (.sort 0) (.var 0),
        ByteArray.mk #[0x81, code, 0x00, 0x10])
      for r in [:4] do
        cases := cases.push (s!"forall-{u}-{v}-{r}",
          .all contract valueContracts[r]! (.sort 0) (.var 0),
          ByteArray.mk #[0x91, code + 16 * r.toUInt8, 0x00, 0x10])
      for flags in [:4] do
        let lc : LetContract := {
          nonDep := flags % 2 == 1
          kind := if flags / 2 == 1 then .borrowShared else .value
          binder := contract
        }
        cases := cases.push (s!"let-{u}-{v}-{flags}", .letE lc (.sort 0) (.var 1) (.var 0),
          ByteArray.mk #[0xA0 + flags.toUInt8, code, 0x00, 0x11, 0x10])
  return cases.toList

def modeFixtures : List (String × Expr) := modeCases.map fun (label, expr, _) => (label, expr)

def parseHex : List Char → Except String (List UInt8)
  | [] => .ok []
  | hi :: lo :: rest => do
    let some hi := natOfHex hi | throw "invalid hex digit"
    let some lo := natOfHex lo | throw "invalid hex digit"
    return (hi * 16 + lo).toUInt8 :: (← parseHex rest)
  | _ => .error "odd hex length"

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

def malformed : Array ByteArray := (#[] : Array ByteArray) ++ #[
  .mk #[0x70], .mk #[0x80], .mk #[0x90],
  .mk #[0x71, 0x71, 0x10, 0x11, 0x12],
  .mk #[0x81, 0x07, 0x00, 0x81, 0x07, 0x00, 0x10],
  .mk #[0x91, 0x17, 0x00, 0x91, 0x17, 0x00, 0x10],
  .mk #[0xA4, 0x07, 0x00, 0x10, 0x10],
  .mk #[0x18, 0x00], .mk #[0x28, 0x07, 0x00], .mk #[0x20, 0x80, 0x00],
  .mk #[0x87, 0x07, 0x00, 0x10], .mk #[0x77, 0x10]
]

def runGolden : IO Nat := do
  let file ← IO.FS.readFile "Tests/Fixtures/ixon-v3/expressions.txt"
  let mut checks := 0
  for (name, expr) in fixtures do
    let some line := (file.splitOn "\n").find? (·.startsWith (name ++ " "))
      | throw <| IO.userError s!"missing fixture {name}"
    let some hex := (line.splitOn " ")[1]?
      | throw <| IO.userError s!"missing bytes for {name}"
    let expected ← match parseHex hex.toList with
      | .ok bytes => pure (ByteArray.mk bytes.toArray)
      | .error e => throw <| IO.userError e
    checks := checks + (← checkBytes name expr expected)
  for (name, expr, expected) in modeCases do
    checks := checks + (← checkBytes name expr expected)
  for bytes in malformed do
    if (runGetExact getExpr bytes).toOption.isSome then
      throw <| IO.userError s!"accepted noncanonical bytes {hexOfBytes bytes}"
    checks := checks + 1
  for code in [16:256] do
    for bytes in #[ByteArray.mk #[0x81, code.toUInt8, 0x00, 0x10],
        ByteArray.mk #[0xA0, code.toUInt8, 0x00, 0x10, 0x10]] do
      if (runGetExact getExpr bytes).toOption.isSome then
        throw <| IO.userError s!"accepted reserved contract bits {code}"
      checks := checks + 1
  for code in [64:256] do
    if (runGetExact getExpr (.mk #[0x91, code.toUInt8, 0x00, 0x10])).toOption.isSome then
      throw <| IO.userError s!"accepted reserved forall bits {code}"
    checks := checks + 1
  return checks

end Tests.IxonV3
