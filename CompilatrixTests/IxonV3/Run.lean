import CompilatrixTests.IxonV3.Fixtures
import CompilatrixTests.IxonV3.Handoff
import CompilatrixTests.IxonV3.Typing
import CompilatrixTests.IxonV3.Primitives
import CompilatrixTests.IxonV3.Catalog.Run
import CompilatrixTests.IxonV3.K1
import Compilatrix.Tools.Check

namespace CompilatrixTests.IxonV3

open Compilatrix.Ixon Compilatrix.Ixon.V3

private def require (accepted : Bool) (message : String) : IO Unit :=
  unless accepted do throw (IO.userError message)

private def hex (source : String) : IO ByteArray :=
  IO.ofExcept (Compilatrix.Tools.Check.unhex source)

private def dataLines (file : System.FilePath) : IO (List String) := do
  return (← IO.FS.readFile file).splitOn "\n" |>.filter fun line =>
    !line.isEmpty && !line.startsWith "#"

def run : IO Bool := do
  try
    let root : System.FilePath := "fixtures/ixon-v3"
    let mut assertions := 0
    for line in ← dataLines (root / "expressions.txt") do
      let [label, encoded] := line.splitOn " "
        | throw (IO.userError "invalid expression fixture row")
      let bytes ← hex encoded
      let decoded ← IO.ofExcept (decodeExpr bytes)
      require (exprBytes decoded.value == bytes) s!"expression bytes differ: {label}"
      assertions := assertions + 1
      for length in [:bytes.size] do
        require ((decodeExpr (bytes.extract 0 length)).toOption.isNone)
          s!"accepted truncated expression: {label}/{length}"
        assertions := assertions + 1
      require ((decodeExpr (bytes.push 0)).toOption.isNone) s!"accepted trailing byte: {label}"
      assertions := assertions + 1
    for code in [:256] do
      let binder := BinderContract.ofBits? code.toUInt8
      require (binder.isSome == (code < 16)) s!"binder reserved bits accepted: {code}"
      if let some value := binder then
        require (value.toBits.toNat == code) s!"binder contract lost bits: {code}"
      let arrow := unpackAllContract? code.toUInt8
      require (arrow.isSome == (code < 64)) s!"arrow reserved bits accepted: {code}"
      if let some (input, result) := arrow then
        require ((packAllContract input result).toNat == code) s!"arrow contract lost bits: {code}"
      assertions := assertions + 2 + (if binder.isSome then 1 else 0) + (if arrow.isSome then 1 else 0)
    for line in ← dataLines (root / "resource.tsv") do
      let [label, expected, typeHex, bodyHex] := line.splitOn "\t"
        | throw (IO.userError "invalid resource fixture row")
      let type ← IO.ofExcept (decodeExpr (← hex typeHex))
      let body ← IO.ofExcept (decodeExpr (← hex bodyHex))
      let actual := match Fixtures.runCase type.value body.value with
        | .ok _ => "ok"
        | .error error => Fixtures.errorCode error
      require (actual == expected) s!"resource {label}: expected {expected}, got {actual}"
      assertions := assertions + 1
    let huge := tag4Bytes ⟨8, UInt64.ofNat (UInt64.size - 1)⟩
    require ((decodeExpr huge).toOption.isNone) "accepted impossible telescope count"
    require ((decodeExpr (← hex "a400000000")).toOption.isNone) "accepted reserved let flags"
    require ((decodeExpr (← hex "81200010")).toOption.isNone) "accepted reserved binder bits"
    require ((decodeExpr (← hex "91400000")).toOption.isNone) "accepted reserved arrow bits"
    assertions := assertions + 4
    let bounded : Compilatrix.Ixon.V3.Expr := .lam .many (.sort 0) (.var 0)
    require ((decodeExpr (exprBytes bounded) (depth := 2)).toOption.isSome)
      "rejected expression at exact depth bound"
    let nested := Compilatrix.Ixon.V3.Expr.lam .many (.sort 0) bounded
    require ((decodeExpr (exprBytes nested) (depth := 2)).toOption.isNone)
      "telescope bypassed semantic expression depth"
    let oversizedLevels := tag4Bytes ⟨2, 4097⟩ ++ tag0Bytes ⟨0⟩ ++
      ByteArray.mk (Array.replicate 4097 0)
    require ((decodeExpr oversizedLevels).toOption.isNone) "universe arguments bypassed count bound"
    assertions := assertions + 3
    assertions := assertions + (← handoff root)
    assertions := assertions + (← Typing.run root)
    assertions := assertions + (← Primitives.run root)
    assertions := assertions + (← CatalogTests.run root)
    assertions := assertions + (← K1.run root)
    IO.println s!"ixon-v3-tests-ok: {assertions} contract, wire, typing, and resource assertions"
    return true
  catch error =>
    IO.eprintln s!"FAIL: Ixon v3: {error}"
    return false

end CompilatrixTests.IxonV3
