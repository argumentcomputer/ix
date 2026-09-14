/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.FrontendExpressions

open Aiur Aiur.NativeAIR

namespace AiurTests.FrontendExpressions

private def fixtures : Array Expr := Id.run do
  let mut result : Array Expr := #[.konst 0, .konst 1, .konst (0 - 1), .konst 17]
  for source in [Source.preprocessed, .main, .stage2] do
    for offset in [RowOffset.current, .next] do
      result := result.push (.var ⟨source, offset, 2⟩)
  let x := (mainCurrent 0).expr
  let y := (mainCurrent 1).expr
  return result ++ #[.publicInput 0, .publicInput 2, .isFirstRow, .isLastRow, .isTransition,
    .neg x, .add x y, .sub (.konst 0) x, .mul (.konst 0) y,
    .neg (.konst 0), .neg (.konst 1), .neg (.neg x), .neg (.neg (.konst 1)),
    .add (.konst 1) (.konst 1)]

private def matrix (seed slot : Nat) : Array G := Array.ofFn fun index : Fin 16 =>
  let choices : Array G := #[0, 1, 2, 17, 255, 256, 65536, 0 - 1]
  if slot == 2 && index.val == 6 then (#[0, 1, 2, 0 - 1] : Array G)[seed]?.getD 0
  else choices[(slot * 3 + seed * 5 + index.val * 7) % choices.size]?.getD 0

private def assignment (seed : Nat) : Values G :=
  ⟨(fun source offset => matrix seed
    ((match source with | .preprocessed => 0 | .main => 2 | .stage2 => 4) +
      (match offset with | .current => 0 | .next => 1))),
    matrix seed 6, (if seed == 0 then 1 else 0), (if seed == 3 then 1 else 0),
    (if seed == 3 then 0 else 1)⟩

private abbrev Reader := StateT (ByteArray × Nat) (Except String)

private def takeBytes (count : Nat) : Reader ByteArray := do
  let (bytes, cursor) ← get
  if cursor + count > bytes.size then throw s!"frontend snapshot truncated at {cursor}"
  set (bytes, cursor + count)
  return bytes.extract cursor (cursor + count)

private def readNat (count : Nat := 8) : Reader Nat := do
  let bytes ← takeBytes count
  let mut value := 0
  for index in [:count] do value := value + bytes[index]!.toNat * 256^index
  return value

private def readField : Reader G := do
  let value ← readNat
  unless value < gSize.toNat do throw "noncanonical frontend field value"
  return G.ofNat value

private def readBool : Reader Bool := do
  match ← readNat with
  | 0 => return false
  | 1 => return true
  | _ => throw "invalid frontend boolean"

private def readList (count : Nat) (reader : Reader α) : Reader (List α) :=
  (List.range count).mapM fun _ => reader

private def readExpr : Nat → Reader Expr
  | 0 => throw "frontend expression exceeds snapshot depth bound"
  | fuel + 1 => do
    match ← readNat 1 with
    | 0 => return .konst (← readField)
    | 1 =>
      let source ← match ← readNat 1 with
        | 0 => pure Source.preprocessed | 1 => pure Source.main | 2 => pure Source.stage2
        | _ => throw "invalid frontend column source"
      let offset ← match ← readNat 1 with
        | 0 => pure RowOffset.current | 1 => pure RowOffset.next
        | _ => throw "invalid frontend row offset"
      return .var ⟨source, offset, ← readNat⟩
    | 2 => return .publicInput (← readNat)
    | 3 => return .isFirstRow
    | 4 => return .isLastRow
    | 5 => return .isTransition
    | 6 => return .add (← readExpr fuel) (← readExpr fuel)
    | 7 => return .sub (← readExpr fuel) (← readExpr fuel)
    | 8 => return .mul (← readExpr fuel) (← readExpr fuel)
    | 9 => return .neg (← readExpr fuel)
    | _ => throw "invalid frontend expression tag"

private def readFixture : Reader Expr := do
  let index ← readNat
  let some expr := fixtures[index]? | throw "frontend fixture index out of range"
  return expr

private def readSmart : Reader Unit := do
  let kind ← readNat 1
  let left ← readFixture
  let right ← readFixture
  let expected ← match kind with
    | 0 => pure (left.frontAdd right)
    | 1 => pure (left.frontSub right)
    | 2 => pure (left.frontMul right)
    | 3 => pure left.frontNeg
    | _ => throw "invalid smart operation tag"
  let actual ← readExpr 64
  unless actual == expected do throw s!"native smart-constructor tree differs for operation {kind}"
  unless (← readBool) == expected.isConstant do throw "native smart constant flag differs"
  if left.noConstantNegs && (kind == 3 || right.noConstantNegs) then
    unless expected.noConstantNegs do throw "smart constructor lost the negation invariant"
  for seed in [:4] do
    let value ← readField
    unless expected.eval goldilocksOps (assignment seed) == some value do
      throw s!"native smart value differs for operation {kind}, assignment {seed}"

private def sameEmission (left right : AIR.OpEmission) : Bool :=
  left.outputs == right.outputs && left.used == right.used && left.equations == right.equations &&
    left.queries.isEmpty && right.queries.isEmpty && left.calls.isEmpty && right.calls.isEmpty

private def readEmission : Reader Unit := do
  let kind ← readNat 1
  let leftExpr ← readFixture
  let rightExpr ← readFixture
  let left : RowExpr := ⟨leftExpr, ← readNat⟩
  let right : RowExpr := ⟨rightExpr, ← readNat⟩
  unless left.expr.noConstantNegs && right.expr.noConstantNegs do throw "invalid core expression fixture"
  let used ← readNat
  let degree ← readNat
  let output ← readExpr 64
  let equationCount ← readNat
  unless equationCount ≤ 2 do throw "too many core equations"
  let equations ← readList equationCount (readExpr 64)
  let selector := (mainCurrent 6).expr
  let (expected, op) ← match kind with
    | 0 => pure (emitEqZero selector 7 left, Bytecode.Op.eqZero 0)
    | 1 => pure (ScalarEmission.mk (left.add right) 0 [], Bytecode.Op.add 0 1)
    | 2 => pure (ScalarEmission.mk (left.sub right) 0 [], Bytecode.Op.sub 0 1)
    | 3 => pure (emitMul selector 7 left right, Bytecode.Op.mul 0 1)
    | _ => throw "invalid scalar operation tag"
  unless output == expected.output.expr && degree == expected.output.degree &&
      used == expected.used && equations == expected.equations do
    throw s!"native scalar expression emission differs for operation {kind}"
  unless expected.output.expr.noConstantNegs do throw "scalar output lost the negation invariant"
  for seed in [:4] do
    let value ← readField
    let constant ← readBool
    let polynomialValues ← readList equationCount readField
    let values := assignment seed
    let some evaluated := expected.eval values | throw "scalar expression evaluation failed"
    let native : AIR.OpEmission := {
      outputs := #[⟨value, degree, constant⟩], used, equations := polynomialValues }
    unless sameEmission evaluated native do throw "native scalar evaluated emission differs"
    let some a := left.eval values | throw "scalar left input evaluation failed"
    let some b := right.eval values | throw "scalar right input evaluation failed"
    let row := fun index => (matrix seed 2)[7 + index]?.getD 0
    let selected := (matrix seed 2)[6]?.getD 0
    let some valued := AIR.emitOp row selected 0 op #[a, b] | throw "valued scalar emission failed"
    unless sameEmission evaluated valued do throw "symbolic and valued scalar emissions differ"

private def readCorpus : Reader Unit := do
  let header := "Aiur frontend expressions v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "frontend snapshot version differs"
  let count ← readNat
  unless count == 24 && fixtures.size == 24 do throw "incomplete frontend fixtures"
  unless (← readList count (readExpr 64)).toArray == fixtures do throw "frontend input trees differ"
  unless (fixtures.filter (·.noConstantNegs)).size == 21 do throw "incomplete negation-invariant boundary cases"
  unless (← readNat) == 1752 do throw "incomplete smart-constructor corpus"
  for _ in [:1752] do readSmart
  unless (← readNat) == 9804 do throw "incomplete scalar-emission corpus"
  for _ in [:9804] do readEmission
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "frontend snapshot has trailing bytes"

def run (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match readCorpus.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok _ => IO.println "frontend expressions: 1,752 smart trees, 9,804 scalar emissions and 46,224 native/Lean assignments match"

end AiurTests.FrontendExpressions

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.FrontendExpressions.run path
  | _ => throw (IO.userError "expected native frontend-expression snapshot")
