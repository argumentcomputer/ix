import Compilatrix.Tools.Check
import Compilatrix.Tools.AiurCheck
import Compilatrix.Aiur.AIR.Memory.Model

/-! Compare the Lean memory builder with frozen outputs of the actual
pinned Rust builder. These are expression graphs, not accepted STARK proofs. -/

namespace Compilatrix.Tools.AiurMemoryCheck

open Lean System Check
open Compilatrix.Aiur.AIR (Circuit Lookup)

private def tuple (fields : List Json) : Json := Json.arr fields.toArray

def expression : Compilatrix.Aiur.AIR.Expr → Json
  | .constant value => tuple [toJson "constant", toJson (toString value.n)]
  | .main column => tuple [toJson "main", toJson column]
  | .next column => tuple [toJson "next", toJson column]
  | .transition => tuple [toJson "transition"]
  | .add left right => tuple [toJson "add", expression left, expression right]
  | .sub left right => tuple [toJson "sub", expression left, expression right]
  | .mul left right => tuple [toJson "mul", expression left, expression right]
  | .neg value => tuple [toJson "neg", expression value]

def lookup (value : Lookup) : Json := Json.mkObj [
  ("multiplicity", expression value.multiplicity),
  ("arguments", tuple (value.arguments.map expression))]

def circuit (bucket : Nat) : Json :=
  let built := Compilatrix.Aiur.AIR.Memory.build bucket
  Json.mkObj [("bucket", toJson bucket),
    ("zeros", tuple (built.zeros.map expression)),
    ("lookups", tuple (built.lookups.map lookup))]

def report : Json := Json.mkObj [
  ("schema", toJson "aiur-memory-air/1"),
  ("ix_revision", toJson AiurCheck.revision),
  ("multi_stark_revision", toJson "9a90612286625b6cec59516532d4501677cf468c"),
  ("circuits", tuple ([0, 1, 2, 7, 256].map circuit))]

def verifyValue (value : Json) : IO Unit :=
  need (value == report) "memory AIR graph differs from the pinned reference fixture"

private def replace (value : Json) (key : String) (replacement : Json) : IO Json := do
  return Json.mkObj ((← pairs value).map fun (name, entry) =>
    (name, if name == key then replacement else entry))

private def reject (label : String) (value : Json) : IO Unit := do
  let rejected ← try verifyValue value; pure false catch _ => pure true
  need rejected s!"memory AIR mutation accepted: {label}"

def mutationChecks : IO Unit := do
  reject "revision" (← replace report "ix_revision" (toJson "wrong"))
  let circuits ← arrField report "circuits"
  reject "missing circuit" (← replace report "circuits" (toJson (circuits.toList.drop 1)))
  let first := circuits[0]!
  let zeros ← arrField first "zeros"
  let lookups ← arrField first "lookups"
  let pull := lookups[0]!
  let arguments ← arrField pull "arguments"
  let changes ← [
    ("bucket", replace first "bucket" (toJson (1 : Nat))),
    ("activity", replace first "zeros" (toJson (zeros.toList.eraseIdx 1))),
    ("transition", replace first "zeros" (toJson (zeros.set! 2
      (expression (.mul (.next 1) (.sub (.main 1) (.constant 1))))))),
    ("pull sign", do
      let pull ← replace pull "multiplicity" (expression (.main 0))
      replace first "lookups" (toJson [pull])),
    ("channel", do
      let pull ← replace pull "arguments" (toJson (arguments.set! 0 (expression (.constant 2))))
      replace first "lookups" (toJson [pull])),
    ("pointer", do
      let pull ← replace pull "arguments" (toJson (arguments.set! 2 (expression (.main 0))))
      replace first "lookups" (toJson [pull]))].mapM fun (label, action) => return (label, ← action)
  for (label, changed) in changes do
    reject label (← replace report "circuits" (toJson (circuits.set! 0 changed)))

def emit (path : FilePath) : IO Unit := IO.FS.writeFile path (report.pretty ++ "\n")

def verifyFixtures (root : FilePath) : IO Unit := IO.FS.withTempDir fun temporary => do
  let expected ← readJson (root / "fixtures/aiur-memory-air/expected.json")
  verifyValue expected
  let output := temporary / "memory-air.json"
  let _ ← Check.run (← IO.appPath).toString #["--dump-memory-air", output.toString]
  let fresh ← readJson output
  need (fresh == expected) "fresh-process memory AIR graph differs"
  mutationChecks
  IO.println "aiur-memory-air-check-ok: 5 Rust reference graphs, fresh-process export, 8 mutation rejections"

end Compilatrix.Tools.AiurMemoryCheck
