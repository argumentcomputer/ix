import Compilatrix.Tools.AiurMemoryCheck
import CompilatrixTests.Aiur.RankAIR.Fixtures

/-! Frozen conformance against the actual pinned Rust constraint builder
and all rows of the fixed table's scalar-range column projection. -/

namespace Compilatrix.Tools.AiurRankCheck

open Lean System Check
open Compilatrix.Aiur.AIR
open Compilatrix.Aiur.AIR.Rank

private def tuple (fields : List Json) : Json := Json.arr fields.toArray

private def circuit (built : Circuit) : Json := Json.mkObj [
  ("width", toJson built.width), ("selectors", toJson ([1, 2] : List Nat)),
  ("zeros", tuple (built.zeros.map AiurMemoryCheck.expression)),
  ("lookups", tuple (built.lookups.map AiurMemoryCheck.lookup))]

def report : Json := Json.mkObj [
  ("schema", toJson "aiur-rank-air/1"),
  ("ix_revision", toJson AiurCheck.revision),
  ("multi_stark_revision", toJson "9a90612286625b6cec59516532d4501677cf468c"),
  ("range", Json.mkObj [("main_width", toJson (8 : Nat)),
    ("preprocessed_width", toJson (11 : Nat)), ("height", toJson (65536 : Nat)),
    ("projection_columns", toJson ([0, 1] : List Nat)),
    ("pull", AiurMemoryCheck.lookup rangePull)]),
  ("fixtures", tuple (CompilatrixTests.Aiur.RankAIR.graphFixtures.map fun (name, circuits) =>
    Json.mkObj [("name", toJson name), ("circuits", tuple (circuits.map circuit))]))]

def rangeProjection : ByteArray := Id.run do
  let mut result := ByteArray.emptyWithCapacity 131072
  for index in [:65536] do
    result := result.push (index / 256).toUInt8
    result := result.push (index % 256).toUInt8
  return result

def verifyValue (value : Json) : IO Unit :=
  need (value == report) "rank AIR graph differs from the pinned reference fixture"

def verifyProjection (bytes : ByteArray) : IO Unit :=
  need (bytes == rangeProjection) "scalar-u16 fixed-table projection differs from Rust"

private def replace (value : Json) (key : String) (replacement : Json) : IO Json := do
  return Json.mkObj ((← pairs value).map fun (name, entry) =>
    (name, if name == key then replacement else entry))

private def reject (label : String) (value : Json) : IO Unit := do
  let rejected ← try verifyValue value; pure false catch _ => pure true
  need rejected s!"rank AIR mutation accepted: {label}"

private def rejectProjection (label : String) (bytes : ByteArray) : IO Unit := do
  let rejected ← try verifyProjection bytes; pure false catch _ => pure true
  need rejected s!"rank range-table mutation accepted: {label}"

def mutationChecks : IO Unit := do
  reject "revision" (← replace report "ix_revision" (toJson "wrong"))
  let fixtures ← arrField report "fixtures"
  reject "missing fixture" (← replace report "fixtures" (toJson (fixtures.toList.drop 1)))
  let first := fixtures[0]!
  let circuits ← arrField first "circuits"
  let parent := circuits[0]!
  let lookups ← arrField parent "lookups"
  let call := lookups[4]!
  let args ← arrField call "arguments"
  for (label, rank) in [
      ("missing positive step", packColumns 3),
      ("reversed limbs", pack (.main 5) (.main 4) (.main 3)),
      ("bound instead of ordered", Expr.main 7)] do
    let changedCall ← replace call "arguments" (toJson (args.set! 4 (AiurMemoryCheck.expression rank)))
    let changedParent ← replace parent "lookups" (toJson (lookups.set! 4 changedCall))
    let changedFixture ← replace first "circuits" (toJson (circuits.set! 0 changedParent))
    reject label (← replace report "fixtures" (toJson (fixtures.set! 0 changedFixture)))
  let provider := lookups[0]!
  let providerArgs ← arrField provider "arguments"
  let changedProvider ← replace provider "arguments" (toJson (providerArgs.toList.take 4))
  let changedParent ← replace parent "lookups" (toJson (lookups.set! 0 changedProvider))
  let changedFixture ← replace first "circuits" (toJson (circuits.set! 0 changedParent))
  reject "erased provider rank" (← replace report "fixtures" (toJson (fixtures.set! 0 changedFixture)))
  let range ← field report "range"
  for (label, key, value) in [
      ("wrong range height", "height", toJson (256 : Nat)),
      ("reversed preprocessed columns", "projection_columns", toJson ([1, 0] : List Nat)),
      ("wrong range channel", "pull", AiurMemoryCheck.lookup { rangePull with
        arguments := [.constant 11, .add (.mul (.preprocessed 0) (.constant 256)) (.preprocessed 1)] }),
      ("wrong range sign", "pull", AiurMemoryCheck.lookup { rangePull with multiplicity := .main 7 })] do
    reject label (← replace report "range" (← replace range key value))
  let gated := fixtures[5]!
  let gatedCircuits ← arrField gated "circuits"
  let ungated ← replace gated "circuits" (toJson (gatedCircuits.set! 0 parent))
  reject "removed selector gating" (← replace report "fixtures" (toJson (fixtures.set! 5 ungated)))
  rejectProjection "short table" (rangeProjection.extract 0 131070)
  rejectProjection "changed first row" (rangeProjection.set! 0 1)
  rejectProjection "changed last row" (rangeProjection.set! 131071 0)

def emit (directory : FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "expected.json") (report.pretty ++ "\n")
  IO.FS.writeBinFile (directory / "range-columns.bin") rangeProjection

def verifyFixtures (root : FilePath) : IO Unit := IO.FS.withTempDir fun temporary => do
  let source := root / "fixtures/aiur-rank-air"
  let expected ← readJson (source / "expected.json")
  let projection ← IO.FS.readBinFile (source / "range-columns.bin")
  verifyValue expected
  verifyProjection projection
  let output := temporary / "rank-air"
  let _ ← Check.run (← IO.appPath).toString #["--dump-rank-air", output.toString]
  need ((← readJson (output / "expected.json")) == expected) "fresh-process rank graph differs"
  need ((← IO.FS.readBinFile (output / "range-columns.bin")) == projection) "fresh-process range table differs"
  mutationChecks
  IO.println "aiur-rank-air-check-ok: 6 Rust fixtures, 65536 fixed rows, fresh-process export, 14 mutation rejections"

end Compilatrix.Tools.AiurRankCheck
