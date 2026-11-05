import Ix.IxVM.Toplevel
import Ix.IxVM.FunctionGroups
import Ix.Aiur.Statistics
import Ix.Ixon
import Lean.Data.Json

/-! Per-function query heights and actual AIR shapes for full-closure IxVM
claims. Arguments: `IXE CONSTANT OUTPUT_JSON`. Execution always uses the
generic bytecode backend, so source and grouping changes can be profiled
before regenerating native Rust/CUDA. Its elapsed time is a diagnostic, not
a native-execution benchmark; query counts and FFT costs are comparable.

The JSON is the input of `Scripts/Performance/FunctionGrouping.lean`.
The system uses the benchmark's recursive parameters: blowup 4, 50 queries,
and zero proof-of-work bits. No dependency, role, or admission check is skipped.
-/

open Lean (Json toJson)

/-- A stale-profile diagnostic over the complete function library. Circuit
grouping is excluded so the same execution counts can evaluate new groups. -/
private def libraryDigest (compiled : Aiur.CompiledToplevel) : String :=
  toString (Address.blake3 (reprStr (compiled.bytecode.functions, compiled.bytecode.memorySizes)).toUTF8)

private def profile (compiled : Aiur.CompiledToplevel) (queries : Array Aiur.QueryCount)
    (shapes : Array Aiur.CircuitShape) (metadata : List (String × Json)) : Json := Id.run do
  let mut names : Std.HashMap Nat (Array String) := {}
  for (name, index) in compiled.nameMap do
    let old := names.getD index #[]
    names := names.erase index
    names := names.insert index (old.push (toString name))
  let functions := compiled.bytecode.functions.mapIdx fun i f =>
    let q := queries[i]!
    Json.mkObj [
      ("index", toJson i), ("names", toJson (names.getD i #[])),
      ("rows", toJson q.uniqueRows), ("hits", toJson q.totalHits),
      ("constrained", toJson f.constrained),
      ("inputs", toJson f.layout.inputSize), ("selectors", toJson f.layout.selectors),
      ("auxiliaries", toJson f.layout.auxiliaries), ("lookups", toJson f.layout.lookups)]
  let circuits := compiled.bytecode.circuits.mapIdx fun i c =>
    let shape := shapes[i]!
    let rows := c.members.foldl (fun n j => n + queries[j]!.uniqueRows) 0
    Json.mkObj [
      ("name", toJson c.name), ("members", toJson c.members), ("rows", toJson rows),
      ("mainWidth", toJson shape.mainWidth), ("stage2Width", toJson shape.stage2Width),
      ("quotientDegree", toJson shape.quotientDegree),
      ("committedWidth", toJson shape.committedWidth),
      ("fftCost", toJson (Aiur.fftCost shape rows 2))]
  return Json.mkObj (metadata ++ [("functions", Json.arr functions), ("circuits", Json.arr circuits)])

def main (args : List String) : IO Unit := do
  let [path, label, output] := args | throw (IO.userError "expected IXE NAME OUTPUT")
  let toplevel ← IO.ofExcept IxVM.ixVM
  let compiled ← IO.ofExcept (toplevel.compileWithGroups IxVM.functionGroups)
  let some entry := compiled.getFuncIdx `verify_claim | throw (IO.userError "missing verify_claim")
  let some check := compiled.getFuncIdx `check_const | throw (IO.userError "missing check_const")
  let handle ← IO.ofExcept (Aiur.EnvHandle.fromIxe path)
  let bytes ← IO.FS.readBinFile path
  let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
  let address ← match env.named.get? (Ix.Name.fromLeanName label.toName) with
    | some named => pure named.addr
    | none => match env.named.toArray.find? (fun (name, _) => toString name == label) with
      | some (_, named) => pure named.addr
      | none => throw (IO.userError s!"missing {label}")
  let system := Aiur.AiurSystem.build compiled.bytecode { logBlowup := 2, capHeight := 0 }
    { logFinalPolyLen := 0, maxLogArity := 1, numQueries := 50,
      commitProofOfWorkBits := 0, queryProofOfWorkBits := 0 }
  let shapes := system.circuitShapes
  IO.println s!"profiling {label}: functions={compiled.bytecode.functions.size} circuits={shapes.size}"
  (← IO.getStdout).flush
  let start ← IO.monoMsNow
  let (_, _, queries) ← IO.ofExcept (← IO.lazyPure fun _ =>
    compiled.bytecode.checkAddrWithEnv entry handle address.hash true)
  let elapsed := (← IO.monoMsNow) - start
  let stats := Aiur.computeStats compiled queries shapes 2
  IO.println s!"{label}: constants={queries[check]!.uniqueRows} fft={stats.totalFftCost} interp-ms={elapsed}"
  Aiur.printStats stats
  let metadata := [
    ("libraryDigest", toJson (libraryDigest compiled)),
    ("input", Json.mkObj [("path", toJson path), ("bytes", toJson bytes.size),
      ("binding", toJson (env.roleBinding.map (fun b => toString b.address))),
      ("constant", toJson label)]),
    ("executionBackend", toJson "bytecode"),
    ("constants", toJson queries[check]!.uniqueRows),
    ("totalFftCost", toJson stats.totalFftCost),
    ("logBlowup", toJson (2 : Nat)), ("numQueries", toJson (50 : Nat))]
  IO.FS.writeFile output ((profile compiled queries shapes metadata).pretty ++ "\n")
