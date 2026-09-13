import Compilatrix.Ixby.SymbolicExamples
import Compilatrix.Ixby.SymbolicReport
import Compilatrix.Coverage.Upstream
import Compilatrix.Tools.Check

open Compilatrix Compilatrix.Ixby Compilatrix.Tools.Check
open Lean System

private def digest (text : String) : String := byteHex (Ix.Ixby.Blake3.hash text.toUTF8.data)

private def writeProgram {source config compiled}
    (certificate : @SymbolicCertificate source config compiled) (output : FilePath) : IO Unit := do
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "source.json") (source.json.pretty 100 ++ "\n")
  IO.FS.writeFile (output / "program.txt") (reprStr compiled.program ++ "\n")
  IO.FS.writeFile (output / "config.txt") (reprStr config ++ "\n")
  IO.FS.writeFile (output / "symbolic.json") (certificate.json.pretty 100 ++ "\n")

private def runReference (test : SymbolicExamples.Case) (output : FilePath) : IO Json := do
  let compiled ← checked (compile test.source)
  let certificate ← checked compiled.certifySymbolic
  writeProgram certificate output
  let mut rows : Array Json := #[]
  for seed in [:16] do
    let input := SymbolicExamples.inputs SymbolicExamples.generalPool test.parameters seed
    let args ← checked (Arguments.check test.source {} 64 input)
    let expected := test.expected input
    need (certificate.result.instantiate args.dataAt == expected) s!"symbolic expectation: {test.name} {seed}"
    match evaluated : Ix.Ixby.execute {} compiled.program args.raw 100000 with
    | .error error => throw (IO.userError s!"reference run {test.name}: {reprStr error}")
    | .ok value =>
        have _sourceResult := certificate.refinement 64 args value ⟨100000, evaluated⟩
        let result ← present (decodeData test.source (64 + certificate.dataDepth) value) "reference result decoding"
        need (result == expected) s!"reference expectation: {test.name} {seed}"
        rows := rows.push (Json.mkObj [("input", Json.arr (input.map Data.json)), ("result", result.json)])
  let runs := (Json.arr rows).pretty 100 ++ "\n"
  IO.FS.writeFile (output / "runs.json") runs
  return Json.mkObj [
    ("functions", toJson compiled.program.functions.size),
    ("blocks", toJson (compiled.program.functions.foldl (fun n fn => n + fn.blocks.size) 0)),
    ("program", toJson (digest (reprStr compiled.program ++ "\n"))),
    ("source", toJson (digest (test.source.json.pretty 100 ++ "\n"))),
    ("result", certificate.result.json), ("runs", toJson rows.size), ("runs_digest", toJson (digest runs))]

private def runWire {source config} (compiled : Compiled source config) (output : FilePath)
    (inputs : List (Array Data)) (expected : Array Data → Data) : IO Json := do
  let certificate ← checked compiled.certifySymbolic
  let exported ← checked compiled.export
  writeProgram certificate output
  IO.FS.writeBinFile (output / "profile.ixbp") ⟨exported.profileBytes⟩
  IO.FS.writeBinFile (output / "program.ixby") ⟨exported.programBytes⟩
  let mut rows : Array Json := #[]
  for (data, index) in inputs.zipIdx do
    let args ← checked (Arguments.check source config 64 data)
    let input ← checked (args.export exported)
    match executed : Ix.Ixby.Codec.execute {} exported.programBytes input.bytes 100000 with
    | .error error => throw (IO.userError s!"canonical run: {reprStr error}")
    | .ok execution =>
        have byteRun : Ix.Ixby.Codec.Evaluates {} exported.programBytes input.bytes execution.outputBytes :=
          ⟨100000, by rw [executed]; rfl⟩
        have _sourceResult := certificate.byte_refinement input byteRun
        let result ← present (decodeData source (64 + certificate.dataDepth) execution.output) "canonical result decoding"
        need (result == expected data) "canonical independent expectation differs"
        need (result == certificate.result.instantiate args.dataAt) "canonical symbolic result differs"
        let directory := output / toString index
        IO.FS.createDirAll directory
        IO.FS.writeBinFile (directory / "input.ixbi") ⟨input.bytes⟩
        IO.FS.writeBinFile (directory / "output.ixbo") ⟨execution.outputBytes⟩
        rows := rows.push (Json.mkObj [
          ("input", Json.arr (data.map Data.json)), ("result", result.json),
          ("input_digest", toJson (byteHex (Ix.Ixby.Blake3.hash input.bytes))),
          ("output_digest", toJson (byteHex (Ix.Ixby.Blake3.hash execution.outputBytes)))])
  let runs := (Json.arr rows).pretty 100 ++ "\n"
  IO.FS.writeFile (output / "runs.json") runs
  return Json.mkObj [
    ("program", toJson (byteHex (Ix.Ixby.Blake3.hash exported.programBytes))),
    ("program_bytes", toJson exported.programBytes.size),
    ("result", certificate.result.json), ("runs", toJson rows.size), ("runs_digest", toJson (digest runs))]

private def sourcePool (source : Source) : IO (Array Data) := do
  let zero ← present (source.constructors.find? (fun ctor => ctor.tag == 0 && ctor.fields == 0)) "source zero constructor"
  let succ ← present (source.constructors.find? (fun ctor => ctor.tag == 1 && ctor.fields == 1)) "source successor constructor"
  let nil : Data := .ctor zero.address zero.tag []
  let step := fun data => Data.ctor succ.address succ.tag [data]
  return #[.erased, nil, step nil, step (step nil), step (step (step nil))]

private def asNat : Data → Option Nat
  | .nat n => some n
  | .ctor _ 0 [] => some 0
  | .ctor _ 1 [pred] => (asNat pred).map (· + 1)
  | _ => none

def main (args : List String) : IO UInt32 := cli "source-ixby-symbolic" do
  let (output, upstream) ← match args with
    | [output] => pure (FilePath.mk output, FilePath.mk Coverage.Upstream.directory)
    | [output, upstream] => pure (FilePath.mk output, FilePath.mk upstream)
    | _ => throw (IO.userError "usage: source-ixby-symbolic <new-output-directory> [upstream-directory]")
  need (!(← output.pathExists)) "symbolic fixture requires a new output directory"
  IO.FS.createDirAll output
  let mut rows : Array Json := #[]
  let mut referenceRuns := 0
  let mut canonicalRuns := 0
  for test in SymbolicExamples.cases ++ SymbolicExamples.generated do
    let reference ← runReference test (output / test.name / "reference")
    referenceRuns := referenceRuns + 16
    let wire ← if test.wire then do
        let compiled ← checked (compile test.source Config.crypto)
        let inputs := (List.range 5).map (SymbolicExamples.inputs SymbolicExamples.wirePool test.parameters)
        let wire ← runWire compiled (output / test.name / "wire") inputs test.expected
        canonicalRuns := canonicalRuns + 5
        pure wire
      else pure Json.null
    rows := rows.push (Json.mkObj [("name", toJson test.name), ("parameters", toJson test.parameters),
      ("origin", toJson "ixir0-open"), ("reference", reference), ("wire", wire)])
  for (name, parameters, constants, root) in ← checked SymbolicExamples.ixonSources do
    let compiled ← checked (compileIxon constants root {} Config.crypto parameters)
    let source : Source := {
      declarations := compiled.erasure.erasure.result.raw
      main := entryExpression root parameters, parameters }
    let pool ← sourcePool source
    let inputs := (List.range 5).map (SymbolicExamples.inputs pool parameters)
    let expected := fun input => SymbolicExamples.argument input (if name == "ixon-second" then 1 else 0)
    let wire ← runWire compiled.target (output / name / "wire") inputs expected
    canonicalRuns := canonicalRuns + 5
    rows := rows.push (Json.mkObj [("name", toJson name), ("parameters", toJson parameters),
      ("origin", toJson "checked-ixon-open"), ("reference", Json.null), ("wire", wire)])
  for fixture in Coverage.Upstream.fixtures do
    if let .nat expected := fixture.expected then
      let loaded ← checked (← Coverage.Upstream.load upstream fixture)
      let source := loaded.source
      let compiled ← checked (compileIxon source.constants source.root source.config Config.crypto 0
        source.policy.checkFuel source.policy.eraseFuel source.policy.validateFuel)
      let certificate ← checked compiled.target.certifySymbolic
      let result := certificate.result.instantiate (fun _ => .erased)
      need (asNat result == some expected) s!"upstream symbolic expectation: {fixture.name}"
      let name := "upstream-" ++ fixture.name
      let wire ← runWire compiled.target (output / name / "wire") [#[]] (fun _ => result)
      canonicalRuns := canonicalRuns + 1
      rows := rows.push (Json.mkObj [("name", toJson name), ("parameters", toJson (0 : Nat)),
        ("origin", toJson "upstream-ixon"), ("reference", Json.null), ("wire", wire)])
  let rejected ← checked SymbolicExamples.rejections
  let report := Json.mkObj [
    ("format", toJson "compilatrix/ixby-symbolic-check/1"),
    ("cases", Json.arr rows), ("reference_runs", toJson referenceRuns),
    ("canonical_runs", toJson canonicalRuns), ("rejections", toJson rejected)]
  IO.FS.writeFile (output / "report.json") (report.pretty 100 ++ "\n")
  IO.println s!"source-ixby-symbolic ok: {rows.size} cases, {referenceRuns} reference runs, {canonicalRuns} canonical runs, {rejected.length} rejections"
