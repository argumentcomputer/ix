import Compilatrix.Ixby.Examples
import Compilatrix.Ixby.Report
import Compilatrix.Coverage.Upstream
import Compilatrix.Recursion.Sources
import Compilatrix.Tools.Check

open Compilatrix Compilatrix.Ixby Compilatrix.Tools.Check

private def asNat : Data → Option Nat
  | .nat n => some n
  | .ctor _ 0 [] => some 0
  | .ctor _ 1 [pred] => (asNat pred).map (· + 1)
  | _ => none

private def runAll (upstream : System.FilePath) : IO (List ReportCase × List String × Nat) := do
  let mut results := []
  for test in Examples.cases do
    let source : Source := { declarations := Examples.declarations, main := test.main, parameters := test.input.size }
    let compiled ← checked (compile source)
    let cert ← checked (compiled.certify test.input 10000 100000 1000)
    need (cert.result == test.expected) s!"Ixby expected result differs: {test.name}"
    results := results ++ [reportCase cert test.name "ixir0"]
  let generated ← checked Examples.generated
  let mut rejected ← checked Examples.rejections
  for source in ← checked Coverage.sources do
    let compiled := compileIxon source.constants source.root source.config {} 0
      source.policy.checkFuel source.policy.eraseFuel source.policy.validateFuel
    match source.expected with
    | .scalar number _ =>
      let compiled ← checked compiled
      let cert ← checked (compiled.target.certify #[] 10000 100000 1000)
      need (asNat cert.result == some number) s!"Ixon scalar result differs: {source.name}"
      results := results ++ [reportCase cert ("ixon-" ++ source.name) "checked-ixon"]
    | _ =>
      need (match compiled with | .error _ => true | .ok _ => false) s!"Ixon source gate unexpectedly accepted {source.name}"
      rejected := rejected ++ ["ixon-" ++ source.name]
  for aliased in [false, true] do
    let source ← checked (Recursion.Examples.source [1, 2, 3, 4] aliased)
    let compiled ← checked (compileIxon source.constants source.root source.config {} 0 1000 1000 1000)
    let cert ← checked (compiled.target.certify #[] 10000 100000 1000)
    results := results ++ [reportCase cert (if aliased then "ixon-reverse-aliased" else "ixon-reverse") "checked-ixon"]
  for fixture in Coverage.Upstream.fixtures do
    let loaded ← checked (← Coverage.Upstream.load upstream fixture)
    let source := loaded.source
    let compiled := compileIxon source.constants source.root source.config Config.profile 0
      source.policy.checkFuel source.policy.eraseFuel source.policy.validateFuel
    match fixture.expected with
    | .nat number =>
      let compiled ← checked compiled
      let exported ← checked compiled.target.export
      let cert ← checked (exported.certify #[] 10000 100000 1000)
      need (asNat cert.reference.result == some number) s!"upstream Nat result differs: {fixture.name}"
      results := results ++ [reportCase cert.reference ("upstream-" ++ fixture.name)
        "upstream-ixon" (some cert.bundle)]
    | .missingCovered _ =>
      need (match compiled with | .error _ => true | .ok _ => false) s!"upstream source gate unexpectedly accepted {fixture.name}"
      rejected := rejected ++ ["upstream-" ++ fixture.name]
  let address := Examples.address 9
  let dynamic : Source := {
    declarations := [(address, .ctor 0 1)]
    main := .app (.lam .many (.proj 0 (.var 0))) (.var 0), parameters := 1 }
  let compiled ← checked (compile dynamic Config.profile)
  let exported ← checked compiled.export
  for (name, input) in [("wire-runtime-erased", Data.erased),
      ("wire-runtime-constructor", .ctor address 0 [.erased])] do
    let cert ← checked (exported.certify #[input] 10000 100000 1000)
    results := results ++ [reportCase cert.reference name "ixir0-runtime" (some cert.bundle)]
  return (results, rejected, generated)

def main (args : List String) : IO UInt32 := cli "source-ixby" do
  let (output, upstream) ← match args with
    | [output] => pure (System.FilePath.mk output, System.FilePath.mk Coverage.Upstream.directory)
    | [output, upstream] => pure (System.FilePath.mk output, System.FilePath.mk upstream)
    | _ => throw (IO.userError "usage: source-ixby <new-output-directory> [ixon-upstream-directory]")
  need (!(← output.pathExists)) "source-ixby requires a new output directory"
  let (results, rejected, generated) ← runAll upstream
  for result in results do writeCase (output / result.name) result
  let report := Lean.Json.mkObj [
    ("format", Lean.toJson "compilatrix/ixby/1"),
    ("ixby_revision", Lean.toJson "6836a77c3f432c83c42428490e56811f4a69808d"),
    ("cases", Lean.toJson (results.map ReportCase.row)),
    ("generated", Lean.toJson generated), ("rejections", Lean.toJson rejected)]
  IO.FS.writeFile (output / "report.json") (report.pretty 100 ++ "\n")
  IO.println s!"source-ixby ok: {results.length} cases, {generated} generated, {rejected.length} rejections"
