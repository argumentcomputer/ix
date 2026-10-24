import LSpec
import Tests.Ix.Compile.ClosureWhole

namespace Tests.Ix.Compile.ClosurePhase4

open LSpec Tests.Ix.Compile.ClosureWhole

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def check : IO Nat := do
  let dir ← IO.FS.createTempDir
  IO.println s!"LocalCollapse phase-4 gate artifacts: {dir}"
  -- Only this bounded fixture, never ClosureWhole.run's whole-artifact work.
  -- This executes the existing byte/source/reference/no-support checks too.
  let errors ← localCollapse dir (workers := 1)
  ensure errors.isEmpty ("\n".intercalate errors.toList)
  let json ← IO.ofExcept (Lean.Json.parse
    (← IO.FS.readFile (dir / "local-collapse-validate-lean.json")))
  ensure ((← IO.ofExcept (json.getObjValAs? Bool "passed")) &&
    (← IO.ofExcept (json.getObjValAs? Nat "totalFailures")) == 0) "actual CLI report did not pass"
  let rows ← IO.ofExcept (json.getObjValAs? (Array Lean.Json) "phases")
  let phases ← rows.mapM fun row => IO.ofExcept do
    return (← row.getObjValAs? String "name", ← row.getObjValAs? String "result",
      ← row.getObjValAs? String "detail")
  ensure (localPhaseProblems 0 phases).isEmpty "actual all-phase report was refused"
  let some (_, _, source) := phases.find? (·.1.startsWith "4.")
    | throw (IO.userError "actual CLI omitted phase 4")
  ensure (source.contains "source coverage: 254/254 named constants" &&
    source.contains "declined: partial definition") "actual source coverage/declines changed"
  let edit := fun name result detail => phases.map fun row =>
    if row.1.startsWith "4." then (name, result, detail) else row
  let variants := [
    ("missing", phases.filter (!·.1.startsWith "4."), "phase 4."),
    ("failed", edit "4. Source/reader fidelity" "fail" source, "fidelity: fail"),
    ("skipped", edit "4. Source/reader fidelity" "skip" source, "fidelity: skip"),
    ("old scope", edit "4. Kernel meta roundtrip" "pass" source, "wrong phase-4 scope"),
    ("no coverage", edit "4. Source/reader fidelity" "pass" "no coverage", "nonzero source coverage"),
    ("zero", edit "4. Source/reader fidelity" "pass" "source coverage: 0/0 named constants", "nonzero source coverage"),
    ("partial", edit "4. Source/reader fidelity" "pass" "source coverage: 253/254 named constants", "nonzero source coverage"),
    ("malformed", edit "4. Source/reader fidelity" "pass" "source coverage: bad/254 named constants", "nonzero source coverage"),
    ("duplicate coverage", edit "4. Source/reader fidelity" "pass"
      (source ++ "\nsource coverage: 254/254 named constants"), "nonzero source coverage"),
    ("duplicate row", phases.push ("4. Source/reader fidelity", "pass", source), "phase 4."),
    ("phase 5", phases.map (fun (n, r, d) => if n.startsWith "5." then (n, "fail", d) else (n, r, d)), "5. Decompile: fail")]
  for (label, changed, message) in variants do
    let rejected := localPhaseProblems 0 changed
    ensure (rejected.any (·.contains message)) s!"{label} was accepted or failed for another reason: {rejected}"
  ensure ((localPhaseProblems 1 phases).any (·.contains "exit 1")) "nonzero CLI exit was ignored"
  ensure (variants.length == 11) "not every report control executed"
  IO.println "LocalCollapse phase-4 gate: all 5 actual phases pass, 254/254 source coverage; 12 report refusals"
  return variants.length + 1

def suite : List TestSeq := [
  .individualIO "LocalCollapse requires phase 4 and complete nonzero source coverage" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Compile.ClosurePhase4
