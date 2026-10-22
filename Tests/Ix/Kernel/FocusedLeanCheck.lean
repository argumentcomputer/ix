module

public import Ix.Cli.CheckLeanCmd
public import Ix.CompileM
public import Ix.EnvScope

/-!
Shared harness for checking a small source-level closure with the pure-Lean
kernel.  The Rust compiler writes one temporary Ixon environment, then the
same driver used by `ix check-lean --consts` checks their supporting
closure and requires exact named coverage of the requested regression subjects.
-/

public section

namespace Tests.Ix.Kernel.FocusedLeanCheck

def checkClosure (tag fileStem : String)
    (env : Lean.Environment)
    (names : Array Lean.Name) :
    IO (Bool × Nat × Nat × Option String) := do
  if names.isEmpty then
    return (false, 0, 0, some s!"[{tag}] no subjects selected")
  let consts := Ix.EnvScope.collectSelectedDeps env names.toList
  IO.println s!"[{tag}] {consts.length} constants in the selected IxC closure (recursors, units and checker support)"
  let dir ← IO.FS.createTempDir
  try
    let path := dir / s!"{fileStem}.ixe"
    let status ← Ix.CompileM.rsCompileEnvBytesFFI consts path.toString false
    unless status.ungrounded.isEmpty do
      let first := match status.ungrounded[0]? with
        | some (name, reason) => s!"{name}: {reason}"
        | none => "<missing diagnostic>"
      return (false, 0, names.size, some s!"[{tag}] compile failed for \
        {status.ungrounded.size} constant(s); first: {first}")

    let bytes ← IO.FS.readBinFile path
    let cfg : Ix.Cli.CheckLeanCmd.CheckCfg := {
      workers := 1, verbose := true, progressMs := 0, slowMs := 0, tag := s!"[{tag}]" }
    let only := names.map toString
    let prepared ← match ← Ix.Cli.CheckLeanCmd.prepareInput bytes with
      | .ok p => pure p
      | .error e => return (false, 0, names.size, some e.message)
    let expected ← match only.mapM (Ix.Cli.CheckLeanTargets.findCandidate prepared.inventory) with
      | .ok cs => pure cs
      | .error _ => return (false, 0, names.size, some s!"[{tag}] subject selection failed")
    match ← Ix.Cli.CheckLeanCmd.runPrepared prepared cfg (.only only) with
    | .error err => return (false, 0, names.size, some s!"[{tag}] IxC driver failed: {err.message}")
    | .ok report =>
        IO.println s!"[{tag}] {report.passed}/{report.targetsCovered} passed; selected checker \
          {report.subjectMicros / 1000}ms, support checker {report.supportMicros / 1000}ms, run {report.elapsedMs}ms"
        if report.targets.map (·.target.label) != expected.map (·.label) ||
            report.targets.map (·.target.address) != expected.map (·.address) then
          return (false, report.passed, names.size, some s!"[{tag}] exact named coverage mismatch")
        -- These reduction canaries require logical acceptance.
        if report.targets.any (·.outcome != "accept") then
          return (false, report.passed, names.size, some <| String.intercalate "; " <|
            report.targets.toList.map fun r => s!"{r.target.label}: {r.outcome}: {r.reason}")
        return (true, report.passed, names.size, none)
  finally
    IO.FS.removeDirAll dir

end Tests.Ix.Kernel.FocusedLeanCheck

end
