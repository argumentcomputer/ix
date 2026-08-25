module

public import Ix.Cli.CheckLeanCmd
public import Ix.CompileM

/-!
Shared harness for checking a small source-level closure with the pure-Lean
kernel.  The Rust compiler writes one temporary Ixon environment, then the
same name-filtered driver used by `ix check-lean --consts` checks only the
requested regression subjects.
-/

public section

namespace Tests.Ix.Kernel.FocusedLeanCheck

def checkClosure (tag fileStem : String)
    (consts : List (Lean.Name × Lean.ConstantInfo))
    (names : Array Lean.Name) :
    IO (Bool × Nat × Nat × Option String) := do
  if names.isEmpty then
    return (false, 0, 0, some s!"[{tag}] no subjects selected")
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
    let cfg : Ix.Tc.ParCheckCfg := {
      workers := 1
      verbose := true
      progressMs := 0
      slowMs := 0
      stuckMs := 0
      tag := s!"[{tag}]"
    }
    let only := names.map fun name => toString name
    match ← Ix.Cli.CheckLeanCmd.runMetaCheck bytes cfg true none only none with
    | .error err =>
        return (false, 0, names.size, some s!"[{tag}] Ix.Tc driver failed: {err}")
    | .ok (report, workItems) =>
        IO.println s!"[{tag}] {report.passed}/{report.targetsCovered} passed in \
          {report.elapsedMs}ms"
        if workItems != names.size || report.targetsCovered != names.size then
          return (false, report.passed, names.size, some s!"[{tag}] expected \
            {names.size} work item(s)/target(s), got {workItems}/\
            {report.targetsCovered}")
        if !report.failures.isEmpty then
          let details := String.intercalate "; " <|
            report.failures.toList.map fun (name, msg) => s!"{name}: {msg}"
          return (false, report.passed, names.size, some details)
        return (true, report.passed, names.size, none)
  finally
    IO.FS.removeDirAll dir

end Tests.Ix.Kernel.FocusedLeanCheck

end
