module

public import Ix.Cli.CheckLeanCmd
public import Ix.CompileM
public import Ix.CompileCertified
public import Ix.Ixon
public import Ix.EnvScope
public import Ix.KernelCheck

/-!
Shared harness for checking a small source-level closure with the pure-Lean
kernel.  The certified compiler writes one temporary Ixon environment, then the
same driver used by `ix check-lean --consts` checks their supporting
closure and requires exact named coverage of the requested regression subjects.
-/

public section

namespace Ix.KernelCheck

def rsCheckIxonFFI (path : String) (names : Array Lean.Name)
    (_expectPass : Array Bool) (quiet : Bool) (_failOut : String) :
    IO (Array (Option CheckError)) := do
  let bytes ← IO.FS.readBinFile path
  let cfg : Ix.Cli.CheckLeanCmd.CheckCfg := {
    workers := 1, verbose := !quiet, silent := quiet, progressMs := 0, slowMs := 0 }
  let only := names.map toString
  match ← Ix.Cli.CheckLeanCmd.runMetaCheck bytes cfg (.only only) with
  | .error err =>
    return Array.replicate names.size (some (.kernelException err.message))
  | .ok report =>
    let mut byLabel : Std.HashMap String (String × String) := {}
    for t in report.targets do
      byLabel := byLabel.insert t.target.label (t.outcome, t.reason)
    return names.map fun n =>
      match byLabel[toString n]? with
      | some ("accept", _) | some ("typed", _) => none
      | some (outcome, reason) => some (.kernelException s!"{outcome}: {reason}")
      | none => some (.kernelException s!"missing target verdict for {n}")

def rsCheckConstsFFI (consts : List (Lean.Name × Lean.ConstantInfo))
    (names : Array Lean.Name) (_expectPass : Array Bool) (quiet : Bool) :
    IO (Array (Option CheckError)) := do
  let rawEnv := Ix.CompileM.canonInput consts.toArray 32
  let (compiledEnv, failures) ← match Ix.Cert.compileReport rawEnv with
    | .ok res => pure res
    | .error err =>
      return Array.replicate names.size (some (.compileError (toString err)))
  let failMap := failures.toMap
  let bytes ← match Ixon.serEnv compiledEnv with
    | .ok b => pure b
    | .error err =>
      return Array.replicate names.size (some (.compileError (toString err)))
  let cfg : Ix.Cli.CheckLeanCmd.CheckCfg := {
    workers := 1, verbose := !quiet, silent := quiet, progressMs := 0, slowMs := 0 }
  let unfailed := names.filter fun n => !failMap.contains (Ix.Name.fromLeanName n)
  let only := unfailed.map toString
  let mut byLabel : Std.HashMap String (Option CheckError) := {}
  if !only.isEmpty then
    match ← Ix.Cli.CheckLeanCmd.runMetaCheck bytes cfg (.only only) with
    | .error err =>
      for n in unfailed do
        byLabel := byLabel.insert (toString n) (some (.kernelException err.message))
    | .ok report =>
      for t in report.targets do
        let v := match t.outcome with
          | "accept" | "typed" => none
          | outcome => some (.kernelException s!"{outcome}: {t.reason}")
        byLabel := byLabel.insert t.target.label v
  return names.map fun n =>
    if let some reason := failMap[Ix.Name.fromLeanName n]? then
      some (.compileError reason)
    else
      match byLabel[toString n]? with
      | some res => res
      | none => some (.kernelException s!"missing target verdict for {n}")

end Ix.KernelCheck

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
    let outEnv ← match ← Ix.CompileM.compileCertified env consts with
      | .ok out => pure out
      | .error err => return (false, 0, names.size, some s!"[{tag}] compile failed: {err}")
    unless outEnv.failures.isEmpty do
      let first := match outEnv.failures.toMap.toList.head? with
        | some (name, reason) => s!"{name}: {reason}"
        | none => "<missing diagnostic>"
      return (false, 0, names.size, some s!"[{tag}] compile failed for \
        {outEnv.failures.toMap.size} constant(s); first: {first}")
    let bytes ← match Ixon.serEnv outEnv.env with
      | .ok b => pure b
      | .error err => return (false, 0, names.size, some s!"[{tag}] serEnv failed: {err}")
    IO.FS.writeBinFile path bytes
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
