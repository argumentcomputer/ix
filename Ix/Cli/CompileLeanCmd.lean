module
public import Cli
public import Ix.Common
public import Ix.Meta
public import Ix.CompileM
public import Ix.CompileDriver
public import Ix.CompileCertified
public import Ix.RoleBinding.Compile
public import Ix.Cli.ValidateCmd

/-!
  `ix compile-lean <path.lean> [--out out.ixe]`: compile a Lean file's
  environment to a serialized Ixon `.ixe` with the certified compiler,
  `Ix.Cert.compileReport`, the function `Ix.Cert.CompileCorrect` is about
  (`Ix.CompileM.compileAndFinalize`): the source contracts are prepared, the
  input is canonicalized (`Ix.CanonM`), compiled and checked by
  `compileReport`, its accounting and resources are checked; the role support,
  evidence and binding are added (`Ix.RoleBinding.Compile.finalize`, which
  checks the finalized artifact again), and the artifact is serialized
  (`Ixon.serEnv`) and written atomically.

  Exit codes: 0 success (including an explicitly allowed partial output);
  1 pipeline error or an unallowed compilation failure; 2 usage.
-/

public section

open System (FilePath)
open Ix.EnvScope
open Ix.Cli (rootCausesFirst)

namespace Ix.Cli.CompileLeanCmd

/-- A compile's finalized, serialized artifact and the summary line's counts. -/
private structure Compiled where
  bytes : ByteArray
  failures : Std.HashMap Ix.Name String
  summary : String

/-- Fail-closed by default, as `ix compile`: a recorded compilation failure
causes a nonzero exit and leaves the output path untouched. `--allow-partial`
permits writing the successfully compiled subset. -/
private def refusePartial (outPath : String) (failures : Std.HashMap Ix.Name String) : IO Unit := do
  IO.eprintln s!"[compile-lean] error: {failures.size} constant(s) \
failed to compile; nothing written to {outPath} (use --allow-partial to \
serialize the grounded subset)"
  for (n, e) in (rootCausesFirst failures.toList).take 8 do
    IO.eprintln s!"  [ungrounded] {n.pretty}: {(e.replace "\n" " ").take 200}"

/-- The certified compile, finalized (`Ix.CompileM.compileAndFinalize`). A compile of
the whole import environment (not `--local`) publishes every role, so it
prefetches every role's certificates beside the source compile. -/
private def compileFinalized (fe : FileEnv) (constList : List (Lean.Name × Lean.ConstantInfo))
    (workers : Nat) (allowPartial : Bool) (outPath : String) (wholeEnv : Bool)
    (binderData : Ix.CompileM.BinderDataMode) (strictBinderData : Bool) :
    IO (Except UInt32 Compiled) := do
  let log (s : String) : IO Unit := IO.println s!"  [compile-lean] {s}"
  match ← Ix.CompileM.compileAndFinalize fe.env constList workers allowPartial log
      (prefetch := wholeEnv) (binderData := binderData) (strictBinderData := strictBinderData)
      (onBinders := fun r a => r.print a "compile-lean") with
  | .error e =>
    IO.println s!"[compile-lean] FAILED: {e}"
    return .error 1
  | .ok (out, .refused) =>
    refusePartial outPath out.failures.toMap
    return .error 1
  | .ok (_, .failed e) => throw (IO.userError e)
  | .ok (out, .done _ bytes) =>
    let failures := out.failures.toMap
    return .ok { bytes, failures
                 summary := s!"{out.inputs} input constants, {failures.size} failures" }

def runCompileLeanCmd (p : Cli.Parsed) : IO UInt32 := do
  let args : Array String := p.variableArgsAs! String
  let some (pathStr : String) := args[0]?
    | p.printError "error: must specify <path> to a Lean source file"
      return 2
  let outPath := match p.flag? "out" with
    | some f => f.as! String
    | none =>
      let stem := (FilePath.mk pathStr).fileStem.getD "out"
      s!"{stem.toLower}.ixe"
  let workers := match p.flag? "workers" with
    | some f => max 1 (f.as! Nat)
    | none => 32
  let allowPartial := p.hasFlag "allow-partial"

  -- Reuse existing imports when the caller already built them: the input file
  -- is still elaborated; only Lake's dependency build and cache step is skipped.
  unless p.hasFlag "no-build" do
    IO.println s!"[compile-lean] building {pathStr}..."
    buildFile pathStr
  let fe ← getFileEnvCore pathStr
  let constList ← if p.hasFlag "local" then pure (localConstList fe) else defaultConstList fe pathStr
  IO.println s!"[compile-lean] {constList.length} constants, {workers} workers, certified compiler"

  let some binderData := Ix.CompileM.BinderDataMode.parse?
      ((p.flag? "binder-data").map (·.as! String) |>.getD "inline")
    | IO.eprintln "[compile-lean] --binder-data is off, inline or post"
      return 1
  let t0 ← IO.monoMsNow
  let compiled ← compileFinalized fe constList workers allowPartial outPath (!p.hasFlag "local")
    binderData (p.hasFlag "strict-binder-data")
  let out ← match compiled with
    | .ok out => pure out
    | .error code => return code
  Ix.RoleBinding.Compile.writeAtomic (FilePath.mk outPath) out.bytes
  let elapsed := (← IO.monoMsNow) - t0
  IO.println s!"[compile-lean] wrote {out.bytes.size} bytes to {outPath} ({out.summary}) \
in {elapsed}ms"
  if out.failures.size > 0 then
    IO.println s!"[compile-lean] PARTIAL: {out.failures.size} constants failed to compile"
    for (n, e) in (rootCausesFirst out.failures.toList).take 8 do
      IO.println s!"  {n.pretty}: {e.take 200}"
  return 0

end Ix.Cli.CompileLeanCmd

open Ix.Cli.CompileLeanCmd in
def compileLeanCmd : Cli.Cmd := `[Cli|
  "compile-lean" VIA runCompileLeanCmd;
  "Compile a Lean file to Ixon with the certified compiler (`Ix.Cert.compileReport`: canon → graph → ground → condense → compile → checks), then add the role support and binding and serialize"

  FLAGS:
    out          : String; "Output path for the serialized Ixon.Env bytes; defaults to the lowercased input file stem with `.ixe`"
    workers      : Nat;    "Worker count for the parallel phases (default 32)"
    "no-build" ;           "Skip the Lake build/cache step and reuse existing import artifacts. The input file is still elaborated. The caller must ensure all imports are built and up to date."
    "local" ;              "Compile only the constants the input file itself declares, with their transitive dependencies (the selected closure: recursors, whole logical units, checker support), instead of the whole import env."
    "allow-partial" ;      "Allow writing the successfully compiled subset despite requested compilation failures. Without this flag, those failures cause a nonzero exit and leave the output path untouched."
    "binder-data" : String; "How records get their binder data: inline (the default: while each record is built, from Lean's elaboration of its sources), off (every binder undecided; for measurement), or post (off, then IxC's pass over the finalized artifact and re-addressing; for comparison)."
    "strict-binder-data" ; "Fail the compile, naming the record and binder, where the annotator cannot decide a binder's datum. Without it such a binder carries the undecided node (Ixon section tag 4), which IxVM rejects when it reads it, and is reported."

  ARGS:
    ...path : String; "Path to the Lean source file to compile."
]

end
