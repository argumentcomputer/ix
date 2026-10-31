/-
  `ix compile-export <export.ndjson> [--out out.ixe]`: compile a Lean
  environment exported by `lean4export` (NDJSON format 3.1.0) to a bound
  Ixon `.ixe`, on ix's own toolchain.

  This is how a library elaborated by another Lean toolchain, older or newer
  than ix's, is compiled without building ix on that toolchain: its
  `lean4export` writes the declarations, and this command reads them
  (`Ix.LeanExport`) and runs the same pipeline as `ix compile-lean`:
  `compileLeanInputValidated`, then the role binding (`finalize`), whose
  support and certificate theorems come from the export itself, so from that
  toolchain's `Init` and its `IxC.Kernel.PinGen.Certs`. With
  `--certificates` they come from a second export of the same toolchain
  instead, for an export that does not carry them.

  The output matches the native compile of the same declarations in content
  (every constant, address and the role binding), not in metadata: an export
  carries no syntax-valued `mdata`, and one from an unpatched `lean4export`
  only one set of binder names and binder info per α-equivalence class of
  subterms (see `Ix.LeanExport`).
  `--compare <native.ixe>` checks the content against a native compile and
  reports the metadata differences.

  Exit codes: 0 success (and content exact, when compared); 1 a refused
  export, a pipeline error, a block failure, a Rust divergence or a content
  difference; 2 usage.
-/
module
public import Cli
public import Ix.Common
public import Ix.CompileM
public import Ix.CompileDriver
public import Ix.CompileResource
public import Ix.RoleBinding.Compile
public import Ix.LeanExport
public import Ix.LeanExport.Compare
public import Ix.Cli.DriverOptions
public section

open System (FilePath)

namespace Ix.Cli.CompileExportCmd

/-- Read an export and report what it is. -/
def readExport (what : String) (path : String) : IO Ix.LeanExport.Imported := do
  let im ← Ix.LeanExport.importFile path
  let m := im.exportMeta
  IO.println s!"[compile-export] {what} {path}: {im.constants.size} declarations from Lean \
{m.leanVersion} ({m.leanGithash}), written by {Ix.LeanExport.exporterName} {m.exporterVersion}; \
{im.droppedSyntaxMData} syntax-valued metadata entries dropped"
  return im

def runCompileExportCmd (p : Cli.Parsed) : IO UInt32 := do
  let args : Array String := p.variableArgsAs! String
  let some (path : String) := args[0]?
    | p.printError "error: must specify <export.ndjson>"
      return 2
  let outPath := match p.flag? "out" with
    | some f => f.as! String
    | none => s!"{((FilePath.mk path).fileStem.getD "out").toLower}.ixe"
  let workers := match p.flag? "workers" with
    | some f => max 1 (f.as! Nat)
    | none => 32
  let opts ← match ← Ix.Cli.driverOptionsFromEnv (dbg := true) with
    | .ok opts => pure opts
    | .error e =>
      p.printError s!"error: {e}"
      return 2
  let t0 ← IO.monoMsNow
  let exported ← readExport "export" path
  let env ← Ix.LeanExport.environment exported.constants
  -- The certificate theorems must be elaborated by the same toolchain.
  let certSource : IO Lean.Environment ← match p.flag? "certificates" with
    | none => pure (pure env)
    | some f =>
      let certs ← readExport "certificates" (f.as! String)
      unless certs.exportMeta.leanGithash == exported.exportMeta.leanGithash do
        IO.eprintln s!"[compile-export] error: the certificates come from Lean \
{certs.exportMeta.leanVersion} ({certs.exportMeta.leanGithash}), the export from Lean \
{exported.exportMeta.leanVersion} ({exported.exportMeta.leanGithash})"
        return 1
      let certEnv ← Ix.LeanExport.environment certs.constants
      pure (pure certEnv)
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env env.constants.toList).mapError toString)
  let out ← match ← Ix.CompileM.compileLeanInputValidated input (numWorkers := workers) (opts := opts) with
    | .error e =>
      IO.println s!"[compile-export] FAILED: {e}"
      return 1
    | .ok out => pure out
  let failed := out.cenv.ungrounded.size
  if failed > 0 then
    IO.eprintln s!"[compile-export] error: {failed} constant(s) failed to compile; nothing written to {outPath}"
    for (n, e) in out.cenv.ungrounded.toList.take 8 do
      IO.eprintln s!"  [ungrounded] {n.pretty}: {(e.replace "\n" " ").take 200}"
    return 1
  let artifact ← Ix.RoleBinding.Compile.finalize (Ix.RoleBinding.Compile.leanBackend workers opts)
    env certSource input out.env Ix.Resource.typingLimits
  let out := { out with env := artifact, bytes := ← IO.ofExcept (Ixon.serEnv artifact) }
  IO.ofExcept (Ix.CompileM.resourcePostStep out)
  Ix.RoleBinding.Compile.writeAtomic (FilePath.mk outPath) out.bytes
  let binding := match artifact.roleBinding with
    | some b => s!"role binding {b.address}"
    | none => "no role binding"
  IO.println s!"[compile-export] wrote {out.bytes.size} bytes to {outPath} ({out.blockCount} blocks, \
{binding}) in {(← IO.monoMsNow) - t0}ms"
  if p.hasFlag "rust-check" then
    let tR ← IO.monoMsNow
    let rustBytes ← IO.FS.withTempDir fun dir => do
      let rustOut := dir / "rust-check.ixe"
      let constants ← IO.ofExcept input.prepare
      let _ ← Ix.CompileM.rsCompileEnvBytesFFI constants rustOut.toString true
      let raw ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile rustOut))
      let bound ← Ix.RoleBinding.Compile.finalize Ix.RoleBinding.Compile.rustBackend env certSource
        input raw Ix.Resource.typingLimits
      IO.ofExcept (Ixon.serEnv bound)
    if rustBytes == out.bytes then
      IO.println s!"[compile-export] ALIGNED: {out.bytes.size} bytes byte-identical with Rust \
({(← IO.monoMsNow) - tR}ms)"
    else
      IO.println s!"[compile-export] DIVERGED: lean {out.bytes.size}B vs rust {rustBytes.size}B"
      return 1
  if let some f := p.flag? "compare" then
    let nativePath := f.as! String
    let native ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile nativePath))
    let c := Ix.LeanExport.compare native artifact
    IO.println s!"[compile-export] compared with {nativePath}:"
    for line in c.report native artifact do IO.println s!"  {line}"
    unless c.contentExact do return 1
  return 0

end Ix.Cli.CompileExportCmd

open Ix.Cli.CompileExportCmd in
def compileExportCmd : Cli.Cmd := `[Cli|
  "compile-export" VIA runCompileExportCmd;
  "Compile a Lean environment exported by lean4export (NDJSON 3.1.0), possibly from another Lean toolchain, to a bound Ixon .ixe"

  FLAGS:
    out          : String; "Output path; defaults to the lowercased input file stem with `.ixe`"
    workers      : Nat;    "Worker count for the parallel phases (default 32)"
    certificates : String; "An export of the same toolchain carrying the certificate theorems (`IxC.Kernel.PinGen.Certs`), when the main export does not"
    "rust-check" ;         "Also compile through the Rust compiler and byte-compare the outputs; exit 1 on divergence"
    compare      : String; "A native compile of the same declarations: check that the content is equal (exit 1 if not) and report the metadata differences"

  ARGS:
    ...path : String; "The export (NDJSON, one record per line)."
]

end
