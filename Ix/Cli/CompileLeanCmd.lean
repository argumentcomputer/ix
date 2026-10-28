/-
  `ix compile-lean <path.lean> [--out out.ixe]`: compile a Lean file's
  environment to a serialized Ixon `.ixe` with the certified compiler,
  `Ix.Cert.compileReport`, the function `Ix.Cert.CompileCorrect` is about
  (`Ix.CompileM.compileCertified`): the source contracts are prepared, the
  input is canonicalized (`Ix.CanonM`), compiled and checked by
  `compileReport`, its accounting and resources are checked; the role support,
  evidence and binding are added (`Ix.RoleBinding.Compile.finalize`, which
  checks the finalized artifact again), and the artifact is serialized
  (`Ixon.serEnv`) and written atomically.

  The certified compiler runs at the default sharing limits, which the theorem
  fixes: `--sharing-limits` or `IX_SHARING_LIMITS` is refused, unless
  `--streamed` is given. `--streamed` selects the streamed pipeline
  (`Ix.CompileM.compileLeanInputValidated`), which is uncertified: its fold is
  `compileReport`'s (`Ix.Cert.Hybrid`), but its streamed canonicalization,
  graph, ground filter and condensation are only tested to be. It is kept for
  comparison.

  `--rust-check` additionally compiles the same environment through the
  Rust FFI compiler (`rs_compile_env_bytes` — the exact bytes
  `ix compile --rust` writes) and byte-compares the two outputs: this is the
  ALIGNED gate. The comparison covers both compilers and serializers
  (Rust `Env::put` and Lean `Ixon.serEnv`) on this input. It is measured
  whole-output parity, not a universal refinement or value-preservation
  proof.

  Exit codes: 0 success (including an explicitly allowed partial output,
  and aligned when checked); 1 pipeline error, an unallowed block failure,
  or divergence; 2 usage. The Lean output is written before `--rust-check`,
  so a later divergence leaves that output on disk.
-/
module
public import Cli
public import Ix.Common
public import Ix.Meta
public import Ix.CompileM
public import Ix.CompileDriver
public import Ix.CompileResource
public import Ix.CompileCertified
public import Ix.RoleBinding.Compile
public import Ix.Cli.DriverOptions
public import Ix.Cli.ValidateCmd
public import Ix.Cli.CompileCmd
public section

open System (FilePath)
open Ix.EnvScope

namespace Ix.Cli.CompileLeanCmd

/-- Failures listed root causes first: a constant that failed only because a
    dependency is missing is a cascade, listed after the ones that name the
    cause (a refusal's message must be visible in the bounded listing). -/
private def rootCausesFirst {α : Type} (xs : List (α × String)) : List (α × String) :=
  let cascade (e : String) := e.startsWith "missingConstant" || e.startsWith "missing constant"
  xs.filter (!cascade ·.2) ++ xs.filter (cascade ·.2)

/-- A compile's finalized, serialized artifact, the input `--rust-check`
compiles, and the summary line's counts. -/
private structure Compiled where
  bytes : ByteArray
  prepared : Unit → Except String (List (Lean.Name × Lean.ConstantInfo))
  failures : Std.HashMap Ix.Name String
  summary : String

/-- Fail-closed by default, as `ix compile`: any failure means a nonzero exit
and no output file, unless `--allow-partial` opts into the grounded subset. -/
private def refusePartial (allowPartial : Bool) (outPath : String)
    (failures : Std.HashMap Ix.Name String) : IO Bool := do
  if allowPartial || failures.isEmpty then return false
  IO.eprintln s!"[compile-lean] error: {failures.size} constant(s) \
failed to compile; nothing written to {outPath} (use --allow-partial to \
serialize the grounded subset)"
  for (n, e) in (rootCausesFirst failures.toList).take 8 do
    IO.eprintln s!"  [ungrounded] {n.pretty}: {(e.replace "\n" " ").take 200}"
  return true

/-- The certified compile (`Ix.CompileM.compileCertified`), finalized. -/
private def compileCertified (fe : FileEnv) (constList : List (Lean.Name × Lean.ConstantInfo))
    (workers : Nat) (allowPartial : Bool) (outPath : String) : IO (Except UInt32 Compiled) := do
  let log (s : String) : IO Unit := IO.println s!"  [compile-lean] {s}"
  let out ← match ← Ix.CompileM.compileCertified fe.env constList workers log with
    | .ok out => pure out
    | .error e =>
      IO.println s!"[compile-lean] FAILED: {e}"
      return .error 1
  log s!"rss after the compile: {← Ix.Cli.residentSetSize}"
  let failures := out.failures.toMap
  if ← refusePartial allowPartial outPath failures then return .error 1
  let t0 ← IO.monoMsNow
  let artifact ← Ix.RoleBinding.Compile.finalize (Ix.RoleBinding.Compile.certifiedBackend workers)
    fe.env Ix.RoleBinding.Compile.nativeCertSource (.plain constList) out.env
    Ix.Resource.typingLimits
  IO.ofExcept (Ix.CompileM.validateFinalized out.annotated artifact)
  let t1 ← IO.monoMsNow
  log s!"finalize: {t1 - t0}ms, rss {← Ix.Cli.residentSetSize}"
  let bytes ← IO.ofExcept (Ixon.serEnv artifact)
  log s!"serialize ({bytes.size} bytes): {(← IO.monoMsNow) - t1}ms"
  let prepared := out.prepared
  return .ok { bytes, prepared := fun _ => .ok prepared, failures
               summary := s!"{out.inputs} input constants, {failures.size} failures" }

/-- The streamed pipeline (`Ix.CompileM.compileLeanInputValidated`), finalized:
uncertified, kept for comparison. -/
private def compileStreamed (fe : FileEnv) (constList : List (Lean.Name × Lean.ConstantInfo))
    (workers : Nat) (opts : Ix.CompileM.DriverOptions) (allowPartial : Bool) (outPath : String) :
    IO (Except UInt32 Compiled) := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv fe.env constList).mapError toString)
  -- The compile, then the resource post-step (an input with semantic
  -- contracts is emitted only if its resources validate).
  let out ← match ← Ix.CompileM.compileLeanInputValidated input (numWorkers := workers)
      (opts := opts) with
    | .ok out => pure out
    | .error e =>
      IO.println s!"[compile-lean] FAILED: {e}"
      return .error 1
  let failures := out.cenv.ungrounded
  if ← refusePartial allowPartial outPath failures then return .error 1
  let artifact ← Ix.RoleBinding.Compile.finalize (Ix.RoleBinding.Compile.leanBackend workers opts)
    fe.env Ix.RoleBinding.Compile.nativeCertSource input out.env Ix.Resource.typingLimits
  let out := { out with env := artifact, bytes := ← IO.ofExcept (Ixon.serEnv artifact) }
  IO.ofExcept (Ix.CompileM.resourcePostStep out)
  return .ok { bytes := out.bytes, prepared := fun _ => input.prepare, failures
               summary := s!"{out.blockCount} blocks, {out.ungroundedCount} ungrounded, \
{failures.size} block failures" }

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
  let streamed := p.hasFlag "streamed"
  let allowPartial := p.hasFlag "allow-partial"
  if let some e ← applySharingLimitsFlag p then
    p.printError s!"error: {e}"
    return 2
  -- The streamed pipeline's options: limits (`--sharing-limits` /
  -- `IX_SHARING_LIMITS`), traces (`IX_COMPILE_DBG`); phase timings always on.
  let opts ← match ← Ix.Cli.driverOptionsFromEnv (dbg := true) with
    | .ok opts => pure opts
    | .error e =>
      p.printError s!"error: {e}"
      return 2
  unless streamed do
    if let some e ← certifiedLimitsRefusal p then
      p.printError s!"error: {e}"
      return 2

  -- Reuse existing imports when the caller already built them: the input file
  -- is still elaborated; only Lake's dependency build and cache step is skipped.
  unless p.hasFlag "no-build" do
    IO.println s!"[compile-lean] building {pathStr}..."
    buildFile pathStr
  let fe ← getFileEnvCore pathStr
  let constList ← if p.hasFlag "local" then pure (localConstList fe) else defaultConstList fe pathStr
  IO.println s!"[compile-lean] {constList.length} constants, {workers} workers, \
{if streamed then "streamed pipeline (uncertified)" else "certified compiler"}"

  let t0 ← IO.monoMsNow
  let compiled ← if streamed then compileStreamed fe constList workers opts allowPartial outPath
    else compileCertified fe constList workers allowPartial outPath
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

  if p.hasFlag "rust-check" then
    IO.println "[compile-lean] --rust-check: compiling via Rust FFI..."
    let tR ← IO.monoMsNow
    let rustBytes ← IO.FS.withTempDir fun dir => do
      let rustOut := dir / "rust-check.ixe"
      let prepared ← IO.ofExcept (out.prepared ())
      let _ ← Ix.CompileM.rsCompileEnvBytesFFI prepared rustOut.toString true
      let raw ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile rustOut))
      let bound ← Ix.RoleBinding.Compile.finalize Ix.RoleBinding.Compile.rustBackend fe.env
        Ix.RoleBinding.Compile.nativeCertSource (.plain constList) raw Ix.Resource.typingLimits
      IO.ofExcept (Ixon.serEnv bound)
    let tRe := (← IO.monoMsNow) - tR
    if rustBytes == out.bytes then
      IO.println s!"[compile-lean] ALIGNED: {out.bytes.size} bytes byte-identical with Rust ({tRe}ms)"
    else
      let n := min rustBytes.size out.bytes.size
      let mut firstDiff := n
      for i in [0:n] do
        if firstDiff == n && rustBytes.get! i != out.bytes.get! i then
          firstDiff := i
      IO.println s!"[compile-lean] DIVERGED: lean {out.bytes.size}B vs \
rust {rustBytes.size}B, first difference at byte {firstDiff}"
      return 1
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
    "rust-check" ;         "Also compile via the Rust FFI compiler and byte-compare the outputs (the ALIGNED gate); exit 1 on divergence"
    "local" ;              "Compile only the constants the input file itself declares, with their transitive dependencies (the selected closure: recursors, whole logical units, checker support), instead of the whole import env. --rust-check compiles the same list."
    "allow-partial" ;      "Serialize the grounded subset and exit 0 even when some constants fail to compile. Default is fail-closed: any block failure means a nonzero exit and NO output file."
    streamed ;             "Compile with the streamed pipeline instead of the certified compiler. UNCERTIFIED: only its fold is proved to be the certified compiler's; its streamed front end is tested, not proved. Kept for comparison."
    "sharing-limits" : String; "Override resource limits of the canonical sharing construction (same format as `ix compile --sharing-limits`); only with --streamed, since the certified compiler's theorem fixes the default limits. Applies to --rust-check too. Sets IX_SHARING_LIMITS."

  ARGS:
    ...path : String; "Path to the Lean source file to compile."
]

end
