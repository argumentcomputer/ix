/-
  `ix compile-lean <path.lean> [--out out.ixe]`: compile a Lean file's
  environment to a serialized Ixon `.ixe` through the PURE-LEAN pipeline
  end-to-end — the `Ix.CompileM` counterpart of `ix compile` (which
  drives the Rust FFI compiler). Phases: elaborate → canonicalize
  (`Ix.CanonM`) → reference graph (`Ix.GraphM`) → groundedness filter
  (`Ix.Ground`) → Tarjan condense (`Ix.CondenseM`) → aux-aware parallel
  compile (`Ix.CompileM.compileEnvParallelAux`) → `Ixon.serEnv`.

  `--rust-check` additionally compiles the same environment through the
  Rust FFI compiler (`rs_compile_env_bytes` — the exact bytes
  `ix compile` writes) and byte-compares the two outputs: this is the
  ALIGNED gate. The comparison is cross-serializer (Rust `Env::put`
  vs Lean `Ixon.serEnv`), which the serde gate guarantees agree on
  identical environments — so byte equality here certifies the full
  pipeline, not just the compiler core.

  Exit codes: 0 success (and aligned, when checked); 1 pipeline error or
  divergence; 2 usage.
-/
module
public import Cli
public import Ix.Common
public import Ix.Meta
public import Ix.CompileM
public import Ix.CompileDriver
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

def runCompileLeanCmdCore (p : Cli.Parsed) : IO UInt32 := do
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
  if let some e ← applySharingLimitsFlag p then
    p.printError s!"error: {e}"
    return 2

  IO.println s!"[compile-lean] building {pathStr}..."
  Ix.PhaseTimers.timeWall "lake build of the input module" (buildFile pathStr)
  let fe ← Ix.PhaseTimers.timeWall "Lean environment import and elaboration"
    (getFileEnvCore pathStr)
  let constList ← Ix.PhaseTimers.timeWall "constant list" do
    if p.hasFlag "local" then pure (localConstList fe) else defaultConstList fe pathStr
  IO.println s!"[compile-lean] {constList.length} constants, {workers} workers"

  let t0 ← IO.monoMsNow
  let input ← Ix.PhaseTimers.timeWall "source-contract preparation (compileInputFromEnv)" do
    IO.ofExcept ((Ix.Compile.compileInputFromEnv fe.env constList).mapError toString)
  -- `--rust-check`: the Rust compile is independent of the Lean one, so it runs
  -- alongside it on a thread of its own (`IX_RUST_CHECK_SERIAL=1`: after it, for
  -- timings of the Lean compile alone); its bytes are compared below.
  let rustSerial := (← IO.getEnv "IX_RUST_CHECK_SERIAL").any (· != "0")
  let rustCompile : IO (ByteArray × Nat) := do
    let tR ← IO.monoMsNow
    let dir ← IO.FS.createTempDir
    let rustOut := dir / "rust-check.ixe"
    let constants ← IO.ofExcept input.prepare
    let _ ← Ix.CompileM.rsCompileEnvBytesFFI constants rustOut.toString true
    let rustBytes ← IO.FS.readBinFile rustOut
    IO.FS.removeDirAll dir
    return (rustBytes, (← IO.monoMsNow) - tR)
  let rustTask? ← if p.hasFlag "rust-check" && !rustSerial then
      some <$> IO.asTask (prio := .dedicated) rustCompile
    else pure none
  match ← Ix.CompileM.compileLeanInput input (numWorkers := workers)
      (dbg := true) with
  | .error e =>
    IO.println s!"[compile-lean] FAILED: {e}"
    return 1
  | .ok out =>
    let elapsed := (← IO.monoMsNow) - t0
    -- Same exit policy as `ix compile`: fail-closed by default — any
    -- block failure means a nonzero exit and no output file, unless
    -- `--allow-partial` explicitly opts into the grounded subset.
    let ungroundedCount := out.cenv.ungrounded.size
    if !p.hasFlag "allow-partial" && ungroundedCount > 0 then
      IO.eprintln s!"[compile-lean] error: {ungroundedCount} constant(s) \
failed to compile; nothing written to {outPath} (use --allow-partial to \
serialize the grounded subset)"
      for (n, e) in (rootCausesFirst out.cenv.ungrounded.toList).take 8 do
        IO.eprintln s!"  [ungrounded] {n.pretty}: {(e.replace "\n" " ").take 200}"
      return 1
    Ix.PhaseTimers.timeWall "write the output file" (IO.FS.writeBinFile outPath out.bytes)
    IO.println s!"[compile-lean] wrote {out.bytes.size} bytes to {outPath} \
({out.blockCount} blocks, {out.ungroundedCount} ungrounded, \
{ungroundedCount} block failures) in {elapsed}ms"
    if ungroundedCount > 0 then
      IO.println s!"[compile-lean] PARTIAL: {ungroundedCount} constants failed to compile"
      for (n, e) in (rootCausesFirst out.cenv.ungrounded.toList).take 8 do
        IO.println s!"  {n.pretty}: {e.take 200}"

    if p.hasFlag "rust-check" then
      IO.println s!"[compile-lean] --rust-check: compiling via Rust FFI{if rustTask?.isSome then " (ran alongside the Lean compile)" else ""}..."
      let (rustBytes, tRe) ← match rustTask? with
        | some t => IO.ofExcept (← IO.wait t)
        | none => rustCompile
      Ix.PhaseTimers.wall " (not the Lean compiler) --rust-check: Rust compile" tRe
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

/-- `runCompileLeanCmdCore`, then the phase table on stderr when
    `IX_PHASE_TIMERS` is set (`Ix.PhaseTimers`; nothing otherwise). -/
def runCompileLeanCmd (p : Cli.Parsed) : IO UInt32 := do
  let rc ← runCompileLeanCmdCore p
  for line in ← Ix.PhaseTimers.report do
    IO.eprintln line
  return rc

end Ix.Cli.CompileLeanCmd

open Ix.Cli.CompileLeanCmd in
def compileLeanCmd : Cli.Cmd := `[Cli|
  "compile-lean" VIA runCompileLeanCmd;
  "Compile a Lean file to Ixon through the pure-Lean pipeline (canon → graph → ground → condense → aux-aware compile → serialize)"

  FLAGS:
    out          : String; "Output path for the serialized Ixon.Env bytes; defaults to the lowercased input file stem with `.ixe`"
    workers      : Nat;    "Worker count for the parallel phases (default 32)"
    "local" ;              "Compile only the constants the input file itself declares, with their transitive dependencies, instead of the whole import env (as `ix compile --local`); applies to --rust-check too."
    "rust-check" ;         "Also compile via the Rust FFI compiler and byte-compare the outputs (the ALIGNED gate); exit 1 on divergence"
    "allow-partial" ;      "Serialize the grounded subset and exit 0 even when some constants fail to compile. Default is fail-closed: any block failure means a nonzero exit and NO output file."
    "sharing-limits" : String; "Override resource limits of the canonical sharing construction (same format as `ix compile --sharing-limits`); applies to the Lean compile and to --rust-check. Sets IX_SHARING_LIMITS."

  ARGS:
    ...path : String; "Path to the Lean source file to compile."
]

end

