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
public section

open System (FilePath)

namespace Ix.Cli.CompileLeanCmd

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

  IO.println s!"[compile-lean] building {pathStr}..."
  buildFile pathStr
  let leanEnv ← getFileEnv pathStr
  let constList := leanEnv.constants.toList
  IO.println s!"[compile-lean] {constList.length} constants, {workers} workers"

  let t0 ← IO.monoMsNow
  match ← Ix.CompileM.compileLeanConsts constList (numWorkers := workers)
      (dbg := true) with
  | .error e =>
    IO.println s!"[compile-lean] FAILED: {e}"
    return 1
  | .ok out =>
    let elapsed := (← IO.monoMsNow) - t0
    IO.FS.writeBinFile outPath out.bytes
    IO.println s!"[compile-lean] wrote {out.bytes.size} bytes to {outPath} \
({out.blockCount} blocks, {out.ungroundedCount} ungrounded, \
{out.cenv.ungrounded.size} block failures) in {elapsed}ms"
    if out.cenv.ungrounded.size > 0 then
      IO.println s!"[compile-lean] WARNING: {out.cenv.ungrounded.size} constants failed to compile"
      for (n, e) in out.cenv.ungrounded.toList.take 8 do
        IO.println s!"  {n.pretty}: {e.take 200}"

    if p.hasFlag "rust-check" then
      IO.println "[compile-lean] --rust-check: compiling via Rust FFI..."
      let tR ← IO.monoMsNow
      let dir ← IO.FS.createTempDir
      let rustOut := dir / "rust-check.ixe"
      let _ ← Ix.CompileM.rsCompileEnvBytesFFI constList rustOut.toString
      let rustBytes ← IO.FS.readBinFile rustOut
      IO.FS.removeDirAll dir
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
  "Compile a Lean file to Ixon through the pure-Lean pipeline (canon → graph → ground → condense → aux-aware compile → serialize)"

  FLAGS:
    out          : String; "Output path for the serialized Ixon.Env bytes; defaults to the lowercased input file stem with `.ixe`"
    workers      : Nat;    "Worker count for the parallel phases (default 32)"
    "rust-check" ;         "Also compile via the Rust FFI compiler and byte-compare the outputs (the ALIGNED gate); exit 1 on divergence"

  ARGS:
    ...path : String; "Path to the Lean source file to compile."
]

end
