/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.CompileDriver
import Ix.Meta
import Tests.Ix.Kernel.ReaderFidelity
import Tests.Ix.Kernel.ReaderRoundtrip
import Tests.Ix.Kernel.EgressFidelity

/-! # `kernel-reader-fidelity`: the reader against Lean on Init and Std

Compares the Ixon reader's reading of a compiled environment with the
reference translation of the Lean environment it was compiled from
(`Tests.Ix.Kernel.ReaderFidelity`). The Lean side is `Init` and `Std`, loaded
from this toolchain's `.olean` files.

* `kernel-reader-fidelity <input.ixe> [limit]`: the compiled side is an
  `.ixe`, normally the census corpus `.lake/envs/initstd.ixe` (compiled by
  `ix compile` from `Benchmarks/Compile/CompileInitStd.lean`, which imports
  exactly `Init` and `Std`); `limit` bounds the records read, in the census
  order.
* `kernel-reader-fidelity --compile [limit]`: compiles `Init` and `Std` in
  process with Ix's Rust compiler (`Ix.CompileM.rsCompileEnvBytes`, the
  compiler behind `ix compile`) and compares that.
* `kernel-reader-fidelity --check-kernel`: what `lake run check-kernel` runs,
  the census corpus if it is present and an in-process compile otherwise,
  at `checkKernelLimit` records.
* `kernel-reader-fidelity --fixture`: the `lake test` suite's check of the fixture closure
  (`Tests.Ix.Kernel.ReaderRoundtrip.evaluate`: expected verdicts and tampers).
* `kernel-reader-fidelity --egress <input.ixe>`: the output side only, with no
  Lean side, for an environment of any size (Mathlib): every block's
  projection records and its order (`Tests.Ix.Kernel.EgressFidelity.projections`).

`FIDELITY_ROOTS` (comma-separated Lean names) restricts a run to the prelude
and the closure of those constants. Every mode also checks the kernel's
output side on the same records (`Tests.Ix.Kernel.EgressFidelity`: each
block's projection records as the certified writer writes them, its canonical
order; with `--fixture`, re-reading and the certified entries' installed
environments as well). The report goes to stdout; the exit code is 1 on any
unexplained difference or problem. -/

namespace Tests.Ix.Kernel.ReaderFidelityMain

open Tests.Ix.Kernel.ReaderFidelity

/-- The records `check-kernel` compares (in the census order, about a
fifth of Init and Std: the prelude, `Init.Prelude`'s closure and well past
it, which covers the nested `Lean.Syntax` block). -/
def checkKernelLimit : Nat := 20000

def corpus : System.FilePath := ".lake/envs/initstd.ixe"

/-- `Init` and `Std` compiled in process by Ix's Rust compiler. -/
def compileInitStd (leanEnv : Lean.Environment) : IO Ixon.Env := do
  let dir ← IO.FS.createTempDir
  try
    let path := dir / "initstd.ixe"
    let _ ← Ix.CompileM.rsCompileEnvBytes leanEnv path.toString
    IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
  finally
    IO.FS.removeDirAll dir

def report (r : Report) : IO UInt32 := do
  IO.println r.summary
  (← IO.getStdout).flush
  return if r.unexplained.isEmpty && r.problems.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 := do
  if args == ["--fixture"] then
    let (r, lines, errors) ← Tests.Ix.Kernel.ReaderRoundtrip.evaluate
    IO.println r.summary
    for l in lines do IO.println l
    for e in errors do IO.eprintln s!"reader-fidelity: fixture: {e}"
    return if errors.isEmpty then 0 else 1
  let started ← IO.monoMsNow
  if let ["--egress", path] := args then
    let ixon ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
    let mut store : Benchmarks.Kernel.CheckIxeStep.RecordStore := {}
    for (address, lazy) in ixon.consts.toList do
      store := store.insert address (← IO.ofExcept lazy.get)
    IO.eprintln s!"reader-fidelity: {path}: {store.size} constants decoded in \
      {(← IO.monoMsNow) - started} ms"
    let proj := Tests.Ix.Kernel.EgressFidelity.projections store ixon.blobs.toList
    IO.println proj.summary
    for p in proj.orderProblems do IO.println s!"block order: {p}"
    IO.eprintln s!"reader-fidelity: done in {(← IO.monoMsNow) - started} ms"
    let ok := proj.problems.isEmpty && proj.matched == proj.compiled && proj.orderProblems.isEmpty
    IO.Process.exit (if ok then 0 else 1)
  let leanEnv ← getCompileEnv #[`Init, `Std]
  let (ixon, limit, source) ← match args with
    | ["--check-kernel"] =>
      if ← corpus.pathExists then
        pure (← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile corpus)), some checkKernelLimit,
          corpus.toString)
      else pure (← compileInitStd leanEnv, some checkKernelLimit, "in-process compile")
    | "--compile" :: rest => pure (← compileInitStd leanEnv, rest.head?.bind String.toNat?,
        "in-process compile")
    | [path] | [path, _] =>
      pure (← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path)), args[1]?.bind String.toNat?, path)
    | _ =>
      IO.eprintln "usage: kernel-reader-fidelity <input.ixe> [limit] | --compile [limit] | \
        --check-kernel | --fixture | --egress <input.ixe>"
      return 2
  let loaded ← IO.monoMsNow
  let input ← Input.ofEnv leanEnv ixon
  let decoded ← IO.monoMsNow
  IO.eprintln s!"reader-fidelity: {source}: {input.names.size} Lean constants with records, \
    {input.store.size} records; loaded in {loaded - started} ms, decoded in {decoded - loaded} ms"
  let roots ← match ← IO.getEnv "FIDELITY_ROOTS" with
    | none => pure none
    | some list => pure <| some <| ((list.splitOn ",").filter (!·.isEmpty)).toArray.filterMap fun n =>
        (ixon.named[Ix.Name.fromLeanName n.toName]?).map (·.addr)
  let code ← report (← run input limit (roots := roots))
  -- the kernel's output side: every block's projection records as the
  -- certified writer writes them, and its canonical order
  let proj := Tests.Ix.Kernel.EgressFidelity.projections input.store ixon.blobs.toList
  IO.println proj.summary
  let code := if proj.problems.isEmpty && proj.matched == proj.compiled && proj.orderProblems.isEmpty
    then code else 1
  IO.eprintln s!"reader-fidelity: done in {(← IO.monoMsNow) - started} ms"
  -- exit without tearing the environments down (the Rust compiler's
  -- environment took minutes to free at exit)
  IO.Process.exit code.toUInt8

end Tests.Ix.Kernel.ReaderFidelityMain

def main (args : List String) : IO UInt32 := Tests.Ix.Kernel.ReaderFidelityMain.main args
