/-
  Cross-process compile determinism.

  Two `ix compile` runs of the same module in separate subprocesses must
  produce Blake3-identical `.ixe` files — committing not only the canonical
  constants (`status.root`), but also blobs, hints, and names.
  (Large-corpus cross-process byte determinism against a pinned reference
  digest is also gated by `initstd-reference` in `ci:landing-initstd-cli`.)
-/
module

public import LSpec
public import Ix.FileDigest

public section

open LSpec

namespace Tests.Ix.CompileDeterminism

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

/-- One `ix compile` run in a fresh subprocess. -/
private def compileOnce (source : String) (out : System.FilePath) :
    IO (Except String Unit) := do
  let exe ← IO.FS.realPath ixExe
  let r ← IO.Process.output {
    cmd := exe.toString
    args := #["compile", source, "--out", out.toString] }
  if r.exitCode != 0 then
    return .error s!"ix compile {source} failed ({r.exitCode}): \
{r.stderr.take 300} … {(r.stdout.takeEnd 300).toString}"
  unless (← out.pathExists) do
    return .error s!"ix compile {source} exited 0 but wrote no {out}"
  return .ok ()

/-- Two separate `ix compile` processes over `source`, byte identity asserted via their Blake3
digests (`Ix.FileDigest.blake3File`). -/
private def determinismLeg (source : String) :
    IO (Bool × Nat × Nat × Option String) := do
  unless (← ixExe.pathExists) do
    return (false, 0, 0, some s!"{ixExe} missing — run `lake build ix` first")
  let dir ← IO.FS.createTempDir
  try
    let out1 := dir / "run1.ixe"
    let out2 := dir / "run2.ixe"
    if let .error e ← compileOnce source out1 then
      return (false, 0, 0, some e)
    if let .error e ← compileOnce source out2 then
      return (false, 0, 0, some e)
    let h1 ← try Ix.FileDigest.blake3File out1
      catch e => return (false, 0, 0, some s!"blake3 of {out1}: {e}")
    let h2 ← try Ix.FileDigest.blake3File out2
      catch e => return (false, 0, 0, some s!"blake3 of {out2}: {e}")
    let bytes := (← out1.metadata).byteSize.toNat
    if h1 != h2 then
      return (false, bytes, 0, some s!"{source}: cross-process compile \
is nondeterministic — {h1} vs {h2}")
    return (true, bytes, 0, none)
  finally
    IO.FS.removeDirAll dir

def suite : List TestSeq := [
  .individualIO
    "compile determinism: fixture corpus, two processes, Blake3-identical"
    none (determinismLeg "Tests/Ix/Compile/Mutual.lean") .done ]

end Tests.Ix.CompileDeterminism
