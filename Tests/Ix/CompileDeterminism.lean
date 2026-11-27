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
    -- `--local`: the fixture's own declarations and their dependency
    -- closure. The fixture is a `module` with `public import Lean`, whose
    -- default scope is every public declaration of Init, Std and Lean.
    args := #["compile", source, "--local", "--out", out.toString] }
  if r.exitCode != 0 then
    return .error s!"ix compile {source} failed ({r.exitCode}): \
{r.stderr.take 300} … {(r.stdout.takeEnd 300).toString}"
  unless (← out.pathExists) do
    return .error s!"ix compile {source} exited 0 but wrote no {out}"
  return .ok ()

/-- Two separate `ix compile` processes over `source`, byte identity asserted via their Blake3
digests (`Ix.FileDigest.blake3File`). -/
private def determinismLeg (source : String) : AssertM Unit := do
  unless (← ixExe.pathExists) do
    fail s!"{ixExe} missing — run `lake build ix` first"
  let dir ← IO.FS.createTempDir
  try
    let out1 := dir / "run1.ixe"
    let out2 := dir / "run2.ixe"
    let task1 ← IO.asTask (prio := .dedicated) (compileOnce source out1)
    let task2 ← IO.asTask (prio := .dedicated) (compileOnce source out2)
    let res1 ← IO.wait task1
    let res2 ← IO.wait task2
    if let Except.error e ← IO.ofExcept res1 then
      fail e
    if let Except.error e ← IO.ofExcept res2 then
      fail e
    let h1 ← match ← (Ix.FileDigest.blake3File out1).toBaseIO with
      | .ok h => pure h
      | .error e => fail s!"blake3 of {out1}: {e}"
    let h2 ← match ← (Ix.FileDigest.blake3File out2).toBaseIO with
      | .ok h => pure h
      | .error e => fail s!"blake3 of {out2}: {e}"
    if h1 != h2 then
      fail s!"{source}: cross-process compile is nondeterministic — {h1} vs {h2}"
  finally
    IO.FS.removeDirAll dir

public def suite : LSpec.Spec := do
  it "compile determinism: fixture corpus, two processes, Blake3-identical" do
    determinismLeg "Tests/Ix/Compile/Mutual.lean"

end Tests.Ix.CompileDeterminism
