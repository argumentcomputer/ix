/-
  Cross-process compile determinism.

  Two `ix compile` runs of the same module in separate subprocesses must
  produce `sha256`-identical `.ixe` files — committing not only the canonical
  constants (`status.root`), but also blobs, hints, and names.
  (Large-corpus cross-process byte determinism against a pinned reference
  digest is also gated by `initstd-reference` in `ci:landing-initstd-cli`.)
-/
module

public import LSpec

public section

open LSpec

namespace Tests.Ix.CompileDeterminism

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

/-- `sha256sum` of a file. -/
private def sha256 (path : System.FilePath) : IO (Except String String) := do
  let out ← IO.Process.output {
    cmd := "sha256sum", args := #[path.toString] }
  if out.exitCode != 0 then
    return .error s!"sha256sum {path} failed ({out.exitCode}): {out.stderr.take 200}"
  match out.stdout.splitOn " " with
  | hash :: _ =>
    if hash.length == 64 then return .ok hash
    else return .error s!"sha256sum {path}: unparsable output {out.stdout.take 80}"
  | _ => return .error s!"sha256sum {path}: empty output"

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

/-- Two separate `ix compile` processes over `source`, byte identity asserted via `sha256`. -/
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
    let h1 ← match ← sha256 out1 with
      | .ok h => pure h
      | .error e => return (false, 0, 0, some e)
    let h2 ← match ← sha256 out2 with
      | .ok h => pure h
      | .error e => return (false, 0, 0, some e)
    let bytes := (← out1.metadata).byteSize.toNat
    if h1 != h2 then
      return (false, bytes, 0, some s!"{source}: cross-process compile \
is nondeterministic — {h1} vs {h2}")
    return (true, bytes, 0, none)
  finally
    IO.FS.removeDirAll dir

def suite : List TestSeq := [
  .individualIO
    "compile determinism: fixture corpus, two processes, sha256-identical"
    none (determinismLeg "Tests/Ix/Compile/Mutual.lean") .done ]

end Tests.Ix.CompileDeterminism
