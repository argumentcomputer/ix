/-
  Cross-process compile determinism (ixc-catalog plan Phase 0.1 / A0.1).

  Every existing determinism gate runs both compiles in ONE process
  (memory/parallelism modes over a shared frontend env). The piece
  cache of the `.ixc` catalog trusts more: two `ix compile` runs of
  the same member, in separate processes on possibly different days,
  must produce `sha256`-identical `.ixe` files — the file hash in the
  catalog manifest is the cache key's witness. The root alone is not
  enough: `status.root` commits only §2, while the file also carries
  blobs, hints, and names.

  Two legs, both driving the real CLI binary in fresh subprocesses:

  * fixture-class: `Tests/Ix/Compile/Mutual.lean` — the aux-gen
    fixture corpus, module-visible closure, seconds.
  * Batteries-class: `Benchmarks/Compile/CompileBatteries.lean` — a
    real library through the sub-workspace bootstrap path
    (`buildFile` + oleans), minutes.

  `IxTests` depends on the `ix` executable target, so the ignored suite
  (`lake test -- --ignored compile-determinism`) is self-contained. The
  Batteries leg needs network on the first workspace build.
-/
module

public import LSpec

public section

open LSpec

namespace Tests.Ix.CompileDeterminism

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

/-- `sha256sum` of a file (Linux coreutils, same availability class as
    the RSS gates). -/
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

/-- One `ix compile` run in a fresh subprocess. Output captured; tails
    surfaced on failure. -/
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

/-- The gate: two separate `ix compile` processes over `source`, byte
    identity asserted via `sha256`. -/
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
    none (determinismLeg "Tests/Ix/Compile/Mutual.lean") .done,
  .individualIO
    "compile determinism: Batteries, two processes, sha256-identical"
    none (determinismLeg "Benchmarks/Compile/CompileBatteries.lean") .done ]

end Tests.Ix.CompileDeterminism
