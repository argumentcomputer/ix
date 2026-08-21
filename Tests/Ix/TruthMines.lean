/-
  The TruthMines corpus tier (consolidation plan Phase 0.4): build the
  full 77-member admission spec into a single `truthmines.ixe` through
  the `truthmines` driver, and kernel-check the artifact.

  Two chained ignored suites so build and typecheck gate independently:

  * `truthmines` — runs `.lake/build/bin/truthmines build` with its
    default outputs (`truthmines.ixe` + `truthmines.report.json` at the
    repo root, both gitignored — the `compilemathlib.ixe` convention),
    then asserts the report: written fail-closed with zero ungrounded,
    all members present, a positive replay count, and peak RSS measured
    (hard failure where the Linux sampler is unavailable, like the
    spine gate) and under a coarse safety ceiling — tighten it once the
    first green run records baselines.
  * `truthmines-check` — `ix check-rs` over the artifact the build leg
    left behind, with `IX_MAX_REC_FUEL` raised (the spine run needed
    10⁹ for `Spine.BET.periodicPt_mem_recurrentSet`).

  Corpus-heavy and manual: needs `lake build ix` and
  `lake build truthmines` first, network + `lake exe cache get` on the
  first workspace build, ~124 GiB-box territory, and roughly an hour.
  Run `lake test -- --ignored truthmines truthmines-check`.
-/
module

public import LSpec
public import Benchmarks.TruthMinesSpec.Projection

public section

open LSpec
open TruthMinesSpec

namespace Tests.Ix.TruthMines

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"
private def driverExe : System.FilePath :=
  ".lake" / "build" / "bin" / "truthmines"
private def artifactPath : System.FilePath := "truthmines.ixe"
private def reportPath : System.FilePath := "truthmines.report.json"

/-- Coarse safety ceiling until the first green run records baselines:
    the spine leg peaks at ~35 GiB; the corpus estimate is ~40–50 GiB. -/
private def peakRssCeilingBytes : Nat := 96 * 1024 * 1024 * 1024

private def buildTest : IO (Bool × Nat × Nat × Option String) := do
  unless (← ixExe.pathExists) do
    return (false, 0, 0, some s!"{ixExe} missing — run `lake build ix` first")
  unless (← driverExe.pathExists) do
    return (false, 0, 0,
      some s!"{driverExe} missing — run `lake build truthmines` first")
  let exe ← IO.FS.realPath driverExe
  let child ← IO.Process.spawn {
    cmd := exe.toString
    args := #["build", "--out", artifactPath.toString,
              "--report", reportPath.toString] }
  let exit ← child.wait
  if exit != 0 then
    return (false, 0, 0, some s!"truthmines build failed ({exit})")
  let content ← IO.FS.readFile reportPath
  let checks : Except String (Nat × Nat) := do
    let json ← Lean.Json.parse content
    let written ← (← json.getObjVal? "written").getBool?
    unless written do throw "report says the artifact was not written"
    let ungrounded ← (← json.getObjVal? "ungroundedCount").getNat?
    unless ungrounded == 0 do
      throw s!"{ungrounded} ungrounded constants — fail-closed corpus \
expected zero"
    let libs ← (← json.getObjVal? "libs").getArr?
    unless libs.size == catalogSpec.libs.size do
      throw s!"report carries {libs.size} members, admission spec has \
{catalogSpec.libs.size}"
    let replayed ← (← json.getObjVal? "replayed").getNat?
    unless replayed > 0 do throw "zero declarations replayed"
    let peak ← (← json.getObjVal? "peakRssBytes").getNat?
    if peak == 0 then
      throw "peakRssBytes is 0 — RSS sampler unavailable (non-Linux?)"
    unless peak < peakRssCeilingBytes do
      throw s!"peak RSS {peak} B is over the {peakRssCeilingBytes} B \
safety ceiling"
    return (replayed, peak / (1024 * 1024))
  match checks with
  | .ok (replayed, peakMiB) => return (true, replayed, peakMiB, none)
  | .error message => return (false, 0, 0, some message)

private def checkTest : IO (Bool × Nat × Nat × Option String) := do
  unless (← ixExe.pathExists) do
    return (false, 0, 0, some s!"{ixExe} missing — run `lake build ix` first")
  unless (← artifactPath.pathExists) do
    return (false, 0, 0, some s!"{artifactPath} missing — run \
`lake test -- --ignored truthmines` or `lake exe truthmines build` first")
  let exe ← IO.FS.realPath ixExe
  let child ← IO.Process.spawn {
    cmd := exe.toString
    args := #["check-rs", artifactPath.toString]
    env := #[("IX_MAX_REC_FUEL", some "1000000000")] }
  let exit ← child.wait
  if exit != 0 then
    return (false, 0, 0, some s!"ix check-rs rejected the corpus ({exit})")
  return (true, 0, 0, none)

def buildSuite : List TestSeq := [
  .individualIO
    "truthmines: full admitted corpus builds fail-closed via the driver"
    none buildTest .done ]

def checkSuite : List TestSeq := [
  .individualIO "truthmines: kernel check over the corpus artifact"
    none checkTest .done ]

end Tests.Ix.TruthMines
