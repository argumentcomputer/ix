/-
  The TruthMines corpus tiers (consolidation plan Phase 0.4): build the
  admission specs into single `.ixe` artifacts through the `truthmines`
  driver, and kernel-check what they produce.

  Ignored suites (build and typecheck gate independently; the mini tier
  chains both):

  * `truthmines` — the full corpus: `.lake/build/bin/truthmines build`
    with its default outputs (`truthmines.ixe` + `truthmines.report.json`
    at the repo root, both gitignored — the `compilemathlib.ixe`
    convention), then assert the report: written fail-closed with zero
    ungrounded, all members present, a positive replay count, and peak
    RSS measured (hard failure where the Linux sampler is unavailable,
    like the spine gate) and under a coarse safety ceiling — tighten it
    once the first green run records baselines.
  * `truthmines-check` — `ix check-rs` over `truthmines.ixe`, with
    `IX_MAX_REC_FUEL` raised (the spine run needed 10⁹ for
    `Spine.BET.periodicPt_mem_recurrentSet`).
  * `truthmines-mini` — the small infrastructure tier end to end:
    `build --mini --audit-only A,B` (toolchain base + RelocFixture
    collision pair + spine + Mathlib + FLT; the fixture audit proves the
    anon-address invariant through the driver), then `ix check-rs` over
    `truthmines-mini.ixe`. Spine-class cost (~35 GiB, ~20 min).

  All heavy steps run under the driver's `Ix.Watchdog` ceiling. Needs
  `lake build ix` and `lake build truthmines` first, network +
  `lake exe cache get` on the first workspace build.
  Run `lake test -- --ignored truthmines-mini` (or `truthmines
  truthmines-check` for the full corpus).
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

/-- Coarse safety ceiling until green runs record baselines: the spine
    leg peaks at ~35 GiB; the corpus estimate is ~40–50 GiB. The
    driver's watchdog enforces the hard cap — this asserts the
    measurement stayed sane. -/
private def peakRssCeilingBytes : Nat := 96 * 1024 * 1024 * 1024

/-- Drive `truthmines build` and assert its report. -/
private def driverBuild (mini : Bool) (auditOnly : Option String)
    (artifact report : System.FilePath) (expectMembers : Nat) :
    IO (Bool × Nat × Nat × Option String) := do
  unless (← ixExe.pathExists) do
    return (false, 0, 0, some s!"{ixExe} missing — run `lake build ix` first")
  unless (← driverExe.pathExists) do
    return (false, 0, 0,
      some s!"{driverExe} missing — run `lake build truthmines` first")
  let exe ← IO.FS.realPath driverExe
  let mut args := #["build", "--out", artifact.toString,
    "--report", report.toString]
  if mini then
    args := args.push "--mini"
  if let some qualifiers := auditOnly then
    args := args ++ #["--audit-only", qualifiers]
  let child ← IO.Process.spawn { cmd := exe.toString, args }
  let exit ← child.wait
  if exit != 0 then
    return (false, 0, 0, some s!"truthmines build failed ({exit})")
  let content ← IO.FS.readFile report
  let checks : Except String (Nat × Nat) := do
    let json ← Lean.Json.parse content
    let written ← (← json.getObjVal? "written").getBool?
    unless written do throw "report says the artifact was not written"
    let ungrounded ← (← json.getObjVal? "ungroundedCount").getNat?
    unless ungrounded == 0 do
      throw s!"{ungrounded} ungrounded constants — fail-closed catalog \
expected zero"
    let libs ← (← json.getObjVal? "libs").getArr?
    unless libs.size == expectMembers do
      throw s!"report carries {libs.size} members, the spec has \
{expectMembers}"
    let replayed ← (← json.getObjVal? "replayed").getNat?
    unless replayed > 0 do throw "zero declarations replayed"
    if auditOnly.isSome then
      let audited ← (← json.getObjVal? "auditedQualifiers").getArr?
      unless !audited.isEmpty do
        throw "audit requested but the report records no audited qualifiers"
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

/-- `ix check-rs` over an artifact a build leg left behind. -/
private def checkArtifact (artifact : System.FilePath) (hint : String) :
    IO (Bool × Nat × Nat × Option String) := do
  unless (← ixExe.pathExists) do
    return (false, 0, 0, some s!"{ixExe} missing — run `lake build ix` first")
  unless (← artifact.pathExists) do
    return (false, 0, 0, some s!"{artifact} missing — run {hint} first")
  let exe ← IO.FS.realPath ixExe
  let child ← IO.Process.spawn {
    cmd := exe.toString
    args := #["check-rs", artifact.toString]
    env := #[("IX_MAX_REC_FUEL", some "1000000000")] }
  let exit ← child.wait
  if exit != 0 then
    return (false, 0, 0, some s!"ix check-rs rejected {artifact} ({exit})")
  return (true, 0, 0, none)

def buildSuite : List TestSeq := [
  .individualIO
    "truthmines: full admitted corpus builds fail-closed via the driver"
    none (driverBuild false none "truthmines.ixe" "truthmines.report.json"
      catalogSpec.libs.size) .done ]

def checkSuite : List TestSeq := [
  .individualIO "truthmines: kernel check over the corpus artifact"
    none (checkArtifact "truthmines.ixe"
      "`lake test -- --ignored truthmines` or `lake exe truthmines build`")
    .done ]

def miniSuite : List TestSeq := [
  .individualIO
    "truthmines-mini: fixtures + spine + Mathlib + FLT build with fixture audit"
    none (driverBuild true (some "A,B") "truthmines-mini.ixe"
      "truthmines-mini.report.json" catalogMiniSpec.libs.size) .done,
  .individualIO "truthmines-mini: kernel check over the mini artifact"
    none (checkArtifact "truthmines-mini.ixe"
      "the `truthmines-mini` build leg") .done ]

end Tests.Ix.TruthMines
