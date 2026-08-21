/-
  Mathlib-spine peak-RSS gate (plan Item 8 / I8): a catalog whose
  members share one heavy closure — mathlib — must build with peak RSS
  ~1× that closure, not ~N×. `Benchmarks/CatalogReal` cannot exhibit
  the pre-streaming failure (its members barely share closures);
  `Benchmarks/CatalogSpine` adds three small real-corpus mathlib
  dependents (BET, GibbsMeasure, KolmogorovExtension4) whose
  environments each contain the full mathlib closure.

  Two subprocess legs of `ix catalog … --report …` (dogfooding I7,
  positional member vector): a baseline over mathlib + its dependency
  spine, then the full spine with the three dependents. The gate asserts the spine
  peak (`peakRssBytes`, process-tree VmHWM) stays under 1.6× the
  baseline — pre-streaming, each extra dependent held its own mathlib
  environment and the ratio lands well above that.

  Heavy and manual (`--ignored catalog-spine`): needs `lake build ix`
  first, network + `lake exe cache get` on the first workspace build,
  and the RSS sampler is Linux-only (the gate fails, not skips, where
  it cannot measure).
-/
module

public import LSpec
public import Ix.Catalog

public section

open LSpec

namespace Tests.Ix.CatalogSpine

private def spineDir : System.FilePath := "Benchmarks" / "CatalogSpine"
private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

/-- Mathlib's dependency spine, dependencies first: every non-toolchain
    package in any member's import closure needs a catalog entry. -/
private def depMembers : List (String × String) := [
  ("Batteries", "Batteries"), ("Qq", "Qq"), ("Aesop", "Aesop"),
  ("ProofWidgets", "ProofWidgets"), ("Cli", "Cli"),
  ("ImportGraph", "ImportGraph"), ("LeanSearchClient", "LeanSearchClient"),
  ("Plausible", "Plausible"), ("Mathlib", "Mathlib") ]

/-- The heavy dependents: small libraries whose closures each contain
    all of mathlib. -/
private def heavyDependents : List (String × String) := [
  ("BET", "BET"), ("GibbsMeasure", "GibbsMeasure"),
  ("KolmogorovExtension4", "KolmogorovExtension4") ]

/-- Run one `ix catalog` leg in a temp dir and return its reported
    `peakRssBytes`. Members go as the positional
    `Qualifier=Root[,Root…]` vector — there is no spec file format. -/
private def runLeg (label : String) (libs : List (String × String)) :
    IO (Except String Nat) := do
  let dir ← IO.FS.createTempDir
  try
    let reportPath := dir / s!"{label}-report.json"
    let outPath := dir / s!"{label}.ixe"
    let exe ← IO.FS.realPath ixExe
    let out ← IO.Process.output {
      cmd := exe.toString
      args := #["catalog", "--prefix", "Spine",
                "--out", outPath.toString, "--report", reportPath.toString]
        ++ libs.toArray.map (fun (q, r) => s!"{q}={r}")
      cwd := some spineDir }
    if out.exitCode != 0 then
      return .error s!"{label} leg failed ({out.exitCode}): \
{out.stderr.take 300} … {(out.stdout.takeEnd 300).toString}"
    let content ← IO.FS.readFile reportPath
    return do
      let json ← Lean.Json.parse content
      let peak ← (← json.getObjVal? "peakRssBytes").getNat?
      if peak == 0 then
        throw s!"{label}: peakRssBytes is 0 — RSS sampler unavailable \
(non-Linux?)"
      return peak
  finally
    IO.FS.removeDirAll dir

private def spineTest : IO (Bool × Nat × Nat × Option String) := do
  unless (← ixExe.pathExists) do
    return (false, 0, 0, some s!"{ixExe} missing — run `lake build ix` first")
  -- Fetch + build the member libraries. First run needs network and
  -- pulls the mathlib olean cache; idempotent afterwards. `cache get`
  -- failure is tolerated — the build below is authoritative.
  let cacheOut ← IO.Process.output {
    cmd := "lake", args := #["exe", "cache", "get"], cwd := some spineDir }
  let build ← IO.Process.output {
    cmd := "lake"
    args := #["build"] ++ (depMembers ++ heavyDependents).toArray.map (·.2)
    cwd := some spineDir }
  if build.exitCode != 0 then
    return (false, 0, 0, some s!"spine workspace build failed \
(cache get exit {cacheOut.exitCode}): {build.stderr.take 400}")
  let basePeak ← match ← runLeg "baseline" depMembers with
    | .ok peak => pure peak
    | .error e => return (false, 0, 0, some e)
  let spinePeak ← match ← runLeg "spine" (depMembers ++ heavyDependents) with
    | .ok peak => pure peak
    | .error e => return (false, 0, 0, some e)
  -- The I1/I8 bound: adding members that share the already-cataloged
  -- heavy closure must not multiply the peak. Pre-streaming, three
  -- extra mathlib environments held simultaneously put this well
  -- above 1.6×.
  if spinePeak * 5 ≥ basePeak * 8 then
    return (false, spinePeak, basePeak,
      some s!"peak RSS {spinePeak} B vs baseline {basePeak} B — over \
1.6×; shared closures are being held per-member")
  return (true, spinePeak, basePeak, none)

def suite : List TestSeq := [
  .individualIO
    "catalog spine: shared mathlib closure peaks ~1×, not ~N× (I8)"
    none spineTest .done ]

end Tests.Ix.CatalogSpine
