/-
  The TruthMines corpus tiers over the piece pipeline: drive
  `truthmines build` (per-member watchdogged `ix compile` straight
  into the self-contained `.ixc` directory → `ix catalog assemble` →
  `ix catalog verify`) and kernel-check what it produces.

  The `.ixc` directory is the whole deliverable AND the
  machine-readable record — there are no report artifacts. Gates read
  the manifest through the in-process core (`rs_catalog_info` /
  `rs_catalog_verify`), never a side file.

  Ignored suites:

  * `truthmines` — the full corpus: `truthmines build` → assert the
    manifest (every member present with a recomputed root, catalog
    verify green over a non-empty union).
  * `truthmines-check` — `truthmines check`: `ix check-rs --anon` over
    every member piece in the `.ixc`, one subprocess per piece (the
    fat-profile rung-1 checking story: embarrassingly parallel, peak =
    max member).
  * `truthmines-mini` — the small infrastructure tier end to end
    (fixtures + spine + Mathlib + FLT → `truthmines-mini.ixc/`), then
    the per-piece check sweep over its members.
  * `truthmines-validate` / `truthmines-validate-mini` — the METADATA
    fidelity rung (Q1): `truthmines validate [--mini]`, the 8-phase
    `ix validate` pipeline (aux-gen congruence, alpha canonicity,
    decompile both ways, per-constant roundtrip) over every native
    member's driver module, plus Palomar.ix as one aggregate library in
    the full tier. The anon check sweep never touches §4/§5; this leg is
    what gates them, per validation target.

  All heavy steps run under the driver's `Ix.Watchdog` ceilings. Needs
  `lake build ix truthmines` first; network + `lake exe cache get` on
  the first workspace build. Run
  `lake test -- --ignored truthmines-mini` (or `truthmines
  truthmines-check` for the full corpus).
-/
module

public import LSpec
public import Benchmarks.TruthMinesSpec.Projection
public import Ix.Cli.CatalogCmd

public section

open LSpec
open TruthMinesSpec

namespace Tests.Ix.TruthMines

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"
private def driverExe : System.FilePath :=
  ".lake" / "build" / "bin" / "truthmines"

/-- The manifest's member labels, via the in-process core. -/
private def memberLabels (ixc : String) : IO (Except String (List String)) := do
  let content ← Ix.Cli.CatalogCmd.rsCatalogInfoFFI ixc
  return do
    let json ← Lean.Json.parse content
    let members ← (← json.getObjVal? "members").getArr?
    let mut labels : List String := []
    for m in members do
      let label ← (← m.getObjVal? "label").getStr?
      let root ← (← m.getObjVal? "envRoot").getStr?
      unless root.length == 64 do
        throw s!"member {label}: malformed env root `{root}`"
      labels := labels ++ [label]
    return labels

/-- Drive `truthmines build` and assert the resulting `.ixc` directory
    through the core: member set complete, roots well-formed, verify
    green over a non-empty union. -/
private def driverBuild (mini : Bool) (ixc : System.FilePath)
    (expectMembers : Nat) : IO (Bool × Nat × Nat × Option String) := do
  unless (← ixExe.pathExists) do
    return (false, 0, 0, some s!"{ixExe} missing — run `lake build ix` first")
  unless (← driverExe.pathExists) do
    return (false, 0, 0,
      some s!"{driverExe} missing — run `lake build truthmines` first")
  let exe ← IO.FS.realPath driverExe
  let mut args := #["build", "--out", ixc.toString]
  if mini then
    args := args.push "--mini"
  let child ← IO.Process.spawn { cmd := exe.toString, args }
  let exit ← child.wait
  if exit != 0 then
    return (false, 0, 0, some s!"truthmines build failed ({exit})")
  unless (← (ixc / "manifest").pathExists) do
    return (false, 0, 0, some s!"driver exited 0 but {ixc} has no manifest")
  let labels ← match ← memberLabels ixc.toString with
    | .ok ls => pure ls
    | .error e => return (false, 0, 0, some s!"manifest: {e}")
  unless labels.length == expectMembers do
    return (false, labels.length, expectMembers,
      some s!"manifest carries {labels.length} members, the spec has \
{expectMembers}")
  -- Independent re-verify through the core (the driver already
  -- verified; this pins the suite's own read of the artifact).
  let verifyContent ← Ix.Cli.CatalogCmd.rsCatalogVerifyFFI ixc.toString false
  let union : Except String Nat := do
    let json ← Lean.Json.parse verifyContent
    (← json.getObjVal? "unionConsts").getNat?
  match union with
  | .ok n =>
    if n == 0 then
      return (false, 0, 0, some "catalog verify reports an empty union")
    return (true, labels.length, n, none)
  | .error e => return (false, 0, 0, some s!"verify: {e}")

/-- Drive `truthmines check [--mini]`: the per-piece `ix check-rs
    --anon` sweep over the tier's `.ixc` — the fat-profile checking
    rung lives in the driver (bounded pool, output captured per piece,
    tails + solo repro surfaced on rejection); the suite is exit-code
    gated like the validate legs. -/
private def driverCheck (mini : Bool) : IO (Bool × Nat × Nat × Option String) := do
  unless (← driverExe.pathExists) do
    return (false, 0, 0,
      some s!"{driverExe} missing — run `lake build truthmines` first")
  let exe ← IO.FS.realPath driverExe
  let mut args := #["check"]
  if mini then
    args := args.push "--mini"
  let child ← IO.Process.spawn { cmd := exe.toString, args }
  let exit ← child.wait
  if exit != 0 then
    return (false, 0, 0, some s!"truthmines check failed ({exit})")
  return (true, 0, 0, none)

def buildSuite : List TestSeq := [
  .individualIO
    "truthmines: full corpus pieces + self-contained .ixc via the driver"
    none (driverBuild false "truthmines.ixc" catalogSpec.libs.size) .done ]

def checkSuite : List TestSeq := [
  .individualIO "truthmines: per-piece kernel check sweep (fat rung 1)"
    none (driverCheck false) .done ]

/-- Drive `truthmines validate [--mini]`: per-member 8-phase metadata
    fidelity, exit-code gated (the driver prints the verdict table). -/
private def driverValidate (mini : Bool) :
    IO (Bool × Nat × Nat × Option String) := do
  unless (← ixExe.pathExists) do
    return (false, 0, 0, some s!"{ixExe} missing — run `lake build ix` first")
  unless (← driverExe.pathExists) do
    return (false, 0, 0,
      some s!"{driverExe} missing — run `lake build truthmines` first")
  let exe ← IO.FS.realPath driverExe
  let mut args := #["validate"]
  if mini then
    args := args.push "--mini"
  let child ← IO.Process.spawn { cmd := exe.toString, args }
  let exit ← child.wait
  if exit != 0 then
    return (false, 0, 0, some s!"truthmines validate failed ({exit})")
  return (true, 0, 0, none)

def validateSuite : List TestSeq := [
  .individualIO
    "truthmines-validate: 8-phase metadata fidelity over every validation target"
    none (driverValidate false) .done ]

def validateMiniSuite : List TestSeq := [
  .individualIO
    "truthmines-validate-mini: 8-phase metadata fidelity over the mini tier"
    none (driverValidate true) .done ]

def miniSuite : List TestSeq := [
  .individualIO
    "truthmines-mini: fixtures + spine + Mathlib + FLT → .ixc directory"
    none (driverBuild true "truthmines-mini.ixc"
      catalogMiniSpec.libs.size) .done,
  .individualIO "truthmines-mini: per-piece kernel check sweep"
    none (driverCheck true) .done ]

end Tests.Ix.TruthMines
