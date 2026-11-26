module

public import LSpec
public import Benchmarks.TruthMinesSpec.Projection
public import Ix.Cli.CatalogCmd

/-!
  The TruthMines corpus tiers over the piece pipeline: drive
  `truthmines build` (per-member `ix compile` straight
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
  * `truthmines-check` — `truthmines check`: `ix check-lean --anon` over
    every member piece in the `.ixc`, one subprocess per piece (the
    fat-profile rung-1 checking story: embarrassingly parallel, peak =
    max member).
  * `truthmines-mini` — the small infrastructure tier end to end
    (fixtures + spine + Mathlib + FLT → `truthmines-mini.ixc/`), then
    the per-piece check sweep over its members.

  The build runs one member compile at a time (~20 GiB peak). Needs
  `lake build ix truthmines` first; network + `lake exe cache get` on
  the first workspace build. Run
  `lake test -- --ignored truthmines-mini` (or `truthmines
  truthmines-check` for the full corpus).
-/

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
    (expectMembers : Nat) : AssertM Unit := do
  unless (← ixExe.pathExists) do
    fail s!"{ixExe} missing — run `lake build ix` first"
  unless (← driverExe.pathExists) do
    fail s!"{driverExe} missing — run `lake build truthmines` first"
  let exe ← IO.FS.realPath driverExe
  let mut args := #["build", "--out", ixc.toString]
  if mini then
    args := args.push "--mini"
  let child ← IO.Process.spawn { cmd := exe.toString, args }
  let exit ← child.wait
  if exit != 0 then
    fail s!"truthmines build failed ({exit})"
  unless (← (ixc / "manifest").pathExists) do
    fail s!"driver exited 0 but {ixc} has no manifest"
  let labels ← expectOk ((← memberLabels ixc.toString).mapError (s!"manifest: {·}"))
  unless labels.length == expectMembers do
    fail s!"manifest carries {labels.length} members, the spec has {expectMembers}"
  -- Independent re-verify through the core (the driver already
  -- verified; this pins the suite's own read of the artifact).
  let verifyContent ← Ix.Cli.CatalogCmd.rsCatalogVerifyFFI ixc.toString false
  let union : Except String Nat := do
    let json ← Lean.Json.parse verifyContent
    (← json.getObjVal? "unionConsts").getNat?
  let n ← expectOk (union.mapError (s!"verify: {·}"))
  if n == 0 then
    fail "catalog verify reports an empty union"

/-- Drive `truthmines check [--mini]`: the per-piece `ix check-lean
    --anon` sweep over the tier's `.ixc` — the fat-profile checking
    rung lives in the driver (bounded pool, output captured per piece,
    tails + solo repro surfaced on rejection); the suite is exit-code
    gated. -/
private def driverCheck (mini : Bool) : AssertM Unit := do
  unless (← driverExe.pathExists) do
    fail s!"{driverExe} missing — run `lake build truthmines` first"
  let exe ← IO.FS.realPath driverExe
  let mut args := #["check"]
  if mini then
    args := args.push "--mini"
  let child ← IO.Process.spawn { cmd := exe.toString, args }
  let exit ← child.wait
  if exit != 0 then
    fail s!"truthmines check failed ({exit})"

def buildSuite : LSpec.Spec := do
  it "truthmines: full corpus pieces + self-contained .ixc via the driver"
    (driverBuild false "truthmines.ixc" catalogSpec.libs.size)

def checkSuite : LSpec.Spec := do
  it "truthmines: per-piece kernel check sweep (fat rung 1)"
    (driverCheck false)

def miniSuite : LSpec.Spec := do
  it "truthmines-mini: fixtures + spine + Mathlib + FLT → .ixc directory"
    (driverBuild true "truthmines-mini.ixc" catalogMiniSpec.libs.size)
  it "truthmines-mini: per-piece kernel check sweep"
    (driverCheck true)

end Tests.Ix.TruthMines
