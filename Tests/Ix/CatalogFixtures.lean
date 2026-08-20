/-
  Catalog conflict-corpus acceptance (plan C1–C4, `--ignored
  catalog-fixtures`): builds the `Benchmarks/Catalog` fixture workspace
  (the TruthMines RelocFixture{A,B} port — two packages exporting
  colliding `Collision.*` names, an identical-shape pair, near-twins,
  a declaration-kind matrix, and a cross-package dependency), catalogs
  it, and asserts:

  - C1 (audit): every owned constant's standalone anon address equals
    its qualified catalog address — qualification is metadata-only.
  - C2 (dedup matrix): the source-identical `Collision.Tree.map`
    dedups to one address under both qualified names; the deliberately
    different `Collision.Tree.size` / `Collision.tag` do not.
  - C3 (determinism): building and compiling twice reproduces the
    canonical root.
  - D6 (punch-through): `@[no_expose] Collision.concealedDefinition`
    lands as a transparent definition with its full body.
  - Owner-aware rewriting: `FixtureA.importedScore`'s relocated form
    references the qualified `FixtureB` constants (the unqualified
    source names do not exist in the catalog).
  - I4 (loader olean level): member envs come in at private level —
    imported theorems keep their proofs, `_private.*` constants are
    present, `@[no_expose]` definitions load transparent.

  Needs the fixture workspace buildable (network-free; toolchain
  shared), so it lives behind `--ignored`.
-/
module

public import LSpec
public import Ix.Catalog
public import Ix.CompileM
public import Ix.KernelCheck
public import Ix.Meta

public section

open LSpec

namespace Tests.Ix.CatalogFixtures

private def fixtureDir : System.FilePath := "Benchmarks" / "Catalog"

private def spec : Ix.Catalog.CatalogSpec := {
  catalogPrefix := `RelocCat
  libs := #[
    { qualifier := `B, roots := #[`FixtureB] },
    { qualifier := `A, roots := #[`FixtureA] } ] }

private def qual (x : Lean.Name) (n : Lean.Name) : Lean.Name :=
  (`RelocCat ++ x) ++ n

/-- Anon address of `n` in a compiled catalog env. -/
private def addrOf? (env : Ixon.Env) (n : Lean.Name) : Option Address :=
  let (ixName, _) := (Ix.CanonM.canonName n).run {}
  env.named.get? ixName |>.map (·.addr)

private def fixturesTest : IO (Bool × Nat × Nat × Option String) := do
  -- Build the fixture workspace (idempotent, no network).
  let build ← IO.Process.output {
    cmd := "lake", args := #["build", "FixtureA", "FixtureB"]
    cwd := some fixtureDir }
  if build.exitCode != 0 then
    return (false, 0, 0, some s!"fixture workspace build failed: \
{build.stderr.take 400}")
  initLeanSearchPath (some fixtureDir)
  -- Build the catalog and run the C1 audit.
  let result ← Ix.Catalog.buildCatalog spec
  let audit ← Ix.Catalog.auditCatalog spec result.consts
  unless audit.violations.isEmpty do
    return (false, 0, 0, some s!"audit violations \
({audit.violations.size}): {audit.violations[0]!}")
  unless audit.checked > 0 do
    return (false, 0, 0, some "audit checked nothing")
  -- C2 dedup matrix over one compiled catalog env.
  let catEnv ← Ix.CompileM.rsCompileEnvOf result.consts.toList
  let addrA_map := addrOf? catEnv (qual `A `Collision.Tree.map)
  let addrB_map := addrOf? catEnv (qual `B `Collision.Tree.map)
  let addrA_size := addrOf? catEnv (qual `A `Collision.Tree.size)
  let addrB_size := addrOf? catEnv (qual `B `Collision.Tree.size)
  let addrA_tag := addrOf? catEnv (qual `A `Collision.tag)
  let addrB_tag := addrOf? catEnv (qual `B `Collision.tag)
  let names : Std.HashSet Lean.Name :=
    result.consts.foldl (fun s (n, _) => s.insert n) {}
  -- D6: the no_expose definition carries its full body.
  let concealedTransparent :=
    match names.contains (qual `A `Collision.concealedDefinition),
      result.consts.find? (·.1 == qual `A `Collision.concealedDefinition) with
    | true, some (_, .defnInfo _) => true
    | _, _ => false
  let checks : List (String × Bool) := [
    ("audit checked the owned constants", audit.checked > 0),
    ("identical Tree.map dedups across A and B",
      addrA_map.isSome && addrA_map == addrB_map),
    ("near-twin Tree.size does not dedup",
      addrA_size.isSome && addrB_size.isSome && addrA_size != addrB_size),
    ("differing tag does not dedup",
      addrA_tag.isSome && addrB_tag.isSome && addrA_tag != addrB_tag),
    ("mutual Rose/Grove present qualified",
      names.contains (qual `A `Collision.Rose)
        && names.contains (qual `B `Collision.Grove)),
    ("regenerated recursor present qualified",
      names.contains (qual `A `Collision.Tree.rec)),
    ("axiom present qualified", names.contains (qual `B `Collision.seed)),
    ("opaque present qualified", names.contains (qual `A `Collision.hidden)),
    ("cross-package ref target present",
      names.contains (qual `B `FixtureB.Token)),
    ("cross-package user present",
      names.contains (qual `A `FixtureA.importedScore)),
    ("no unqualified Collision leaks", !names.contains `Collision.Tree),
    ("no unqualified FixtureB leaks", !names.contains `FixtureB.Token),
    ("no_expose body punched through (defn, not axiom)",
      concealedTransparent) ]
  match checks.find? (!·.2) with
  | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
  | none => return (true, audit.checked, result.consts.size, none)

/-- I4 gate: the catalog loader must import at `OLeanLevel.private`.
    An exported-level member env (what module-mode header processing
    yields) carries imported public theorems as body-less axioms and
    omits `_private.*` constants — the catalog then axiomizes proofs,
    kernel replay accepts vacuously, and `--audit` compares two
    identically-axiomized legs (#572). Only the loaded env itself can
    witness the regression, so assert on member `A`'s env from
    `resolveLibs` (module-mode fixtures: `@[no_expose]`, theorems, a
    cross-package import). Relies on `fixturesTest` having built the
    fixture workspace. -/
private def loaderLevelTest : IO (Bool × Nat × Nat × Option String) := do
  initLeanSearchPath (some fixtureDir)
  let (libEnvs, _, _) ← Ix.Catalog.resolveLibs spec
  let some envA := libEnvs[1]?
    | return (false, 0, 0, some "resolveLibs produced no env for member `A`")
  -- Imported toolchain theorem: a real proof whose references all
  -- resolve in the same env (at exported level it is a body-less axiom).
  match envA.constants.find? `Nat.add_comm with
  | some (.thmInfo v) =>
    for r in v.value.getUsedConstants do
      unless envA.contains r do
        return (false, 0, 0,
          some s!"Nat.add_comm proof ref {r} dangling — env not closed")
  | some _ => return (false, 0, 0,
      some "Nat.add_comm is not a theorem — exported-level trim suspected")
  | none => return (false, 0, 0, some "Nat.add_comm missing from member env")
  -- The member's own module-mode theorem keeps its proof.
  match envA.constants.find? `FixtureA.importedScore_eq with
  | some (.thmInfo _) => pure ()
  | some _ => return (false, 0, 0,
      some "FixtureA.importedScore_eq is not a theorem")
  | none => return (false, 0, 0,
      some "FixtureA.importedScore_eq missing from member env")
  -- `@[no_expose]` loads as a transparent definition (D6 at the loader).
  match envA.constants.find? `Collision.concealedDefinition with
  | some (.defnInfo _) => pure ()
  | some _ => return (false, 0, 0,
      some "no_expose Collision.concealedDefinition did not load as a defn")
  | none => return (false, 0, 0,
      some "Collision.concealedDefinition missing from member env")
  -- Non-exported `_private.*` constants from imports are present.
  let privCount := envA.constants.toList.countP
    fun (n, _) => (`_private).isPrefixOf n
  if privCount == 0 then
    return (false, 0, 0,
      some "no `_private.*` constants — exported-level trim suspected")
  return (true, privCount, envA.constants.toList.length, none)

/-- C3: two independent build+compile passes agree on the canonical
    root. -/
private def determinismTest : IO (Bool × Nat × Nat × Option String) := do
  initLeanSearchPath (some fixtureDir)
  let dir ← IO.FS.createTempDir
  try
    let r1 ← Ix.Catalog.buildCatalog spec
    let s1 ← Ix.CompileM.rsCompileEnvBytesFFI r1.consts.toList
      (dir / "c1.ixe").toString false
    let r2 ← Ix.Catalog.buildCatalog spec
    let s2 ← Ix.CompileM.rsCompileEnvBytesFFI r2.consts.toList
      (dir / "c2.ixe").toString false
    if s1.ungrounded.size > 0 then
      return (false, 0, 0, some s!"ungrounded: {s1.ungrounded}")
    if s1.root != s2.root then
      return (false, 0, 0, some s!"root drift: {s1.root.take 12}… vs \
{s2.root.take 12}…")
    if s1.bytes != s2.bytes then
      return (false, 0, 0, some "byte-size drift between runs")
    -- C4: the Rust kernel accepts every named constant of the catalog
    -- artifact.
    let ixePath := (dir / "c1.ixe").toString
    let names ← Ix.KernelCheck.rsIxonNamesFFI ixePath
    let expectPass := Array.replicate names.size true
    let results ← Ix.KernelCheck.rsCheckIxonFFI ixePath names expectPass true ""
    let mut rejected := 0
    for r in results do
      if r.isSome then rejected := rejected + 1
    if rejected > 0 then
      return (false, 0, 0,
        some s!"kernel check rejected {rejected}/{names.size} constants")
    return (true, s1.bytes.toNat, names.size, none)
  finally
    IO.FS.removeDirAll dir

def suite : List TestSeq := [
  .individualIO "catalog fixtures: audit + dedup matrix (C1/C2)" none
    fixturesTest .done,
  .individualIO "catalog fixtures: loader imports at private level (I4)"
    none loaderLevelTest .done,
  .individualIO
    "catalog fixtures: deterministic root + kernel check (C3/C4)"
    none determinismTest .done ]

end Tests.Ix.CatalogFixtures
