/-
  Fast coherence gate for the typed TruthMines corpus records
  (`Benchmarks.TruthMinesSpec`) — runs in the default `lake test` sweep:

  * catalog validation is clean (the `run_cmd` gate enforces this at
    elaboration; re-asserting here reports the errors instead of a build
    failure when records are edited);
  * one toolchain by construction: the derived `expectedToolchain` equals
    the repo's `lean-toolchain` and both nested workspaces' copies;
  * every generated workspace and per-library compile-driver file is
    byte-identical to its projection (`lake exe truthmines gen --check`
    as a test);
  * Lake's lockfile pins every admitted git record at exactly the recorded
    revision, carries the two local fixtures at their ported paths, and
    names no direct git package outside the workspace pin set (inherited
    transitive entries are exempt);
  * the positional `Qualifier=Root[,Root…]` member vector — the exact
    argv the driver hands `ix catalog`; no spec file, no JSON — is
    well-formed entry-for-entry for both tiers.
-/
module

public import LSpec
public import Benchmarks.TruthMinesSpec.Projection

public section

open LSpec
open TruthMinesSpec

namespace Tests.Ix.TruthMinesRecords

private def check (ok : Bool) (message : String) :
    Bool × Nat × Nat × Option String :=
  (ok, 0, 0, if ok then none else some message)

private def validationTest : IO (Bool × Nat × Nat × Option String) := do
  let errors := catalogValidationErrors
  return check errors.isEmpty
    s!"catalog validation errors:\n{String.intercalate "\n" errors.toList}"

private def toolchainTest : IO (Bool × Nat × Nat × Option String) := do
  let repo := (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  let workspace := (← IO.FS.readFile workspaceToolchainPath).trimAscii.toString
  let compileWorkspace :=
    (← IO.FS.readFile compileWorkspaceToolchainPath).trimAscii.toString
  if repo != expectedToolchain then
    return check false
      s!"repo lean-toolchain `{repo}` != derived `{expectedToolchain}`"
  if workspace != expectedToolchain then
    return check false
      s!"workspace lean-toolchain `{workspace}` != derived `{expectedToolchain}`"
  if compileWorkspace != expectedToolchain then
    return check false
      s!"compile workspace lean-toolchain `{compileWorkspace}` != derived `{expectedToolchain}`"
  return check true ""

private def projectionTest : IO (Bool × Nat × Nat × Option String) := do
  let mut expected := [
    (workspaceLakefilePath, renderWorkspaceLakefile),
    (workspaceToolchainPath, renderWorkspaceToolchain),
    (compileWorkspaceLakefilePath, renderCompileWorkspaceLakefile),
    (compileWorkspaceToolchainPath, renderWorkspaceToolchain),
    (compilePalomarModulePath, renderCompilePalomarModule)]
  for lib in driverLibs do
    expected := expected ++ [
      (driverModulePath lib.qualifier, renderDriverModule lib),
      (compileMemberModulePath lib.qualifier, renderCompileMemberModule lib)]
  for (path, content) in expected do
    unless (← path.pathExists) do
      return check false s!"{path} missing — run `lake exe truthmines gen`"
    unless (← IO.FS.readFile path) == content do
      return check false s!"{path} is stale — run `lake exe truthmines gen`"
  return check true ""

/-- Lake stores non-identifier package names guillemet-quoted in the
lockfile (`«lean-grpc»`); the records carry them bare. -/
private def stripGuillemets (name : String) : String :=
  if name.startsWith "«" && name.endsWith "»" then
    name.drop 1 |>.dropEnd 1 |>.toString
  else name

/-- Walk Lake's lockfile and cross-check it against the records: every
admitted git pin present at the recorded revision, both local fixtures at
their ported paths, no direct git entry outside the admitted set. -/
private def manifestErrors (content : String) : Except String (Array String) := do
  let json ← Lean.Json.parse content
  let packages ← (← json.getObjVal? "packages").getArr?
  let mut entries : Array (String × String × String × Bool) := #[]
  let mut fixtureDirs : Array (String × String) := #[]
  for package in packages do
    let name := stripGuillemets <| ← (← package.getObjVal? "name").getStr?
    let type ← (← package.getObjVal? "type").getStr?
    if type == "path" then
      fixtureDirs := fixtureDirs.push (name, ← (← package.getObjVal? "dir").getStr?)
    else
      let rev ← (← package.getObjVal? "rev").getStr?
      let inherited ← (← package.getObjVal? "inherited").getBool?
      entries := entries.push (name, type, rev, inherited)
  let mut errors := #[]
  for (name, rev) in recordPins do
    match entries.find? (·.1 == name) with
    | none => errors := errors.push s!"admitted package `{name}` missing from the lockfile"
    | some (_, _, lockRev, _) =>
      unless lockRev == rev do
        errors := errors.push
          s!"lockfile pins `{name}` at {lockRev}, records say {rev}"
  for (name, _, _, inherited) in entries do
    unless inherited || (recordPins.any (·.1 == name)) do
      errors := errors.push
        s!"lockfile carries direct git package `{name}` outside the admitted records"
  for (fixture, dir) in [("relocFixtureA", "../Catalog/RelocFixtureA"),
      ("relocFixtureB", "../Catalog/RelocFixtureB")] do
    match fixtureDirs.find? (·.1 == fixture) with
    | none => errors := errors.push s!"lockfile is missing local fixture `{fixture}`"
    | some (_, lockDir) =>
      unless lockDir == dir do
        errors := errors.push
          s!"lockfile places `{fixture}` at `{lockDir}`, expected `{dir}`"
  return errors

private def manifestTest : IO (Bool × Nat × Nat × Option String) := do
  let content ← IO.FS.readFile workspaceManifestPath
  match manifestErrors content with
  | .error error => return check false s!"lockfile walk failed: {error}"
  | .ok errors =>
    return check errors.isEmpty
      s!"lockfile/record drift:\n{String.intercalate "\n" errors.toList}"

/-- The independent fidelity workspace shares the canonical package store and
    adds exactly one authored source pin: the aggregate Palomar.ix library. -/
private def compileManifestErrors (content : String) : Except String (Array String) := do
  let json ← Lean.Json.parse content
  let packagesDir ← (← json.getObjVal? "packagesDir").getStr?
  let packages ← (← json.getObjVal? "packages").getArr?
  let mut errors := #[]
  unless packagesDir == "../../TruthMines/.lake/packages" do
    errors := errors.push
      s!"compile lockfile packagesDir is `{packagesDir}`"
  let mut foundPalomar := false
  let mut foundTruthMines := false
  for package in packages do
    let name := stripGuillemets <| ← (← package.getObjVal? "name").getStr?
    if name == "palomar_ix" then
      foundPalomar := true
      let url ← (← package.getObjVal? "url").getStr?
      let rev ← (← package.getObjVal? "rev").getStr?
      let inherited ← (← package.getObjVal? "inherited").getBool?
      unless url == palomarRepoUrl && rev == palomarRev && !inherited do
        errors := errors.push
          s!"compile lockfile Palomar pin is `{url}@{rev}` (inherited={inherited})"
    if name == "truthmines" then
      foundTruthMines := true
      let type ← (← package.getObjVal? "type").getStr?
      let dir ← (← package.getObjVal? "dir").getStr?
      unless type == "path" && dir == "../../TruthMines" do
        errors := errors.push
          s!"compile lockfile TruthMines source is `{type}:{dir}`"
  unless foundPalomar do
    errors := errors.push "compile lockfile is missing direct Palomar.ix pin"
  unless foundTruthMines do
    errors := errors.push "compile lockfile is missing canonical TruthMines path"
  return errors

private def compileManifestTest : IO (Bool × Nat × Nat × Option String) := do
  let content ← IO.FS.readFile compileWorkspaceManifestPath
  match compileManifestErrors content with
  | .error error => return check false s!"compile lockfile walk failed: {error}"
  | .ok errors =>
    return check errors.isEmpty
      s!"compile lockfile drift:\n{String.intercalate "\n" errors.toList}"

/-- The positional member vector is what `ix catalog` receives: one
`Qualifier=Root[,Root…]` entry per member, parseable by the same
splitting the CLI does (`=` once, roots comma-joined, no whitespace or
empty components anywhere). -/
private def specArgvTest : IO (Bool × Nat × Nat × Option String) := do
  for (label, spec) in [("full", catalogSpec), ("mini", catalogMiniSpec)] do
    let rendered := commandArguments spec
    if rendered.size != spec.libs.size then
      return check false
        s!"{label}: {rendered.size} argv entries for {spec.libs.size} members"
    for (entry, lib) in rendered.zip spec.libs do
      let parts := entry.splitOn "="
      match parts with
      | [qualifier, roots] =>
        if qualifier.isEmpty || qualifier != lib.qualifier.toString (escape := false) then
          return check false s!"{label}: qualifier drift in `{entry}`"
        let rootParts := roots.splitOn ","
        if rootParts.length != lib.roots.size ||
            rootParts.any (·.isEmpty) then
          return check false s!"{label}: root list drift in `{entry}`"
        if entry.any (fun c => c == ' ' || c == '\n') then
          return check false s!"{label}: whitespace in argv entry `{entry}`"
      | _ =>
        return check false s!"{label}: entry `{entry}` is not `Qualifier=Roots`"
  return check true ""

def suite : List TestSeq := [
  .individualIO "truthmines records: catalog validation clean"
    none validationTest .done,
  .individualIO "truthmines records: one toolchain by construction"
    none toolchainTest .done,
  .individualIO "truthmines records: workspace projections byte-identical"
    none projectionTest .done,
  .individualIO "truthmines records: lockfile pins match the records"
    none manifestTest .done,
  .individualIO "truthmines records: compile workspace pins are coherent"
    none compileManifestTest .done,
  .individualIO "truthmines records: positional spec argv is well-formed"
    none specArgvTest .done ]

end Tests.Ix.TruthMinesRecords
