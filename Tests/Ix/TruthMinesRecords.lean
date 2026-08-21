/-
  Fast coherence gate for the typed TruthMines corpus records
  (`Benchmarks.TruthMinesSpec`) — runs in the default `lake test` sweep:

  * catalog validation is clean (the `run_cmd` gate enforces this at
    elaboration; re-asserting here reports the errors instead of a build
    failure when records are edited);
  * one toolchain by construction: the derived `expectedToolchain` equals
    the repo's `lean-toolchain` and the generated workspace's copy;
  * the generated workspace files are byte-identical to their projections
    (`lake exe truthmines gen --check` as a test);
  * Lake's lockfile pins every admitted git record at exactly the recorded
    revision, carries the two local fixtures at their ported paths, and
    names no direct git package outside the admitted set (inherited
    transitive entries are exempt);
  * the rendered `--spec` JSON round-trips through
    `Ix.Catalog.specFromJson` member-for-member — the driver and
    `ix catalog` agree on the interchange format.
-/
module

public import LSpec
public import Ix.Catalog
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
  if repo != expectedToolchain then
    return check false
      s!"repo lean-toolchain `{repo}` != derived `{expectedToolchain}`"
  if workspace != expectedToolchain then
    return check false
      s!"workspace lean-toolchain `{workspace}` != derived `{expectedToolchain}`"
  return check true ""

private def projectionTest : IO (Bool × Nat × Nat × Option String) := do
  let expected := [
    (workspaceLakefilePath, renderWorkspaceLakefile),
    (workspaceToolchainPath, renderWorkspaceToolchain)]
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

private def specParseTest : IO (Bool × Nat × Nat × Option String) := do
  match Lean.Json.parse renderSpecJson with
  | .error error => return check false s!"rendered spec is not JSON: {error}"
  | .ok json =>
    match _root_.Ix.Catalog.specFromJson json with
    | .error error => return check false s!"ix rejects the rendered spec: {error}"
    | .ok parsed =>
      if parsed.catalogPrefix != catalogSpec.catalogPrefix then
        return check false s!"prefix drift: {parsed.catalogPrefix}"
      if parsed.libs.size != catalogSpec.libs.size then
        return check false
          s!"member count drift: {parsed.libs.size} != {catalogSpec.libs.size}"
      for (theirs, ours) in parsed.libs.zip catalogSpec.libs do
        unless theirs.qualifier == ours.qualifier && theirs.roots == ours.roots do
          return check false s!"member drift at `{ours.qualifier}`"
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
  .individualIO "truthmines records: spec JSON round-trips through ix's parser"
    none specParseTest .done ]

end Tests.Ix.TruthMinesRecords
