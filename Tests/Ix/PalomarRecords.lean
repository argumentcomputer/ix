/- Fast, network-free coherence gate for the separate Palomar registry
snapshot and its projection into isolated Lake workspaces. -/
module

public import LSpec
public import Benchmarks.PalomarSpec.Projection
public import Benchmarks.TruthMinesSpec.Projection

public section

open LSpec

namespace Tests.Ix.PalomarRecords

private def check (ok : Bool) (message : String) :
    Bool × Nat × Nat × Option String :=
  (ok, 0, 0, if ok then none else some message)

private def validationTest : IO (Bool × Nat × Nat × Option String) := do
  let errors := PalomarSpec.catalogValidationErrors
  return check errors.isEmpty
    s!"Palomar validation errors:\n{String.intercalate "\n" errors.toList}"

private def projectionTest : IO (Bool × Nat × Nat × Option String) := do
  for file in PalomarSpec.generatedFiles do
    unless ← file.path.pathExists do
      return check false s!"{file.path} missing — run `lake exe palomar gen`"
    unless (← IO.FS.readFile file.path) == file.content do
      return check false s!"{file.path} is stale — run `lake exe palomar gen`"
  return check true ""

private def isolationTest : IO (Bool × Nat × Nat × Option String) := do
  let paths := PalomarSpec.catalog.map PalomarSpec.entryWorkspaceDir
  if (PalomarSpec.duplicateValues paths).size != 0 then
    return check false "Palomar entries do not have distinct workspaces"
  let solutionCount := PalomarSpec.catalog.filter (·.solutionModule == `Solution) |>.size
  if solutionCount < 2 then
    return check false "isolation fixture disappeared: no repeated `Solution` roots"
  for entry in PalomarSpec.catalog do
    if TruthMinesSpec.driverLibs.any (·.qualifier == entry.qualifier) then
      return check false s!"{entry.qualifier} leaked into the shared Drivers library"
    if TruthMinesSpec.workspaceMembers.any (·.qualifier == entry.qualifier) then
      return check false s!"{entry.qualifier} leaked into the shared Lake workspace"
  return check true ""

private def truthMinesProjectionTest : IO (Bool × Nat × Nat × Option String) := do
  unless TruthMinesSpec.catalogSpec.libs.size == 97 &&
      TruthMinesSpec.catalogSpec.rootModules.size == 584 do
    return check false s!"TruthMines spec is \
{TruthMinesSpec.catalogSpec.libs.size} members / \
{TruthMinesSpec.catalogSpec.rootModules.size} roots, expected 97 / 584"
  for entry in PalomarSpec.catalog do
    let some record := TruthMinesSpec.catalogQualifier? entry.qualifier
      | return check false s!"{entry.qualifier} missing from TruthMines records"
    unless record.rootModules == #[entry.solutionModule] do
      return check false s!"{entry.qualifier}: TruthMines solution-root drift"
    unless TruthMinesSpec.catalogSpec.libs.any (·.qualifier == entry.qualifier) do
      return check false s!"{entry.qualifier} is not admitted to TruthMines"
    if TruthMinesSpec.catalogMiniSpec.libs.any (·.qualifier == entry.qualifier) then
      return check false s!"{entry.qualifier} unexpectedly entered the mini tier"
    match record.source with
    | .local _ => return check false s!"{entry.qualifier}: TruthMines source is local"
    | .git source =>
      unless source.url == entry.source.url && source.rev == entry.source.rev &&
          source.subdir? == entry.source.subdir? do
        return check false s!"{entry.qualifier}: TruthMines source-pin drift"
  return check true ""

private def toolchainTest : IO (Bool × Nat × Nat × Option String) := do
  let repo := (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  if PalomarSpec.renderToolchain.trimAscii.toString != repo then
    return check false "generated Palomar compatibility toolchain differs from ix"
  if PalomarSpec.expectedToolchain != TruthMinesSpec.expectedToolchain then
    return check false "Palomar and TruthMines compatibility toolchains differ"
  let some mathlib := TruthMinesSpec.catalogPackage? "mathlib"
    | return check false "TruthMines has no mathlib compatibility record"
  match mathlib.source with
  | .local _ => return check false "TruthMines mathlib source is local"
  | .git source =>
    unless source.url == PalomarSpec.compatibilityMathlibUrl &&
        source.rev == PalomarSpec.compatibilityMathlibRevision do
      return check false "Palomar and TruthMines Mathlib compatibility pins differ"
  unless PalomarSpec.catalog.any
      (·.upstreamToolchain != TruthMinesSpec.expectedToolchain) do
    return check false "upstream-toolchain provenance was flattened"
  return check true ""

def suite : List TestSeq := [
  .individualIO "palomar records: exactly 19 immutable current entries"
    none validationTest .done,
  .individualIO "palomar records: generated isolated workspaces byte-identical"
    none projectionTest .done,
  .individualIO "palomar records: repeated Solution roots remain isolated"
    none isolationTest .done,
  .individualIO "palomar records: all entries admitted to TruthMines"
    none truthMinesProjectionTest .done,
  .individualIO "palomar records: ix compatibility toolchain preserves provenance"
    none toolchainTest .done
]

end Tests.Ix.PalomarRecords
