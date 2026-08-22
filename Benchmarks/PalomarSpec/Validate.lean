module

public import Benchmarks.PalomarSpec.Catalog
meta import Benchmarks.PalomarSpec.Catalog
public meta import Lean.Elab.Command

@[expose] public section

namespace PalomarSpec

def isHexDigit (char : Char) : Bool :=
  char.isDigit || ('a' ≤ char && char ≤ 'f') || ('A' ≤ char && char ≤ 'F')

def isFullGitRevision (revision : String) : Bool :=
  revision.length == 40 && revision.toList.all isHexDigit

def isSimpleQualifier : Lean.Name → Bool
  | .str .anonymous component => !component.isEmpty &&
      !component.contains '\n' && !component.contains '\r' &&
      !component.contains '/' && !component.contains '»'
  | _ => false

def duplicateValues [BEq α] [Inhabited α] (values : Array α) : Array α := Id.run do
  let mut duplicates := #[]
  for i in [0:values.size] do
    for j in [i + 1:values.size] do
      if values[i]! == values[j]! && !duplicates.contains values[i]! then
        duplicates := duplicates.push values[i]!
  return duplicates

def catalogValidationErrors (entries : Array Entry := catalog) : Array String := Id.run do
  let mut errors := #[]
  unless entries.size == 19 do
    errors := errors.push s!"expected the 19 current registry projects, found {entries.size}"
  if catalogRevision.isEmpty then
    errors := errors.push "catalog revision is empty"
  for duplicate in duplicateValues (entries.map (·.registryId)) do
    errors := errors.push s!"duplicate registry id `{duplicate}`"
  for duplicate in duplicateValues (entries.map (·.qualifier)) do
    errors := errors.push s!"duplicate qualifier `{duplicate}`"
  for entry in entries do
    unless entry.registryId.startsWith "PALOMAR-" do
      errors := errors.push s!"{entry.title}: malformed registry id `{entry.registryId}`"
    if entry.version == 0 then
      errors := errors.push s!"{entry.title}: registry version must be positive"
    unless isSimpleQualifier entry.qualifier do
      errors := errors.push s!"{entry.title}: qualifier `{entry.qualifier}` is not simple"
    if entry.title.isEmpty || entry.packageName.isEmpty then
      errors := errors.push s!"{entry.registryId}: empty title or package name"
    unless entry.registryPath.startsWith "entries/PALOMAR-" &&
        entry.registryPath.endsWith s!"-v{entry.version}.json" do
      errors := errors.push s!"{entry.title}: malformed registry path"
    if entry.source.url.isEmpty || !isFullGitRevision entry.source.rev then
      errors := errors.push s!"{entry.title}: source is not an immutable full Git revision"
    if entry.source.subdir?.any (fun path =>
        path.isEmpty || path.startsWith "/" || path.contains "..") then
      errors := errors.push s!"{entry.title}: unsafe source subdirectory"
    unless entry.upstreamToolchain.startsWith "leanprover/lean4:v4." do
      errors := errors.push s!"{entry.title}: malformed upstream toolchain"
    if entry.license.isEmpty then
      errors := errors.push s!"{entry.title}: missing license"
    if entry.solutionModule == .anonymous || entry.formalizationPath.isEmpty then
      errors := errors.push s!"{entry.title}: missing verified solution root"
    if entry.directDependencies.isEmpty then
      errors := errors.push s!"{entry.title}: no recorded direct dependencies"
    for duplicate in duplicateValues entry.directDependencies do
      errors := errors.push s!"{entry.title}: repeats dependency `{duplicate}`"
  return errors

def validateCatalog (entries : Array Entry := catalog) : Except String Unit :=
  match catalogValidationErrors entries with
  | #[] => .ok ()
  | errors => .error (String.intercalate "\n" errors.toList)

run_cmd do
  match validateCatalog with
  | .ok () => pure ()
  | .error errors => Lean.throwError m!"invalid Palomar catalog:\n{errors}"

end PalomarSpec
