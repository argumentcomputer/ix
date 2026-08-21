module

public import Benchmarks.TruthMinesSpec.Catalog
public import Benchmarks.TruthMinesSpec.Spec
meta import Benchmarks.TruthMinesSpec.Catalog
meta import Benchmarks.TruthMinesSpec.Spec
public meta import Lean.Elab.Command

@[expose] public section

namespace TruthMinesSpec

def isHexDigit (char : Char) : Bool :=
  char.isDigit || ('a' ≤ char && char ≤ 'f') || ('A' ≤ char && char ≤ 'F')

def isFullGitRevision (revision : String) : Bool :=
  revision.length == 40 && revision.toList.all isHexDigit

def isSimpleQualifier : Lean.Name → Bool
  | .str .anonymous component => !component.isEmpty &&
      !component.contains '\n' && !component.contains '\r' &&
      !component.contains '»' && !component.contains '/' &&
      !component.toList.contains (Char.ofNat 0)
  | _ => false

def isRepresentableName : Lean.Name → Bool
  | .anonymous => false
  | .str pre component =>
      (pre == .anonymous || isRepresentableName pre) &&
      !component.isEmpty && !component.contains '\n' &&
      !component.contains '\r' && !component.contains '»' &&
      !component.contains '/' && !component.toList.contains (Char.ofNat 0)
  | .num pre _ => pre != .anonymous && isRepresentableName pre

def isSafeCatalogString (value : String) : Bool :=
  !value.toList.contains (Char.ofNat 0)

def duplicateValues [BEq α] [Inhabited α] (values : Array α) : Array α := Id.run do
  let mut duplicates := #[]
  for i in [0:values.size] do
    for j in [i + 1:values.size] do
      if values[i]! == values[j]! && !duplicates.contains values[i]! then
        duplicates := duplicates.push values[i]!
  return duplicates

/-- Stable package dependency order for regeneration. Catalog order never
substitutes for the declared dependency graph; lexicographic tie-breaking
makes projections deterministic. Validation checks the frozen spec order
directly (providers before consumers); this is the generator's ordering. -/
def topologicalCatalog (specs : Array PackageSpec) : Except String (Array PackageSpec) := Id.run do
  let mut remaining := specs
  let mut ordered : Array PackageSpec := #[]
  while !remaining.isEmpty do
    let mut ready := remaining.filter fun spec =>
      spec.directDeps.all fun dependency =>
        !specs.any (·.lakeName == dependency) ||
          ordered.any (·.lakeName == dependency)
    ready := ready.qsort (·.lakeName < ·.lakeName)
    if ready.isEmpty then
      let names := remaining.map (·.lakeName)
      return .error s!"catalog dependency cycle involving {names}"
    for spec in ready do
      ordered := ordered.push spec
    remaining := remaining.filter fun spec =>
      !ready.any (·.lakeName == spec.lakeName)
  return .ok ordered

/-- A catalog record is admitted exactly when the frozen admission spec
carries its qualifier. -/
def PackageSpec.isAdmitted (spec : PackageSpec)
    (admission : CatalogSpecProjection := catalogSpec) : Bool :=
  admission.libs.any (·.qualifier == spec.qualifier)

/-- Admitted records in admission-spec (dependency) order — the order every
projection uses. -/
def admittedInSpecOrder
    (specs : Array PackageSpec := catalog)
    (admission : CatalogSpecProjection := catalogSpec) : Array PackageSpec :=
  admission.libs.filterMap fun lib =>
    specs.find? (·.qualifier == lib.qualifier)

def catalogValidationErrors
    (specs : Array PackageSpec := catalog)
    (admission : CatalogSpecProjection := catalogSpec)
    (revision : String := catalogRevision) : Array String := Id.run do
  let mut errors := #[]

  if revision.isEmpty then
    errors := errors.push "catalog revision is empty"

  for duplicate in duplicateValues (specs.map (·.lakeName)) do
    errors := errors.push s!"duplicate Lake package name `{duplicate}`"
  for duplicate in duplicateValues (specs.map (·.qualifier)) do
    errors := errors.push s!"duplicate qualifier `{duplicate}`"

  for spec in specs do
    unless isSimpleQualifier spec.qualifier do
      errors := errors.push s!"qualifier `{spec.qualifier}` must be one name component"
    if spec.qualifier == `Internal then
      errors := errors.push "qualifier `Internal` is reserved"
    if spec.lakeName.isEmpty then
      errors := errors.push "a package has an empty Lake name"
    unless isSafeCatalogString spec.lakeName do
      errors := errors.push s!"package `{spec.lakeName}` has an unsafe Lake name"
    if spec.lakeName.contains '\n' || spec.lakeName.contains '\r' ||
        spec.lakeName.contains '»' then
      errors := errors.push s!"package `{spec.lakeName}` cannot be represented as a Lake identifier"
    unless isSafeCatalogString spec.upstreamToolchain do
      errors := errors.push s!"package `{spec.lakeName}` has an unsafe toolchain string"
    if spec.upstreamToolchain.isEmpty then
      errors := errors.push s!"package `{spec.lakeName}` has an empty upstream toolchain"
    if !spec.upstreamToolchain.isEmpty &&
        spec.upstreamToolchain != expectedToolchain then
      errors := errors.push
        s!"package `{spec.lakeName}` targets toolchain `{spec.upstreamToolchain}`, \
but the corpus is built on `{expectedToolchain}` (ix's toolchain)"
    unless isSafeCatalogString spec.license && isSafeCatalogString spec.lastCommit &&
        isSafeCatalogString spec.notes do
      errors := errors.push s!"package `{spec.lakeName}` has an unsafe textual field"
    if spec.lastCommit.isEmpty then
      errors := errors.push s!"package `{spec.lakeName}` has an empty last-commit field"
    for rootModule in spec.rootModules do
      unless isRepresentableName rootModule do
        errors := errors.push
          s!"package `{spec.lakeName}` has unrepresentable root module `{rootModule}`"
    for moduleName in spec.moduleIncludes ++ spec.moduleExcludes do
      unless isRepresentableName moduleName do
        errors := errors.push
          s!"package `{spec.lakeName}` has unrepresentable module override `{moduleName}`"
    for duplicate in duplicateValues spec.rootModules do
      errors := errors.push s!"package `{spec.lakeName}` repeats root module `{duplicate}`"
    for duplicate in duplicateValues spec.moduleIncludes do
      errors := errors.push s!"package `{spec.lakeName}` repeats module include `{duplicate}`"
    for duplicate in duplicateValues spec.moduleExcludes do
      errors := errors.push s!"package `{spec.lakeName}` repeats module exclude `{duplicate}`"
    for moduleName in spec.moduleIncludes do
      if spec.moduleExcludes.contains moduleName then
        errors := errors.push
          s!"package `{spec.lakeName}` both includes and excludes module `{moduleName}`"
    if (!spec.moduleIncludes.isEmpty || !spec.moduleExcludes.isEmpty) &&
        spec.notes.isEmpty then
        errors := errors.push
          s!"package `{spec.lakeName}` uses module overrides without explanatory notes"
    for duplicate in duplicateValues spec.directDeps do
      errors := errors.push s!"package `{spec.lakeName}` repeats dependency `{duplicate}`"
    for dependency in spec.directDeps do
      if dependency == spec.lakeName then
        errors := errors.push s!"package `{spec.lakeName}` depends on itself"
      unless specs.any (·.lakeName == dependency) do
        errors := errors.push
          s!"package `{spec.lakeName}` names unknown catalog dependency `{dependency}`"
    match spec.source with
    | .local path =>
      if path.isEmpty then
        errors := errors.push s!"package `{spec.lakeName}` has an empty local source path"
      unless isSafeCatalogString path do
        errors := errors.push s!"package `{spec.lakeName}` has an unsafe local source path"
    | .git source =>
      if source.url.isEmpty then
        errors := errors.push s!"package `{spec.lakeName}` has an empty Git URL"
      unless isSafeCatalogString source.url && isSafeCatalogString source.rev do
        errors := errors.push s!"package `{spec.lakeName}` has an unsafe Git source"
      unless isFullGitRevision source.rev do
        errors := errors.push
          s!"package `{spec.lakeName}` Git revision is not a full 40-hex commit"
      if source.subdir?.any (·.isEmpty) then
        errors := errors.push s!"package `{spec.lakeName}` has an empty Git subdirectory"
      if source.subdir?.any (fun path => !isSafeCatalogString path) then
        errors := errors.push s!"package `{spec.lakeName}` has an unsafe Git subdirectory"
    match spec.disposition with
    | .candidate =>
      unless spec.hermetic do
        errors := errors.push s!"candidate `{spec.lakeName}` is not hermetic"
      if spec.license.isEmpty then
        errors := errors.push s!"candidate `{spec.lakeName}` has no license"
      if spec.rootModules.isEmpty then
        errors := errors.push s!"candidate `{spec.lakeName}` has no root modules"
    | .excluded reason =>
      if reason.isEmpty then
        errors := errors.push s!"excluded package `{spec.lakeName}` has no reason"

  /- Admission-spec coherence: membership in the frozen spec is admission, so
  the spec must resolve into the catalog, admit only candidates, and list
  providers before consumers (`ix catalog` streams members in this order and
  fails closed on a misordering — catch it at elaboration instead). -/
  for duplicate in duplicateValues (admission.libs.map (·.qualifier)) do
    errors := errors.push s!"admission spec repeats qualifier `{duplicate}`"
  let mut seen : Array String := #[]
  for lib in admission.libs do
    if lib.roots.isEmpty then
      errors := errors.push s!"admission spec member `{lib.qualifier}` has no roots"
    for root in lib.roots do
      unless isRepresentableName root do
        errors := errors.push
          s!"admission spec member `{lib.qualifier}` has unrepresentable root `{root}`"
    for duplicate in duplicateValues lib.roots do
      errors := errors.push
        s!"admission spec member `{lib.qualifier}` repeats root `{duplicate}`"
    match specs.find? (·.qualifier == lib.qualifier) with
    | none =>
      errors := errors.push
        s!"admission spec names unknown qualifier `{lib.qualifier}`"
    | some record =>
      unless record.isCandidate do
        errors := errors.push
          s!"admission spec admits excluded package `{record.lakeName}`"
      for dependency in record.directDeps do
        if let some depRecord := specs.find? (·.lakeName == dependency) then
          if depRecord.isAdmitted admission then
            unless seen.contains dependency do
              errors := errors.push
                s!"admission spec lists `{record.lakeName}` before its dependency `{dependency}`"
          else
            errors := errors.push
              s!"admitted package `{record.lakeName}` depends on non-admitted `{dependency}`"
      seen := seen.push record.lakeName

  return errors

def validateCatalog
    (specs : Array PackageSpec := catalog)
    (admission : CatalogSpecProjection := catalogSpec)
    (revision : String := catalogRevision) : Except String Unit :=
  match catalogValidationErrors specs admission revision with
  | #[] => .ok ()
  | errors => .error (String.intercalate "\n" errors.toList)

run_cmd do
  match validateCatalog with
  | .ok () => pure ()
  | .error errors => Lean.throwError m!"invalid TruthMines catalog:\n{errors}"

end TruthMinesSpec
