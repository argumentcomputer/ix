/-
  Lake-side root closure for `ix catalog --close-roots` (the fix behind the
  I5 diagnostic; catalog-scale plan Item 5's follow-on, absorbed from
  TruthMines `TruthMinesBuild/Workspace.lean`).

  A provider's umbrella need not import every module a downstream member
  uses: the loader renames every module of a cataloged package it meets in
  any member's environment while replaying only the closures of declared
  roots, so a module reachable from some consumer and rooted by nobody would
  be renamed and never replayed (real-corpus case: TorchLean directly
  imports a ProofWidgets demo module the umbrella skips). `closeRoots`
  extends each member's module set to the global source-import fixed point —
  every cross-package source edge becomes coverage of its provider — and
  re-roots each member at its terminal modules. The I5 coverage gate in
  `buildCatalog` stays as the fail-closed backstop.

  Everything here is source-level Lake/header analysis; nothing imports a
  Lean environment. Lake remains the authority for module providers, and
  source headers (never filename guessing) the authority for import edges.
-/
module

public import Lake
public import Lake.Load.Workspace
public import Lean.Elab.Import
public import Ix.Catalog

public section

open Lean System

namespace Ix.Catalog

/-- One module in the global import closure seeded by member roots. -/
structure SourceModule where
  qualifier : Lean.Name
  library : Lean.Name
  moduleName : Lean.Name
  sourcePath : FilePath
  imports : Array Lean.Name
deriving Repr, BEq, Inhabited

/-- One member with its resolved Lake package and module inventory. -/
structure ResolvedMember where
  lib : LibSpec
  pkg : Lake.Package
  modules : Array SourceModule

def loadLakeEnvironment : IO Lake.Env := do
  let (elan?, lean?, lake?) ← Lake.findInstall?
  let some lean := lean?
    | throw <| IO.userError "cannot locate the active Lean installation"
  let some lake := lake?
    | throw <| IO.userError "cannot locate the active Lake installation"
  match ← (Lake.Env.compute lake lean elan?).toBaseIO with
  | .ok env => return env
  | .error error =>
    throw <| IO.userError s!"cannot construct Lake environment: {error}"

/-- Load the manifest-resolved workspace at `root` without updating or
    fetching dependencies (members must already be fetched — run the
    workspace's `lake build` first). -/
def loadCurrentWorkspace (root : FilePath := ".") : IO Lake.Workspace := do
  let root ← IO.FS.realPath root
  let config : Lake.LoadConfig := {
    lakeEnv := ← loadLakeEnvironment
    wsDir := root
    updateDeps := false
    updateToolchain := false
  }
  let some workspace ← (Lake.loadWorkspace config).toBaseIO {
      outLv := .warning
      failLv := .error
      ansiMode := .noAnsi }
    | throw <| IO.userError "Lake could not load the resolved catalog workspace"
  return workspace

/-- Direct imports from a source header — Lean's parser, never filename
    guessing. -/
def parseModuleImports (path : FilePath) : IO (Array Lean.Name) := do
  let source ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext source path.toString
  let (header, _, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors then
    let rendered ← messages.toList.mapM (·.toString)
    throw <| IO.userError <|
      s!"cannot parse imports from {path}:\n{String.intercalate "\n" rendered}"
  let importSpecs := Elab.HeaderSyntax.imports header
  return importSpecs.foldl (init := #[]) fun result importSpec =>
    if result.contains importSpec.module then result
    else result.push importSpec.module

/-- Modules the toolchain itself provides; imports of these resolve outside
    the workspace and stay unqualified. -/
def isBuiltinToolchainModule (moduleName : Lean.Name) : Bool :=
  #[`Init, `Lean, `Std, `Lake].any (·.isPrefixOf moduleName)

private def resolvePackageModule (pkg : Lake.Package) (moduleName : Lean.Name) :
    IO Lake.Module := do
  let mut found : Array Lake.Module := #[]
  for library in pkg.leanLibs do
    let candidate : Lake.Module := {lib := library, name := moduleName}
    if ← candidate.leanFile.pathExists then
      unless found.any (·.leanFile == candidate.leanFile) do
        found := found.push candidate
  if found.size != 1 then
    throw <| IO.userError <|
      s!"module `{moduleName}` for `{pkg.prettyName}` matched {found.size} \
distinct source files"
  let some moduleInfo := found[0]?
    | throw <| IO.userError s!"module `{moduleName}` disappeared"
  return moduleInfo

/-- The one Lake package providing every root of `lib`. -/
private def memberPackage (workspace : Lake.Workspace) (lib : LibSpec) :
    IO Lake.Package := do
  let mut pkg? : Option Lake.Package := none
  for root in lib.roots do
    let providers := workspace.findModules root
    let mut pkgs : Array Lake.Package := #[]
    for provider in providers do
      if (← provider.leanFile.pathExists) &&
          !pkgs.any (·.keyName == provider.pkg.keyName) then
        pkgs := pkgs.push provider.pkg
    if pkgs.size != 1 then
      throw <| IO.userError <|
        s!"member `{lib.qualifier}`: root module `{root}` resolved to \
{pkgs.size} workspace packages"
    let some pkg := pkgs[0]?
      | throw <| IO.userError s!"member `{lib.qualifier}`: provider of \
`{root}` disappeared"
    match pkg? with
    | none => pkg? := some pkg
    | some previous =>
      unless previous.keyName == pkg.keyName do
        throw <| IO.userError <|
          s!"member `{lib.qualifier}`: roots span packages \
`{previous.prettyName}` and `{pkg.prettyName}`"
  let some pkg := pkg?
    | throw <| IO.userError s!"member `{lib.qualifier}` has no roots"
  return pkg

/-- The member's local module inventory: its roots plus their package-local
    import closure. A Lake package may declare test, benchmark, or doc
    `lean_lib`s alongside its public library; following the import closure
    of the declared roots keeps those outside the catalog while umbrella
    roots still cover every public module. -/
private def memberSeedModules (workspace : Lake.Workspace)
    (lib : LibSpec) (pkg : Lake.Package) : IO (Array Lake.Module) := do
  let mut modules : Array Lake.Module := #[]
  for root in lib.roots do
    modules := modules.push (← resolvePackageModule pkg root)
  let mut index := 0
  while index < modules.size do
    let some moduleInfo := modules[index]?
      | throw <| IO.userError "module inventory index disappeared"
    if ← moduleInfo.leanFile.pathExists then
      for imported in ← parseModuleImports moduleInfo.leanFile do
        unless modules.any (·.name == imported) do
          if let some importedModule := pkg.findModule? imported then
            -- Workspace resolution must agree with the package-local
            -- provider: a source-module collision surfaces here before it
            -- can bind the wrong source.
            let providers := workspace.findModules imported
            if providers.any (fun provider =>
                provider.pkg.keyName == pkg.keyName) then
              modules := modules.push importedModule
    index := index + 1
  return modules

private def sourceModuleOf (qualifier : Lean.Name) (moduleInfo : Lake.Module) :
    IO SourceModule := do
  return {
    qualifier
    library := moduleInfo.lib.name
    moduleName := moduleInfo.name
    sourcePath := moduleInfo.leanFile
    imports := ← parseModuleImports moduleInfo.leanFile
  }

/-- Modules of a member not imported by another module of the same member;
    their import closures cover every connected component. -/
def terminalModules (modules : Array SourceModule) : Array SourceModule :=
  modules.filter fun candidate =>
    !modules.any fun moduleInfo =>
      moduleInfo.imports.contains candidate.moduleName

/-- Close every member's module set over cross-package source imports to a
    global fixed point, then re-root each member at its terminal modules.
    Fail-closed: an import that resolves to no workspace module (and is not
    a toolchain builtin), to a package outside the spec, or to two distinct
    cataloged providers is an error, as is one module provided by two
    members. Member order and the prefix are preserved. -/
def closeRoots (workspace : Lake.Workspace) (spec : CatalogSpec) :
    IO CatalogSpec := do
  -- Seed: each member's package-local closure of its declared roots.
  let mut members : Array ResolvedMember := #[]
  let mut providerOf : NameMap Nat := {}   -- moduleName → member index
  let mut queue : Array SourceModule := #[]
  for lib in spec.libs do
    let pkg ← memberPackage workspace lib
    if members.any (·.pkg.keyName == pkg.keyName) then
      throw <| IO.userError <|
        s!"member `{lib.qualifier}`: package `{pkg.prettyName}` is already \
claimed by another member"
    let mut modules : Array SourceModule := #[]
    for moduleInfo in ← memberSeedModules workspace lib pkg do
      let source ← sourceModuleOf lib.qualifier moduleInfo
      if let some other := providerOf.find? source.moduleName then
        throw <| IO.userError <|
          s!"module `{source.moduleName}` is provided by both \
`{spec.libs[other]!.qualifier}` and `{lib.qualifier}`"
      providerOf := providerOf.insert source.moduleName members.size
      modules := modules.push source
      queue := queue.push source
    members := members.push { lib, pkg, modules }

  -- Fixed point: any imported module a cataloged package provides but no
  -- member covers yet becomes additional coverage of its provider.
  let mut inspectedMissing : NameSet := {}
  let mut queueIndex := 0
  while queueIndex < queue.size do
    let moduleInfo := queue[queueIndex]!
    queueIndex := queueIndex + 1
    for imported in moduleInfo.imports do
      if (providerOf.find? imported).isSome ||
          inspectedMissing.contains imported then
        continue
      inspectedMissing := inspectedMissing.insert imported
      let allProviders := workspace.findModules imported
      let mut providers : Array (Nat × Lake.Module) := #[]
      for provider in allProviders do
        if let some memberIndex :=
            members.findIdx? (·.pkg.keyName == provider.pkg.keyName) then
          if (← provider.leanFile.pathExists) &&
              !providers.any (·.2.leanFile == provider.leanFile) then
            providers := providers.push (memberIndex, provider)
      if providers.size > 1 then
        throw <| IO.userError <|
          s!"imported module `{imported}` has {providers.size} distinct \
cataloged source providers"
      let some (memberIndex, provider) := providers[0]? | do
        if isBuiltinToolchainModule imported then continue
        if allProviders.isEmpty then
          throw <| IO.userError <|
            s!"module `{moduleInfo.moduleName}` imports unresolved module \
`{imported}`"
        throw <| IO.userError <|
          s!"module `{moduleInfo.moduleName}` imports `{imported}` from \
outside the cataloged members"
      let some member := members[memberIndex]?
        | throw <| IO.userError s!"cataloged provider of `{imported}` disappeared"
      let source ← sourceModuleOf member.lib.qualifier provider
      providerOf := providerOf.insert imported memberIndex
      members := members.set! memberIndex
        { member with modules := member.modules.push source }
      queue := queue.push source

  -- Re-root at terminal modules, deterministically ordered.
  let libs := members.map fun member =>
    let sorted := member.modules.qsort (·.moduleName.quickLt ·.moduleName)
    let roots := terminalModules sorted |>.map (·.moduleName)
    { qualifier := member.lib.qualifier, roots }
  for lib in libs do
    if lib.roots.isEmpty then
      throw <| IO.userError <|
        s!"member `{lib.qualifier}` closed to an empty root set"
  return { spec with libs }

end Ix.Catalog
