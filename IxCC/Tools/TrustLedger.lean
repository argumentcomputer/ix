import IxCC.Tools.SourceScan
import Lake.Toml.Load

/-! Fail-closed validation of the hand-reviewed native/build trust ledger.
Inventories are derived from source and lock metadata. This program never
generates or refreshes ledger entries. -/

namespace IxCC.Tools.TrustLedger

open Lean System Check SourceScan

private def nonempty : Json → Bool
  | .null => false
  | .bool value => value
  | .str value => !value.isEmpty
  | .arr value => !value.isEmpty
  | .obj value => !value.toList.isEmpty
  | .num value => value != 0

private def fields (entry : Json) (keys : List String) : IO Unit := do
  for key in keys do
    need (nonempty (← field entry key)) s!"missing nonempty {key}: {entry.compress}"

private def retirement (entry : Json) : IO Unit := do
  fields (← field entry "retirement") ["milestone", "replacement", "exit_criteria"]

private def unique [BEq α] [Repr α] (values : List α) (label : String) : IO Unit :=
  need (values.eraseDups.length == values.length) s!"{label}: duplicate entries {repr values}"

private def sameSet [BEq α] [Repr α] (actual expected : List α) (label : String) : IO Unit :=
  need (actual.all expected.contains && expected.all actual.contains)
    s!"{label} drifted:\nledger={repr expected}\nactual={repr actual}"

private def jsonStrings (value : Json) : IO (List String) := do
  (← array value).toList.mapM string

private def stringPairs (value : Json) : IO (List (String × String)) := do
  (← pairs value).mapM fun (key, value) => return (key, ← string value)

/-- A Cargo inventory maps each crate to its version, or to a list of versions
when the lockfile resolves several releases of that crate. -/
private def cargoPairs (value : Json) : IO (List (String × String)) := do
  (← pairs value).foldlM (init := []) fun acc (name, versions) => do
    match versions with
    | .str version => return acc ++ [(name, version)]
    | _ =>
      let versions ← jsonStrings versions
      need (versions.length ≥ 2) s!"Cargo crate {name}: a version list needs several versions"
      return acc ++ versions.map (name, ·)

/-- Pure Lean Lake dependencies (`lean_dependencies`, absent: none). They carry
no native code, so they have no `native_interfaces` entry; each records its
Lake package and how it is pinned (`source_kind`), the source directory of its
modules relative to the package root, the modules IxCC imports from it, and
the SHA-256 of every file of their import closure. A `git` dependency pins a
Lake revision and the flake node pinning the same revision for Nix; a
`workspace_path` dependency is a package of the enclosing workspace, at
`pins.workspace_path` relative to the project root (`../IxCK` inside ix). -/
def leanDependencies (ledger : Json) : IO (Array Json) :=
  match ledger.getObjVal? "lean_dependencies" with
  | .ok value => array value
  | .error _ => pure #[]

/-- How a Lake dependency is pinned: a git revision, or a directory of the
enclosing workspace (as `lake-manifest.json` records them). -/
inductive Pin where
  | git (rev : String)
  | path (dir : String)
  deriving BEq, Repr

private def manifestPin (entry : Json) : IO (String × Pin) := do
  let name ← strField entry "name"
  match ← strField entry "type" with
  | "git" => return (name, .git (← strField entry "rev"))
  | "path" => return (name, .path (← strField entry "dir"))
  | other => throw (IO.userError s!"Lake dependency {name}: unsupported manifest type {other}")

/-- The pin the ledger records for a pure Lean dependency. -/
def leanDependencyPin (entry : Json) : IO Pin := do
  let pins ← field entry "pins"
  match ← strField entry "source_kind" with
  | "git" => return .git (← strField pins "lake_rev")
  | "workspace_path" =>
      let dir ← strField pins "workspace_path"
      need (!dir.isEmpty && !(FilePath.mk dir).isAbsolute)
        s!"{(← strField entry "lake_package")}: workspace_path must be relative to the project root"
      return .path dir
  | other => throw (IO.userError s!"unknown lean dependency source_kind {other}")

/-- The repository around the project: where its `flake.lock` and CI
workflows are. Standalone the project is the repository. Inside a larger one,
`policy.repository.root` (relative to the project, e.g. `..`) names it, and
`policy.repository.workflows` (relative to it) scopes the workflow files or
directories whose actions this ledger inventories, absent: `.github/workflows`. -/
structure Repository where
  root : FilePath
  flakeLock : FilePath
  workflows : List FilePath
  /-- Whether the workflows were configured, so must exist. -/
  configured : Bool

private def relativeString (value : Json) (label : String) : IO String := do
  let path ← string value
  need (!path.isEmpty && !(FilePath.mk path).isAbsolute) s!"{label} must be a relative path: {path}"
  return path

/-- The repository configuration, with command-line overrides of its root
and of its `flake.lock`. -/
def repository (root : FilePath) (ledger : Json) (rootOverride flakeLock : Option FilePath := none) :
    IO Repository := do
  let config := ((← field ledger "policy").getObjVal? "repository").toOption
  let relative ← match config with
    | some value => do relativeString (← field value "root") "policy.repository.root"
    | none => pure "."
  let base ← IO.FS.realPath (rootOverride.getD (root / relative))
  let workflows := config.bind fun value => (value.getObjVal? "workflows").toOption
  let configured ← match workflows with
    | some value => do
        let paths ← (← array value).toList.mapM fun path =>
          relativeString path "policy.repository.workflows"
        pure (some (paths.map fun (path : String) => base / path))
    | none => pure none
  return { root := base, flakeLock := flakeLock.getD (base / "flake.lock"),
           workflows := configured.getD [base / ".github" / "workflows"], configured := configured.isSome }

def validateShape (ledger : Json) : IO (Array Json × Array Json × Array Json) := do
  need ((← nat (← field ledger "schema_version")) == 2) "unsupported ledger schema_version"
  let interfaces ← arrField ledger "native_interfaces"
  let seeds ← arrField ledger "seed_and_build_trust"
  let specifications ← arrField ledger "specification_assumptions"
  need (!interfaces.isEmpty && !seeds.isEmpty && !specifications.isEmpty) "empty trust inventory"
  let mut ids := []
  for entry in interfaces do
    fields entry ["id", "status", "owner", "source_kind", "lean_module", "semantics_assumed",
      "proof_effect", "trust_basis", "tests", "retirement"]
    let kind ← strField entry "source_kind"
    if kind == "dependency" then fields entry ["lake_package", "import_root", "pins"]
    else if kind == "project" then fields entry ["foreign_source", "source_sha256"]
    else throw (IO.userError s!"unknown native source_kind {kind}")
    retirement entry
    let symbols ← arrField entry "foreign_symbols"
    need (!symbols.isEmpty) "empty foreign_symbols"
    for symbol in symbols do fields symbol ["lean_name", "symbol", "module", "reachability"]
    ids := (← strField entry "id") :: ids
  for entry in seeds do
    fields entry ["id", "status", "owner", "version", "current_role", "assumption", "trust_basis", "retirement"]
    ids := (← strField entry "id") :: ids
  for entry in specifications do
    fields entry ["id", "status", "owner", "scope", "assumption", "proof_effect", "trust_basis", "tests", "retirement"]
    retirement entry
    ids := (← strField entry "id") :: ids
  for entry in ← leanDependencies ledger do
    fields entry ["id", "status", "owner", "lake_package", "source_dir", "closure",
      "pins", "semantics_assumed", "proof_effect", "trust_basis", "tests", "retirement"]
    let _ ← jsonStrings (← field entry "imported_modules")
    match ← leanDependencyPin entry with
    | .git _ => fields (← field entry "pins") ["lake_rev", "flake_node"]
    | .path _ =>
      let package ← strField entry "lake_package"
      need ((← pairs (← field entry "pins")).length == 1)
        s!"{package}: a workspace_path dependency pins only its path"
    retirement entry
    ids := (← strField entry "id") :: ids
  unique ids "ledger ids"
  let modeled ← arrField ledger "modeled_oracles"
  let mut modeledIds := []
  for entry in modeled do
    fields entry ["id", "address", "declaration", "scope", "semantics"]
    let _ ← checked (← field entry "arity").getInt?
    let coherence ← field entry "address_coherence"
    let status ← strField coherence "status"
    need (["proved", "stable-key", "unsupported"].contains status) "unknown address-coherence status"
    fields coherence ["evidence"]
    if status != "unsupported" then fields coherence ["fixture"]
    need ((← field entry "native_code") == Json.bool false &&
      (← field entry "production_approved") == Json.bool false) "modeled oracle is approved/native"
    modeledIds := (← strField entry "id") :: modeledIds
  unique modeledIds "modeled oracle ids"
  need (!modeledIds.any ids.contains) "modeled ids overlap trusted ids"
  return (interfaces, seeds, specifications)

private def tokenAt (tokens : Array Token) (index : Nat) : String :=
  tokens[index]?.map (·.text) |>.getD ""

private def assignment (tokens : Array Token) (key : String) : IO (Option (Array Token)) := do
  let positions := (List.range tokens.size).filter fun index =>
    tokens[index]!.kind == .name && tokens[index]!.text == key
  need (positions.length ≤ 1) s!"duplicate Lake {key} field"
  match positions with
  | [] => return none
  | index :: _ =>
      need (tokenAt tokens (index + 1) == ":" && tokenAt tokens (index + 2) == "=")
        s!"unsupported Lake {key} assignment"
      return some (tokens.extract (index + 3) tokens.size)

private def moduleName (token : Token) : Bool :=
  token.kind == .name && !token.text.isEmpty &&
    token.text.toList.all (fun char => char.isAlphanum || char == '_' || char == '.' || char == '\'')

def lakeRoots (tokens : Array Token) : IO (List (String × String)) := do
  let positions := (List.range tokens.size).filter fun index =>
    tokens[index]!.kind == .name && ["lean_lib", "lean_exe"].contains tokens[index]!.text
  need (!positions.isEmpty) "lakefile.lean declares no auditable Lean roots"
  let mut roots := []
  for position in [:positions.length] do
    let index := positions[position]!
    let finish := positions[position + 1]?.getD tokens.size
    let some name := tokens[index + 1]? | throw (IO.userError "Lake target has no name")
    need (name.kind == .name || name.kind == .quotedName) "unsupported Lake target name"
    let body := tokens.extract (index + 2) finish
    let sourceDir ← match ← assignment body "srcDir" with
      | none => pure "."
      | some value =>
          need (value[0]?.map (·.kind) == some .literal && !(tokenAt value 0).isEmpty)
            "unsupported Lake srcDir"
          pure (tokenAt value 0)
    need (!(FilePath.mk sourceDir).isAbsolute && !(sourceDir.splitOn "/").contains "..")
      "Lake source root escapes project"
    let single ← assignment body "root"
    let multiple ← assignment body "roots"
    need (!(single.isSome && multiple.isSome)) "Lake target declares both root and roots"
    let modules ← match single, multiple with
      | some value, none =>
          need (tokenAt value 0 == String.singleton (Char.ofNat 96) &&
            (value[1]?.map moduleName).getD false) "unsupported Lake root"
          pure [tokenAt value 1]
      | none, some value =>
          need (tokenAt value 0 == "#" && tokenAt value 1 == "[") "unsupported Lake roots"
          let mut index := 2
          let mut modules := []
          while tokenAt value index != "]" do
            need (tokenAt value index == String.singleton (Char.ofNat 96) &&
              (value[index + 1]?.map moduleName).getD false) "unsupported/empty Lake roots"
            modules := tokenAt value (index + 1) :: modules
            index := index + 2
            if tokenAt value index == "," then index := index + 1
            else need (tokenAt value index == "]") "unsupported Lake root separator"
          need (!modules.isEmpty) "empty Lake roots"
          pure modules.reverse
      | none, none =>
          need (moduleName name) "Lake target needs an explicit root"
          pure [name.text]
      | _, _ => throw (IO.userError "ambiguous Lake roots")
    roots := roots ++ modules.map (sourceDir, ·)
  return roots

def leanSources (root : FilePath) (lake : Array Token) : IO (List FilePath) := do
  let mut sources := []
  for (directory, mod) in ← lakeRoots lake do
    let path := root / directory / mod.replace "." "/"
    let file := path.withExtension "lean"
    let mut found := []
    if ← file.pathExists then found := [file]
    if ← path.isDir then
      found := found ++ ((← files path).filter (·.extension == some "lean"))
    need (!found.isEmpty) s!"Lake root {mod} has no Lean sources"
    sources := sources ++ found
  return sources.eraseDups.mergeSort (fun a b => a.toString ≤ b.toString)

private def scanFile (path : FilePath) (cSource : Bool := false) : IO (Array Token) := do
  checked ((scan (← IO.FS.readFile path) cSource).mapError (fun message => s!"{path}: {message}"))

def validateIntegrity (root : FilePath) (ledger : Json) (flakeLock : FilePath) : IO Unit := do
  let integrity ← field ledger "integrity"
  let tracked ← stringPairs (← field integrity "tracked_files")
  need (!tracked.isEmpty) "empty integrity.tracked_files"
  for (relative, expected) in tracked do
    let actual ← sha256 (root / relative)
    need (actual == expected) s!"{relative} changed: ledger {expected}, actual {actual}"
  let lock ← readJson flakeLock
  let mut revisions := []
  for (name, node) in ← pairs (← field lock "nodes") do
    if let .ok locked := node.getObjVal? "locked" then
      if let .ok rev := locked.getObjValAs? String "rev" then
        revisions := (name, rev) :: revisions
  sameSet revisions (← stringPairs (← field integrity "flake_nodes")) "flake node/revision inventory"

private def dependencies (interfaces : Array Json) : IO (Array Json) :=
  interfaces.filterM fun entry => return (← strField entry "source_kind") == "dependency"

private def localInterfaces (interfaces : Array Json) : IO (Array Json) :=
  interfaces.filterM fun entry => return (← strField entry "source_kind") == "project"

def validateImports (root : FilePath) (ledger : Json) (interfaces : Array Json)
    (sources : List (FilePath × Array Token)) : IO Unit := do
  let manifest ← readJson (root / "lake-manifest.json")
  let actual ← (← arrField manifest "packages").toList.mapM manifestPin
  let deps ← dependencies interfaces
  let native ← deps.toList.mapM fun entry => do
    return (← strField entry "lake_package", Pin.git (← strField (← field entry "pins") "lake_rev"))
  let leanPins ← (← leanDependencies ledger).toList.mapM fun entry => do
    return (← strField entry "lake_package", ← leanDependencyPin entry)
  sameSet actual (native ++ leanPins) "Lake dependency inventory"
  let locals ← jsonStrings (← field (← field ledger "policy") "local_import_roots")
  need (!locals.isEmpty) "empty local_import_roots"
  let actualImports := sources.flatMap (fun source => imports source.2)
  let actualExternal := actualImports.map (fun mod => (mod.splitOn ".").headD "") |>.filter (!locals.contains ·)
  let expectedExternal ← deps.toList.mapM (strField · "import_root")
  sameSet actualExternal expectedExternal "external Lean import roots"
  for entry in interfaces do
    let mod ← strField entry "lean_module"
    let actualCalls := sources.flatMap fun (_, tokens) =>
      tokens.toList.filterMap fun token =>
        if token.kind == .name && token.text.startsWith (mod ++ ".") then
          some (mod ++ "." ++ ((token.text.drop (mod.length + 1)).toString.splitOn ".").headD "")
        else none
    sameSet actualCalls (← jsonStrings (← field entry "project_entrypoints")) s!"qualified uses of {mod}"

private def modulePath (root : FilePath) (mod : String) : FilePath :=
  root / (mod.replace "." "/" ++ ".lean")

private def pathModule (root path : FilePath) : IO String := do
  let base := (← IO.FS.realPath root).toString ++ "/"
  let path := (← IO.FS.realPath path).withExtension "" |>.toString
  need (path.startsWith base) s!"source escapes project root: {path}"
  return ((path.drop base.length).toString.replace "/" ".")

private def symbolsOf (root : FilePath) (sources : List (FilePath × Array Token))
    : IO (List (String × String × String)) := do
  let mut symbols := []
  for (path, tokens) in sources do
    let mod ← pathModule root path
    for (symbol, name) in ← checked ((externs tokens).mapError (fun e => s!"{path}: {e}")) do
      symbols := (mod, if name.contains "." then name else mod ++ "." ++ name, symbol) :: symbols
  return symbols

private def expectedSymbols (entries : Array Json) : IO (List (String × String × String)) := do
  let mut symbols := []
  for entry in entries do
    for symbol in ← arrField entry "foreign_symbols" do
      symbols := (← strField symbol "module", ← strField symbol "lean_name", ← strField symbol "symbol") :: symbols
  return symbols

private def reachability (entry : Json) (imported : List String) : IO Unit := do
  for symbol in ← arrField entry "foreign_symbols" do
    let claim ← strField symbol "reachability"
    let mod ← strField symbol "module"
    need (claim.startsWith "imported" || claim.startsWith "present, unimported")
      s!"unsupported reachability for {mod}"
    need (claim.startsWith "imported" == imported.contains mod) s!"reachability disagrees with imports of {mod}"

private def tomlString (table : Lake.Toml.Table) (key : String) : IO String := do
  let some (.string _ value) := table.find? key.toName | throw (IO.userError s!"Cargo missing string {key}")
  return value

private def cargoPackages (path : FilePath) : IO (List Lake.Toml.Table) := do
  let input ← IO.FS.readFile path
  let table ← match ← (Lake.Toml.loadToml (Parser.mkInputContext input path.toString)).toBaseIO with
    | .ok table => pure table
    | .error _ => throw (IO.userError s!"invalid Cargo TOML: {path}")
  let some (.array _ entries) := table.find? "package".toName
    | throw (IO.userError "Cargo TOML lacks package array")
  entries.toList.mapM fun
    | .table _ entry => pure entry
    | _ => throw (IO.userError "Cargo package is not a table")

def validateNative (root : FilePath) (interfaces : Array Json)
    (sources : List (FilePath × Array Token)) (lake : Array Token)
    (overrides : List (String × String)) (flakeLock : FilePath) : IO Nat := do
  let manifest ← readJson (root / "lake-manifest.json")
  let lock ← readJson flakeLock
  let nodes ← field lock "nodes"
  let locals ← localInterfaces interfaces
  sameSet (← symbolsOf root sources) (← expectedSymbols locals) "project extern inventory"
  let imported := sources.flatMap (fun source => imports source.2)
  let cFiles := lake.toList.filterMap fun token =>
    if token.kind == .literal && token.text.endsWith ".c" then some token.text else none
  sameSet cFiles (← locals.toList.mapM (strField · "foreign_source")) "project foreign-source inventory"
  for entry in locals do
    let mod ← strField entry "lean_module"
    need (← (modulePath root mod).pathExists) s!"missing native module {mod}"
    let relative ← strField entry "foreign_source"
    let path ← IO.FS.realPath (root / relative)
    need (path.toString.startsWith (root.toString ++ "/")) s!"foreign source escapes root: {path}"
    need ((← sha256 path) == (← strField entry "source_sha256")) s!"foreign source hash drifted: {relative}"
    let actual ← checked (cExports (← scanFile path true))
    let expected ← (← arrField entry "foreign_symbols").toList.mapM (strField · "symbol")
    sameSet actual expected s!"{relative} C export inventory"
    reachability entry imported
  let mut cargoCount := 0
  for entry in ← dependencies interfaces do
    let package ← strField entry "lake_package"
    let packagesDir := (manifest.getObjValAs? String "packagesDir").toOption.getD ".lake/packages"
    let packageRoot ← IO.FS.realPath (FilePath.mk (option overrides package (root / packagesDir / package).toString))
    let mod ← strField entry "lean_module"
    need (← (modulePath packageRoot mod).pathExists) s!"missing dependency native module {mod}"
    let packageFiles := (← files packageRoot true).filter (·.extension == some "lean")
    need (!packageFiles.isEmpty) s!"empty dependency source tree: {package}"
    let packageSources ← packageFiles.mapM fun path => return (path, ← scanFile path)
    sameSet (← symbolsOf packageRoot packageSources) (← expectedSymbols #[entry])
      s!"{package} package-tree extern inventory"
    reachability entry imported
    let pins ← field entry "pins"
    if let .ok cargo := entry.getObjVal? "cargo_lock" then
      let path := packageRoot / (← strField cargo "path")
      need ((← sha256 path) == (← strField cargo "sha256")) s!"Cargo lockfile hash drifted for {package}"
      let records ← cargoPackages path
      let packages ← records.mapM fun table => return (← tomlString table "name", ← tomlString table "version")
      unique packages "Cargo package records"
      let expected ← cargoPairs (← field cargo "packages")
      unique expected "ledger Cargo package versions"
      sameSet packages expected s!"{package} Cargo package inventory"
      need (packages.filter (·.1 == "blake3") == [("blake3", ← strField pins "blake3_version")])
        "BLAKE3 crate version drifted"
      let mut ffiSource := ""
      for record in records do
        if (← tomlString record "name") == "lean-ffi" then ffiSource ← tomlString record "source"
      need (ffiSource.contains (← strField pins "lean_ffi_rev")) "lean-ffi Cargo revision drifted"
      cargoCount := cargoCount + packages.length
    let node ← field nodes (← strField pins "flake_node")
    need ((← strField (← field node "locked") "rev") == (← strField pins "lake_rev")) "flake/Lake pin mismatch"
    need ((← strField (← field (← field nodes "blake3") "locked") "rev") ==
      (← strField pins "blake3_upstream_rev")) "upstream BLAKE3 revision drifted"
  return cargoCount


/-! ## Pure Lean dependencies -/

/-- Toolchain import roots a dependency's closure may import. -/
private def toolchainRoots : List String := ["Init", "Lean", "Std", "Lake"]

/-- Whether a module is one of this project's own Lake sources. -/
private def localModule (root : FilePath) (lake : Array Token) (mod : String) : IO Bool := do
  for (directory, _) in ← lakeRoots lake do
    if ← (root / directory / (mod.replace "." "/" ++ ".lean")).pathExists then return true
  return false

/-- Lake's checkout directory name for a package (`«a-b»` is checked out as `a-b`). -/
private def checkoutName (package : String) : String :=
  if package.startsWith "«" && package.endsWith "»" then
    ((package.drop 1).dropEnd 1).toString
  else package

/-- Whether a Lake configuration declares the package `name` (as the manifest
spells it, `«a-b»` for a name that needs quoting). -/
private def declaresPackage (lakefile : FilePath) (name : String) : IO Bool := do
  let tokens ← scanFile lakefile
  return (List.range tokens.size).any fun index =>
    tokens[index]!.kind == .name && tokens[index]!.text == "package" &&
      (match tokens[index + 1]? with
       | some token => (if token.kind == .quotedName then s!"«{token.text}»" else token.text) == name
       | none => false)

/-- Every import of the project's sources that names neither a project module
nor a toolchain module is a recorded module of a pure Lean dependency; every
file of each dependency's recorded import closure has its recorded hash, no
native declaration, no `implemented_by`, no `axiom`/`sorry`/`native_decide`,
and imports only closure or toolchain modules. A `git` dependency's Lake and
flake pins agree; a `workspace_path` dependency's directory holds that
package's `lakefile.lean` (a `--dependency-root` override replaces the
directory, as it replaces a git checkout). Returns the number of closure files
checked. -/
def validateLeanDependencies (root : FilePath) (ledger : Json) (lake : Array Token)
    (sources : List (FilePath × Array Token)) (overrides : List (String × String))
    (flakeLock : FilePath) : IO Nat := do
  let manifest ← readJson (root / "lake-manifest.json")
  let packagesDir := (manifest.getObjValAs? String "packagesDir").toOption.getD ".lake/packages"
  let packages ← arrField manifest "packages"
  let locals ← jsonStrings (← field (← field ledger "policy") "local_import_roots")
  let mut unresolved := []
  for mod in (sources.flatMap fun source => imports source.2).eraseDups do
    let head := (mod.splitOn ".").headD ""
    if toolchainRoots.contains head || !locals.contains head then continue
    if ← localModule root lake mod then continue
    unresolved := mod :: unresolved
  let mut declared := []
  let mut checkedFiles := 0
  for entry in ← leanDependencies ledger do
    let package ← strField entry "lake_package"
    let pins ← field entry "pins"
    let mut found := none
    for candidate in packages do
      if (← strField candidate "name") == package then found := some candidate
    let some record := found | throw (IO.userError s!"lean dependency {package} is not in lake-manifest.json")
    let pin ← leanDependencyPin entry
    let packageRoot : FilePath := match optional overrides package, pin with
      | some path, _ => path
      | none, .path dir => root / dir
      | none, .git _ => root / packagesDir / checkoutName package /
          ((record.getObjValAs? String "subDir").toOption.getD ".")
    match pin with
    | .git rev =>
        let node ← field (← field (← readJson flakeLock) "nodes") (← strField pins "flake_node")
        need ((← strField (← field node "locked") "rev") == rev) s!"{package}: flake/Lake pin mismatch"
    | .path dir =>
        need (← declaresPackage (packageRoot / "lakefile.lean") package)
          s!"{package}: {dir} does not hold its lakefile.lean"
    let sourceRoot ← IO.FS.realPath (packageRoot / (← strField entry "source_dir"))
    let closure ← stringPairs (← field entry "closure")
    need (!closure.isEmpty) s!"{package}: empty closure"
    let closureModules := closure.map fun (relative, _) =>
      ((FilePath.mk relative).withExtension "").toString.replace "/" "."
    for (relative, expected) in closure do
      let path := sourceRoot / relative
      need ((← sha256 path) == expected) s!"{package}: {relative} changed"
      let tokens ← scanFile path
      checked ((hygiene tokens).mapError (fun error => s!"{package}: {relative}: {error}"))
      let natives ← checked ((externs tokens).mapError (fun error => s!"{package}: {relative}: {error}"))
      need natives.isEmpty s!"{package}: {relative} declares native symbols"
      need (!tokens.any fun token => token.kind == .name && token.text == "implemented_by")
        s!"{package}: {relative} uses implemented_by"
      for mod in imports tokens do
        need (closureModules.contains mod || toolchainRoots.contains ((mod.splitOn ".").headD ""))
          s!"{package}: {relative} imports {mod} outside the recorded closure"
      checkedFiles := checkedFiles + 1
    let imported ← jsonStrings (← field entry "imported_modules")
    need (imported.all closureModules.contains) s!"{package}: an imported module is outside its closure"
    declared := declared ++ imported
  sameSet unresolved declared "imports of pure Lean dependencies"
  return checkedFiles

def validateSeeds (root : FilePath) (seeds : Array Json) (gmp : Option String) : IO Unit := do
  let toolchain := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  let marker := "leanprover/lean4:v"
  need (toolchain.startsWith marker && toolchain.length > marker.length) "unrecognized lean-toolchain"
  let mut foundLean := false
  let mut foundGmp := false
  for entry in seeds do
    if (← strField entry "id") == "lean-seed-runtime" then
      foundLean := true
      need ((← strField entry "version") == (toolchain.drop marker.length).toString) "Lean seed version drifted"
    if (← strField entry "id") == "gmp-seed" then
      foundGmp := true
      if let some version := gmp then
        need ((← strField entry "version") == version) "GMP ledger version differs from Nix"
  need (foundLean && foundGmp) "missing Lean/GMP seed entries"

private def yaml (path : FilePath) : Bool :=
  path.extension == some "yml" || path.extension == some "yaml"

/-- The `uses:` references of a workflow or action file, with their lines. -/
private def usesReferences (path : FilePath) : IO (List (Nat × String)) := do
  let mut result : List (Nat × String) := []
  for (line, index) in (← IO.FS.readFile path).splitOn "\n" |>.zipIdx do
    let line := line.trimAscii.toString
    let line := if line.startsWith "-" &&
        (line.toList[1]?.map Char.isWhitespace).getD false then
      (line.drop 1).toString.trimAscii.toString else line
    if !line.startsWith "uses:" then continue
    let parts := words (line.drop 5).toString
    need (parts.tail.isEmpty || (parts.tail.headD "").startsWith "#")
      s!"{path}:{index + 1}: unsupported CI action reference"
    let reference := parts.headD ""
    let first := reference.toList.headD '\x00'
    let reference ← if first == '"' || first == '\'' then do
      need (reference.length ≥ 2 && reference.endsWith (String.singleton first))
        s!"{path}:{index + 1}: malformed quoted CI action"
      pure (String.ofList (reference.toList.drop 1 |>.take (reference.length - 2)))
    else pure reference
    result := (index + 1, reference) :: result
  return result.reverse

/-- The file a repository-local reference (`./path` or `$/path`) names: a
reusable workflow, or a local action's `action.yml`/`action.yaml`. It must
stay inside the repository. -/
private def localTarget (repo : Repository) (origin : FilePath) (line : Nat) (relative : String) :
    IO FilePath := do
  let location := s!"{origin}:{line}"
  let base := repo.root / relative
  let target ← if ← base.isDir then do
      if ← (base / "action.yml").pathExists then pure (base / "action.yml")
      else if ← (base / "action.yaml").pathExists then pure (base / "action.yaml")
      else throw (IO.userError s!"{location}: local action {relative} has no action.yml")
    else if (← base.pathExists) && yaml base then pure base
    else throw (IO.userError s!"{location}: missing local action or workflow {relative}")
  let target ← IO.FS.realPath target
  need (target.toString.startsWith (repo.root.toString ++ "/"))
    s!"{location}: local action escapes the repository: {relative}"
  return target

/-- Every remote action the scoped workflows use is pinned to a full commit and
recorded in `ci_actions`. A repository-local action or reusable workflow is
reviewed with the repository: it is followed, and the remote actions it uses
are inventoried in its place. -/
def validateCI (repo : Repository) (ledger : Json) : IO Unit := do
  let mut pending : List FilePath := []
  for entry in repo.workflows do
    if ← entry.isDir then
      pending := pending ++ ((← entry.readDir).toList.map (·.path) |>.filter yaml)
    else if ← entry.pathExists then
      need (yaml entry) s!"configured CI workflow is not YAML: {entry}"
      pending := pending ++ [entry]
    else need (!repo.configured) s!"missing configured CI workflow path: {entry}"
  let mut seen : List FilePath := []
  let mut actual : List (String × String) := []
  while !pending.isEmpty do
    let path := pending.head!
    pending := pending.tail!
    let real ← IO.FS.realPath path
    if seen.contains real then continue
    seen := real :: seen
    for (line, reference) in ← usesReferences path do
      let relative := if reference.startsWith "./" || reference.startsWith "$/" then
        some (reference.drop 2).toString else none
      if let some relative := relative then
        pending := pending ++ [← localTarget repo path line relative]
        continue
      let [repository, commit] := reference.splitOn "@"
        | throw (IO.userError s!"{path}:{line}: unpinned CI action {reference}")
      need (!repository.isEmpty && isHex 40 commit) s!"{path}:{line}: unpinned CI action {reference}"
      actual := (repository, commit) :: actual
  let expected ← (← arrField ledger "ci_actions").toList.mapM fun entry =>
    return (← strField entry "repository", ← strField entry "commit")
  sameSet actual expected "CI action inventory"

/-- The complete audit. `repositoryRoot` and `flakeLock` override the ledger's
repository root and the `flake.lock` in it (for a copy of the project taken
out of its repository, as in a Nix check). -/
def audit (root : FilePath) (overrides : List (String × String)) (gmp : Option String)
    (repositoryRoot flakeLock : Option FilePath := none) : IO Unit := do
  let root ← IO.FS.realPath root
  let ledger ← readJson (root / "docs/trusted-externs.json")
  let (interfaces, seeds, specifications) ← validateShape ledger
  let repo ← repository root ledger repositoryRoot flakeLock
  let lake ← scanFile (root / "lakefile.lean")
  let paths ← leanSources root lake
  let sources ← paths.mapM fun path => return (path, ← scanFile path)
  validateIntegrity root ledger repo.flakeLock
  for (path, tokens) in sources do
    checked ((hygiene tokens).mapError (fun error => s!"{path}: {error}"))
  validateImports root ledger interfaces sources
  let cargoCount ← validateNative root interfaces sources lake overrides repo.flakeLock
  let leanFiles ← validateLeanDependencies root ledger lake sources overrides repo.flakeLock
  validateSeeds root seeds gmp
  validateCI repo ledger
  let mut symbols := 0
  for entry in interfaces do symbols := symbols + (← arrField entry "foreign_symbols").size
  IO.println s!"trusted-extern ledger ok: {interfaces.size} native interface, {symbols} symbols, {cargoCount} Cargo packages, {(← leanDependencies ledger).size} pure Lean dependency ({leanFiles} files), {seeds.size} seed/build entries, {specifications.size} specification assumptions"

end IxCC.Tools.TrustLedger
