import IxCC.Tools.SourceScan
import Lake.Toml.Load

/-! Fail-closed validation of the hand-reviewed native/build trust ledger.
Inventories are derived from source and lock metadata. This program never
edits the ledger; `recordPins` prints the mechanical pins (hashes and
revisions) as the tree stands, for a reviewed update. -/

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
Lake package, how it is pinned (`leanSource`), the source directory of its
modules relative to the package root, the modules IxCC imports from it, and the
SHA-256 of every file of their import closure, which fixes the audited source
whatever the pin. -/
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

/-- How a pure Lean dependency is pinned (`source_kind`).

- `workspace_path`: a package of the enclosing workspace, at `pins.workspace_path`
  relative to the project root (`../IxCK` inside ix); the pins hold nothing else.
- `git`: a package Lake checks out at the revision `pins.lake_rev` (a full
  commit, which `lake-manifest.json` must record) and that Nix builds from the
  node `pins.flake_node` of the repository's `flake.lock` (locked at the same
  revision); the pins hold nothing else. Its modules are those under the
  module root `import_root`, and the project's uses of names under that root
  are exactly `project_entrypoints`. -/
inductive LeanSource where
  | workspace (dir : String)
  | git (rev node importRoot : String)
  deriving BEq, Repr

/-- A pure Lean dependency's pin, with its shape checked. -/
def leanSource (entry : Json) : IO LeanSource := do
  let package ← strField entry "lake_package"
  let pins ← field entry "pins"
  let keys := (← pairs pins).map (·.1)
  match ← strField entry "source_kind" with
  | "workspace_path" =>
    need (keys == ["workspace_path"]) s!"{package}: a workspace_path dependency pins only its path"
    let dir ← strField pins "workspace_path"
    need (!dir.isEmpty && !(FilePath.mk dir).isAbsolute)
      s!"{package}: workspace_path must be relative to the project root"
    return .workspace dir
  | "git" =>
    need (keys.length == 2 && keys.contains "lake_rev" && keys.contains "flake_node")
      s!"{package}: a git dependency pins only lake_rev and flake_node"
    let rev ← strField pins "lake_rev"
    need (isHex 40 rev) s!"{package}: lake_rev must be a full commit (40 lowercase hex digits)"
    let node ← strField pins "flake_node"
    need (!node.isEmpty) s!"{package}: empty flake_node"
    let importRoot ← strField entry "import_root"
    need (!importRoot.isEmpty && !importRoot.contains '.')
      s!"{package}: import_root must be a single module name component"
    let _ ← jsonStrings (← field entry "project_entrypoints")
    return .git rev node importRoot
  | kind => throw (IO.userError s!"{package}: unknown lean dependency source_kind {kind}")

/-- A pure Lean dependency's pin as `lake-manifest.json` records it. -/
def leanPin (entry : Json) : IO Pin := do
  match ← leanSource entry with
  | .workspace dir => return .path dir
  | .git rev _ _ => return .git rev

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

/-- A reviewed `@[csimp]` inventory: each theorem as `(file, theorem,
replaces, replacement)`, the file relative to the dependency's source
directory (or, for the project's own `csimp_theorems`, to the project root). A
csimp theorem changes the code the compiler emits for every call of
`replaces`, so each one is listed and any other fails the audit. -/
def csimpRecords (value : Json) : IO (List (String × String × String × String)) := do
  (← array value).toList.mapM fun entry => do
    return (← strField entry "file", ← strField entry "theorem", ← strField entry "replaces",
      ← strField entry "replacement")

/-- A dependency entry's `implemented_by_sites` (absent: none) as `(file,
declaration, implementation)`: the substitutions its closure declares, each
admitted by name, with the ruling of the dependency's own audit that admits it
(`ruling`, required and non-empty). Any other `implemented_by` in the closure
fails the audit. -/
def implementedByRecords (entry : Json) : IO (List (String × String × String)) := do
  match entry.getObjVal? "implemented_by_sites" with
  | .error _ => pure []
  | .ok value =>
    (← array value).toList.mapM fun site => do
      need (!(← strField site "ruling").isEmpty) "an implemented_by site names no ruling"
      return (← strField site "file", ← strField site "declaration", ← strField site "implementation")

/-- A dependency entry's `native_decide_sites` (absent: none) as `(file,
declaration)`, one record per occurrence of the tactic in the closure: the
reviewed `native_decide`s, each with the reason it is admitted (`ruling`,
required and non-empty). Any other occurrence, and a listed one that is not in
the closure, fails the audit (`validateLeanDependencies`). -/
def nativeDecideRecords (entry : Json) : IO (List (String × String)) := do
  match entry.getObjVal? "native_decide_sites" with
  | .error _ => pure []
  | .ok value =>
    (← array value).toList.mapM fun site => do
      need (!(← strField site "ruling").isEmpty) "a native_decide site names no ruling"
      return (← strField site "file", ← strField site "declaration")

/-- The ledger's shape. The native-interface list may be empty (IxCC links no
native interface); what an empty list cannot hide is checked by the
inventories it would otherwise have to account for: the project's own externs
and C sources (`validateNative`), the external import roots (`validateImports`),
each pure dependency's closure (`validateLeanDependencies`), and the symbols of
the built executables (`auditLinkedFiles`). -/
def validateShape (ledger : Json) : IO (Array Json × Array Json × Array Json) := do
  need ((← nat (← field ledger "schema_version")) == 2) "unsupported ledger schema_version"
  let interfaces ← arrField ledger "native_interfaces"
  let seeds ← arrField ledger "seed_and_build_trust"
  let specifications ← arrField ledger "specification_assumptions"
  need (!seeds.isEmpty && !specifications.isEmpty) "empty trust inventory"
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
    let _ ← csimpRecords (← field entry "csimp_theorems")
    let _ ← implementedByRecords entry
    let _ ← nativeDecideRecords entry
    let _ ← leanSource entry
    retirement entry
    ids := (← strField entry "id") :: ids
  unique ids "ledger ids"
  let _ ← csimpRecords (← field ledger "csimp_theorems")
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

/-! ## Integrity pins

`integrity.tracked_files` pins the SHA-256 of exactly the project files that
`integrity.rule` covers; `integrity.repository_files` pins files of the
enclosing repository, among them every configured CI workflow file. -/

/-- Whether `name` matches the wildcard `pattern`, in which `*` matches any run
of characters. -/
def wildcardMatches : List Char → List Char → Bool
  | [], [] => true
  | '*' :: pattern, [] => wildcardMatches pattern []
  | '*' :: pattern, c :: name =>
      wildcardMatches pattern (c :: name) || wildcardMatches ('*' :: pattern) name
  | p :: pattern, c :: name => p == c && wildcardMatches pattern name
  | _, _ => false

/-- Whether the `/`-separated `path` matches the glob `pattern`, whose segments
are wildcards and in which a `**` segment matches any number of segments. -/
def globMatches : List String → List String → Bool
  | [], [] => true
  | "**" :: pattern, [] => globMatches pattern []
  | "**" :: pattern, s :: path =>
      globMatches pattern (s :: path) || globMatches ("**" :: pattern) path
  | p :: pattern, s :: path => wildcardMatches p.toList s.toList && globMatches pattern path
  | _, _ => false

/-- The project files the ledger pins: those matching an `include` glob and no
`exclude` glob, relative to the project root. -/
structure IntegrityRule where
  includes : List String
  excludes : List String

def IntegrityRule.covers (rule : IntegrityRule) (relative : String) : Bool :=
  let path := relative.splitOn "/"
  let hit (pattern : String) : Bool := globMatches (pattern.splitOn "/") path
  rule.includes.any hit && !rule.excludes.any hit

def integrityRule (integrity : Json) : IO IntegrityRule := do
  let rule ← field integrity "rule"
  let includes ← jsonStrings (← field rule "include")
  let excludes ← jsonStrings (← field rule "exclude")
  need (!includes.isEmpty) "empty integrity.rule.include"
  for pattern in includes ++ excludes do
    need (!pattern.isEmpty && !(FilePath.mk pattern).isAbsolute &&
      !(pattern.splitOn "/").contains ".." && !(pattern.splitOn "/").contains "")
      s!"unsupported integrity.rule pattern {pattern}"
  return { includes, excludes }

/-- The files under `root` that `rule` covers, relative to `root`, sorted.
Hidden files and directories (`.lake`, `.gitignore`) are never covered. -/
def ruleFiles (root : FilePath) (rule : IntegrityRule) : IO (List String) := do
  let base := root.toString ++ "/"
  return ((← files root true).map fun path => (path.toString.dropPrefix base).toString)
    |>.filter rule.covers

private def flakeRevisions (flakeLock : FilePath) : IO (List (String × String)) := do
  let lock ← readJson flakeLock
  let mut revisions := []
  for (name, node) in ← pairs (← field lock "nodes") do
    if let .ok locked := node.getObjVal? "locked" then
      if let .ok rev := locked.getObjValAs? String "rev" then
        revisions := (name, rev) :: revisions
  return revisions.reverse

/-- `integrity.repository_files`, absent: none. -/
private def repositoryPins (integrity : Json) : IO (List (String × String)) :=
  match integrity.getObjVal? "repository_files" with
  | .ok value => stringPairs value
  | .error _ => pure []

/-- The configured CI workflow files, relative to the repository root. -/
private def workflowFiles (repo : Repository) : IO (List String) := do
  let base := repo.root.toString ++ "/"
  let mut result := []
  if repo.configured then
    for path in repo.workflows do
      if (← path.pathExists) && !(← path.isDir) then
        result := result ++ [(path.toString.dropPrefix base).toString]
  return result

/-- Every pinned project and repository file has its recorded hash, every
configured workflow file is pinned, and the flake nodes are recorded with
their revisions. Whether the pinned set is exactly the rule's is
`validateIntegrityRule`, run at the end of the audit. -/
def validateIntegrity (root : FilePath) (ledger : Json) (repo : Repository) : IO Unit := do
  let integrity ← field ledger "integrity"
  let tracked ← stringPairs (← field integrity "tracked_files")
  need (!tracked.isEmpty) "empty integrity.tracked_files"
  let digests ← sha256Many (tracked.map fun (relative, _) => root / relative)
  for ((relative, expected), actual) in tracked.zip digests do
    need (actual == expected) s!"{relative} changed: ledger {expected}, actual {actual}"
  let pins ← repositoryPins integrity
  for (relative, _) in pins do
    need (!relative.isEmpty && !(FilePath.mk relative).isAbsolute &&
      !(relative.splitOn "/").contains "..") s!"repository file must be a relative path: {relative}"
  let pinDigests ← sha256Many (pins.map fun (relative, _) => repo.root / relative)
  for ((relative, expected), actual) in pins.zip pinDigests do
    need (actual == expected) s!"repository file {relative} changed: ledger {expected}, actual {actual}"
  for workflow in ← workflowFiles repo do
    need (pins.any (·.1 == workflow))
      s!"configured CI workflow {workflow} is not pinned in integrity.repository_files"
  sameSet (← flakeRevisions repo.flakeLock) (← stringPairs (← field integrity "flake_nodes"))
    "flake node/revision inventory"

/-- The pinned project files are exactly the files `integrity.rule` covers: a
covered file without a pin, or a pin outside the rule, fails. -/
def validateIntegrityRule (root : FilePath) (ledger : Json) : IO Unit := do
  let integrity ← field ledger "integrity"
  let rule ← integrityRule integrity
  let pinned := (← pairs (← field integrity "tracked_files")).map (·.1)
  let covered ← ruleFiles root rule
  let listed (paths : List String) : String :=
    s!"{paths.take 20}{if paths.length > 20 then s!" and {paths.length - 20} more" else ""}"
  let unpinned := covered.filter (!pinned.contains ·)
  need unpinned.isEmpty
    s!"integrity rule: files the rule covers have no pin (record them with check-trusted-externs --record and review): {listed unpinned}"
  let outside := pinned.filter (!rule.covers ·)
  need outside.isEmpty s!"integrity rule: pinned files the rule does not cover: {listed outside}"

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
    return (← strField entry "lake_package", ← leanPin entry)
  -- a git-pinned pure dependency's revision, named, before the inventory as a whole
  for (package, pin) in leanPins do
    if let .git rev := pin then
      let recorded := actual.filter (·.1 == package) |>.map (·.2)
      need (recorded == [pin])
        s!"{package}: lake-manifest.json records {repr recorded}, the ledger pins the git revision {rev}"
  sameSet actual (native ++ leanPins) "Lake dependency inventory"
  let locals ← jsonStrings (← field (← field ledger "policy") "local_import_roots")
  need (!locals.isEmpty) "empty local_import_roots"
  let actualImports := sources.flatMap (fun source => imports source.2)
  let actualExternal := actualImports.map (fun mod => (mod.splitOn ".").headD "") |>.filter (!locals.contains ·)
  let gitRoots ← (← leanDependencies ledger).toList.filterMapM fun entry => do
    match ← leanSource entry with
    | .git _ _ importRoot => return some importRoot
    | .workspace _ => return none
  let expectedExternal := (← deps.toList.mapM (strField · "import_root")) ++ gitRoots
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
native declaration, no `implemented_by` other than the entry's
`implemented_by_sites`, no `axiom` declaration (`hygieneDependency`), no
`sorry`, no native evaluation but the `native_decide`s the entry's
`native_decide_sites` list (exactly, occurrence by occurrence), and imports
only closure or toolchain modules; its `@[csimp]` theorems are exactly the
entry's. Each dependency's root holds that package's `lakefile.lean` (a
`--dependency-root` override replaces the root). A git-pinned dependency
(`LeanSource.git`) is the one its `flake.lock` node locks at the same
revision, and the project's imports under its `import_root` are exactly its
`imported_modules` and its uses of names under that root exactly its
`project_entrypoints`: this is the audit that refuses an import of another
module of the package (`Blake3.Rust`, `Blake3.C`, the root module `Blake3`).
Returns the number of closure files checked and of `native_decide`s admitted. -/
def validateLeanDependencies (root : FilePath) (ledger : Json) (lake : Array Token)
    (sources : List (FilePath × Array Token)) (overrides : List (String × String))
    (flakeLock : FilePath) : IO (Nat × Nat) := do
  let manifest ← readJson (root / "lake-manifest.json")
  let packages ← arrField manifest "packages"
  let packagesDir := (manifest.getObjValAs? String "packagesDir").toOption.getD ".lake/packages"
  let locals ← jsonStrings (← field (← field ledger "policy") "local_import_roots")
  let mut unresolved := []
  for mod in (sources.flatMap fun source => imports source.2).eraseDups do
    let head := (mod.splitOn ".").headD ""
    if toolchainRoots.contains head || !locals.contains head then continue
    if ← localModule root lake mod then continue
    unresolved := mod :: unresolved
  let mut declared := []
  let mut checkedFiles := 0
  let mut admitted := 0
  for entry in ← leanDependencies ledger do
    let package ← strField entry "lake_package"
    let mut found := false
    for candidate in packages do
      if (← strField candidate "name") == package then found := true
    need found s!"lean dependency {package} is not in lake-manifest.json"
    let source ← leanSource entry
    let packageRoot : FilePath ← match source with
      | .workspace dir => pure (((optional overrides package).map FilePath.mk).getD (root / dir))
      | .git rev node _ => do
        -- the revision Nix builds is the one Lake checks out (the manifest's
        -- revision is checked against the same pin by `validateImports`)
        let nodes ← field (← readJson flakeLock) "nodes"
        let some flakeNode := (nodes.getObjVal? node).toOption
          | throw (IO.userError s!"{package}: flake.lock has no node {node}")
        let locked ← strField (← field flakeNode "locked") "rev"
        need (locked == rev) s!"{package}: flake.lock node {node} is at {locked}, the ledger pins {rev}"
        pure (FilePath.mk (option overrides package (root / packagesDir / package).toString))
    need (← declaresPackage (packageRoot / "lakefile.lean") package)
      s!"{package}: {packageRoot} does not hold its lakefile.lean"
    let sourceRoot ← IO.FS.realPath (packageRoot / (← strField entry "source_dir"))
    let closure ← stringPairs (← field entry "closure")
    need (!closure.isEmpty) s!"{package}: empty closure"
    let closureModules := closure.map fun (relative, _) =>
      ((FilePath.mk relative).withExtension "").toString.replace "/" "."
    let mut replacements : List (String × String × String × String) := []
    let mut substitutions : List (String × String × String) := []
    let mut nativeDecides : List (String × String × Nat) := []
    for (relative, expected) in closure do
      let path := sourceRoot / relative
      need ((← sha256 path) == expected) s!"{package}: {relative} changed"
      let tokens ← scanFile path
      for (declaration, line) in ← checked ((dependencyHygiene tokens).mapError
          (fun error => s!"{package}: {relative}: {error}")) do
        nativeDecides := nativeDecides ++ [(relative, declaration, line)]
      let natives ← checked ((externs tokens).mapError (fun error => s!"{package}: {relative}: {error}"))
      need natives.isEmpty s!"{package}: {relative} declares native symbols"
      for (declaration, implementation) in ← checked ((implementedBys tokens).mapError
          (fun error => s!"{package}: {relative}: {error}")) do
        substitutions := (relative, declaration, implementation) :: substitutions
      for mod in imports tokens do
        need (closureModules.contains mod || toolchainRoots.contains ((mod.splitOn ".").headD ""))
          s!"{package}: {relative} imports {mod} outside the recorded closure"
      for c in ← checked ((csimps tokens).mapError (fun error => s!"{package}: {relative}: {error}")) do
        replacements := (relative, c.name, c.replaces, c.replacement) :: replacements
      checkedFiles := checkedFiles + 1
    sameSet replacements (← csimpRecords (← field entry "csimp_theorems")) s!"{package} csimp inventory"
    sameSet substitutions (← implementedByRecords entry) s!"{package} implemented_by inventory"
    -- the closure's native_decides are exactly the listed sites, occurrence by occurrence
    let mut listed ← nativeDecideRecords entry
    for (relative, declaration, line) in nativeDecides do
      need (listed.contains (relative, declaration))
        s!"{package}: {relative}:{line}: native_decide in {declaration} is not a listed native_decide site"
      listed := listed.erase (relative, declaration)
    if let (relative, declaration) :: _ := listed then
      throw (IO.userError
        s!"{package}: stale native_decide site: {declaration} in {relative} has no native_decide left to admit")
    admitted := admitted + nativeDecides.length
    let imported ← jsonStrings (← field entry "imported_modules")
    need (imported.all closureModules.contains) s!"{package}: an imported module is outside its closure"
    match source with
    | .workspace _ => declared := declared ++ imported
    | .git _ _ importRoot =>
      -- the project's imports under the dependency's root are exactly its recorded modules
      for (path, tokens) in sources do
        for mod in imports tokens do
          if (mod.splitOn ".").headD "" == importRoot then
            need (imported.contains mod)
              s!"{package}: {path} imports {mod}; the project may import only {imported} under {importRoot}"
      let projectImports := sources.flatMap fun source => imports source.2
      for mod in imported do
        need (projectImports.contains mod) s!"{package}: recorded module {mod} is not imported by the project"
      sameSet (sources.flatMap fun source => namesUnder source.2 importRoot)
        (← jsonStrings (← field entry "project_entrypoints")) s!"qualified uses of {importRoot}"
  sameSet unresolved declared "imports of pure Lean dependencies"
  return (checkedFiles, admitted)

/-- The Lean seed is the project's `lean-toolchain`, and inside a larger
repository the repository's `lean-toolchain` (whose Lean ix's flake builds IxCC
with) names the same release; the GMP seed is Nix's GMP when given. -/
def validateSeeds (root : FilePath) (repo : Repository) (seeds : Array Json) (gmp : Option String) :
    IO Unit := do
  let toolchain := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  let marker := "leanprover/lean4:v"
  need (toolchain.startsWith marker && toolchain.length > marker.length) "unrecognized lean-toolchain"
  if repo.root.toString != root.toString then
    let outer := repo.root / "lean-toolchain"
    need (← outer.pathExists) s!"missing repository lean-toolchain: {outer}"
    need ((← IO.FS.readFile outer).trimAscii.toString == toolchain)
      "the repository's lean-toolchain differs from the project's"
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

/-- The remote actions the scoped workflows use, as `(repository, commit)`,
each pinned to a full commit. A repository-local action or reusable workflow
is reviewed with the repository: it is followed, and the remote actions it uses
are inventoried in its place. -/
def ciInventory (repo : Repository) : IO (List (String × String)) := do
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
  return actual.reverse

/-- Every remote action the scoped workflows use is pinned to a full commit and
recorded in `ci_actions` (`ciInventory`). -/
def validateCI (repo : Repository) (ledger : Json) : IO Unit := do
  let expected ← (← arrField ledger "ci_actions").toList.mapM fun entry =>
    return (← strField entry "repository", ← strField entry "commit")
  sameSet (← ciInventory repo) expected "CI action inventory"

/-- The required-check inventory: `required_checks` lists exactly the
attributes `nix/checks.nix` defines (each exposed by ix's flake as
`ixcc-<name>`, and compared again with the flake's evaluated checks by
`ixcc.yml`), with no duplicate. -/
def validateRequiredChecks (root : FilePath) (ledger : Json) : IO Unit := do
  let expected ← jsonStrings (← field ledger "required_checks")
  need (!expected.isEmpty) "empty required_checks"
  unique expected "required_checks"
  let actual ← checked ((nixBodyAttributes (← IO.FS.readFile (root / "nix/checks.nix"))).mapError
    fun error => s!"nix/checks.nix: {error}")
  unique actual "nix/checks.nix attributes"
  sameSet actual expected "required check inventory (nix/checks.nix against required_checks)"

/-- Every `@[csimp]` theorem in the project's audited sources is in the
ledger's `csimp_theorems`, and every listed one exists. -/
def validateProjectCSimps (root : FilePath) (ledger : Json)
    (sources : List (FilePath × Array Token)) : IO Unit := do
  let mut actual : List (String × String × String × String) := []
  for (path, tokens) in sources do
    let relative := (path.toString.dropPrefix (root.toString ++ "/")).toString
      |>.dropPrefix "./" |>.toString
    for c in ← checked ((csimps tokens).mapError (fun error => s!"{path}: {error}")) do
      actual := (relative, c.name, c.replaces, c.replacement) :: actual
  sameSet actual (← csimpRecords (← field ledger "csimp_theorems")) "project csimp inventory"

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
  validateIntegrity root ledger repo
  for (path, tokens) in sources do
    checked ((hygiene tokens).mapError (fun error => s!"{path}: {error}"))
  validateImports root ledger interfaces sources
  validateProjectCSimps root ledger sources
  let cargoCount ← validateNative root interfaces sources lake overrides repo.flakeLock
  let (leanFiles, nativeDecides) ← validateLeanDependencies root ledger lake sources overrides repo.flakeLock
  validateSeeds root repo seeds gmp
  validateCI repo ledger
  validateRequiredChecks root ledger
  validateIntegrityRule root ledger
  let mut symbols := 0
  for entry in interfaces do symbols := symbols + (← arrField entry "foreign_symbols").size
  IO.println s!"trusted-extern ledger ok: {interfaces.size} native interfaces, {symbols} foreign symbols, {cargoCount} Cargo packages, {(← leanDependencies ledger).size} pure Lean dependencies ({leanFiles} files, {nativeDecides} admitted native_decide sites), {seeds.size} seed/build entries, {specifications.size} specification assumptions"

/-! ## The link audit

No executable the checks ship or run may link a native backend of the Blake3
package: IxCC hashes with the pure `Blake3.Pure`. The audit reads each
executable's symbol table as `nm -P` prints it (one symbol per line, its name
first) and refuses the backends' symbols by name. -/

/-- Symbol-name prefixes of the Blake3 package's native backends: the Rust FFI's
exports (`rs_blake3_`), the C FFI's (`c_blake3_`), the upstream BLAKE3 C
library's (`blake3_`, which either backend links), and the compiled Lean
declarations of the backend modules `Blake3.Rust` and `Blake3.C` (Lean names
them `lp_<package>_<declaration>`, the pure module's declarations
`lp_Blake3_Blake3_Pure_…`). -/
def forbiddenSymbolPrefixes : List String :=
  ["rs_blake3_", "c_blake3_", "blake3_", "lp_Blake3_Blake3_Rust_", "lp_Blake3_Blake3_C_"]

/-- Symbol-name suffixes: the module initializers of `Blake3.Rust` and
`Blake3.C` (`initialize_…` and Lean's `runtime_initialize_…` and
`meta_initialize_…`). -/
def forbiddenSymbolSuffixes : List String :=
  ["initialize_Blake3_Blake3_Rust", "initialize_Blake3_Blake3_C"]

def forbiddenSymbol (name : String) : Bool :=
  forbiddenSymbolPrefixes.any (fun pre => name.startsWith pre) ||
    forbiddenSymbolSuffixes.any (fun suffix => name.endsWith suffix)

/-- The symbol names of `nm -P` output: the first field of each line. -/
def nmSymbols (output : String) : List String :=
  (output.splitOn "\n").filterMap fun line => (words line).head?

/-- The link audit of one executable, from its `nm -P` output: its symbol table
was read (it lists `main`) and it names no symbol of a Blake3 native backend.
Returns the number of symbols read. -/
def auditLinked (label output : String) : Except String Nat := do
  let symbols := nmSymbols output
  unless symbols.contains "main" do
    throw s!"{label}: nm lists no main symbol, so its symbol table was not read"
  match symbols.filter forbiddenSymbol with
  | [] => return symbols.length
  | found => throw s!"{label} links a native backend of the Blake3 package: {found.eraseDups.take 12}"

/-- Whether `path` is an ELF file (its first four bytes are `0x7f E L F`). -/
private def elf (path : FilePath) : IO Bool := do
  let handle ← IO.FS.Handle.mk path .read
  return (← handle.read 4).data == #[0x7f, 0x45, 0x4c, 0x46]

/-- `check-trusted-externs --linked`: the link audit of every ELF file of each
directory of `paths` (not recursively; Lake's other outputs beside the
executables are skipped) and of each file of `paths`, which must be ELF,
running `nm` (`nm -P FILE`). At least one executable is audited. -/
def auditLinkedFiles (nm : String) (paths : List FilePath) : IO Unit := do
  let mut binaries : List FilePath := []
  for path in paths do
    if ← path.isDir then
      for entry in ← path.readDir do
        if !(← entry.path.isDir) && (← elf entry.path) then binaries := binaries ++ [entry.path]
    else
      need (← elf path) s!"{path} is not an ELF file"
      binaries := binaries ++ [path]
  need (!binaries.isEmpty) s!"link audit: no executable among {paths}"
  let mut symbols := 0
  for binary in binaries.mergeSort (fun a b => a.toString ≤ b.toString) do
    symbols := symbols + (← checked (auditLinked binary.toString (← run nm #["-P", binary.toString])))
  IO.println s!"link audit ok: {binaries.length} executables, {symbols} symbols, none of a Blake3 native backend"

/-- The ledger's mechanical pins as the tree now stands, for review before
they replace the recorded ones (`tools/record-ledger-pins.jq`): the hash of
every file `integrity.rule` covers and of every listed or configured
repository file, the revision of every `flake.lock` node, and the commit of
every remote CI action. It never edits the ledger, and records nothing else:
seed versions, symbols, closures and the other entries are reviewed by hand. -/
def recordPins (root : FilePath) (repositoryRoot flakeLock : Option FilePath := none) :
    IO Json := do
  let root ← IO.FS.realPath root
  let ledger ← readJson (root / "docs/trusted-externs.json")
  let repo ← repository root ledger repositoryRoot flakeLock
  let integrity ← field ledger "integrity"
  let covered ← ruleFiles root (← integrityRule integrity)
  let digests ← sha256Many (covered.map fun (relative : String) => root / relative)
  let repositoryFiles := ((← repositoryPins integrity).map (·.1) ++ (← workflowFiles repo)).eraseDups
  let repositoryDigests ← sha256Many (repositoryFiles.map fun (relative : String) => repo.root / relative)
  let actions ← ciInventory repo
  for (repository, commit) in actions do
    need (actions.all fun (other, pin) => other != repository || pin == commit)
      s!"{repository} is pinned at several commits; record ci_actions by hand"
  let object (entries : List (String × String)) : Json :=
    Json.mkObj (entries.map fun (key, value) => (key, toJson value))
  return Json.mkObj [
    ("tracked_files", object (covered.zip digests)),
    ("repository_files", object (repositoryFiles.zip repositoryDigests)),
    ("flake_nodes", object (← flakeRevisions repo.flakeLock)),
    ("ci_actions", object actions.eraseDups)]

end IxCC.Tools.TrustLedger
