import Compilatrix.Tools.SourceScan
import Lake.Toml.Load

/-! Fail-closed validation of the hand-reviewed native/build trust ledger.
Inventories are derived from source and lock metadata. This program never
generates or refreshes ledger entries. -/

namespace Compilatrix.Tools.TrustLedger

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
  unique ids "ledger ids"
  let modeled ← arrField ledger "modeled_oracles"
  need (!modeled.isEmpty) "empty modeled_oracles"
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

def validateIntegrity (root : FilePath) (ledger : Json) : IO Unit := do
  let integrity ← field ledger "integrity"
  let tracked ← stringPairs (← field integrity "tracked_files")
  need (!tracked.isEmpty) "empty integrity.tracked_files"
  for (relative, expected) in tracked do
    let actual ← sha256 (root / relative)
    need (actual == expected) s!"{relative} changed: ledger {expected}, actual {actual}"
  let lock ← readJson (root / "flake.lock")
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
  let actual ← (← arrField manifest "packages").toList.mapM fun entry =>
    return (← strField entry "name", ← strField entry "rev")
  let deps ← dependencies interfaces
  let expected ← deps.toList.mapM fun entry =>
    return (← strField entry "lake_package", ← strField (← field entry "pins") "lake_rev")
  sameSet actual expected "Lake dependency inventory"
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
    (overrides : List (String × String)) : IO Nat := do
  let manifest ← readJson (root / "lake-manifest.json")
  let lock ← readJson (root / "flake.lock")
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
      unique (packages.map (·.1)) "Cargo package names; ledger needs name+version keys"
      sameSet packages (← stringPairs (← field cargo "packages")) s!"{package} Cargo package inventory"
      need (optional packages "blake3" == some (← strField pins "blake3_version")) "BLAKE3 crate version drifted"
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

def validateCI (root : FilePath) (ledger : Json) : IO Unit := do
  let workflows := (← (root / ".github/workflows").readDir).toList.filter fun entry =>
    entry.path.extension == some "yml" || entry.path.extension == some "yaml"
  need (!workflows.isEmpty) "no CI workflows found"
  let mut actual := []
  for workflow in workflows do
    for (line, index) in (← IO.FS.readFile workflow.path).splitOn "\n" |>.zipIdx do
      let line := line.trimAscii.toString
      let line := if line.startsWith "-" &&
          (line.toList[1]?.map Char.isWhitespace).getD false then
        (line.drop 1).toString.trimAscii.toString else line
      if !line.startsWith "uses:" then continue
      let parts := words (line.drop 5).toString
      need (parts.tail.isEmpty || (parts.tail.headD "").startsWith "#")
        s!"{workflow.path}:{index + 1}: unsupported CI action reference"
      let reference := parts.headD ""
      let first := reference.toList.headD '\x00'
      let reference ← if first == '"' || first == '\'' then do
        need (reference.length ≥ 2 && reference.endsWith (String.singleton first))
          s!"{workflow.path}:{index + 1}: malformed quoted CI action"
        pure (String.ofList (reference.toList.drop 1 |>.take (reference.length - 2)))
      else pure reference
      let [repository, commit] := reference.splitOn "@"
        | throw (IO.userError s!"{workflow.path}:{index + 1}: unpinned CI action {reference}")
      need (!repository.isEmpty && isHex 40 commit) s!"{workflow.path}:{index + 1}: unpinned CI action {reference}"
      actual := (repository, commit) :: actual
  let expected ← (← arrField ledger "ci_actions").toList.mapM fun entry =>
    return (← strField entry "repository", ← strField entry "commit")
  sameSet actual expected "CI action inventory"

def audit (root : FilePath) (overrides : List (String × String)) (gmp : Option String) : IO Unit := do
  let root ← IO.FS.realPath root
  let ledger ← readJson (root / "docs/trusted-externs.json")
  let (interfaces, seeds, specifications) ← validateShape ledger
  let lake ← scanFile (root / "lakefile.lean")
  let paths ← leanSources root lake
  let sources ← paths.mapM fun path => return (path, ← scanFile path)
  validateIntegrity root ledger
  for (path, tokens) in sources do
    checked ((hygiene tokens).mapError (fun error => s!"{path}: {error}"))
  validateImports root ledger interfaces sources
  let cargoCount ← validateNative root interfaces sources lake overrides
  validateSeeds root seeds gmp
  validateCI root ledger
  let mut symbols := 0
  for entry in interfaces do symbols := symbols + (← arrField entry "foreign_symbols").size
  IO.println s!"trusted-extern ledger ok: {interfaces.size} native interface, {symbols} symbols, {cargoCount} Cargo packages, {seeds.size} seed/build entries, {specifications.size} specification assumptions"

end Compilatrix.Tools.TrustLedger
