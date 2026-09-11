import Ix.Compiler.Tools.SourceScan
import Ix.Compiler.Tools.TrustProfile
import Lake.Toml.Load

/-! Compiler-scoped native/source audit. The reviewed Lake section fixes its build
inputs; the rest of the monorepo uses its own CI checks. No ledger is regenerated. -/

namespace Ix.Compiler.Tools.TrustLedger
open Lean System Check SourceScan TrustProfile

private def sameSet [BEq α] [Repr α] (actual expected : List α) (label : String) : IO Unit :=
  need (actual.all expected.contains && expected.all actual.contains)
    s!"{label} drifted:\nexpected={repr expected}\nactual={repr actual}"

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

def compilerSection (text : String) : IO String := do
  let [_, rest] := text.splitOn "section Compiler\n"
    | throw (IO.userError "expected exactly one Compiler Lake section")
  let [body, _] := rest.splitOn "end Compiler\n"
    | throw (IO.userError "expected exactly one Compiler Lake section end")
  return body

def textSha256 (text : String) : IO String := IO.FS.withTempFile fun handle path => do
  handle.putStr text
  handle.flush
  sha256 path

def compilerLake (root : FilePath) : IO (Array Token) := do
  checked (scan (← compilerSection (← IO.FS.readFile (root / "lakefile.lean"))))

private def under (root name : String) : Bool := name == root || name.startsWith (root ++ ".")

private def validateImports (sources : List (FilePath × Array Token)) : IO Unit := do
  let localRoots := ["Ix.Compiler", "Tests.Compiler", "Benchmarks.Compiler", "Lean", "Std", "Init", "Lake"]
  let imported := sources.flatMap (fun source => imports source.2)
  let external := imported.filter fun name => !localRoots.any (under · name)
  sameSet external ["Blake3.Rust"] "external Lean imports"
  for (mod, expected) in entrypoints do
    let calls := sources.flatMap fun (_, tokens) => tokens.toList.filterMap fun token =>
      if token.kind == .name && token.text.startsWith (mod ++ ".") then
        some (mod ++ "." ++ ((token.text.drop (mod.length + 1)).toString.splitOn ".").headD "")
      else none
    sameSet calls expected s!"qualified uses of {mod}"

def auditWith (profile : Profile) (root blake : FilePath) : IO Unit := do
  let root ← IO.FS.realPath root
  let blake ← IO.FS.realPath blake
  let buildSection ← compilerSection (← IO.FS.readFile (root / "lakefile.lean"))
  need ((← textSha256 buildSection) == profile.lakeSectionSha256) "Compiler Lake section hash drifted"
  let lake ← checked (scan buildSection)
  let paths ← leanSources root lake
  let sources ← paths.mapM fun path => return (path, ← scanFile path)
  for (path, tokens) in sources do
    checked ((hygiene tokens).mapError (fun error => s!"{path}: {error}"))
  validateImports sources
  sameSet (← symbolsOf root sources) projectSymbols "project extern inventory"
  let native := "native/compiler/hpt_cache_sync.c"
  let cFiles := lake.toList.filterMap fun token =>
    if token.kind == .literal && token.text.endsWith ".c" then some token.text else none
  sameSet cFiles [native] "project foreign-source inventory"
  need ((← sha256 (root / native)) == profile.durableSha256) "foreign source hash drifted"
  sameSet (← checked (cExports (← scanFile (root / native) true)))
    (projectSymbols.map (·.2.2)) "durability C export inventory"
  let packageFiles := (← files blake true).filter (·.extension == some "lean")
  let packageSources ← packageFiles.mapM fun path => return (path, ← scanFile path)
  sameSet (← symbolsOf blake packageSources) dependencySymbols "Blake3 package-tree extern inventory"
  let imported := sources.flatMap (fun source => imports source.2)
  need (imported.contains "Blake3.Rust" && !imported.contains "Blake3.C" &&
    imported.contains "Ix.Compiler.DurableSync") "native import reachability drifted"
  let manifest ← readJson (root / "lake-manifest.json")
  let packages ← (← arrField manifest "packages").filterM fun entry =>
    return (← strField entry "name") == "Blake3"
  need (packages.size == 1) "missing/duplicate Blake3 Lake dependency"
  need ((← strField packages[0]! "rev") == profile.blakeRevision) "Blake3 Lake revision drifted"
  let nodes ← field (← readJson (root / "flake.lock")) "nodes"
  for (node, revision) in [("blake3-lean", profile.blakeRevision), ("blake3", profile.blakeUpstreamRevision)] do
    need ((← strField (← field (← field nodes node) "locked") "rev") == revision)
      s!"{node} flake revision drifted"
  need ((← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString == profile.leanVersion)
    "Lean seed version drifted"
  let cargo := blake / "rust/Cargo.lock"
  need ((← sha256 cargo) == profile.cargoSha256) "Cargo lockfile hash drifted"
  let records ← cargoPackages cargo
  let inventory ← records.mapM fun record => return (← tomlString record "name", ← tomlString record "version")
  need (inventory.eraseDups.length == inventory.length) "duplicate Cargo package identity"
  need (inventory.contains ("blake3", profile.blakeVersion)) "BLAKE3 crate version drifted"
  let mut ffiSources := []
  for record in records do
    if (← tomlString record "name") == "lean-ffi" then
      ffiSources := (← tomlString record "source") :: ffiSources
  need (ffiSources.length == 1 && ffiSources.all (·.endsWith ("#" ++ profile.leanFfiRevision)))
    "lean-ffi Cargo revision drifted"
  IO.println s!"compiler trust audit OK: {sources.length} Lean files, 2 native interfaces, 14 symbols, {inventory.length} Cargo packages; reviewed component build and seed pins"

def audit (root : FilePath) (overrides : List (String × String)) : IO Unit := do
  let root ← IO.FS.realPath root
  need (overrides.all (·.1 == "Blake3")) "unknown dependency override"
  auditWith reviewed root (option overrides "Blake3" (root / ".lake/packages/Blake3").toString)

end Ix.Compiler.Tools.TrustLedger
