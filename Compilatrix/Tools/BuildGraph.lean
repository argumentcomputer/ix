import Compilatrix.Tools.TrustLedger

/-! The checked import manifest defines Nix's separate production, test-program,
and proof source sets. Generate it after changing imports or Lake roots; CI
recomputes it from the full audit source tree before accepting the manifest. -/

namespace Compilatrix.Tools.BuildGraph

open Lean System Check SourceScan

def manifest (root : FilePath) : IO Json := do
  let lake ← checked (scan (← IO.FS.readFile (root / "lakefile.lean")))
  let roots ← TrustLedger.lakeRoots lake
  let directories := (roots.map Prod.fst).eraseDups.mergeSort (fun a b => a.length ≥ b.length)
  let mut modules := []
  for path in ← TrustLedger.leanSources root lake do
    let relative := (path.toString.dropPrefix (root.toString ++ "/")).toString
      |>.dropPrefix "./" |>.toString
    let directory := (directories.find? (fun directory =>
      directory != "." && relative.startsWith (directory ++ "/"))).getD "."
    let modulePath := if directory == "." then relative
      else (relative.dropPrefix (directory ++ "/")).toString
    let name := (FilePath.mk modulePath).withExtension "" |>.toString.replace "/" "."
    need (!(modules.map Prod.fst).contains name) s!"duplicate local module {name}"
    let imports := imports (← checked (scan (← IO.FS.readFile path)))
    modules := modules ++ [(name, Json.mkObj [("path", toJson relative), ("imports", toJson imports)])]
  let positions := (List.range lake.size).filter fun i =>
    lake[i]!.kind == .name && ["lean_lib", "lean_exe"].contains lake[i]!.text
  let mut targets := []
  for i in [:positions.length] do
    let start := positions[i]!
    let stop := positions[i + 1]?.getD lake.size
    let name := lake[start + 1]!.text
    let targetRoots ← TrustLedger.lakeRoots (lake.extract start stop)
    targets := targets ++ [(name, Json.mkObj [
      ("kind", toJson lake[start]!.text),
      ("roots", toJson (targetRoots.map Prod.snd))])]
  return Json.mkObj [("schema_version", toJson (1 : Nat)),
    ("modules", Json.mkObj modules), ("targets", Json.mkObj targets)]

def closure (graph : Json) (roots : List String) : IO (List String) := do
  let modules ← pairs (← field graph "modules")
  let mut seen := []
  let mut pending := roots
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    if let some (_, entry) := modules.find? (·.1 == name) then
      seen := name :: seen
      let imports ← (← arrField entry "imports").toList.mapM string
      pending := imports ++ pending
  return seen.mergeSort (· ≤ ·)

/-- Preserve the theorem spelling and the complete expected message together. -/
def axiomAssertions (source : String) : IO (List String) := do
  let blocks ← (source.splitOn "/-- info:").tail!.mapM fun tail => do
    let lines := tail.splitOn "\n"
    let command ← present (lines.find? (·.startsWith "#guard_msgs in #print axioms "))
      "axiom fence has an expected message without its assertion"
    return "/-- info:" ++ String.intercalate "\n"
      (lines.takeWhile (· != command) ++ [command]) ++ "\n"
  let tokens ← checked (scan source)
  let prints := (List.range tokens.size).countP fun i =>
    tokens[i]?.map (·.text) == some "print" &&
      tokens[i + 1]?.map (·.text) == some "axioms"
  need (prints == blocks.length) "axiom fence contains an unguarded/unrecognized axiom assertion"
  return blocks

def runtimeFailures (source : String) : IO (List String) := do
  return (← checked (scan source)).toList.filterMap fun token =>
    if token.kind == .literal && token.text.startsWith "FAIL:" then some token.text else none

def digest (values : List String) : IO String :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr ((toJson (values.mergeSort (· ≤ ·))).compress ++ "\n")
    handle.flush
    sha256 path

def checkCoverage (root : FilePath) (graph : Json) : IO Unit := do
  let expected ← readJson (root / "nix/ci-coverage.json")
  let proofs ← closure graph ["CompilatrixTests.Proofs"]
  for name in ← (← arrField expected "proof_modules").toList.mapM string do
    need (proofs.contains name) s!"required proof aggregate no longer builds {name}"
  let mut axioms := []
  for path in ← files (root / "CompilatrixTests/Fences") do
    if path.extension != some "lean" then continue
    let name := "CompilatrixTests.Fences." ++ (path.fileStem.getD "")
    need (proofs.contains name) s!"unregistered axiom-fence module {name}"
    axioms := axioms ++ (← axiomAssertions (← IO.FS.readFile path))
  need (axioms.length == (← nat (← field expected "axiom_count")) &&
    (← digest axioms) == (← strField expected "axiom_sha256"))
    "required axiom assertions or expected messages changed; review the coverage inventory"
  let mut failures := []
  let runtime ← closure graph ["CompilatrixTests.Runtime"]
  for suite in ["Addressing", "Pipeline", "HPT", "Ixon"] do
    need (runtime.contains s!"CompilatrixTests.{suite}.Run") s!"unregistered runtime suite {suite}"
    failures := failures ++ (← runtimeFailures
      (← IO.FS.readFile (root / s!"CompilatrixTests/{suite}/Run.lean")))
  need (failures.length == (← nat (← field expected "runtime_failure_count")) &&
    (← digest failures) == (← strField expected "runtime_failure_sha256"))
    "runtime assertion inventory changed; review the coverage inventory"
  IO.println s!"coverage ok: {axioms.length} exact axiom assertions, {failures.length} runtime failure assertions"

def check (root : FilePath) : IO Unit := do
  let actual ← manifest root
  let expected ← checked (Json.parse (← IO.FS.readFile (root / "nix/lean-modules.json")))
  need (actual == expected)
    "Nix import manifest is stale; run lake exe check-build-graph --write"
  let production ← closure actual ["Compilatrix"]
  for name in production do
    need (!name.startsWith "CompilatrixTests" &&
      !["Examples", "Fixtures", "Fence", "Tests", "WellModedGen", "ThesisBench"].any (name.endsWith ·))
      s!"production imports regression module {name}"
  checkCoverage root actual
  IO.println s!"build-graph ok: {production.length} production modules, exact source/import inventory"

end Compilatrix.Tools.BuildGraph
