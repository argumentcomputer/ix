import IxCC.Tools.TrustLedger

/-! The checked import manifest defines Nix's separate production, test-program,
and proof source sets. Generate it after changing imports or Lake roots; CI
recomputes it from the full audit source tree before accepting the manifest. -/

namespace IxCC.Tools.BuildGraph

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

/-- The exact axiom assertions of every registered fence module. -/
def fenceAssertions (root : FilePath) (proofs : List String) : IO (List String) := do
  let mut axioms := []
  let directory := root / "IxCCTests/Fences"
  for path in ← files directory do
    if path.extension != some "lean" then continue
    let relative := (path.toString.dropPrefix (directory.toString ++ "/")).toString
    let name := "IxCCTests.Fences." ++
      ((FilePath.mk relative).withExtension "").toString.replace "/" "."
    need (proofs.contains name) s!"unregistered axiom-fence module {name}"
    axioms := axioms ++ (← axiomAssertions (← IO.FS.readFile path))
  return axioms

/-- The grounding library's fence (`IxCCGrounding/Fence.lean`), built with the library by the
required check `ixcc-grounding`, not by the shared proof aggregate. -/
def groundingFence : String := "IxCCGrounding/Fence.lean"

/-- The grounding library's modules and its fence's exact axiom assertions. -/
def groundingAssertions (root : FilePath) (graph : Json) : IO (List String × List String) := do
  let modules := (← closure graph ["IxCCGrounding"]).filter (·.startsWith "IxCCGrounding")
  need (modules.contains "IxCCGrounding.Fence") "the grounding library no longer builds its fence"
  return (modules, ← axiomAssertions (← IO.FS.readFile (root / groundingFence)))

/-- The kernel's model, which only the grounding library may import. -/
def modelModule (name : String) : Bool :=
  ["IxCK.Kernel.Denotes", "IxCK.Kernel.SetModel", "IxCK.Kernel.SetTheory", "IxCK.Kernel.Verify"].any
    fun p => name == p || name.startsWith (p ++ ".")

/-- The executables built by `ixcc-grounding` rather than by the shared program build. -/
def groundingTargets : List String := ["tests-grounding"]

/-- No module of `names`' closure is the grounding library's or imports the kernel's model. -/
def beside (graph : Json) (what : String) (names : List String) : IO Unit := do
  let modules ← pairs (← field graph "modules")
  for name in ← closure graph names do
    need (!name.startsWith "IxCCGrounding")
      s!"{what} imports the grounding library: {name}"
    if let some (_, entry) := modules.find? (·.1 == name) then
      for imp in ← (← arrField entry "imports").toList.mapM string do
        need (!modelModule imp) s!"{what} imports the kernel's model: {name} imports {imp}"

/-- Runtime failure assertions of each suite `S`, whose `IxCCTests.S.Run`
module must be reachable from its executable root `IxCCTests.S.Main`. -/
def suiteFailures (root : FilePath) (graph : Json) (suites : List String) :
    IO (List String) := do
  let mut failures := []
  for suite in suites do
    let runtime ← closure graph [s!"IxCCTests.{suite}.Main"]
    need (runtime.contains s!"IxCCTests.{suite}.Run") s!"unregistered runtime suite {suite}"
    failures := failures ++ (← runtimeFailures
      (← IO.FS.readFile (root / s!"IxCCTests/{suite}/Run.lean")))
  return failures

/-- The coverage inventory of the current tree, for review before it replaces
`nix/ci-coverage.json`. -/
def coverage (root : FilePath) (graph : Json) (baseline : String)
    (suites : List String) : IO Json := do
  let proofs := (← closure graph ["IxCCTests.Proofs"]).filter (· != "IxCCTests.Proofs")
  let axioms ← fenceAssertions root proofs
  let failures ← suiteFailures root graph suites
  let (gmodules, gaxioms) ← groundingAssertions root graph
  return Json.mkObj [("baseline", toJson baseline),
    ("proof_modules", toJson proofs),
    ("axiom_count", toJson axioms.length), ("axiom_sha256", toJson (← digest axioms)),
    ("grounding_modules", toJson gmodules),
    ("grounding_axiom_count", toJson gaxioms.length),
    ("grounding_axiom_sha256", toJson (← digest gaxioms)),
    ("runtime_suites", toJson suites),
    ("runtime_failure_count", toJson failures.length),
    ("runtime_failure_sha256", toJson (← digest failures))]

def checkCoverage (root : FilePath) (graph : Json) : IO Unit := do
  let expected ← readJson (root / "nix/ci-coverage.json")
  let proofs ← closure graph ["IxCCTests.Proofs"]
  for name in ← (← arrField expected "proof_modules").toList.mapM string do
    need (proofs.contains name) s!"required proof aggregate no longer builds {name}"
  let axioms ← fenceAssertions root proofs
  need (axioms.length == (← nat (← field expected "axiom_count")) &&
    (← digest axioms) == (← strField expected "axiom_sha256"))
    "required axiom assertions or expected messages changed; review the coverage inventory"
  let (gmodules, gaxioms) ← groundingAssertions root graph
  for name in ← (← arrField expected "grounding_modules").toList.mapM string do
    need (gmodules.contains name) s!"the grounding library no longer builds {name}"
  need (gaxioms.length == (← nat (← field expected "grounding_axiom_count")) &&
    (← digest gaxioms) == (← strField expected "grounding_axiom_sha256"))
    "grounding axiom assertions or expected messages changed; review the coverage inventory"
  let suites ← (← arrField expected "runtime_suites").toList.mapM string
  let failures ← suiteFailures root graph suites
  need (failures.length == (← nat (← field expected "runtime_failure_count")) &&
    (← digest failures) == (← strField expected "runtime_failure_sha256"))
    "runtime assertion inventory changed; review the coverage inventory"
  IO.println s!"coverage ok: {axioms.length} exact axiom assertions, {failures.length} runtime failure assertions"

def check (root : FilePath) : IO Unit := do
  let actual ← manifest root
  let expected ← checked (Json.parse (← IO.FS.readFile (root / "nix/lean-modules.json")))
  need (actual == expected)
    "Nix import manifest is stale; run lake exe check-build-graph --write"
  let production ← closure actual ["IxCC"]
  for name in production do
    need (!name.startsWith "IxCCTests" &&
      !["Examples", "Fixtures", "Fence", "Tests", "WellModedGen", "ThesisBench"].any (name.endsWith ·))
      s!"production imports regression module {name}"
  beside actual "production" ["IxCC"]
  beside actual "the shared proof aggregate" ["IxCCTests.Proofs"]
  for (name, target) in ← pairs (← field actual "targets") do
    if (← strField target "kind") == "lean_exe" && !groundingTargets.contains name then
      beside actual s!"shared program {name}" (← (← arrField target "roots").toList.mapM string)
  checkCoverage root actual
  IO.println s!"build-graph ok: {production.length} production modules, exact source/import inventory"

end IxCC.Tools.BuildGraph
