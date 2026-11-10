import IxCC.Tools.TrustLedger
import IxCC.Tools.X86Check
import IxCC.Tools.BuildGraph
import IxCCTests.Tools.BuildGraph

/-! Regression tests for the trust gate's failure paths. Mutations are confined
to fresh temporary copies; the source tree and reviewed ledger are never edited. -/

open Lean System IxCC.Tools.Check IxCC.Tools.SourceScan
open IxCC.Tools.TrustLedger

private def rejects (label fragment : String) (action : IO Unit) : IO Unit := do
  let error ← try action; pure none catch error => pure (some error.toString)
  let some error := error | throw (IO.userError s!"{label}: unexpectedly accepted")
  need (error.contains fragment) s!"{label}: rejected for the wrong reason: {error}"

private def replaceField (value : Json) (key : String) (replacement : Json) : IO Json := do
  let entries ← pairs value
  need (entries.any (·.1 == key)) s!"test fixture is missing {key}"
  return Json.mkObj (entries.map fun (name, value) => (name, if name == key then replacement else value))

private def withFile (path : FilePath) (value : String) (action : IO Unit) : IO Unit := do
  let original ← if ← path.pathExists then some <$> IO.FS.readBinFile path else pure none
  if let some parent := path.parent then IO.FS.createDirAll parent
  try
    IO.FS.writeFile path value
    action
  finally
    match original with
    | some bytes => IO.FS.writeBinFile path bytes
    | none => IO.FS.removeFile path

private def copyFile (source target : FilePath) : IO Unit := do
  if let some parent := target.parent then IO.FS.createDirAll parent
  IO.FS.writeBinFile target (← IO.FS.readBinFile source)

private def copyRelative (sourceRoot targetRoot source : FilePath) : IO Unit := do
  let source ← IO.FS.realPath source
  let base := sourceRoot.toString ++ "/"
  need (source.toString.startsWith base) s!"test source escapes root: {source}"
  copyFile source (targetRoot / (source.toString.drop base.length).toString)

/-- Copy what the audit reads of the project at `source` and of the
repository around it into `target`, the copy's repository root: the project's
Lean sources, tracked files and ledger, at the project's path in the
repository; each pure Lean dependency's lakefile and recorded closure; the
repository's `flake.lock` and `lean-toolchain`; and its `.github` (workflows and
local actions).
Returns the copied project's root. -/
private def cloneWorkspace (source target : FilePath) : IO FilePath := do
  let ledger ← readJson (source / "docs/trusted-externs.json")
  let repo ← repository source ledger
  let copy := copyRelative repo.root target
  let lake ← checked (scan (← IO.FS.readFile (source / "lakefile.lean")))
  for path in ← leanSources source lake do copy path
  for (path, _) in ← pairs (← field (← field ledger "integrity") "tracked_files") do
    copy (source / path)
  copy (source / "docs/trusted-externs.json")
  for entry in ← leanDependencies ledger do
    let directory ← strField (← field entry "pins") "workspace_path"
    let sourceDir ← strField entry "source_dir"
    copy (source / directory / "lakefile.lean")
    for (relative, _) in ← pairs (← field entry "closure") do
      copy (source / directory / sourceDir / relative)
  copy repo.flakeLock
  copy (repo.root / "lean-toolchain")
  let github := repo.root / ".github"
  if ← github.isDir then
    for path in ← files github do copy path
  let project ← IO.FS.realPath source
  return target / (project.toString.drop (repo.root.toString.length + 1)).toString

private def lexerTests : IO Unit := do
  let safe := "/- outer /- axiom hidden : False -/ sorry -/\n" ++
    "-- native_decide\n" ++
    "def text := \"sorry axiom native_decide @[extern nope]\"\n" ++
    "def quote := '\"'\ndef indexed := values[0]'(by omega)\n" ++
    "def f' := Namespace.sorry\n"
  checked (hygiene (← checked (scan safe)))
  for token in ["axiom", "sorry", "native_decide"] do
    rejects token (token ++ " is not allowed") do
      checked (hygiene (← checked (scan s!"def safe := \"{token}\"\n{token} injected")))
  rejects "Unicode-delimited proof hole" "sorry is not allowed" do
    checked (hygiene (← checked (scan "def pair : Nat × Nat := ⟨sorry, 0⟩")))
  rejects "Unicode-delimited native tactic" "native_decide is not allowed" do
    checked (hygiene (← checked (scan "by exact ⟨by native_decide⟩")))
  -- every spelling of native evaluation the lexer can see
  for (source, fragment) in [
      ("theorem t : 2 + 2 = 4 := by decide +native", "decide +native is not allowed"),
      ("theorem t : 2 + 2 = 4 := by decide +kernel +native", "decide +native is not allowed"),
      ("theorem t : 2 + 2 = 4 := by decide (config := { native := true })",
        "native := true is not allowed"),
      ("theorem t : 2 + 2 = 4 := by decide (config := {kernel := false, native := true})",
        "native := true is not allowed"),
      ("theorem t : True := Lean.ofReduceBool _ _ rfl", "Lean.ofReduceBool is not allowed"),
      ("open Lean in theorem t : True := ofReduceBool _ _ rfl", "ofReduceBool is not allowed"),
      ("example := Lean.ofReduceNat", "Lean.ofReduceNat is not allowed"),
      ("example := Lean.trustCompiler", "Lean.trustCompiler is not allowed"),
      ("example := Lean.reduceBool true", "Lean.reduceBool is not allowed")] do
    rejects source fragment do checked (hygiene (← checked (scan source)))
  -- kernel decision, a variable or field named `native`, the bare marker
  -- names IxCC uses as fields, comments and literals are accepted
  checked (hygiene (← checked (scan ("theorem t : 2 + 2 = 4 := by decide +kernel\n" ++
    "def f (native : Nat) := 1 + native\ndef g := { native := 0, kernel := true }\n" ++
    "def h := let native := 1; native\ndef r (p : P) := p.reduceBool\n" ++
    "-- by decide +native\n/- Lean.ofReduceBool -/\ndef s := \"native := true\"\n"))))
  let externInput := "/- @[extern \"ignored\"] opaque absent : Nat -/\n" ++
    "@[extern 1 \"ffi_first\"] private unsafe opaque first : Nat\n" ++
    "attribute [extern \"ffi_second\"] second Qualified.third\n"
  let found ← checked (externs (← checked (scan externInput)))
  need (found == [("ffi_first", "first"), ("ffi_second", "second"), ("ffi_second", "Qualified.third")])
    "extern declaration/attribute inventory changed"
  rejects "trailing quoted extern attribute target" "unsupported attribute-command target" do
    discard (checked (externs (← checked (scan "attribute [extern \"ffi\"] ok «quoted»\n"))))
  rejects "trailing quoted csimp attribute target" "unsupported csimp attribute target" do
    discard (checked (csimps (← checked (scan "theorem ok : @f = @g := rfl\nattribute [csimp] ok «quoted»\n"))))
  rejects "unsupported extern" "unrecognized extern declaration" do
    let _ ← checked (externs (← checked (scan "@[extern \"unaccounted\"] theorem unsupported : True := by trivial")))
  rejects "implicit extern" "explicit symbol" do
    let _ ← checked (externs (← checked (scan "@[extern] opaque unsupported : Nat")))
  let csimpInput := "/- @[csimp] theorem hidden : @a = @b := rfl -/\n" ++
    "def text := \"@[csimp] theorem quoted : @a = @b := rfl\"\n" ++
    "@[inline, csimp] private theorem f_eq : @f = @fFast := rfl\n" ++
    "theorem g_eq : g = gFast := by rfl\nattribute [csimp] g_eq\n"
  need ((← checked (csimps (← checked (scan csimpInput)))) ==
      ([⟨"f_eq", "f", "fFast"⟩, ⟨"g_eq", "g", "gFast"⟩] : List CSimp)) "csimp declaration/attribute inventory changed"
  rejects "csimp with binders" "is not stated as" do
    let _ ← checked (csimps (← checked (scan "@[csimp] theorem h_eq (x : Nat) : f x = g x := rfl")))
  rejects "csimp attribute without its theorem" "not a theorem of this source" do
    let _ ← checked (csimps (← checked (scan "attribute [csimp] elsewhere_eq\n")))
  rejects "csimp on a definition" "csimp attribute not on a theorem" do
    let _ ← checked (csimps (← checked (scan "@[csimp] def notATheorem : Nat := 0")))
  rejects "unterminated comment" "unterminated block comment" do
    let _ ← checked (scan "/- nested /- closed -/")
  let cInput := "/* LEAN_EXPORT int ignored(void); */\n" ++
    "const char *text = \"LEAN_EXPORT int fake(void)\";\n" ++
    "LEAN_EXPORT lean_obj_res actual(b_lean_obj_arg x) { return x; }\n"
  need ((← checked (cExports (← checked (scan cInput true)))) == ["actual"])
    "C comments/literals leaked into export inventory"
  let tick := String.singleton (Char.ofNat 96)
  let roots ← lakeRoots (← checked (scan (
    s!"lean_lib Main where\n  roots := #[{tick}Main, {tick}Aux]\n" ++
    s!"lean_exe «extra-cli» where\n  srcDir := \"tools\"\n  root := {tick}Extra\n")))
  need (roots == [(".", "Main"), (".", "Aux"), ("tools", "Extra")]) "Lake root discovery changed"
  rejects "empty roots" "empty Lake roots" do
    let _ ← lakeRoots (← checked (scan "lean_lib Main where\n  roots := #[]\n"))
  rejects "unauditable roots" "unsupported Lake roots" do
    let _ ← lakeRoots (← checked (scan "lean_lib Main where\n  roots := computedRoots\n"))

/-- The Nix attribute lexer behind the required-check inventory, and the globs
of the integrity rule. -/
private def inventoryTests : IO Unit := do
  let source := "{ pkgs, system }: let\n  x = \"}\" + ''\n  ${f ''{ nested }''} '' ;\n" ++
    "  # { comment = 1; }\nin\n{\n  a = mkCheck \"a\" [] ''\n    echo \"${y}\" ''${z} '''\n  '';\n" ++
    "  b-c = { inner = 1; };\n  inherit (pkgs) d e;\n}\n" ++
    "// pkgs.lib.optionalAttrs (system == \"x\") {\n  f = /* { g = 1; } */ 2;\n}\n"
  need ((← checked (nixBodyAttributes source)) == ["a", "b-c", "d", "e", "f"])
    "Nix attribute inventory changed"
  rejects "quoted Nix attribute" "unsupported binding" do
    discard (checked (nixBodyAttributes "{}: let in { \"a-b\" = 1; }"))
  rejects "Nix attribute path" "unsupported binding" do
    discard (checked (nixBodyAttributes "{}: let in { a.b = 1; }"))
  rejects "antiquoted Nix attribute" "unsupported binding" do
    discard (checked (nixBodyAttributes "{}: let in { ${n} = 1; }"))
  rejects "unterminated Nix string" "unterminated" do
    discard (checked (nixBodyAttributes "{}: let in { a = ''x; }"))
  rejects "Nix file without let" "no top-level" do
    discard (checked (nixBodyAttributes "{}: { a = 1; }"))
  let glob (pattern path : String) : Bool := globMatches (pattern.splitOn "/") (path.splitOn "/")
  need (glob "IxCC/**" "IxCC/A/B.lean" && glob "fixtures/**/*.c" "fixtures/x86/a.c" &&
      glob "docs/aiur-*.md" "docs/aiur-wire.md" && glob "**" "a/b" &&
      glob "lean-toolchain" "lean-toolchain" && glob "IxCC/**" "IxCC/A.lean")
    "integrity glob rejected a match"
  need (!glob "docs/aiur-*.md" "docs/x/aiur-wire.md" && !glob "IxCC/**" "IxCCTests/A.lean" &&
      !glob "benchmarks/runner/entry/*.c" "benchmarks/runner/entry/x/y.c" &&
      !glob "fixtures/**/*.c" "fixtures/x86/a.h" && !glob "IxCC.lean" "IxCC.leanx")
    "integrity glob accepted a non-match"

private def disassemblyTests : IO Unit := do
  let body := "   0:\t48 89 f8\tmov    rax,rdi\n   3:\tc3\tret"
  let dump := "/tmp/r12-rsp-push (bad)/object.o: file format elf64-x86-64\n" ++
    "0000000000000000 <rbx_pop>:\n" ++ body ++ "\n\t4: R_X86_64_PC32 r15\n"
  let actual := IxCC.Tools.X86Check.instructionText dump
  need (actual == body) "objdump filenames or symbols leaked into instruction checks"
  for register in ["rbx", "rbp", "rsp", "r12", "r13", "r14", "r15"] do
    let instruction := s!"   0:\t49 89 fc\tmov    {register},rdi\n"
    need ((IxCC.Tools.X86Check.instructionText instruction).contains register)
      "actual register use escaped the instruction check"
  need ((IxCC.Tools.X86Check.instructionText "   a:\t0f\t(bad)\n").contains "(bad)")
    "invalid instruction escaped the instruction check"

private def buildGraphTests (root : FilePath) : IO Unit := do
  IxCCTests.Tools.BuildGraph.run
  let checkGraph := IxCC.Tools.BuildGraph.check root
  checkGraph
  let api := root / "IxCC.lean"
  withFile api ("import IxCCTests.IxonV3.Run\n" ++ (← IO.FS.readFile api)) do
    rejects "stale source manifest" "Nix import manifest is stale" checkGraph
    let actual ← IxCC.Tools.BuildGraph.manifest root
    withFile (root / "nix/lean-modules.json") actual.pretty do
      rejects "production imports tests" "production imports regression module" checkGraph
  let proofs := root / "IxCCTests/Proofs.lean"
  withFile proofs ((← IO.FS.readFile proofs).replace
      "import IxCC.X86.ELFExamples\n" "") do
    rejects "missing moved proof module" "required proof aggregate no longer builds" do
      IxCC.Tools.BuildGraph.checkCoverage root (← IxCC.Tools.BuildGraph.manifest root)
  let fence := root / "IxCCTests/Fences/X86.lean"
  let source ← IO.FS.readFile fence
  let assertions ← IxCC.Tools.BuildGraph.axiomAssertions source
  need (!assertions.isEmpty) "empty axiom-fence regression fixture"
  withFile fence (source.replace assertions.head! "") do
    rejects "removed axiom assertion" "required axiom assertions or expected messages changed" checkGraph
  let runtime := root / "IxCCTests/IxonV3/Run.lean"
  withFile runtime ((← IO.FS.readFile runtime).replace "FAIL:" "REMOVED:") do
    rejects "removed runtime assertions" "runtime assertion inventory changed" checkGraph

/-- `ledger` with `relative`'s integrity hash re-recorded from `root`. -/
private def rehash (ledger : Json) (root : FilePath) (relative : String) : IO Json := do
  let integrity ← field ledger "integrity"
  let tracked ← replaceField (← field integrity "tracked_files") relative (toJson (← sha256 (root / relative)))
  replaceField ledger "integrity" (← replaceField integrity "tracked_files" tracked)

/-- `ledger` with the project file `relative` pinned at its current hash
(added if absent). -/
private def pinProject (ledger : Json) (root : FilePath) (relative : String) : IO Json := do
  let integrity ← field ledger "integrity"
  let tracked := (← field integrity "tracked_files").setObjVal! relative (toJson (← sha256 (root / relative)))
  replaceField ledger "integrity" (integrity.setObjVal! "tracked_files" tracked)

/-- `ledger` with the repository file `relative` pinned at its current hash
(added if absent). -/
private def pinRepository (ledger : Json) (repositoryRoot : FilePath) (relative : String) : IO Json := do
  let integrity ← field ledger "integrity"
  let pins := ((integrity.getObjVal? "repository_files").toOption.getD (Json.mkObj [])).setObjVal!
    relative (toJson (← sha256 (repositoryRoot / relative)))
  replaceField ledger "integrity" (integrity.setObjVal! "repository_files" pins)

private def withPolicy (ledger : Json) (key : String) (value : Json) : IO Json := do
  replaceField ledger "policy" ((← field ledger "policy").setObjVal! key value)

/-- `ledger` with its repository's workflow scope replaced by `scope`, or
removed (the default, `.github/workflows`) for `none`. -/
private def withScope (ledger : Json) (scope : Option (List String)) : IO Json := do
  let root ← field (← field (← field ledger "policy") "repository") "root"
  withPolicy ledger "repository" (Json.mkObj ([("root", root)] ++
    (match scope with | some paths => [("workflows", toJson paths)] | none => [])))

/-- The repository around the project (`repositoryRoot`): an explicit
`flake.lock` in place of its own, and scoped workflows, with the remote actions
of the repository-local actions and reusable workflows they use. -/
private def repositoryTests (temporary repositoryRoot root blake : FilePath) (ledger : Json) : IO Unit := do
  let overrides := [("Blake3", blake.toString)]
  let audited : IO Unit := audit root overrides (some "6.3.0")
  let auditedWith (flakeLock : FilePath) : IO Unit := audit root overrides (some "6.3.0") none (some flakeLock)
  let ledgerPath := root / "docs/trusted-externs.json"
  -- an explicit flake.lock replaces the repository's
  let outerLock := temporary / "outer.lock"
  copyFile (repositoryRoot / "flake.lock") outerLock
  auditedWith outerLock
  let rev ← strField (← field (← field (← field (← readJson outerLock) "nodes") "lean4-nix") "locked") "rev"
  withFile outerLock ((← IO.FS.readFile outerLock).replace rev (String.ofList (List.replicate 40 '0'))) do
    rejects "flake lock override" "flake node/revision inventory drifted" (auditedWith outerLock)
  rejects "missing flake lock" "missing.lock" (auditedWith (temporary / "missing.lock"))
  -- a scoped workflow, followed through a reusable workflow and a local action
  let pinned := String.join (List.replicate 40 "1")
  let workflows := repositoryRoot / ".github" / "workflows"
  let setup := repositoryRoot / ".github" / "actions" / "regression-setup"
  IO.FS.createDirAll workflows
  IO.FS.createDirAll setup
  let scopedWorkflow := workflows / "regression-scoped.yml"
  IO.FS.writeFile (workflows / "regression-outer.yml")
    "jobs:\n  test:\n    steps:\n      - uses: actions/checkout@main\n"
  IO.FS.writeFile scopedWorkflow ("jobs:\n  local:\n    uses: ./.github/workflows/regression-reusable.yml\n" ++
    "  test:\n    steps:\n      - uses: ./.github/actions/regression-setup\n")
  IO.FS.writeFile (workflows / "regression-reusable.yml")
    "jobs:\n  test:\n    steps:\n      - uses: $/.github/actions/regression-setup\n"
  IO.FS.writeFile (setup / "action.yml")
    s!"runs:\n  using: composite\n  steps:\n    - uses: reviewed/action@{pinned} # v1\n"
  let reviewed (ledger : Json) : IO Json := replaceField ledger "ci_actions" (Json.arr #[Json.mkObj
    [("repository", toJson "reviewed/action"), ("commit", toJson pinned)]])
  let scope := some [".github/workflows/regression-scoped.yml"]
  -- a configured workflow file is pinned in full (`integrity.repository_files`)
  let pinScoped (ledger : Json) : IO Json :=
    pinRepository ledger repositoryRoot ".github/workflows/regression-scoped.yml"
  withFile ledgerPath (← pinScoped (← reviewed (← withScope ledger scope))).compress do
    audited
  withFile ledgerPath (← reviewed (← withScope ledger scope)).compress do
    rejects "unpinned configured workflow" "is not pinned in integrity.repository_files" audited
  withFile ledgerPath (← pinScoped (← reviewed (← withScope ledger scope))).compress do
    withFile scopedWorkflow ((← IO.FS.readFile scopedWorkflow) ++ "# edited\n") do
      rejects "edited configured workflow" "repository file .github/workflows/regression-scoped.yml changed" audited
  withFile ledgerPath (← pinScoped (← withScope ledger scope)).compress do
    rejects "remote action of a local action" "CI action inventory drifted" audited
  withFile ledgerPath (← reviewed (← withScope ledger none)).compress do
    rejects "unscoped repository workflows" "unpinned CI action" audited
  withFile ledgerPath (← reviewed (← withScope ledger (some [".github/workflows/absent.yml"]))).compress do
    rejects "missing scoped workflow" "missing configured CI workflow path" audited
  withFile scopedWorkflow "jobs:\n  test:\n    steps:\n      - uses: ./.github/actions/absent\n" do
    withFile ledgerPath (← pinScoped (← reviewed (← withScope ledger scope))).compress do
      rejects "missing local action" "missing local action or workflow" audited
  -- a local action outside the repository
  IO.FS.createDirAll (temporary / "escape")
  IO.FS.writeFile (temporary / "escape" / "action.yml") "runs:\n  using: composite\n  steps: []\n"
  withFile scopedWorkflow "jobs:\n  test:\n    steps:\n      - uses: ./../escape\n" do
    withFile ledgerPath (← pinScoped (← reviewed (← withScope ledger scope))).compress do
      rejects "escaping local action" "local action escapes the repository" audited
  -- the repository's toolchain is the project's
  withFile (repositoryRoot / "lean-toolchain") "leanprover/lean4:v4.0.0\n" do
    rejects "repository toolchain" "the repository's lean-toolchain differs from the project's" audited

/-- The pure Lean dependency is a package of the enclosing workspace, pinned
by its path (`../IxCK` from `IxCC/` inside ix): the manifest and the ledger
must agree on it, the path must be relative and hold that package, and the pin
records nothing else. -/
private def workspaceDependencyTests (root blake : FilePath) (ledger : Json) : IO Unit := do
  let audited : IO Unit := audit root [("Blake3", blake.toString)] (some "6.3.0")
  let ledgerPath := root / "docs/trusted-externs.json"
  let manifestPath := root / "lake-manifest.json"
  let manifest ← readJson manifestPath
  let dependency := (← arrField ledger "lean_dependencies")[0]!
  let package ← strField dependency "lake_package"
  let recorded ← strField (← field dependency "pins") "workspace_path"
  let pathManifest (dir : String) : IO String := do
    let packages ← (← arrField manifest "packages").mapM fun entry => do
      if (← strField entry "name") != package then return entry
      return entry.setObjVal! "dir" (toJson dir)
    return (← replaceField manifest "packages" (Json.arr packages)).compress
  let pinned (pins : List (String × Json)) : IO Json := do
    let entries ← (← arrField ledger "lean_dependencies").mapM fun entry =>
      replaceField entry "pins" (Json.mkObj pins)
    replaceField ledger "lean_dependencies" (Json.arr entries)
  -- the manifest and the ledger record the dependency by path; the ledger
  -- re-records the manifest's hash
  let withPaths (manifestDir : String) (pins : List (String × Json)) (action : IO Unit) : IO Unit := do
    withFile manifestPath (← pathManifest manifestDir) do
      withFile ledgerPath (← rehash (← pinned pins) root "lake-manifest.json").compress action
  let workspace := [("workspace_path", toJson recorded)]
  withPaths recorded workspace audited
  withPaths "../Elsewhere" workspace do
    rejects "workspace manifest path" "Lake dependency inventory drifted" audited
  withPaths recorded (workspace ++ [("lake_rev", toJson (String.ofList (List.replicate 40 '0')))]) do
    rejects "workspace pin with a revision" "pins only its path" audited
  withPaths "/ix/IxCK" [("workspace_path", toJson "/ix/IxCK")] do
    rejects "absolute workspace path" "must be relative" audited
  withFile (root / recorded / "lakefile.lean") "import Lake\nopen Lake DSL\n\npackage other where\n" do
    rejects "workspace path holding another package" "does not hold its lakefile.lean" audited
  -- a pure Lean dependency is a workspace package: a git pin is refused
  let gitPinned ← (← arrField ledger "lean_dependencies").mapM fun entry =>
    replaceField entry "source_kind" (toJson "git")
  withFile ledgerPath (← replaceField ledger "lean_dependencies" (Json.arr gitPinned)).compress do
    rejects "git-pinned pure dependency" "unknown lean dependency source_kind git" audited

private def regressionTests (source blakeSource : FilePath) : IO Unit := IO.FS.withTempDir fun temporary => do
  let repositoryRoot := temporary / "repository"
  let root ← cloneWorkspace source repositoryRoot
  let blake := temporary / "Blake3"
  let originalLedger ← readJson (root / "docs/trusted-externs.json")
  -- the pure Lean dependency's recorded closure, under the source directory
  -- its module names are relative to
  let dependency := (← arrField originalLedger "lean_dependencies")[0]!
  let ixCKSources := root / (← strField (← field dependency "pins") "workspace_path") /
    (← strField dependency "source_dir")
  let ixClosure := (← pairs (← field dependency "closure")).map (·.1)
  need (!ixClosure.isEmpty) "test fixture lost the ix-ck closure"
  for path in (← files blakeSource true).filter (·.extension == some "lean") do
    copyRelative blakeSource blake path
  let interfaces ← arrField originalLedger "native_interfaces"
  let mut cargoRelative := ""
  let mut blake3Version := ""
  for entry in interfaces do
    if (entry.getObjValAs? String "lake_package").toOption == some "Blake3" then
      cargoRelative ← strField (← field entry "cargo_lock") "path"
      blake3Version ← strField (← field entry "pins") "blake3_version"
  need (!cargoRelative.isEmpty) "test fixture lost the Blake3 Cargo lock"
  copyFile (blakeSource / cargoRelative) (blake / cargoRelative)
  let check := audit root [("Blake3", blake.toString)] (some "6.3.0")
  check
  withFile (root / "IxCC/AuditRegression.lean") "import IxCK.Ixon.Verify\n" do
    rejects "unledgered pure dependency import" "imports of pure Lean dependencies drifted" check
  let codec := ixCKSources / ixClosure.head!
  withFile codec ((← IO.FS.readFile codec) ++ "\n") do
    rejects "pure dependency source drift" "changed" check
  withFile codec ((← IO.FS.readFile codec) ++ "\n@[extern \"rogue\"] opaque rogue : Nat\n") do
    -- with its hash re-recorded, the native declaration itself is refused
    let entries ← (← arrField originalLedger "lean_dependencies").mapM fun entry => do
      let closure ← replaceField (← field entry "closure") ixClosure.head! (toJson (← sha256 codec))
      replaceField entry "closure" closure
    let ledger ← replaceField originalLedger "lean_dependencies" (Json.arr entries)
    withFile (root / "docs/trusted-externs.json") ledger.compress do
      rejects "pure dependency native code" "declares native symbols" check
  -- the reviewed dependency csimp inventory is exact: dropping a listed
  -- theorem is refused
  let dropped ← (← arrField originalLedger "lean_dependencies").mapM fun entry => do
    let listed ← arrField entry "csimp_theorems"
    need (!listed.isEmpty) "test fixture lost the dependency csimp inventory"
    replaceField entry "csimp_theorems" (Json.arr listed.pop)
  withFile (root / "docs/trusted-externs.json")
      (← replaceField originalLedger "lean_dependencies" (Json.arr dropped)).compress do
    rejects "dropped dependency csimp" "csimp inventory drifted" check
  -- a csimp theorem added to the dependency closure, with its hash
  -- re-recorded: refused until the ledger lists it
  let csimpRecord (file : String) : Json := Json.mkObj [("file", toJson file),
    ("theorem", toJson "rogue_eq"), ("replaces", toJson "rogue"), ("replacement", toJson "rogueFast")]
  let csimpTheorem := "@[csimp] theorem rogue_eq : @rogue = @rogueFast := rfl\n"
  withFile codec ((← IO.FS.readFile codec) ++ "\n" ++ csimpTheorem) do
    let rehashed (records : Array Json) : IO Json := do
      let entries ← (← arrField originalLedger "lean_dependencies").mapM fun entry => do
        let closure ← replaceField (← field entry "closure") ixClosure.head! (toJson (← sha256 codec))
        let listed ← arrField entry "csimp_theorems"
        replaceField (← replaceField entry "closure" closure) "csimp_theorems" (Json.arr (listed ++ records))
      replaceField originalLedger "lean_dependencies" (Json.arr entries)
    withFile (root / "docs/trusted-externs.json") (← rehashed #[]).compress do
      rejects "unlisted dependency csimp" "csimp inventory drifted" check
    withFile (root / "docs/trusted-externs.json") (← rehashed #[csimpRecord ixClosure.head!]).compress do
      check
  buildGraphTests root
  let regression := root / "IxCC/AuditRegression.lean"
  -- the project's own csimp theorems are inventoried the same way
  withFile regression csimpTheorem do
    rejects "unlisted project csimp" "project csimp inventory drifted" check
    let existingCsimps ← arrField originalLedger "csimp_theorems"
    let listed ← replaceField originalLedger "csimp_theorems"
      (Json.arr (existingCsimps ++ #[csimpRecord "IxCC/AuditRegression.lean"]))
    -- the integrity rule covers the new file: unpinned, it fails last
    withFile (root / "docs/trusted-externs.json") listed.compress do
      rejects "unpinned covered source" "files the rule covers have no pin" check
    withFile (root / "docs/trusted-externs.json")
      (← pinProject listed root "IxCC/AuditRegression.lean").compress check
  for token in ["axiom", "sorry", "native_decide"] do
    withFile regression s!"{token} injected\n" do
      rejects token (token ++ " is not allowed") check
  withFile regression "@[extern \"unexpected_symbol\"] opaque rogue : Nat\n" do
    rejects "project extern drift" "project extern inventory drifted" check
  withFile regression "import UnreviewedPackage\n" do
    rejects "external import drift" "external Lean import roots drifted" check
  withFile regression "def drift := Blake3.Rust.internalVersion\n" do
    rejects "native entrypoint drift" "qualified uses of Blake3.Rust drifted" check
  -- Every remote action of a scoped workflow must be pinned and reviewed into
  -- the ledger (`ci_actions`).
  let workflow := repositoryRoot / ".github/workflows/regression.yml"
  let repositoryPolicy ← field (← field originalLedger "policy") "repository"
  let scope ← (← arrField repositoryPolicy "workflows").toList.mapM string
  let scopedLedger ← withScope originalLedger (some (scope ++ [".github/workflows/regression.yml"]))
  let withWorkflow (content : String) (action : IO Unit) : IO Unit :=
    withFile workflow content do
      withFile (root / "docs/trusted-externs.json")
        (← pinRepository scopedLedger repositoryRoot ".github/workflows/regression.yml").compress action
  withWorkflow "jobs:\n  test:\n    steps:\n      - run: true\n" check
  withWorkflow "jobs:\n  test:\n    steps:\n      - uses: actions/checkout@main\n" do
    rejects "unpinned CI action" "unpinned CI action" check
  withWorkflow ("jobs:\n  test:\n    steps:\n      - uses: \"unreviewed/action@" ++
      String.join (List.replicate 40 "1") ++ "\"\t# reviewed\n") do
    rejects "new quoted pinned CI action" "CI action inventory drifted" check
  withWorkflow ("jobs:\n  test:\n    steps:\n      - uses: unreviewed/action@" ++
      String.join (List.replicate 40 "1") ++ "\n") do
    rejects "new pinned CI action" "CI action inventory drifted" check
  -- the check workflow is pinned in full: narrowing the checks it runs, or
  -- dropping its pin, fails
  let checkWorkflow := repositoryRoot / ".github/workflows/ixcc.yml"
  let original ← IO.FS.readFile checkWorkflow
  let narrowed := original.replace "name == \"ixcc-\"" "name == \"ixcc-\" && name != \"ixcc-census\""
  need (narrowed != original) "test fixture: ixcc.yml no longer selects the ixcc- checks by prefix"
  withFile checkWorkflow narrowed do
    rejects "narrowed check workflow" "repository file .github/workflows/ixcc.yml changed" check
  let integrity ← field originalLedger "integrity"
  let unpinned ← replaceField originalLedger "integrity"
    (integrity.setObjVal! "repository_files" (Json.mkObj []))
  withFile (root / "docs/trusted-externs.json") unpinned.compress do
    rejects "unpinned check workflow" "ixcc.yml is not pinned in integrity.repository_files" check
  -- the required-check inventory is exactly nix/checks.nix's attributes
  let checksNix := root / "nix/checks.nix"
  let checksSource ← IO.FS.readFile checksNix
  let renamed := checksSource.replace "    census = mkCheck" "    census-renamed = mkCheck"
  need (renamed != checksSource) "test fixture: nix/checks.nix has no census check"
  withFile checksNix renamed do
    withFile (root / "docs/trusted-externs.json") (← rehash originalLedger root "nix/checks.nix").compress do
      rejects "check renamed in nix/checks.nix" "required check inventory" check
  let required ← arrField originalLedger "required_checks"
  withFile (root / "docs/trusted-externs.json")
      (← replaceField originalLedger "required_checks" (Json.arr (required.push (toJson "absent")))).compress do
    rejects "required check absent from nix/checks.nix" "required check inventory" check
  -- the integrity rule: a covered file without a pin, and a pin outside the rule
  withFile (root / "fixtures/x86/rogue_harness.c") "int main(void) { return 0; }\n" do
    rejects "unpinned covered harness" "files the rule covers have no pin" check
  withFile (root / "docs/regression-notes.md") "notes\n" do
    withFile (root / "docs/trusted-externs.json")
        (← pinProject originalLedger root "docs/regression-notes.md").compress do
      rejects "pin outside the integrity rule" "pinned files the rule does not cover" check
  let build := root / "nix/build.nix"
  withFile build ((← IO.FS.readFile build) ++ "\n") do
    rejects "integrity drift" "nix/build.nix changed" check
  let invalidSchema ← replaceField originalLedger "schema_version" (toJson (3 : Nat))
  withFile (root / "docs/trusted-externs.json") invalidSchema.compress do
    rejects "ledger schema" "unsupported ledger schema_version" check
  -- A reviewed lakefile hash must not let a new executable escape inventory.
  let lake := root / "lakefile.lean"
  let added := (← IO.FS.readFile lake) ++
    "\nlean_exe regression where\n  root := " ++ String.singleton (Char.ofNat 96) ++ "Regression\n"
  withFile lake added do
    let integrity ← field originalLedger "integrity"
    let tracked ← replaceField (← field integrity "tracked_files") "lakefile.lean" (toJson (← sha256 lake))
    let ledger ← replaceField originalLedger "integrity" (← replaceField integrity "tracked_files" tracked)
    withFile (root / "docs/trusted-externs.json") ledger.compress do
      withFile (root / "Regression.lean") "axiom outsideLibrary : False\n" do
        rejects "new executable inventory" "axiom is not allowed" check
  withFile (blake / "Sibling.lean") "@[extern \"unreviewed_sibling\"] opaque sibling : Nat\n" do
    rejects "dependency sibling extern" "package-tree extern inventory drifted" check
  let cargo := blake / cargoRelative
  let original ← IO.FS.readFile cargo
  let record (version : String) := s!"\n[[package]]\nname = \"blake3\"\nversion = \"{version}\"\n"
  for (contents, diagnostic) in [(original ++ record blake3Version, "Cargo package records"),
      (original ++ record "999.0.0", "Cargo package inventory drifted"),
      ("package = [", "invalid Cargo TOML")] do
    withFile cargo contents do
      rejects "Cargo hash drift" "Cargo lockfile hash drifted" check
      let entries ← interfaces.mapM fun entry => do
        if (entry.getObjValAs? String "lake_package").toOption != some "Blake3" then return entry
        let data ← replaceField (← field entry "cargo_lock") "sha256" (toJson (← sha256 cargo))
        replaceField entry "cargo_lock" data
      let ledger ← replaceField originalLedger "native_interfaces" (Json.arr entries)
      withFile (root / "docs/trusted-externs.json") ledger.compress do
        rejects "Cargo metadata drift" diagnostic check
  repositoryTests temporary repositoryRoot root blake originalLedger
  workspaceDependencyTests root blake originalLedger

def main (args : List String) : IO UInt32 := cli "Lean check regressions failed" do
  let args ← checked (parseArgs ["--root", "--blake3"] args)
  let root ← IO.FS.realPath (option args "--root" ".")
  let blake ← IO.FS.realPath (option args "--blake3" (root / ".lake/packages/Blake3").toString)
  lexerTests
  inventoryTests
  disassemblyTests
  regressionTests root blake
  IO.println "Lean check regressions ok: source lexing (including native evaluation), root/native/csimp inventories, Nix check inventory, build graph, proof/runtime coverage, integrity pins and rule, Cargo, CI, repository and workspace-dependency rejection paths"
