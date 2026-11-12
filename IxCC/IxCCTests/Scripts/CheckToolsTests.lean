import IxCC.Tools.TrustLedger
import IxCC.Tools.X86Check
import IxCC.Tools.BuildGraph
import IxCCTests.Tools.BuildGraph

/-! Regression tests for the trust gate's failure paths. Mutations are confined
to fresh temporary copies; the source tree and reviewed ledger are never edited. -/

open Lean System IxCC.Tools.Check IxCC.Tools.SourceScan
open IxCC.Tools.TrustLedger

/-- `action` fails, and its error contains every one of `fragments`. -/
private def rejectsAll (label : String) (fragments : List String) (action : IO Unit) : IO Unit := do
  let error ← try action; pure none catch error => pure (some error.toString)
  let some error := error | throw (IO.userError s!"{label}: unexpectedly accepted")
  need (fragments.all fun fragment => error.contains fragment)
    s!"{label}: rejected for the wrong reason: {error}"

private def rejects (label fragment : String) (action : IO Unit) : IO Unit :=
  rejectsAll label [fragment] action

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

/-- The index of the ledger's one pure Lean dependency whose `source_kind` is
`kind`. -/
private def dependencyIndex (ledger : Json) (kind : String) : IO Nat := do
  let entries ← arrField ledger "lean_dependencies"
  let mut found := none
  for index in [:entries.size] do
    if (← strField entries[index]! "source_kind") == kind then
      need found.isNone s!"test fixture has several {kind} dependencies"
      found := some index
  present found s!"test fixture has no {kind} dependency"

/-- `ledger` with its pure Lean dependency at `index` replaced by `change` of it. -/
private def changeDependency (ledger : Json) (index : Nat) (change : Json → IO Json) : IO Json := do
  let entries ← arrField ledger "lean_dependencies"
  replaceField ledger "lean_dependencies" (Json.arr (entries.set! index (← change entries[index]!)))

/-- `ledger` with the closure file `relative` of its pure Lean dependency at
`index` re-recorded from `path`. -/
private def rehashClosure (ledger : Json) (index : Nat) (relative : String) (path : FilePath) :
    IO Json :=
  changeDependency ledger index fun entry => do
    replaceField entry "closure" (← replaceField (← field entry "closure") relative (toJson (← sha256 path)))

/-- Copy what the audit reads of the project at `source` and of the
repository around it into `target`, the copy's repository root: the project's
Lean sources, tracked files and ledger, at the project's path in the
repository; each workspace dependency's lakefile and recorded closure (a git
dependency is read from the copy `--blake3` gives); the repository's
`flake.lock` and `lean-toolchain`; and its `.github` (workflows and local
actions).
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
    let .workspace directory ← leanSource entry | continue
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
  -- a dependency's constructor named `axiom` is not an axiom declaration;
  -- every declaration form still is
  checked (hygieneDependency (← checked (scan
    "inductive Spec where\n  | axiom (n : Nat)\n  | other\ndef k : Spec := .axiom 0\ndef m : Spec → Nat\n  | .axiom n => n\n  | _ => 0\n")))
  for source in ["axiom bad : False\n", "private axiom bad : False\n", "@[simp] axiom bad : False\n",
      "noncomputable axiom bad : False\n"] do
    rejects s!"dependency {source}" "axiom is not allowed" do
      checked (hygieneDependency (← checked (scan source)))
  rejects "a project constructor named axiom" "axiom is not allowed" do
    checked (hygiene (← checked (scan "inductive Spec where\n  | axiom (n : Nat)\n")))
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
  -- the implemented_by inventory: attributes on a def or an opaque and the
  -- attribute command; comments and literals ignored; any other spelling refused
  let implInput := "/- @[implemented_by hiddenImpl] def hidden : Nat := 0 -/\n" ++
    "def text := \"@[implemented_by quotedImpl]\"\n" ++
    "@[inline, implemented_by fImpl] private def f : Nat := 0\n" ++
    "@[implemented_by gImpl] opaque g : Nat\nattribute [implemented_by hImpl] h\n"
  need ((← checked (implementedBys (← checked (scan implInput)))) ==
      [("f", "fImpl"), ("g", "gImpl"), ("h", "hImpl")]) "implemented_by inventory changed"
  rejects "implemented_by on a theorem" "not on a def or an opaque" do
    let _ ← checked (implementedBys (← checked (scan "@[implemented_by tImpl] theorem t : True := trivial")))
  rejects "implemented_by outside an attribute" "outside an attribute" do
    let _ ← checked (implementedBys (← checked (scan "def x := implemented_by")))
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
  -- every spelling of the import command the module system has, and module
  -- names with guillemet-quoted components; a keyword without a module name
  -- yields a name no module has
  let importInput := "module\nimport A.B\npublic import C\nmeta import D.E\npublic meta import F\n" ++
    "import all G\npublic import all H.I\nimport «J».K\nimport L.«M»\nimport «N»\n" ++
    "-- import Hidden\ndef s := \"import Quoted\"\n"
  need (imports (← checked (scan importInput)) == ["A.B", "C", "D.E", "F", "G", "H.I", "J.K", "L.M", "N"])
    "import inventory changed"
  need ((imports (← checked (scan "def x := 1\nimport\n"))).all (·.startsWith "<unreadable import"))
    "an import without a module name was not refused"
  -- the names under a module root, outside import commands, comments and literals
  need (namesUnder (← checked (scan ("import Blake3.Pure\nopen Blake3\ndef f := Blake3.Pure.hash x\n" ++
      "def g := «Blake3».Rust.v\n-- Blake3.Rust\ndef s := \"Blake3.C\"\ndef h := Blake3NoCollision\n")))
      "Blake3" == ["Blake3", "Blake3.Pure.hash", "Blake3"])
    "names under a module root changed"
  -- each native_decide with the declaration that holds it, qualified by the
  -- open namespaces
  let decideInput := "theorem top : 1 = 1 := by native_decide\nnamespace A.B\npublic section\n" ++
    "namespace C\ndef f (h : 2 < 3 := by native_decide) := 0\nend C\nend\nend A.B\nmutual\n" ++
    "def g := by native_decide\nend\ntheorem _root_.r : True := by native_decide\n"
  need ((← checked (nativeDecideSites (← checked (scan decideInput)))) ==
      [("top", 1), ("A.B.C.f", 5), ("g", 10), ("r", 12)]) "native_decide sites changed"
  for (source, fragment) in [("example : 1 = 1 := by native_decide\n", "outside a named declaration"),
      ("def f := 0\nvariable (h : 1 = 1 := by native_decide)\n", "outside a named declaration"),
      ("instance : Inhabited Nat := by native_decide\n", "outside a named declaration"),
      ("namespace A\nend A\nend\n", "end closes no open scope")] do
    rejects s!"native_decide site of {source}" fragment do
      discard (checked (nativeDecideSites (← checked (scan source))))
  -- a dependency's hygiene leaves native_decide to the site inventory and
  -- refuses every other spelling of native evaluation
  need ((← checked (dependencyHygiene (← checked (scan "def f (h : 1 = 1 := by native_decide) := 0\n")))) ==
    [("f", 1)]) "dependency hygiene lost a native_decide site"
  for (source, fragment) in [("theorem t : 2 + 2 = 4 := by decide +native", "decide +native is not allowed"),
      ("theorem t : True := Lean.ofReduceBool _ _ rfl", "Lean.ofReduceBool is not allowed"),
      ("theorem t : False := sorry", "sorry is not allowed")] do
    rejects s!"dependency {source}" fragment do discard (checked (dependencyHygiene (← checked (scan source))))

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
  -- the grounding library and the kernel's model stay beside production and the shared build
  let offend (path : FilePath) (imp : String) (label fragment : String) : IO Unit := do
    withFile path (s!"import {imp}\n" ++ (← IO.FS.readFile path)) do
      let actual ← IxCC.Tools.BuildGraph.manifest root
      withFile (root / "nix/lean-modules.json") actual.pretty do
        rejects label fragment checkGraph
  offend api "IxCCGrounding.Check" "production imports the grounding library"
    "production imports the grounding library"
  offend api "IxCK.Kernel.Denotes" "production imports the kernel's model"
    "production imports the kernel's model"
  offend (root / "IxCCTests/IxonV3/Main.lean") "IxCCGrounding.Check"
    "a shared program imports the grounding library" "shared program tests-ixon-v3 imports the grounding library"
  offend (root / "IxCCTests/Proofs.lean") "IxCK.Kernel.Denotes"
    "the proof aggregate imports the kernel's model" "the shared proof aggregate imports the kernel's model"
  let gfence := root / IxCC.Tools.BuildGraph.groundingFence
  let gsource ← IO.FS.readFile gfence
  let gassertions ← IxCC.Tools.BuildGraph.axiomAssertions gsource
  need (!gassertions.isEmpty) "empty grounding fence"
  withFile gfence (gsource.replace gassertions.head! "") do
    rejects "removed grounding axiom assertion" "grounding axiom assertions or expected messages changed"
      checkGraph

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

/-- The workspace dependency (the kernel package) is pinned by its path
(`../IxCK` from `IxCC/` inside ix): the manifest and the ledger must agree on
it, the path must be relative and hold that package, and the pin records
nothing else. -/
private def workspaceDependencyTests (root blake : FilePath) (ledger : Json) : IO Unit := do
  let audited : IO Unit := audit root [("Blake3", blake.toString)] (some "6.3.0")
  let ledgerPath := root / "docs/trusted-externs.json"
  let manifestPath := root / "lake-manifest.json"
  let manifest ← readJson manifestPath
  let index ← dependencyIndex ledger "workspace_path"
  let dependency := (← arrField ledger "lean_dependencies")[index]!
  let package ← strField dependency "lake_package"
  let recorded ← strField (← field dependency "pins") "workspace_path"
  let pathManifest (dir : String) : IO String := do
    let packages ← (← arrField manifest "packages").mapM fun entry => do
      if (← strField entry "name") != package then return entry
      return entry.setObjVal! "dir" (toJson dir)
    return (← replaceField manifest "packages" (Json.arr packages)).compress
  let pinned (pins : List (String × Json)) : IO Json :=
    changeDependency ledger index fun entry => replaceField entry "pins" (Json.mkObj pins)
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
  -- a workspace package recorded as git-pinned keeps a workspace pin, which
  -- is not a git dependency's; an unknown kind is refused
  for (kind, fragment) in [("git", "a git dependency pins only lake_rev and flake_node"),
      ("registry", "unknown lean dependency source_kind registry")] do
    withFile ledgerPath (← changeDependency ledger index fun entry =>
        replaceField entry "source_kind" (toJson kind)).compress do
      rejects s!"workspace dependency recorded as {kind}" fragment audited

/-- The git-pinned pure dependency (the Blake3 package, of which IxCC takes
`Blake3/Pure.lean` and the root module `Blake3.lean`): its revision against
the ledger, `lake-manifest.json` and `flake.lock`; the package its root holds;
its closure's hashes, hygiene and admitted `native_decide`s; and the project's
imports and names under its root, the audit that refuses a native backend. -/
private def gitDependencyTests (repositoryRoot root blake : FilePath) (ledger : Json) : IO Unit := do
  let check : IO Unit := audit root [("Blake3", blake.toString)] (some "6.3.0")
  let ledgerPath := root / "docs/trusted-externs.json"
  let index ← dependencyIndex ledger "git"
  let entry := (← arrField ledger "lean_dependencies")[index]!
  need ((← strField entry "lake_package") == "Blake3") "test fixture: the git dependency is not Blake3"
  let rev ← strField (← field entry "pins") "lake_rev"
  let node ← strField (← field entry "pins") "flake_node"
  let zero := String.ofList (List.replicate 40 '0')
  let regression := root / "IxCC/AuditRegression.lean"
  -- the project imports under Blake3 exactly Blake3.Pure, whatever the spelling
  -- of the import command or of the module name
  for (source, mod) in [("import Blake3.Rust", "Blake3.Rust"), ("import Blake3.C", "Blake3.C"),
      ("import Blake3", "Blake3"), ("public import Blake3.Rust", "Blake3.Rust"),
      ("meta import Blake3.C", "Blake3.C"), ("public meta import Blake3.Rust", "Blake3.Rust"),
      ("import all Blake3.C", "Blake3.C"), ("import «Blake3».Rust", "Blake3.Rust"),
      ("import Blake3.«C»", "Blake3.C")] do
    withFile regression s!"{source}\n" do
      rejects source s!"imports {mod}; the project may import only [Blake3.Pure] under Blake3" check
  withFile ledgerPath (← changeDependency ledger index fun entry =>
      replaceField entry "imported_modules" (toJson ["Blake3.Pure", "Blake3"])).compress do
    rejects "a recorded module the project does not import"
      "recorded module Blake3 is not imported by the project" check
  -- the project's names under Blake3 are exactly Blake3.Pure.hash: a backend's
  -- entry point, the generic interface or an open of the root is refused
  -- (what the native entry's qualified-use inventory guarded)
  for (source, name) in [("def drift := Blake3.Rust.internalVersion\n", "Blake3.Rust.internalVersion"),
      ("def drift := Blake3.HasherOps.hash\n", "Blake3.HasherOps.hash"), ("open Blake3\n", "\"Blake3\"")] do
    withFile regression source do
      rejectsAll s!"name {name}" ["qualified uses of Blake3 drifted", name] check
  -- the revision: the ledger's, the manifest's and the flake lock's node agree
  withFile ledgerPath (← changeDependency ledger index fun entry => do
      replaceField entry "pins" ((← field entry "pins").setObjVal! "lake_rev" (toJson zero))).compress do
    rejects "changed revision in the ledger" s!"the ledger pins the git revision {zero}" check
  let manifestPath := root / "lake-manifest.json"
  let manifest ← IO.FS.readFile manifestPath
  need ((manifest.replace rev zero) != manifest) "test fixture: lake-manifest.json lacks the Blake3 revision"
  withFile manifestPath (manifest.replace rev zero) do
    withFile ledgerPath (← rehash ledger root "lake-manifest.json").compress do
      rejectsAll "changed revision in lake-manifest.json"
        [zero, s!"the ledger pins the git revision {rev}"] check
  let flakeLock := repositoryRoot / "flake.lock"
  let lock ← IO.FS.readFile flakeLock
  need ((lock.replace rev zero) != lock) "test fixture: flake.lock lacks the Blake3 revision"
  withFile flakeLock (lock.replace rev zero) do
    -- with the node inventory re-recorded, the dependency's own pin refuses it
    let integrity ← field ledger "integrity"
    let nodes := (← field integrity "flake_nodes").setObjVal! node (toJson zero)
    withFile ledgerPath (← replaceField ledger "integrity" (integrity.setObjVal! "flake_nodes" nodes)).compress do
      rejects "changed revision in flake.lock" s!"Blake3: flake.lock node {node} is at {zero}, the ledger pins {rev}" check
  withFile ledgerPath (← changeDependency ledger index fun entry => do
      replaceField entry "pins" ((← field entry "pins").setObjVal! "flake_node" (toJson "absent-node"))).compress do
    rejects "absent flake node" "Blake3: flake.lock has no node absent-node" check
  withFile ledgerPath (← changeDependency ledger index fun entry => do
      replaceField entry "pins" ((← field entry "pins").setObjVal! "blake3_lean_rev" (toJson rev))).compress do
    rejects "git pin with another field" "a git dependency pins only lake_rev and flake_node" check
  withFile (blake / "lakefile.lean") "import Lake\nopen Lake DSL\n\npackage other where\n" do
    rejects "git dependency root holding another package" "does not hold its lakefile.lean" check
  -- the two closure files are pinned by hash
  let pure := blake / "Blake3/Pure.lean"
  let shared := blake / "Blake3.lean"
  withFile pure ((← IO.FS.readFile pure) ++ "\n") do
    rejects "changed Blake3/Pure.lean" "Blake3: Blake3/Pure.lean changed" check
  withFile shared ((← IO.FS.readFile shared) ++ "\n") do
    rejects "changed Blake3.lean" "Blake3: Blake3.lean changed" check
  -- with its hash re-recorded, what a closure file holds is still audited
  for (text, label, fragment) in [
      ("\n@[extern \"rogue_blake3\"] opaque rogue : Nat\n", "an extern", "Blake3: Blake3/Pure.lean declares native symbols"),
      ("\npublic import Blake3.Rust\n", "a backend imported",
        "Blake3: Blake3/Pure.lean imports Blake3.Rust outside the recorded closure"),
      ("\ntheorem rogue : 2 + 2 = 4 := by decide +native\n", "decide +native", "decide +native is not allowed"),
      ("\ntheorem rogue : True := Lean.ofReduceBool _ _ rfl\n", "Lean.ofReduceBool", "Lean.ofReduceBool is not allowed"),
      ("\ntheorem rogue : 2 + 2 = 4 := by native_decide\n", "a native_decide",
        "native_decide in rogue is not a listed native_decide site")] do
    withFile pure ((← IO.FS.readFile pure) ++ text) do
      withFile ledgerPath (← rehashClosure ledger index "Blake3/Pure.lean" pure).compress do
        rejects s!"{label} in Blake3/Pure.lean" fragment check
  -- the native_decides of Blake3.lean are exactly the three listed, occurrence
  -- by occurrence
  withFile shared ((← IO.FS.readFile shared) ++ "\ntheorem rogue_nd : 2 + 2 = 4 := by native_decide\n") do
    withFile ledgerPath (← rehashClosure ledger index "Blake3.lean" shared).compress do
      rejects "a fourth native_decide" "native_decide in rogue_nd is not a listed native_decide site" check
  let sharedText ← IO.FS.readFile shared
  let bound := "(h : length < 2 ^ System.Platform.numBits := by native_decide) :"
  let doubled := sharedText.replace bound
    "(h : length < 2 ^ System.Platform.numBits := by native_decide) (_h2 : 0 < 1 := by native_decide) :"
  need (doubled != sharedText) "test fixture: Blake3.lean no longer bounds finalizeWithLength's length"
  withFile shared doubled do
    withFile ledgerPath (← rehashClosure ledger index "Blake3.lean" shared).compress do
      rejects "a second native_decide in a listed declaration"
        "native_decide in Blake3.HasherOps.finalizeWithLength is not a listed native_decide site" check
  withFile shared ((← IO.FS.readFile shared) ++ "\nexample : 2 + 2 = 4 := by native_decide\n") do
    withFile ledgerPath (← rehashClosure ledger index "Blake3.lean" shared).compress do
      rejects "a native_decide in no declaration" "native_decide outside a named declaration" check
  let sites ← arrField entry "native_decide_sites"
  need (sites.size == 3) "test fixture: Blake3's native_decide sites are not three"
  withFile ledgerPath (← changeDependency ledger index fun entry =>
      replaceField entry "native_decide_sites" (Json.arr sites.pop)).compress do
    rejects "a site removed from the list" "native_decide in Blake3.Sponge.squeeze is not a listed native_decide site" check
  let staleSite := Json.mkObj [("file", toJson "Blake3.lean"), ("declaration", toJson "Blake3.HasherOps.hash"),
    ("ruling", toJson "test")]
  withFile ledgerPath (← changeDependency ledger index fun entry =>
      replaceField entry "native_decide_sites" (Json.arr (sites.push staleSite))).compress do
    rejects "a stale site" "stale native_decide site: Blake3.HasherOps.hash in Blake3.lean" check
  let unruled := Json.mkObj [("file", toJson "Blake3.lean"), ("declaration", toJson "Blake3.Sponge.init"),
    ("ruling", toJson "")]
  withFile ledgerPath (← changeDependency ledger index fun entry =>
      replaceField entry "native_decide_sites" (Json.arr (sites.set! 1 unruled))).compress do
    rejects "a site without its ruling" "a native_decide site names no ruling" check

/-- The audit of a native dependency, which the ledger no longer exercises (it
records no native interface), run against a fixture entry planted in the
copy's ledger: the Blake3 package's Rust FFI as it was last recorded
(`fixtures/ledger/blake3-native-entry.json`), with every symbol unimported.
The audit accepts it; each regression then changes one thing. -/
private def nativeFixtureTests (root blake : FilePath) (ledger : Json) : IO Unit := do
  let check : IO Unit := audit root [("Blake3", blake.toString)] (some "6.3.0")
  let ledgerPath := root / "docs/trusted-externs.json"
  let fixture ← readJson (root / "fixtures/ledger/blake3-native-entry.json")
  let planted (entry : Json) : IO Json := replaceField ledger "native_interfaces" (Json.arr #[entry])
  let nativeLedger ← planted fixture
  let regression := root / "IxCC/AuditRegression.lean"
  withFile ledgerPath nativeLedger.compress do
    check
    -- every extern of the package tree is listed, imported or not
    withFile (blake / "Sibling.lean") "@[extern \"unreviewed_sibling\"] opaque sibling : Nat\n" do
      rejects "dependency sibling extern" "package-tree extern inventory drifted" check
    -- the project's qualified uses of the native module are its entry points
    withFile regression "def drift := Blake3.Rust.internalVersion\n" do
      rejects "native entrypoint drift" "qualified uses of Blake3.Rust drifted" check
    -- a symbol recorded as unimported, whose module the project imports
    withFile regression "import Blake3.Rust\n" do
      rejects "reachability of an imported backend" "reachability disagrees with imports of Blake3.Rust" check
  -- the Cargo lock: its hash, its crate inventory and its syntax
  let cargoRelative ← strField (← field fixture "cargo_lock") "path"
  let blake3Version ← strField (← field fixture "pins") "blake3_version"
  let cargo := blake / cargoRelative
  let original ← IO.FS.readFile cargo
  let record (version : String) := s!"\n[[package]]\nname = \"blake3\"\nversion = \"{version}\"\n"
  for (contents, diagnostic) in [(original ++ record blake3Version, "Cargo package records"),
      (original ++ record "999.0.0", "Cargo package inventory drifted"),
      ("package = [", "invalid Cargo TOML")] do
    withFile cargo contents do
      withFile ledgerPath nativeLedger.compress do
        rejects "Cargo hash drift" "Cargo lockfile hash drifted" check
      let data ← replaceField (← field fixture "cargo_lock") "sha256" (toJson (← sha256 cargo))
      withFile ledgerPath (← planted (← replaceField fixture "cargo_lock" data)).compress do
        rejects "Cargo metadata drift" diagnostic check
  -- the upstream BLAKE3 revision and the lean-ffi revision
  for (key, diagnostic) in [("blake3_upstream_rev", "upstream BLAKE3 revision drifted"),
      ("lean_ffi_rev", "lean-ffi Cargo revision drifted")] do
    let pins := (← field fixture "pins").setObjVal! key (toJson (String.ofList (List.replicate 40 '0')))
    withFile ledgerPath (← planted (← replaceField fixture "pins" pins)).compress do
      rejects s!"changed {key}" diagnostic check

/-- The link audit over `nm -P` output: the pure implementation's own symbols
(`lp_Blake3_Blake3_Pure_…`, the root module's `lp_Blake3_Blake3_HasherOps_…`,
IxCC's `…_blake3Pure`) pass; a symbol of either backend (its foreign exports,
the upstream C library's, its compiled Lean declarations and module
initializer), and a symbol table without `main`, are each refused. -/
private def linkAuditTests : IO Unit := do
  let clean := "main T 159f1d0 c0\nlp_Blake3_Blake3_Pure_hash T 1000 10\n" ++
    "initialize_Blake3_Blake3_Pure T 1100 10\nlp_Blake3_Blake3_HasherOps_finalizeWithLength t 1200 10\n" ++
    "lp_ix_x2dcc_IxCC_Ixon_Address_blake3Pure T 1300 10\nmemcpy@GLIBC_2.14 U\n"
  need ((← checked (auditLinked "clean" clean)) == 6) "the link audit read the wrong number of symbols"
  for line in ["rs_blake3_init T 2000 10", "c_blake3_hasher_update T 2000 10", "blake3_hasher_init U",
      "blake3_compress_in_place_portable t 2000 40", "lp_Blake3_Blake3_Rust_hasherInit T 2000 10",
      "lp_Blake3_Blake3_C_hasherFinalize T 2000 10", "initialize_Blake3_Blake3_C T 2000 10",
      "runtime_initialize_Blake3_Blake3_Rust T 2000 10"] do
    let name := (words line).headD ""
    rejectsAll s!"linked {name}" ["links a native backend of the Blake3 package", name] do
      discard (checked (auditLinked "planted" (clean ++ line ++ "\n")))
  rejects "a symbol table without main" "nm lists no main symbol" do
    discard (checked (auditLinked "stripped" "lp_Blake3_Blake3_Pure_hash T 1000 10\n"))

private def regressionTests (source blakeSource : FilePath) : IO Unit := IO.FS.withTempDir fun temporary => do
  let repositoryRoot := temporary / "repository"
  let root ← cloneWorkspace source repositoryRoot
  let blake := temporary / "Blake3"
  let originalLedger ← readJson (root / "docs/trusted-externs.json")
  let ledgerPath := root / "docs/trusted-externs.json"
  -- the workspace dependency's recorded closure, under the source directory
  -- its module names are relative to
  let ixIndex ← dependencyIndex originalLedger "workspace_path"
  let dependency := (← arrField originalLedger "lean_dependencies")[ixIndex]!
  let ixCKSources := root / (← strField (← field dependency "pins") "workspace_path") /
    (← strField dependency "source_dir")
  let ixClosure := (← pairs (← field dependency "closure")).map (·.1)
  need (!ixClosure.isEmpty) "test fixture lost the ix-ck closure"
  -- the Blake3 package: its Lean sources and, for the native fixture entry,
  -- its Cargo lock
  for path in (← files blakeSource true).filter (·.extension == some "lean") do
    copyRelative blakeSource blake path
  let fixture ← readJson (root / "fixtures/ledger/blake3-native-entry.json")
  let cargoRelative ← strField (← field fixture "cargo_lock") "path"
  copyFile (blakeSource / cargoRelative) (blake / cargoRelative)
  need (← arrField originalLedger "native_interfaces").isEmpty
    "test fixture: the ledger records a native interface"
  let check := audit root [("Blake3", blake.toString)] (some "6.3.0")
  check
  withFile (root / "IxCC/AuditRegression.lean") "import IxCK.Ixon.Verify\n" do
    rejects "unledgered pure dependency import" "imports of pure Lean dependencies drifted" check
  let codec := ixCKSources / ixClosure.head!
  let rehashedCodec : IO Json := rehashClosure originalLedger ixIndex ixClosure.head! codec
  withFile codec ((← IO.FS.readFile codec) ++ "\n") do
    rejects "pure dependency source drift" "changed" check
  withFile codec ((← IO.FS.readFile codec) ++ "\n@[extern \"rogue\"] opaque rogue : Nat\n") do
    -- with its hash re-recorded, the native declaration itself is refused
    withFile ledgerPath (← rehashedCodec).compress do
      rejects "pure dependency native code" "declares native symbols" check
  -- the kernel's closure admits no native_decide (it lists no site), and an
  -- import outside the closure is refused in every spelling of the command
  withFile codec ((← IO.FS.readFile codec) ++ "\ntheorem rogue_nd : 2 + 2 = 4 := by native_decide\n") do
    withFile ledgerPath (← rehashedCodec).compress do
      rejects "native_decide in the kernel closure" "native_decide in rogue_nd is not a listed native_decide site" check
  for command in ["public import", "meta import", "import all"] do
    withFile codec ((← IO.FS.readFile codec) ++ s!"\n{command} IxCK.Ixon.Verify\n") do
      withFile ledgerPath (← rehashedCodec).compress do
        rejects s!"{command} outside the kernel closure" "imports IxCK.Ixon.Verify outside the recorded closure" check
  -- the reviewed dependency csimp inventory is exact: dropping a listed
  -- theorem is refused
  withFile ledgerPath (← changeDependency originalLedger ixIndex fun entry => do
      let listed ← arrField entry "csimp_theorems"
      need (!listed.isEmpty) "test fixture lost the dependency csimp inventory"
      replaceField entry "csimp_theorems" (Json.arr listed.pop)).compress do
    rejects "dropped dependency csimp" "csimp inventory drifted" check
  -- a csimp theorem added to the dependency closure, with its hash
  -- re-recorded: refused until the ledger lists it
  let csimpRecord (file : String) : Json := Json.mkObj [("file", toJson file),
    ("theorem", toJson "rogue_eq"), ("replaces", toJson "rogue"), ("replacement", toJson "rogueFast")]
  let csimpTheorem := "@[csimp] theorem rogue_eq : @rogue = @rogueFast := rfl\n"
  withFile codec ((← IO.FS.readFile codec) ++ "\n" ++ csimpTheorem) do
    let rehashed (records : Array Json) : IO Json := do
      changeDependency (← rehashedCodec) ixIndex fun entry => do
        replaceField entry "csimp_theorems" (Json.arr ((← arrField entry "csimp_theorems") ++ records))
    withFile ledgerPath (← rehashed #[]).compress do
      rejects "unlisted dependency csimp" "csimp inventory drifted" check
    withFile ledgerPath (← rehashed #[csimpRecord ixClosure.head!]).compress do
      check
  -- the dependency's implemented_by sites are exact: dropping a listed site is
  -- refused; a site added to the closure, with its hash re-recorded, is refused
  -- until the ledger lists it
  withFile ledgerPath (← changeDependency originalLedger ixIndex fun entry => do
      let listed ← arrField entry "implemented_by_sites"
      need (!listed.isEmpty) "test fixture lost the dependency implemented_by inventory"
      replaceField entry "implemented_by_sites" (Json.arr listed.pop)).compress do
    rejects "dropped dependency implemented_by" "implemented_by inventory drifted" check
  let siteRecord (file : String) : Json := Json.mkObj [("file", toJson file),
    ("declaration", toJson "rogue"), ("implementation", toJson "rogueImpl"),
    ("ruling", toJson "test")]
  withFile codec ((← IO.FS.readFile codec) ++ "\n@[implemented_by rogueImpl] def rogue : Nat := 0\n") do
    let rehashedSites (records : Array Json) : IO Json := do
      changeDependency (← rehashedCodec) ixIndex fun entry => do
        replaceField entry "implemented_by_sites"
          (Json.arr ((← arrField entry "implemented_by_sites") ++ records))
    withFile ledgerPath (← rehashedSites #[]).compress do
      rejects "unlisted dependency implemented_by" "implemented_by inventory drifted" check
    withFile ledgerPath (← rehashedSites #[siteRecord ixClosure.head!]).compress do
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
  -- with no native interface recorded, a project extern and a C source the
  -- Lake file names are each refused
  withFile regression "@[extern \"unexpected_symbol\"] opaque rogue : Nat\n" do
    rejects "project extern drift" "project extern inventory drifted" check
  let lakefile := root / "lakefile.lean"
  withFile lakefile ((← IO.FS.readFile lakefile) ++ "\ndef rogueSource := \"native/rogue.c\"\n") do
    withFile ledgerPath (← rehash originalLedger root "lakefile.lean").compress do
      rejects "unrecorded foreign source" "project foreign-source inventory drifted" check
  withFile regression "import UnreviewedPackage\n" do
    rejects "external import drift" "external Lean import roots drifted" check
  withFile regression "public import UnreviewedPackage.Module\n" do
    rejects "external public import drift" "external Lean import roots drifted" check
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
  repositoryTests temporary repositoryRoot root blake originalLedger
  workspaceDependencyTests root blake originalLedger
  gitDependencyTests repositoryRoot root blake originalLedger
  nativeFixtureTests root blake originalLedger

def main (args : List String) : IO UInt32 := cli "Lean check regressions failed" do
  let args ← checked (parseArgs ["--root", "--blake3"] args)
  let root ← IO.FS.realPath (option args "--root" ".")
  let blake ← IO.FS.realPath (option args "--blake3" (root / ".lake/packages/Blake3").toString)
  lexerTests
  inventoryTests
  disassemblyTests
  linkAuditTests
  regressionTests root blake
  IO.println "Lean check regressions ok: source lexing (including native evaluation, every import spelling and native_decide sites), root/native/csimp inventories, Nix check inventory, build graph, proof/runtime coverage, integrity pins and rule, CI, repository, workspace and git dependency rejection paths, the native-dependency audit on its fixture entry (Cargo included), and the link audit"
