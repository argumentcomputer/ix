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

private def cloneProject (source target : FilePath) : IO Unit := do
  let ledger ← readJson (source / "docs/trusted-externs.json")
  let lake ← checked (scan (← IO.FS.readFile (source / "lakefile.lean")))
  for path in ← leanSources source lake do copyRelative source target path
  for (path, _) in ← pairs (← field (← field ledger "integrity") "tracked_files") do
    copyRelative source target (source / path)
  copyFile (source / "docs/trusted-externs.json") (target / "docs/trusted-externs.json")
  let workflows := source / ".github/workflows"
  if ← workflows.pathExists then
    for entry in ← workflows.readDir do
      copyFile entry.path (target / ".github/workflows" / entry.fileName)

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
  let externInput := "/- @[extern \"ignored\"] opaque absent : Nat -/\n" ++
    "@[extern 1 \"ffi_first\"] private unsafe opaque first : Nat\n" ++
    "attribute [extern \"ffi_second\"] second Qualified.third\n"
  let found ← checked (externs (← checked (scan externInput)))
  need (found == [("ffi_first", "first"), ("ffi_second", "second"), ("ffi_second", "Qualified.third")])
    "extern declaration/attribute inventory changed"
  rejects "unsupported extern" "unrecognized extern declaration" do
    let _ ← checked (externs (← checked (scan "@[extern \"unaccounted\"] theorem unsupported : True := by trivial")))
  rejects "implicit extern" "explicit symbol" do
    let _ ← checked (externs (← checked (scan "@[extern] opaque unsupported : Nat")))
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

private def regressionTests (source blakeSource ixKernelSource : FilePath) : IO Unit := IO.FS.withTempDir fun temporary => do
  let root := temporary / "project"
  let blake := temporary / "Blake3"
  let ixKernel := temporary / "ix" / "IxKernel"
  cloneProject source root
  let originalLedger ← readJson (root / "docs/trusted-externs.json")
  -- the pure Lean dependency's recorded closure, laid out as its package root sees it
  let mut ixClosure : List String := []
  for entry in ← arrField originalLedger "lean_dependencies" do
    let sourceDir ← strField entry "source_dir"
    for (relative, _) in ← pairs (← field entry "closure") do
      copyFile (ixKernelSource / sourceDir / relative) (ixKernel / sourceDir / relative)
      ixClosure := ixClosure ++ [relative]
  need (!ixClosure.isEmpty) "test fixture lost the ix-kernel closure"
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
  let check := audit root [("Blake3", blake.toString), ("«ix-kernel»", ixKernel.toString)] (some "6.3.0")
  check
  withFile (root / "IxCC/AuditRegression.lean") "import Ix.Ixon.Verify\n" do
    rejects "unledgered pure dependency import" "imports of pure Lean dependencies drifted" check
  let codec := ixKernel / ".." / ixClosure.head!
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
  buildGraphTests root
  let regression := root / "IxCC/AuditRegression.lean"
  for token in ["axiom", "sorry", "native_decide"] do
    withFile regression s!"{token} injected\n" do
      rejects token (token ++ " is not allowed") check
  withFile regression "@[extern \"unexpected_symbol\"] opaque rogue : Nat\n" do
    rejects "project extern drift" "project extern inventory drifted" check
  withFile regression "import UnreviewedPackage\n" do
    rejects "external import drift" "external Lean import roots drifted" check
  withFile regression "def drift := Blake3.Rust.internalVersion\n" do
    rejects "native entrypoint drift" "qualified uses of Blake3.Rust drifted" check
  -- The CI action inventory is empty while hosted workflows are removed; any
  -- added workflow action must be pinned and reviewed into the ledger.
  let workflow := root / ".github/workflows/regression.yml"
  withFile workflow "jobs:\n  test:\n    steps:\n      - run: true\n" check
  withFile workflow "jobs:\n  test:\n    steps:\n      - uses: actions/checkout@main\n" do
    rejects "unpinned CI action" "unpinned CI action" check
  withFile workflow ("jobs:\n  test:\n    steps:\n      - uses: \"unreviewed/action@" ++
      String.join (List.replicate 40 "1") ++ "\"\t# reviewed\n") do
    rejects "new quoted pinned CI action" "CI action inventory drifted" check
  withFile workflow ("jobs:\n  test:\n    steps:\n      - uses: unreviewed/action@" ++
      String.join (List.replicate 40 "1") ++ "\n") do
    rejects "new pinned CI action" "CI action inventory drifted" check
  let flake := root / "flake.nix"
  withFile flake ((← IO.FS.readFile flake) ++ "\n") do
    rejects "integrity drift" "flake.nix changed" check
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

def main (args : List String) : IO UInt32 := cli "Lean check regressions failed" do
  let args ← checked (parseArgs ["--root", "--blake3", "--ix-kernel"] args)
  let root ← IO.FS.realPath (option args "--root" ".")
  let blake ← IO.FS.realPath (option args "--blake3" (root / ".lake/packages/Blake3").toString)
  let ixKernel ← IO.FS.realPath (option args "--ix-kernel" (root / ".lake/packages/ix-kernel/IxKernel").toString)
  lexerTests
  disassemblyTests
  regressionTests root blake ixKernel
  IO.println "Lean check regressions ok: source lexing, root/native inventories, build graph, proof/runtime coverage, integrity, Cargo, and CI rejection paths"
