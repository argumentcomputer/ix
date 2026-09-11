import Ix.Compiler.Tools.TrustLedger

/-! Regression tests for the trust gate's failure paths. Mutations are confined
to fresh temporary copies; the source tree and reviewed ledger are never edited. -/

open Lean System Ix.Compiler.Tools.Check Ix.Compiler.Tools.SourceScan
open Ix.Compiler.Tools.TrustLedger

private def rejects (label fragment : String) (action : IO Unit) : IO Unit := do
  let error ← try action; pure none catch error => pure (some error.toString)
  let some error := error | throw (IO.userError s!"{label}: unexpectedly accepted")
  need (error.contains fragment) s!"{label}: rejected for the wrong reason: {error}"

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
  let lake ← compilerLake source
  for path in ← leanSources source lake do copyRelative source target path
  for path in ["lakefile.lean", "lake-manifest.json", "flake.lock", "lean-toolchain", "native/compiler/hpt_cache_sync.c"] do
    copyFile (source / path) (target / path)

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

private def regressionTests (source blakeSource : FilePath) : IO Unit := IO.FS.withTempDir fun temporary => do
  let root := temporary / "project"
  let blake := temporary / "Blake3"
  cloneProject source root
  for path in (← files blakeSource true).filter (·.extension == some "lean") do
    copyRelative blakeSource blake path
  copyFile (blakeSource / "rust/Cargo.lock") (blake / "rust/Cargo.lock")
  let profile := Ix.Compiler.Tools.TrustProfile.reviewed
  let check := auditWith profile root blake
  check
  let regression := root / "Ix/Compiler/AuditRegression.lean"
  for token in ["axiom", "sorry", "native_decide"] do
    withFile regression s!"{token} injected\n" do
      rejects token (token ++ " is not allowed") check
  withFile regression "@[extern \"unexpected_symbol\"] opaque rogue : Nat\n" do
    rejects "project extern drift" "project extern inventory drifted" check
  for name in ["UnreviewedPackage", "Ix.TypeChecker", "Ix.Theory"] do
    withFile regression s!"import {name}\n" do
      rejects "external import drift" "external Lean imports drifted" check
  withFile regression "def drift := Blake3.Rust.internalVersion\n" do
    rejects "native entrypoint drift" "qualified uses of Blake3.Rust drifted" check
  withFile (root / "lean-toolchain") "leanprover/lean4:v4.33.0\n" do
    rejects "seed drift" "Lean seed version drifted" check
  let native := root / "native/compiler/hpt_cache_sync.c"
  withFile native ((← IO.FS.readFile native) ++ "\n") do
    rejects "C source drift" "foreign source hash drifted" check
  let lake := root / "lakefile.lean"
  let added := (← IO.FS.readFile lake).replace "end Compiler\n"
    ("lean_exe regression where\n  root := " ++ String.singleton (Char.ofNat 96) ++ "Regression\nend Compiler\n")
  withFile lake added do
    rejects "build drift" "Compiler Lake section hash drifted" check
    -- Even a newly reviewed build section must inventory additional roots.
    let profile := { profile with lakeSectionSha256 := ← textSha256 (← compilerSection added) }
    withFile (root / "Regression.lean") "axiom outsideLibrary : False\n" do
      rejects "new executable inventory" "axiom is not allowed" (auditWith profile root blake)
  withFile (blake / "Sibling.lean") "@[extern \"unreviewed_sibling\"] opaque sibling : Nat\n" do
    rejects "dependency sibling extern" "package-tree extern inventory drifted" check
  let cargo := blake / "rust/Cargo.lock"
  let duplicate := (← IO.FS.readFile cargo) ++ "\n[[package]]\nname = \"blake3\"\nversion = \"1.8.7\"\n"
  for (contents, diagnostic) in [(duplicate, "duplicate Cargo package identity"), ("package = [", "invalid Cargo TOML")] do
    withFile cargo contents do
      rejects "Cargo hash drift" "Cargo lockfile hash drifted" check
      let profile := { profile with cargoSha256 := ← sha256 cargo }
      rejects "Cargo metadata drift" diagnostic (auditWith profile root blake)

def main (args : List String) : IO UInt32 := cli "Lean check regressions failed" do
  let args ← checked (parseArgs ["--root", "--blake3"] args)
  let root ← IO.FS.realPath (option args "--root" ".")
  let blake ← IO.FS.realPath (option args "--blake3" (root / ".lake/packages/Blake3").toString)
  lexerTests
  regressionTests root blake
  IO.println "Lean check regressions OK: source lexing, component roots, native inventories, build/seed pins, Cargo rejection paths"
