import Lake
open System Lake DSL

package aiur where
  version := v!"0.1.0"
  -- Preserve the elaboration of the verified 4.29 monadic definitions.
  leanOptions := #[⟨`backward.do.legacy, true⟩]

require "leanprover-community" / "mathlib" @ git "v4.34.1"

/-- Keep ordinary Cargo builds independent of Lean. Only the Lean executable
link step needs this archive and the small C object-ABI adapter. -/
target aiur_rs pkg : FilePath := do
  let sources ← inputDir (pkg.dir / ".." / "crates" / "aiur" / "src") true (fun path => path.extension == some "rs")
  let manifests := Job.collectArray #[
    ← inputTextFile (pkg.dir / ".." / "crates" / "aiur" / "Cargo.toml"),
    ← inputTextFile (pkg.dir / ".." / "Cargo.toml"),
    ← inputTextFile (pkg.dir / ".." / "Cargo.lock"),
    ← inputTextFile (pkg.dir / ".." / "rust-toolchain.toml")]
  let deps := sources.zipWith (fun a b => (a,b)) manifests
  let output := pkg.staticLibDir / nameToStaticLib "aiur_rs"
  buildFileAfterDep output deps fun _ => do
    proc { cmd := "cargo", args := #["build", "--release", "-p", "aiur", "--lib", "--locked"], cwd := pkg.dir / ".." } (quiet := true)
    copyFile (pkg.dir / ".." / "target" / "release" / nameToStaticLib "aiur") output

target execution_o pkg : FilePath := do
  let source ← inputTextFile (pkg.dir / "c" / "execution.c")
  buildO (pkg.buildDir / "c" / "execution.o") source
    #["-I", (← getLeanIncludeDir).toString] #["-fPIC"] "cc" getLeanTrace

@[default_target]
lean_lib Aiur where
  globs := #[.andSubmodules `Aiur]

lean_lib AiurTests

@[test_driver]
lean_exe aiur_tests where
  root := `AiurTests
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe blake3_stats where
  root := `Examples.Blake3

lean_exe aiur_execution where
  root := `Examples.Execution
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe execution_tests where
  root := `Examples.ExecutionChecks
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe trace_tests where
  root := `Examples.TraceChecks
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe aiur_hints where
  root := `Examples.ExecutionHints
  moreLinkObjs := #[execution_o, aiur_rs]

lean_exe trie_export where
  root := `Examples.Trie

lean_exe u32_tests where
  root := `Examples.U32

lean_exe library_tests where
  root := `Examples.LibraryChecks

lean_exe grouping_example where
  root := `Examples.Grouping

lean_exe grouping_tune where
  root := `Examples.GroupingTune
