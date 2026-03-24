import Lake
open Lake DSL
open System (FilePath)

package typecheckers where
  version := v!"0.1.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.26.0"

-- Ix project (parent): provides Ix.Kernel, Ix.CompileM, Ix.Benchmark, etc.
require ix from "../.."

-- lean4lean: Lean reimplementation of the Lean 4 kernel
require lean4lean from git
  "https://github.com/digama0/lean4lean.git" @ "f37aeabb8cc0f0bfd9aca9744167a608235f3a6a"

-- lean4checker: uses the C++ kernel (Kernel.Environment.addDeclCore)
require lean4checker from git
  "https://github.com/leanprover/lean4checker.git" @ "v4.26.0"

/-- Local deps directory for non-Lake dependencies (nanoda, lean4export). -/
def depsDir (pkg : Package) : FilePath := pkg.dir / "deps"

section ExternalDeps

/-- Clone and build nanoda (Rust external checker).
    Pinned to a specific commit for reproducibility. -/
target nanoda_bin pkg : FilePath := do
  let nanodaDir := depsDir pkg / "nanoda_lib"
  let bin := nanodaDir / "target" / "release" / "nanoda_bin"
  unless ← nanodaDir.pathExists do
    proc { cmd := "git"
           args := #["clone", "https://github.com/ammkrn/nanoda_lib", nanodaDir.toString] }
    proc { cmd := "git"
           args := #["checkout", "224b7c186e695e2e24f29e272a3b2aa7a97f8219"]
           cwd := nanodaDir }
  proc { cmd := "cargo", args := #["build", "--release"], cwd := nanodaDir } (quiet := true)
  inputBinFile bin

/-- Clone and build lean4export.
    TODO: Convert to `require lean4export from git ...` once Ix is bumped to v4.28.0.
    Currently cloned externally because lean4export requires Lean v4.28.0 while Ix is on v4.26.0. -/
target lean4export_bin pkg : FilePath := do
  let exportDir := depsDir pkg / "lean4export"
  let bin := exportDir / ".lake" / "build" / "bin" / "lean4export"
  unless ← exportDir.pathExists do
    proc { cmd := "git"
           args := #["clone", "https://github.com/leanprover/lean4export",
                     "-b", "v4.28.0", exportDir.toString] }
  proc { cmd := "lake", args := #["build"], cwd := exportDir } (quiet := true)
  inputBinFile bin

end ExternalDeps

@[default_target]
lean_exe «bench-kernel» where
  root := `Main
  supportInterpreter := true
  -- Ensure nanoda and lean4export are built before the benchmark
  extraDepTargets := #[`nanoda_bin, `lean4export_bin]
