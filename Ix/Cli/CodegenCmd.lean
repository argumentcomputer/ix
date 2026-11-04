/-
  `ix codegen`: render the shared role specification shape fixture derived
  from the verified IxC specification data. With `--out DIR`, also write the
  native executors (and with `--cuda` the CUDA trace writers) of the
  certified IxVM, recursive verifier and aggregation programs under `DIR`
  for inspection: the sources `lake build ix` generates and compiles into
  `ix` (see `docs/formal-aiur-codegen.md`). The programs come from the
  compiled-program cache, or are compiled in process on a miss.
-/
module
public import Cli
public import Ix.IxVM.RoleSpecGen
public import Ix.RoleBinding.RustSpecGen
public import Ix.Cli.FormalPrograms

public section

namespace Ix.Cli.CodegenCmd

def emitRustRoleSpecs (root : System.FilePath) (checkOnly : Bool) : IO Bool := do
  let outputs := #[
    (root / "Tests/Fixtures/role-binding-v2/spec-shape.tsv", Ix.RoleBinding.RustSpecGen.shape)]
  let mut ok := true
  for (path, contents) in outputs do
    if checkOnly then
      let existing ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
      if existing == some contents then
        IO.println s!"[codegen --check] {path} up to date"
      else
        IO.eprintln s!"[codegen --check] {path} STALE: re-run `ix codegen` and commit the result."
        ok := false
    else
      IO.FS.writeFile path contents
      IO.println s!"[codegen] wrote {path}"
  return ok

open Ix.Cli.FormalAiur in
def runCodegenCmd (p : Cli.Parsed) : IO UInt32 := do
  let checkOnly := p.hasFlag "check"
  let ok ← emitRustRoleSpecs (← Ix.Cli.FormalAiur.repoRoot) checkOnly
  if let some out := p.flag? "out" then
    let programs := #[ixvmProgram, verifierProgram, aggregationProgram]
    let selected ← compiledPrograms (← FormalProver.Registry.new) programs
      (checkExecutors := false)
    writeGenerated programs selected (out.as! String) (p.hasFlag "cuda")
  return if ok then 0 else 1

end Ix.Cli.CodegenCmd

open Ix.Cli.CodegenCmd in
def codegenCmd : Cli.Cmd := `[Cli|
  "codegen" VIA runCodegenCmd;
  "Emit or verify the role-binding specification fixtures derived from IxC. With --out, also write the certified Aiur programs' generated native executors (and with --cuda their CUDA trace writers) for inspection, compiling the programs on a cache miss."

  FLAGS:
    "check"; "Compare emitted fixtures against disk and exit 0 if identical, 1 otherwise."
    "out" : String; "Write the certified Aiur programs' generated sources under this directory."
    "cuda"; "With --out, also write the CUDA trace writers."
]

end
