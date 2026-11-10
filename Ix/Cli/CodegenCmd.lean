/-
  `ix codegen`: render the shared role specification shape fixture derived from
  the verified IxC specification data, and IxVM's `KernelRoleSpec.lean`, which
  is rebuilt from the specification digest's bytes alone
  (`IxVM.RoleSpecGen.renderFromBytes`). `--check` fails when a file on disk
  differs, so the rendered circuit specification and the digest cannot drift
  apart; `tools/ixvm/check-formal.sh` runs it. With `--out DIR`, also write the
  native executors (and with `--cuda` the CUDA trace writers) of the certified
  IxVM, recursive verifier and aggregation programs under `DIR` for
  inspection: the sources `lake build ix` generates and compiles into `ix`
  (see `docs/formal-aiur-codegen.md`). The programs come from the artifact
  cache, or are compiled on a miss.
-/
module
public import Cli
public import Ix.IxVM.RoleSpecGen
public import Ix.RoleBinding.RustSpecGen
public import Ix.Cli.FormalAiur

public section

namespace Ix.Cli.CodegenCmd

def emitRustRoleSpecs (checkOnly : Bool) : IO Bool := do
  let formalAiur ← IO.ofExcept IxVM.RoleSpecGen.renderFormalAiur
  let outputs := #[
    ("Tests/Fixtures/role-binding-v2/spec-shape.tsv", IxVM.RoleSpecGen.renderSpecShapeTsv),
    ("IxVM/IxVM/Source/KernelRoleSpec.lean", formalAiur)]
  let mut ok := true
  for (path, contents) in outputs do
    if checkOnly then
      let existing ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
      if existing == some contents then
        IO.println s!"[codegen --check] {path} up to date"
      else
        IO.eprintln s!"[codegen --check] {path} STALE: re-run `ix codegen` and commit the result."
        if let some text := existing then
          IO.eprintln s!"[codegen --check] {path}: {IxVM.RoleSpecGen.firstDifference contents text}"
        ok := false
    else
      IO.FS.writeFile path contents
      IO.println s!"[codegen] wrote {path}"
  return ok

def runCodegenCmd (p : Cli.Parsed) : IO UInt32 := do
  let checkOnly := p.hasFlag "check"
  let ok ← emitRustRoleSpecs checkOnly
  if let some out := p.flag? "out" then
    FormalAiur.writeGenerated p (out.as! String) (p.hasFlag "cuda")
  return if ok then 0 else 1

end Ix.Cli.CodegenCmd

open Ix.Cli.CodegenCmd in
def codegenCmd : Cli.Cmd := `[Cli|
  "codegen" VIA runCodegenCmd;
  "Emit or verify the role-binding specification fixtures derived from IxC. With --out, also write the certified Aiur programs' generated native executors (and with --cuda their CUDA trace writers) for inspection."

  FLAGS:
    "check"; "Compare emitted fixtures against disk and exit 0 if identical, 1 otherwise."
    "out" : String; "Write the certified Aiur programs' generated sources under this directory."
    "cuda"; "With --out, also write the CUDA trace writers."
    "aiur-artifact" : String; "With --out, use this trusted IxVM artifact instead of compiling one."
    "aiur-artifact-digest" : String; "Refuse an IxVM artifact whose BLAKE3 digest is not this one."
    "aggr-artifact" : String; "With --out, use this trusted aggregation artifact instead of compiling one."
    "aggr-artifact-digest" : String; "Refuse an aggregation artifact whose BLAKE3 digest is not this one."
    "verifier-artifact" : String; "With --out, use this trusted recursive verifier artifact instead of compiling one."
    "verifier-artifact-digest" : String; "Refuse a recursive verifier artifact whose BLAKE3 digest is not this one."
]

end
