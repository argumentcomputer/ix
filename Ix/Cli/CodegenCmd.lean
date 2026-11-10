/-
  `ix codegen`: render the shared role specification shape fixture derived from
  the verified IxC specification data, and IxVM's `KernelRoleSpec.lean`, which
  is rebuilt from the specification digest's bytes alone
  (`IxVM.RoleSpecGen.renderFromBytes`). `--check` fails when a file on disk
  differs, so the rendered circuit specification and the digest cannot drift
  apart; `tools/ixvm/check-formal.sh` runs it.
-/
module
public import Cli
public import Ix.IxVM.RoleSpecGen
public import Ix.RoleBinding.RustSpecGen

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
  return if ok then 0 else 1

end Ix.Cli.CodegenCmd

open Ix.Cli.CodegenCmd in
def codegenCmd : Cli.Cmd := `[Cli|
  "codegen" VIA runCodegenCmd;
  "Emit or verify the role-binding specification fixtures derived from IxC."

  FLAGS:
    "check"; "Compare emitted fixtures against disk and exit 0 if identical, 1 otherwise."
]

end
