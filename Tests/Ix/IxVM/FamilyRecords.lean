import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.FamilyRecordsDefs
import Ix.IxVM.Model

/-! # The compiled records of two families, with their model advice

`ixvm-family-records` compiles a `List`-nested tree and a mutual pair indexed by `Nat` with Ix's
compiler, generates the model advice of their blocks (`IxVM.Model.generateReport`), and checks
that each block got a payload: a recursor family record, a model for every type, constructor and
recursor, and a theorem for every rule.

With `IX_FAMILY_RECORDS_OUT` set to a file, it writes what it compiled there, one item a line in
hexadecimal: the role table's bytes (`table`), every record with its address (`rec`: the
environment's, then the advice's), every blob (`blob`), and for each family its block's address,
its recursor family record's address, and the addresses of its advice records, member models and
rule theorems (`fam`). The proofs about family records read this file. -/

namespace Tests.Ix.IxVM.FamilyRecords

open IxVM.ClaimHarness

private def defs (s : String) : Lean.Name :=
  (`Tests.Ix.IxVM.FamilyRecordsDefs).str s

/-- The families: a label, the first type, the names compiled, and the expected numbers of member
models and of rule theorems. -/
private def families : List (String × Lean.Name × Array Lean.Name × Nat × Nat) :=
  [("NestedTree", defs "T", #[defs "T", (defs "T").str "rec", (defs "T").str "rec_1"], 4, 3),
   ("IndexedPair", defs "EvT",
     #[defs "EvT", defs "OdT", (defs "EvT").str "rec", (defs "OdT").str "rec"], 7, 3)]

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

private def hex (b : ByteArray) : String :=
  String.mk (b.data.toList.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

private def hexList (as : Array Address) : String :=
  ",".intercalate (as.toList.map fun a => hex a.hash)

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let names := families.foldl (fun acc f => acc ++ f.2.2.1) #[]
  let missing := names.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-family-records] not in the environment: {missing}"
    return 1
  let env0 ← loadSharedIxonEnv names leanEnv
  let (env, rep) ← IO.ofExcept (IxVM.Model.generateReport
    { env0 with models := {}, modelRecords := {}, modelHints := {}, modelBlobs := {},
                modelDeps := {}, modelsAttached := false })
  let mut ok := true
  let mut lines : Array String := #[]
  match env.roleBinding with
  | some b => lines := lines.push s!"table {hex b.bytes}"
  | none =>
    IO.eprintln "[ixvm-family-records] the environment has no role binding"
    ok := false
  for (a, lc) in env.consts do
    lines := lines.push s!"rec {hex a.hash} {hex lc.rawBytes}"
  for (a, c) in env.modelRecords do
    lines := lines.push s!"rec {hex a.hash} {hex (Ixon.serConstant c)}"
  for (a, bytes) in env.blobs do
    lines := lines.push s!"blob {hex a.hash} {hex bytes}"
  for (a, bytes) in env.modelBlobs do
    lines := lines.push s!"blob {hex a.hash} {hex bytes}"
  for (label, first, _, nModels, nIotas) in families do
    let ty ← lookupAddr env first
    let some block := (env.getConst? ty).bind IxVM.Model.projectionBlock?
      | do
        IO.eprintln s!"[ixvm-family-records] {label}: {first} is not a member of a block"
        return 1
    let some (_, adv) := rep.advice.find? (·.1 == block)
      | do
        IO.eprintln s!"[ixvm-family-records] {label}: the block has no model advice"
        return 1
    let p := adv.layout
    let models := p.typeModels.size + p.ctorModels.size + p.recModels.size
    IO.println s!"[ixvm-family-records] {label}: block {block}, recursor family {p.recBlock}, \
      {adv.records.size} advice records, {models} member models, {p.iotas.size} rule theorems"
    unless models == nModels && p.iotas.size == nIotas do
      IO.eprintln s!"[ixvm-family-records] {label}: expected {nModels} member models and \
        {nIotas} rule theorems"
      ok := false
    lines := lines.push s!"fam {label} {hex block.hash} {hex p.recBlock.hash} \
      {hexList (adv.records.map (·.1))} {hexList p.typeModels} {hexList p.ctorModels} \
      {hexList p.recModels} {hexList p.iotas}"
  if let some path ← IO.getEnv "IX_FAMILY_RECORDS_OUT" then
    IO.FS.writeFile path ("\n".intercalate lines.toList ++ "\n")
    IO.println s!"[ixvm-family-records] wrote {lines.size} lines to {path}"
  return if ok then 0 else 1

end Tests.Ix.IxVM.FamilyRecords
