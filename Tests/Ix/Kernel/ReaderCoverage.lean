import Tests.Ix.IxVM
import Tests.Ix.IxVM.S4Bench
import Ix.RoleBinding.Artifact

/-! # The trusted reader on the closures IxVM accepts (decision D10)

`IxVM.consistent` (`Ix.IxVM.Consistency.Statement`) concludes that the records
an accepting run loaded are read by the kernel's reader
(`Ix.Kernel.Admission.prepareWith`, through `ReadIn`). This suite runs that
reader, as `Ix.RoleBinding.Artifact.prepare` drives it over a whole artifact,
on the environments the IxVM suites check, and fails if it declines a record
of the logical fragment:

* the closures of every `ixvm-kernel-checks` constant (the 151 pins' check
  claims), compiled together as that suite compiles them;
* `ixvm-s4-bench`'s declarations (plain, mutual and nested blocks, among them
  `Lean.Syntax` and `Lean.Meta.Grind.Arith.Linear.RingIneqCnstr`), its `Std`
  shards and its module shards (`Std.Data.HashMap`, `Std.Data.DHashMap`).

The reader's safety policy declines unsafe and `partial` definitions, unsafe
axioms and unsafe inductive blocks (`Ix.Kernel.Reader.safetyDeclineOf`,
`readInductive`): they are outside Lean's logic, and an unsafe constant may have
any type, `False` included. IxVM type-checks them (`KernelCheck::is_unsafe_ci`
and `assert_safety` keep safe constants from referencing them). They are set
aside here and counted; the logical rest must read in full. Init+Std and Lean
as wholes were read by `ix check-lean` in lane s4's job `s4-006` (every
mutual and nested block accepted, only the tier and `Lean.trustCompiler`'s
axiom policy set aside). -/

namespace Tests.Ix.Kernel.ReaderCoverage

open IxVM.ClaimHarness

/-- The limits `ix check-lean` reads artifacts at. -/
def limits : Ix.Kernel.Admission.Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

/-- An unsafe inductive block: the reader declines it (`readInductive`). -/
def unsafeInductive : Ixon.ConstantInfo → Bool
  | .muts ms => ms.any fun
    | .indc i => i.isUnsafe || i.ctors.any (·.isUnsafe)
    | .recr r => r.isUnsafe
    | _ => false
  | .recr r => r.isUnsafe
  | _ => false

/-- The records the reader's safety policy declines, with the projections of
their blocks. -/
def outsideLogic (env : Ixon.Env) : Std.HashSet Address := Id.run do
  let mut owners : Std.HashSet Address := {}
  for (a, lc) in env.consts do
    if let some c := lc.get? then
      if Ix.Kernel.Admission.isTierInfo c.info || unsafeInductive c.info then
        owners := owners.insert a
  let mut out := owners
  for (a, lc) in env.consts do
    if let some c := lc.get? then
      let block := match c.info with
        | .dPrj p => some p.block | .iPrj p => some p.block
        | .cPrj p => some p.block | .rPrj p => some p.block
        | _ => none
      if block.any owners.contains then out := out.insert a
  return out

/-- Read `env`'s logical records with the kernel's reader; `true` when it
accepts them all. -/
def readerAccepts (label : String) (env : Ixon.Env) : IO Bool := do
  let set := outsideLogic env
  let logical := { env with consts := env.consts.filter fun a _ => !set.contains a }
  match Ix.RoleBinding.Artifact.prepare logical limits with
  | .ok _ =>
    IO.println s!"[reader-coverage] {label}: {logical.consts.size} records read; \
      {set.size} unsafe or partial records set aside"
    return true
  | .error e =>
    IO.eprintln s!"[reader-coverage] {label}: the reader declines: {e}"
    return false

private def nameOfString (str : String) : Lean.Name :=
  str.splitOn "." |>.foldl (init := .anonymous) fun acc s =>
    match s.toNat? with
    | some n => .mkNum acc n
    | none => .mkStr acc s

/-- The constants declared in modules under `pre`. -/
def moduleNames (env : Lean.Environment) (pre : Lean.Name) : Array Lean.Name := Id.run do
  let mut names : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      if pre.isPrefixOf env.header.moduleNames[i.toNat]! then names := names.push n
  return names.qsort Lean.Name.lt

def run (env : Lean.Environment) : IO UInt32 := do
  let mut groups : Array (String × Array Lean.Name) := #[]
  let pins := (Tests.Ix.IxVM.kernelCheckEntries ++ Tests.Ix.IxVM.validatingCheckEntries).map
    (nameOfString ∘ Prod.fst)
  groups := groups.push ("ixvm-kernel-checks closures", pins.toArray)
  let bench := Tests.Ix.IxVM.S4Bench.targets.flatMap (fun (_, ns, r) => r :: ns) |>.map nameOfString
  groups := groups.push ("ixvm-s4-bench declarations", bench.toArray)
  groups := groups.push ("closure of Std.HashMap.getElem?_insert_self",
    #[nameOfString "Std.HashMap.getElem?_insert_self"])
  for pre in [`Std.Data.HashMap, `Std.Data.DHashMap] do
    groups := groups.push (s!"module shard {pre}", moduleNames env pre)
  let mut failed := 0
  for (label, names) in groups do
    let missing := names.filter (!env.constants.contains ·)
    unless missing.isEmpty do
      IO.eprintln s!"[reader-coverage] {label}: not in the environment: {missing}"
      failed := failed + 1
      continue
    let ixonEnv ← loadSharedIxonEnv names env
    unless ← readerAccepts label ixonEnv do failed := failed + 1
  return if failed == 0 then 0 else 1

end Tests.Ix.Kernel.ReaderCoverage
