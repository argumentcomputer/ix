import Tests.Ix.IxVM
import Tests.Ix.IxVM.S4Bench
import Ix.RoleBinding.Artifact

/-! # The trusted reader on the closures IxVM accepts

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

Each environment is read first as the IxVM suites compile it (the records a
run may load). Where that declines because an inductive block's recursors are
absent (IxVM needs a recursor only where a constant uses it; the reader needs
every block's), the suite names those recursors and reads the environment
again with them: the records `IxVM.consistent`'s `Draws` lets the reading add
at addresses the run did not load. The supplemented reading must succeed.

The reader's safety policy declines unsafe and `partial` definitions, unsafe
axioms and unsafe inductive blocks (`Ix.Kernel.Reader.safetyDeclineOf`,
`readInductive`): they are outside Lean's logic, and an unsafe constant may have
any type, `False` included. IxVM type-checks them (`KernelCheck::is_unsafe_ci`
and `assert_safety` keep safe constants from referencing them). They are set
aside here and counted; the logical rest must read in full. Checked as wholes
with `ix check-lean`, Init+Std and Lean read in full (every mutual and nested
block accepted, only the tier and `Lean.trustCompiler`'s axiom policy set
aside). -/

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
    let names := set.toList.map fun a => (env.addrToName[a]?).map toString |>.getD (toString a)
    IO.println s!"[reader-coverage] {label}: {logical.consts.size} records read; \
      {set.size} unsafe or partial records set aside: {names.take 12}"
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

/-- `names` with the recursors of every inductive in their closure
(`<T>.rec` and the nested `<T>.rec_N`), closed again until stable: the
records `IxVM.consistent`'s `Draws` lets the reading add. -/
def withRecursors (env : Lean.Environment) (names : Array Lean.Name) : Array Lean.Name := Id.run do
  let mut seeds := names
  for _ in [0:8] do
    let mut extra : Array Lean.Name := #[]
    for (_, ci) in Lean.collectDependenciesMany seeds env.constants do
      if let .inductInfo v := ci then
        let recs := Lean.mkRecName v.name ::
          (List.range v.numNested).map fun i => Lean.Name.mkStr (v.all.headD v.name) s!"rec_{i + 1}"
        for r in recs do
          if env.constants.contains r && !seeds.contains r && !extra.contains r then
            extra := extra.push r
    if extra.isEmpty then break
    seeds := seeds ++ extra
  return seeds

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
    -- the environment as the IxVM suites compile it: what a run may load
    let loaded ← loadSharedIxonEnv names env
    if ← readerAccepts s!"{label} (as loaded)" loaded then continue
    -- the same, with the recursors the reading may add (`Draws`)
    let names' := withRecursors env names
    let added := (names'.filter (!names.contains ·)).filter fun r =>
      (loaded.getAddr? (Ix.Name.fromLeanName r)).isNone
    IO.println s!"[reader-coverage] {label}: recursors absent from the loaded records: {added}"
    let supplemented ← loadSharedIxonEnv names' env
    unless ← readerAccepts s!"{label} (with those recursors)" supplemented do failed := failed + 1
  return if failed == 0 then 0 else 1

end Tests.Ix.Kernel.ReaderCoverage
