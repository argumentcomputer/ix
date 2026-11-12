/-
  Guards the IxVM program's address literals.

  The legacy IxVM kernel once hardcoded ~77 primitive constant addresses as
  32-byte literals so reduction could recognize `Nat.add` etc. by address
  alone. A single wrong byte was a soundness-relevant defect, invisible to the
  cost-pinned suite and the arena fixtures; one shipped for months
  (`bool_false_addr`, last 8 bytes wrong). Every constant a native rule
  recognizes or builds is now a role, read through the claim's role binding
  and validated against its specification, so the only literal a claim reads is
  the specification digest.

  This test keeps it that way in the formal IxVM program. It reads every list
  of byte or numeric literals out of the program's source text
  (`Tests.Ix.IxVM.programSources`) and allows exactly two of address length:
  the specification digest (`KernelRoleSpec::spec_digest`, equal to
  `Ix.SpecDigest.specDigest`), and the default role table's binding hash
  (`IxVMCompat::default_binding_addr`, equal to
  `Ix.Kernel.Reader.defaultTableAddress`), which only the benchmark and debug
  entry points read. An address literal reappearing fails, as does another
  function reading the default binding, or the scanner finding neither literal
  (a change in the sources' shape). A literal that reappears is reported with
  the primitive it encodes, if any, from `Ix.PrimAddrs`.
-/
import Ix.Meta
import Ix.Ixon
import Ix.PrimAddrs
import Ix.SpecDigest
import Tests.Ix.IxVM.Sources
import Tests.Ix.Kernel.PrimitiveTable
import LSpec

open LSpec

namespace Tests.Ix.Kernel.PrimAddrs

/-- The functions allowed to hold an address-length literal, with the address
each must hold:
- the specification digest, which a claim's context must name;
- the default role table's binding hash, which only the benchmark and debug
  entry points (`defaultBindingReaders`) use: the production entry point,
  `verify_claim`, reads the binding its claim names. -/
def expectedAddressLiterals : List (String × Except String Address) := [
  ("KernelRoleSpec::spec_digest", Ix.SpecDigest.specDigest),
  ("IxVMCompat::default_binding_addr", Ix.Kernel.Reader.defaultTableAddress)]

/-- The entry points allowed to read the default binding: none is the claim
entry point. -/
def defaultBindingReaders : List String :=
  ["IxVM::verify_constant", "IxVM::verify_transitive", "IxVM::verify_check_env"]

/-- The canonical primitive addresses, for naming a literal that reappears. -/
def canonical : Std.HashMap Address String := Id.run do
  let mut m : Std.HashMap Address String := {}
  for (name, a) in Ix.PrimAddrs.leanParityTable do m := m.insert a name
  for (name, a) in Ix.PrimAddrs.reservedMarkerAddrs do m := m.insert a name
  return m

/-- The guard's findings over the program's functions. -/
def problems (fns : Array Tests.Ix.IxVM.Sources.Function) : Array String := Id.run do
  let found := fns.flatMap fun f =>
    (Tests.Ix.IxVM.Sources.literalLists f.body).filterMap fun xs =>
      if xs.size ≥ 16 then some (f.name, xs) else none
  let mut out : Array String := #[]
  for (name, xs) in found do
    let bytes : Option Address :=
      if xs.size == 32 && xs.all (· < 256) then some ⟨⟨xs.map (·.toUInt8)⟩⟩ else none
    match expectedAddressLiterals.find? (·.1 == name) with
    | some (_, expected) =>
      unless bytes.isSome && bytes == expected.toOption do
        out := out.push s!"{name} holds {xs}, not {expected.toOption}"
    | none =>
      let named := ((bytes.bind fun a => canonical[a]?).map fun n => s!", the address of {n}").getD ""
      out := out.push s!"{name} holds a literal of {xs.size} items{named}"
  for (name, _) in expectedAddressLiterals do
    unless found.any (·.1 == name) do
      out := out.push s!"no literal found in {name}: the scanner no longer reads the sources"
  for f in fns do
    if (f.body.splitOn "default_binding_addr(").length > 1 &&
        !defaultBindingReaders.contains f.name && f.name != "IxVMCompat::default_binding_addr" then
      out := out.push s!"{f.name} reads the default role binding"
  return out

def literalGuard : TestSeq :=
  .individualIO "the IxVM program's only address literals are the specification digest and \
      the debug entry points' default binding" none (do
    let found := problems (Tests.Ix.IxVM.Sources.functions (← Tests.Ix.IxVM.programSources))
    let ok := found.isEmpty
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some ("; ".intercalate found.toList))) .done

def suite : List TestSeq := [literalGuard] ++ Tests.Ix.Kernel.PrimitiveTable.suite

/-- A dotted Lean name as an `Ix.Name` (string components only). -/
private def ixNameOf (s : String) : Ix.Name :=
  s.splitOn "." |>.foldl Ix.Name.mkStr Ix.Name.mkAnon

/-- `prim-addrs-artifact` (manual): every primitive address of `Ix.PrimAddrs`
(`leanParityTable`, without the reserved markers, which are not constants) is the
record a compiled environment (`IX_PRIM_IXE`, an `.ixe` file such as Init+Std's)
holds and publishes under the primitive's Lean name. The table is hand-copied from
the compiler's output (`ixon-v4-primitives`), so a change to the record format or
to the compiler's output that is not carried into it fails here. -/
def artifact : IO UInt32 := do
  let some path ← IO.getEnv "IX_PRIM_IXE"
    | IO.eprintln "[prim-addrs-artifact] set IX_PRIM_IXE to an .ixe file"; return 1
  let env ← IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
  let markers := Ix.PrimAddrs.reservedMarkerAddrs.map (·.2)
  let mut bad : Array String := #[]
  let mut checked := 0
  for (name, a) in Ix.PrimAddrs.leanParityTable do
    if markers.contains a then continue
    checked := checked + 1
    match env.named[ixNameOf name]? with
    | some named =>
      unless named.addr == a do
        bad := bad.push s!"{name}: published at {named.addr}, the table has {a}"
      unless env.consts.contains a do
        bad := bad.push s!"{name}: no record at {a}"
    | none => bad := bad.push s!"{name}: not published"
  for b in bad do IO.eprintln s!"[prim-addrs-artifact] {b}"
  IO.println s!"[prim-addrs-artifact] {checked} primitive addresses against {path}: \
    {checked - bad.size} resolve, {bad.size} problems"
  return if bad.isEmpty then 0 else 1

end Tests.Ix.Kernel.PrimAddrs
