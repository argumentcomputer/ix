import IxCC.Ixon.V3.Wire
import IxCC.Ixon.Merkle
import IxCC.Ixon.PureHash

/-! Ixon environment ingress. The authenticated source boundary consists of
the format header, addressed constants and blobs, assumptions, hints and, in a
role-bound environment, the role binding (`IxCC/docs/byte-contract.md`). As in
ix's anonymous reader, presentation metadata is retained as opaque bytes;
this is not a validator of the full metadata serialization.

Two envelopes are read, as ix writes them (`Ixon.Env.putEnv`, `Ix/Ixon.lean`,
whose module is outside ix's pure codec package):

* the **unbound** envelope: header TagN(4) with flag `0xE` and value 4 (the
  byte `0xE4`), the root, `main`, the assumptions, then the blobs, constants,
  hints and metadata;
* the **role-bound** envelope: value 5 (`0xE5`), the same sections with the
  role binding inserted after the assumptions: a 32-byte address, a TagN(0)
  length and that many bytes, the binding section, which must hash to the
  address (`V3.Binding`). The section is the certified kernel's to decode and
  admit (`Ix.Kernel.RoleTable.ofBytes`, `admitBinding`): every compile path
  passes it to the kernel's acceptance (`KernelFront.accept`), which refuses
  a section that is not a canonical, well-formed role table.

Every count, length, hint delta and hint is a TagN(0) integer read by ix's
codec, and constants are decoded by `decodeConstant` (ix's canonical decoder).
Every blob and constant must hash to its address, and the constant root must be
the canonical Merkle root of the constant addresses, both with pure BLAKE3
(`Address.blake3Pure`): ix's certified reader treats addresses as keys, so
authentication is ours. The root covers the constants only; the binding is
named by its own address. -/

namespace IxCC.Ixon.V3

/-- The unbound `.ixe` envelope version (`Ixon.Env.LEGACY_ENV_VERSION` in ix). -/
def envVersion : UInt64 := 4

/-- The role-bound `.ixe` envelope version (`Ixon.Env.BINDING_ENV_VERSION` in
ix): the unbound layout with a role binding after the assumptions. -/
def boundEnvVersion : UInt64 := 5

/-- The object format byte that claims and catalog manifests bind (ix's
`Ixon.Env.OBJECT_FORMAT`, the checked-object grammar version, which both
envelopes share). -/
def objectFormat : UInt8 := envVersion.toUInt8

/-- A role binding as the envelope carries it: the binding section's address
and bytes. IxCC authenticates the bytes against the address; decoding and
admitting the table is the certified kernel's (`KernelFront.accept`). -/
structure Binding where
  /-- The binding hash: the pure BLAKE3 hash of `bytes`. -/
  address : Address
  /-- The binding section. -/
  bytes : ByteArray
  deriving Inhabited

/-- The most bytes a binding section can have: 255 bound roles and 255
evidence entries of 255 proofs each (the format of
`IxCK/Kernel/Ixon/RoleTable.lean`). -/
def Binding.maxBytes : Nat := 4 + 255 * 33 + 1 + 255 * (2 + 255 * 33)

structure Env where
  consts : Std.HashMap Address ByteArray := {}
  blobs : Std.HashMap Address ByteArray := {}
  root : Address := Merkle.zeroAddress
  main : Option Address := none
  assumptions : Array Address := #[]
  /-- 0 = opaque, 1 = abbrev, 2 + height = regular. -/
  hints : Array (Address × UInt64) := #[]
  metadata : ByteArray := .empty
  /-- The role binding: `some` exactly when the bytes were the role-bound
  envelope (`0xE5`), `none` for the unbound one (`0xE4`). -/
  binding : Option Binding := none
  deriving Inhabited

/-- Whether the environment was read from the role-bound envelope. -/
def Env.isBound (env : Env) : Bool := env.binding.isSome

/-- The role table's address (the binding hash) of a role-bound environment, `none`
for an unbound one: what a compile claim names beside the root. -/
def Env.bindingAddress (env : Env) : Option Address := env.binding.map (·.address)

abbrev EnvM := _root_.Ixon.GetM

def getAddress : EnvM Address := do
  let bytes ← _root_.Ixon.getBytes 32
  match Address.ofBytes? bytes with
  | some address => return address
  | none => throw "ixon-v4: truncated address"

def getNat : EnvM Nat := return (← _root_.Ixon.getTagN 0).value.toNat

def getOptionalAddress : EnvM (Option Address) := do
  match ← _root_.Ixon.getU8 with
  | 0 => return none
  | 1 => some <$> getAddress
  | _ => throw "ixon-v4: invalid optional address"

/-- Count bounds are checked before allocation, including the minimum
encoded size of each entry. -/
def getBoundedCount (limit width : Nat) : EnvM Nat := do
  let count ← getNat
  let state ← get
  if count > limit || count > (state.bytes.size - state.idx) / width then
    throw "ixon-v4: count exceeds input or entry budget"
  return count

def requireAscending (previous : Option Address) (address : Address) : EnvM Unit := do
  if let some before := previous then
    unless Merkle.addressLT before address do
      throw "ixon-v4: addresses must be strictly increasing"

def getAddressList (limit : Nat := 16384) : EnvM (Array Address) := do
  let count ← getBoundedCount limit 32
  let mut result := #[]
  for _ in [:count] do
    let address ← getAddress
    requireAscending result.back? address
    result := result.push address
  return result

def getObjectTable (constants : Bool) : EnvM (Array (Address × ByteArray)) := do
  let count ← getBoundedCount 16384 33
  let mut result : Array (Address × ByteArray) := #[]
  for _ in [:count] do
    let address ← getAddress
    requireAscending (result.back?.map Prod.fst) address
    let size ← getNat
    if size > 1024 * 1024 then throw "ixon-v4: object byte budget exceeded"
    let bytes ← _root_.Ixon.getBytes size
    unless Address.blake3Pure bytes == address do throw "ixon-v4: object hash mismatch"
    if constants then
      match decodeConstant bytes with
      | .ok _ => pure ()
      | .error error => throw error
    result := result.push (address, bytes)
  return result

/-- The role binding of the role-bound envelope (ix's `getBindingHeader`): the
binding section's address, its length (at most the format's largest section,
`Binding.maxBytes`) and its bytes, which must hash to the address with pure
BLAKE3. -/
def getBinding : EnvM Binding := do
  let address ← getAddress
  let size ← getNat
  if size > Binding.maxBytes then throw "role binding: the section exceeds the format's size"
  let bytes ← _root_.Ixon.getBytes size
  unless Address.blake3Pure bytes == address do
    throw "role binding: the section's bytes do not hash to its address"
  return { address, bytes }

def getAnonymousEnv : EnvM Env := do
  let tag ← _root_.Ixon.getTagN 4
  unless tag.flag == 0xE && (tag.value == envVersion || tag.value == boundEnvVersion) do
    throw "ixon-v4: expected environment format 4 (unbound) or 5 (role-bound)"
  let root ← getAddress
  let main ← getOptionalAddress
  let assumptions ← getAddressList
  let binding ← if tag.value == boundEnvVersion then some <$> getBinding else pure none
  let blobs ← getObjectTable false
  let constants ← getObjectTable true
  unless Merkle.rootCanonicalBy Address.blake3Pure (constants.map Prod.fst) == root do
    throw "ixon-v4: constant root mismatch"
  let consts := constants.foldl (fun table (address, bytes) => table.insert address bytes)
    ({} : Std.HashMap Address ByteArray)
  if let some address := main then
    unless consts.contains address do throw "ixon-v4: main is absent from constants"
  let count ← getBoundedCount constants.size 2
  let mut cursor := 0
  let mut hints := #[]
  for _ in [:count] do
    let delta ← getNat
    if delta == 0 then throw "ixon-v4: zero hint delta"
    let index := cursor + delta - 1
    let some (address, _) := constants[index]?
      | throw "ixon-v4: hint index out of range"
    let hint := (← _root_.Ixon.getTagN 0).value
    if hint.toNat > UInt32.size + 1 then throw "ixon-v4: hint height out of range"
    hints := hints.push (address, hint)
    cursor := index + 1
  let state ← get
  let metadata ← _root_.Ixon.getBytes (state.bytes.size - state.idx)
  let blobs := blobs.foldl (fun table (address, bytes) => table.insert address bytes)
    ({} : Std.HashMap Address ByteArray)
  return { consts, blobs, root, main, assumptions, hints, metadata, binding }

/-- Decode the anonymous sections of either envelope (unbound `0xE4` or
role-bound `0xE5`); metadata is outside admission. The result's `binding` says
which envelope it was. The caller must supply an expected source root when one
is externally bound. -/
def decodeAnonymousEnv (bytes : ByteArray) (maxBytes : Nat := 16 * 1024 * 1024) :
    Except String Env := do
  if bytes.size > maxBytes then throw "ixon-v4: environment byte budget exceeded"
  _root_.Ixon.runGetExact getAnonymousEnv bytes

end IxCC.Ixon.V3
