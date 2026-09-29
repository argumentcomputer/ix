import Compilatrix.Ixon.V3.ConstDecode
import Compilatrix.Ixon.Merkle

/-! Anonymous Ixon v3 ingress. The authenticated source boundary consists
of the format header, addressed constants and blobs, assumptions, and hints.
As in ix's anonymous reader, presentation metadata is retained as opaque
bytes; this is not a validator of the full metadata serialization. -/

namespace Compilatrix.Ixon.V3

def producerRevision : String := "0a31c8dbc63755924c645bf1afedc563e395e88a"

structure Env where
  consts : Std.HashMap Address ByteArray := {}
  blobs : Std.HashMap Address ByteArray := {}
  root : Address := Merkle.zeroAddress
  main : Option Address := none
  assumptions : Array Address := #[]
  /-- 0 = opaque, 1 = abbrev, 2 + height = regular. -/
  hints : Array (Address × UInt64) := #[]
  metadata : ByteArray := .empty
  deriving Inhabited

def getOptionalAddress : GetM (Option Address) := do
  match ← getU8 with
  | 0 => return none
  | 1 => some <$> Serialize.get
  | _ => throw "ixon-v3: invalid optional address"

/-- Count bounds are checked before allocation, including the minimum
encoded size of each entry. -/
def getBoundedCount (limit width : Nat) : GetM Nat := do
  let count := (← getTag0).size.toNat
  let state ← get
  if count > limit || count > (state.bytes.size - state.idx) / width then
    throw "ixon-v3: count exceeds input or entry budget"
  return count

def requireAscending (previous : Option Address) (address : Address) : GetM Unit := do
  if let some before := previous then
    unless Merkle.addressLT before address do
      throw "ixon-v3: addresses must be strictly increasing"

def getAddressList (limit : Nat := 16384) : GetM (Array Address) := do
  let count ← getBoundedCount limit 32
  let mut result := #[]
  for _ in [:count] do
    let address ← Serialize.get
    requireAscending result.back? address
    result := result.push address
  return result

def getObjectTable (constants : Bool) : GetM (Array (Address × ByteArray)) := do
  let count ← getBoundedCount 16384 33
  let mut result : Array (Address × ByteArray) := #[]
  for _ in [:count] do
    let address ← Serialize.get
    requireAscending (result.back?.map Prod.fst) address
    let size := (← getTag0).size.toNat
    if size > 1024 * 1024 then throw "ixon-v3: object byte budget exceeded"
    let bytes ← getBytes size
    unless Address.blake3 bytes == address do throw "ixon-v3: object hash mismatch"
    if constants then
      let _ ← (decodeConstant bytes : Except String _)
    result := result.push (address, bytes)
  return result

def getAnonymousEnv : GetM Env := do
  let tag ← getTag4
  unless tag.flag == 0xE && tag.size == 3 do
    throw "ixon-v3: expected environment format 3"
  let root ← Serialize.get
  let main ← getOptionalAddress
  let assumptions ← getAddressList
  let blobs ← getObjectTable false
  let constants ← getObjectTable true
  unless Merkle.rootCanonical (constants.map Prod.fst) == root do
    throw "ixon-v3: constant root mismatch"
  let consts := constants.foldl (fun table (address, bytes) => table.insert address bytes)
    ({} : Std.HashMap Address ByteArray)
  if let some address := main then
    unless consts.contains address do throw "ixon-v3: main is absent from constants"
  let count ← getBoundedCount constants.size 2
  let mut cursor := 0
  let mut hints := #[]
  for _ in [:count] do
    let delta := (← getTag0).size.toNat
    if delta == 0 then throw "ixon-v3: zero hint delta"
    let index := cursor + delta - 1
    let some (address, _) := constants[index]?
      | throw "ixon-v3: hint index out of range"
    let hint := (← getTag0).size
    if hint.toNat > UInt32.size + 1 then throw "ixon-v3: hint height out of range"
    hints := hints.push (address, hint)
    cursor := index + 1
  let state ← get
  let metadata ← getBytes (state.bytes.size - state.idx)
  let blobs := blobs.foldl (fun table (address, bytes) => table.insert address bytes)
    ({} : Std.HashMap Address ByteArray)
  return { consts, blobs, root, main, assumptions, hints, metadata }

/-- Decode only the anonymous sections; metadata is outside admission.
The caller must supply an expected source root when one is externally bound. -/
def decodeAnonymousEnv (bytes : ByteArray) (maxBytes : Nat := 16 * 1024 * 1024) :
    Except String Env := do
  if bytes.size > maxBytes then throw "ixon-v3: environment byte budget exceeded"
  runGet getAnonymousEnv bytes

end Compilatrix.Ixon.V3
