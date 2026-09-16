import Compilatrix.Ixon.V3.Catalog.Basic

/-! Bounded manifest-v2 parser, from ix 2afb4eac340cd4cbe94ed9e507561f3ad8375ebd
Ix/Catalog.lean and crates/ixon/src/catalog.rs. Fixed-width little-endian
integers are distinct from the environment's canonical Tag0 encoding. -/

namespace Compilatrix.Ixon.V3.Catalog

private abbrev Parser := StateT GetState (Except Error)

private def wire (p : GetM α) : Parser α := fun state =>
  (p.run state).mapError Error.syntax

private def u8 : Parser UInt8 := wire getU8

private def u16 : Parser UInt16 := do
  let a ← u8
  let b ← u8
  return a.toUInt16 ||| (b.toUInt16 <<< 8)

private def u32 : Parser UInt32 := do
  let a ← u16
  let b ← u16
  return a.toUInt32 ||| (b.toUInt32 <<< 16)

private def u64 : Parser UInt64 := do
  let a ← u32
  let b ← u32
  return a.toUInt64 ||| (b.toUInt64 <<< 32)

private def addr : Parser Address := wire Serialize.get

private def string16 : Parser String := do
  let bytes ← wire (getBytes (← u16).toNat)
  match String.fromUTF8? bytes with
  | some s => return s
  | none => throw (.syntax "invalid UTF-8 manifest string")

private def boundedCount (name : String) (maximum width : Nat) : Parser Nat := do
  let count := (← u32).toNat
  requireLimit name count maximum
  let state ← get
  if count > (state.bytes.size - state.idx) / width then
    throw (.syntax s!"{name} exceeds the remaining manifest bytes")
  return count

private def member (limits : Limits) (i previousDeps : Nat) : Parser (Member × Nat) := do
  let envRoot ← addr
  let constCount ← u64
  let label ← string16
  unless validLabel label do throw (.manifest s!"member {i}: invalid filename label")
  let toolchain ← string16
  let sourcePin ← string16
  let count ← boundedCount "dependencies" limits.dependencyEdges 4
  let next := previousDeps + count
  requireLimit "dependency edges" next limits.dependencyEdges
  let mut deps := #[]
  for _ in [:count] do
    let d ← u32
    unless d.toNat < i do throw (.manifest s!"member {i}: dependency must precede member")
    deps := deps.push d
  let preimage ← match ← u8 with
    | 0 => pure none
    | 1 => some <$> addr
    | _ => throw (.syntax "invalid preimage tag")
  return (⟨envRoot, constCount, label, toolchain, sourcePin, deps, preimage⟩, next)

/-- Parse only manifest v2 / object format 3 / erased-lean-v1. Unknown future
sections are retained, never promoted to proof or resource evidence. -/
def decodeManifestWith (limits : Limits) (bytes : ByteArray) : Except Error Manifest := do
  requireLimit "manifest bytes" bytes.size limits.manifestBytes
  let parser : Parser Manifest := do
    unless (← wire (getBytes 8)) == magic do throw (.syntax "bad catalog magic")
    let version ← u32
    unless version == 2 do throw (.scope version 0 0)
    let flags ← u32
    unless flags ≤ 1 do throw (.manifest "unknown catalog flags")
    let objectFormat ← u8
    let validator ← u8
    unless objectFormat == 3 && validator == 1 do
      throw (.scope version objectFormat validator)
    let membersRoot ← addr
    let contentRoot ← addr
    let count ← boundedCount "members" limits.members 52
    let mut members := #[]
    let mut dependencyTotal := 0
    let mut labels : Std.HashSet String := {}
    for i in [:count] do
      let (m, next) ← member limits i dependencyTotal
      if labels.contains m.label then throw (.manifest "duplicate member filename label")
      labels := labels.insert m.label
      members := members.push m
      dependencyTotal := next
    let storage ← if flags == 0 then do
      requireLimit "storage units" count limits.storageUnits
      let mut rows := #[]
      for _ in [:count] do
        rows := rows.push (⟨← addr, ← u64⟩ : FatPiece)
      pure (.fat rows)
    else do
      let count ← boundedCount "chunks" limits.storageUnits 76
      let mut rows := #[]
      for _ in [:count] do
        let chunkRoot ← addr
        let fileHash ← addr
        let fileBytes ← u64
        let owner ← u32
        unless owner.toNat < members.size do throw (.manifest "chunk owner out of range")
        rows := rows.push (⟨chunkRoot, fileHash, fileBytes, owner⟩ : Chunk)
      pure (.chunked rows)
    unless membersRootOf members == membersRoot do
      throw (.manifest "member roots do not match members_root")
    let state ← get
    let trailing ← wire (getBytes (state.bytes.size - state.idx))
    return { version, objectFormat, validator, membersRoot, contentRoot, members, storage, trailing }
  return (← parser.run ⟨bytes, 0⟩).1

def decodeManifest (bytes : ByteArray) : Except Error Manifest :=
  decodeManifestWith {} bytes

end Compilatrix.Ixon.V3.Catalog
