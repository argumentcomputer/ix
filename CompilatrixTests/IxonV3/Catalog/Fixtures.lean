import CompilatrixTests.IxonV3.TypingFixtures
import Compilatrix.Ixon.V3.Catalog

namespace CompilatrixTests.IxonV3.CatalogFixtures

open Compilatrix.Ixon Compilatrix.Ixon.V3 Catalog

/-- Independent test framing for the fixed-width manifest wire format. -/
def le (width : Nat) (value : UInt64) : PutM Unit := do
  for i in [:width] do putU8 (value >>> (8 * i).toUInt64).toUInt8

def string16 (s : String) : PutM Unit := do
  le 2 s.toUTF8.size.toUInt64
  putBytes s.toUTF8

def manifestBytes (m : Manifest) : ByteArray := runPut do
  putBytes "IXC".toUTF8
  putBytes ⟨#[0, 0, 0, 0, 0]⟩
  le 4 m.version.toUInt64
  le 4 (match m.storage with | .fat _ => 0 | .chunked _ => 1)
  putU8 m.objectFormat
  putU8 m.validator
  Serialize.put m.membersRoot
  Serialize.put m.contentRoot
  le 4 m.members.size.toUInt64
  for member in m.members do
    Serialize.put member.envRoot
    le 8 member.constCount
    string16 member.label
    string16 member.toolchain
    string16 member.sourcePin
    le 4 member.deps.size.toUInt64
    for dep in member.deps do le 4 dep.toUInt64
    match member.preimage with
    | none => putU8 0
    | some a => putU8 1; Serialize.put a
  match m.storage with
  | .fat rows => for row in rows do
      Serialize.put row.fileHash
      le 8 row.fileBytes
  | .chunked rows =>
    le 4 rows.size.toUInt64
    for row in rows do
      Serialize.put row.chunkRoot
      Serialize.put row.fileHash
      le 8 row.fileBytes
      le 4 row.owner.toUInt64
  putBytes m.trailing

/-- Environment writer used only to exercise independent admission gates. -/
def envBytes (env : Env) : ByteArray := runPut do
  let constants := env.consts.toArray.qsort (fun a b => Merkle.addressLT a.1 b.1)
  let blobs := env.blobs.toArray.qsort (fun a b => Merkle.addressLT a.1 b.1)
  putTag4 ⟨0xE, 3⟩
  Serialize.put (Merkle.rootCanonical (constants.map Prod.fst))
  match env.main with
  | none => putU8 0
  | some a => putU8 1; Serialize.put a
  putTag0 ⟨env.assumptions.size.toUInt64⟩
  for a in env.assumptions do Serialize.put a
  for table in #[blobs, constants] do
    putTag0 ⟨table.size.toUInt64⟩
    for (address, raw) in table do
      Serialize.put address
      putTag0 ⟨raw.size.toUInt64⟩
      putBytes raw
  let hints := env.hints.qsort (fun a b => Merkle.addressLT a.1 b.1)
  putTag0 ⟨hints.size.toUInt64⟩
  let mut cursor := 0
  for (address, hint) in hints do
    let index := (constants.findIdx? (·.1 == address)).getD 0
    putTag0 ⟨(index + 1 - cursor).toUInt64⟩
    putTag0 ⟨hint⟩
    cursor := index + 1
  putBytes env.metadata

def member (env : Env) (i : Nat) : Member :=
  { envRoot := Merkle.rootCanonical (constantAddresses env)
    constCount := env.consts.size.toUInt64, label := s!"m{i}"
    toolchain := "", sourcePin := "", deps := #[], preimage := none }

def fat (pieces : Array ByteArray) : Except String Manifest := do
  let envs ← pieces.mapM decodeAnonymousEnv
  let members := envs.mapIdx fun i env => member env i
  return {
    version := 2, objectFormat := 3, validator := 1
    membersRoot := membersRootOf members
    contentRoot := Merkle.rootCanonical (envs.flatMap constantAddresses)
    members, storage := .fat (pieces.map fun raw => ⟨Address.blake3 raw, raw.size.toUInt64⟩) }

def chunked (members : Array Member) (pieces : Array (ByteArray × Nat)) : Except String Manifest := do
  let envs ← pieces.mapM fun (raw, _) => decodeAnonymousEnv raw
  let rows := pieces.mapIdx fun i (raw, owner) =>
    (⟨envs[i]!.root, Address.blake3 raw, raw.size.toUInt64, owner.toUInt32⟩ : Chunk)
  return {
    version := 2, objectFormat := 3, validator := 1
    membersRoot := membersRootOf members
    contentRoot := Merkle.rootCanonical (envs.flatMap constantAddresses)
    members, storage := .chunked rows }

def membersChanged (m : Manifest) (members : Array Member) : Manifest :=
  { m with members, membersRoot := membersRootOf members }

def mutate (bytes : ByteArray) (offset : Nat) (value : UInt8) : ByteArray :=
  ⟨bytes.data.set! offset value⟩

end CompilatrixTests.IxonV3.CatalogFixtures
