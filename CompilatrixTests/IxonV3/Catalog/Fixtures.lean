import Lean.Data.Json
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
def envBytes (env : Env) : ByteArray := _root_.Ixon.runPut do
  let constants := env.consts.toArray.qsort (fun a b => Merkle.addressLT a.1 b.1)
  let blobs := env.blobs.toArray.qsort (fun a b => Merkle.addressLT a.1 b.1)
  _root_.Ixon.putTagN 4 0xE envVersion
  _root_.Ixon.putBytes (Merkle.rootCanonical (constants.map Prod.fst)).hash
  match env.main with
  | none => _root_.Ixon.putU8 0
  | some a => _root_.Ixon.putU8 1; _root_.Ixon.putBytes a.hash
  _root_.Ixon.putTagN 0 0 env.assumptions.size.toUInt64
  for a in env.assumptions do _root_.Ixon.putBytes a.hash
  for table in #[blobs, constants] do
    _root_.Ixon.putTagN 0 0 table.size.toUInt64
    for (address, raw) in table do
      _root_.Ixon.putBytes address.hash
      _root_.Ixon.putTagN 0 0 raw.size.toUInt64
      _root_.Ixon.putBytes raw
  let hints := env.hints.qsort (fun a b => Merkle.addressLT a.1 b.1)
  _root_.Ixon.putTagN 0 0 hints.size.toUInt64
  let mut cursor := 0
  for (address, hint) in hints do
    let index := (constants.findIdx? (·.1 == address)).getD 0
    _root_.Ixon.putTagN 0 0 (index + 1 - cursor).toUInt64
    _root_.Ixon.putTagN 0 0 hint
    cursor := index + 1
  _root_.Ixon.putBytes env.metadata

def member (env : Env) (i : Nat) : Member :=
  { envRoot := Merkle.rootCanonical (constantAddresses env)
    constCount := env.consts.size.toUInt64, label := s!"m{i}"
    toolchain := "", sourcePin := "", deps := #[], preimage := none }

def fat (pieces : Array ByteArray) : Except String Manifest := do
  let envs ← pieces.mapM decodeAnonymousEnv
  let members := envs.mapIdx fun i env => member env i
  return {
    version := 2, objectFormat := V3.objectFormat, validator := 1
    membersRoot := membersRootOf members
    contentRoot := Merkle.rootCanonical (envs.flatMap constantAddresses)
    members, storage := .fat (pieces.map fun raw => ⟨Address.blake3 raw, raw.size.toUInt64⟩) }

def chunked (members : Array Member) (pieces : Array (ByteArray × Nat)) : Except String Manifest := do
  let envs ← pieces.mapM fun (raw, _) => decodeAnonymousEnv raw
  let rows := pieces.mapIdx fun i (raw, owner) =>
    (⟨envs[i]!.root, Address.blake3 raw, raw.size.toUInt64, owner.toUInt32⟩ : Chunk)
  return {
    version := 2, objectFormat := V3.objectFormat, validator := 1
    membersRoot := membersRootOf members
    contentRoot := Merkle.rootCanonical (envs.flatMap constantAddresses)
    members, storage := .chunked rows }

/-- The chunked reference catalog (`fixtures/ixon-v4/catalog/chunked.ixc`): the
first-owner partition of a fat catalog's pieces. Chunk `i` is member `i`'s
original environment with the constants an earlier member owns removed and
listed as assumptions; it keeps the original blobs and presentation bytes,
and only the hints and `main` of the constants it keeps. The members are the
fat manifest's, and `members.json` lists every member's complete original
address set (the witness chunked admission requires). No constant or blob
bytes are regenerated. -/
def writeChunked (fat out : System.FilePath) : IO Unit := do
  let raw ← IO.FS.readBinFile (fat / "manifest")
  let m ← IO.ofExcept ((decodeManifest raw).mapError reprStr)
  let envs ← (pieceSpecs m).mapM fun spec => do
    IO.ofExcept (decodeAnonymousEnv (← IO.FS.readBinFile (fat / spec.filename)))
  let mut owned : Std.HashSet Compilatrix.Ixon.Address := {}
  let mut pieces : Array (ByteArray × Nat) := #[]
  for h : i in [:envs.size] do
    let env := envs[i]
    let all := constantAddresses env
    let omitted := all.filter owned.contains
    let kept := env.consts.filter fun address _ => !owned.contains address
    let chunk : Env := { env with
      consts := kept
      assumptions := Merkle.dedupSorted (Merkle.sortAddresses (env.assumptions ++ omitted))
      hints := env.hints.filter fun (address, _) => kept.contains address
      main := env.main.filter kept.contains }
    for address in all do owned := owned.insert address
    pieces := pieces.push (envBytes chunk, i)
  let manifest ← IO.ofExcept (chunked m.members pieces)
  IO.FS.createDirAll out
  IO.FS.writeBinFile (out / "manifest") (manifestBytes manifest)
  for (spec, (bytes, _)) in (pieceSpecs manifest).zip pieces do
    IO.FS.writeBinFile (out / spec.filename) bytes
  let witness := Lean.Json.arr (envs.map fun env =>
    Lean.Json.arr ((constantAddresses env).map fun address => Lean.Json.str address.toHex))
  IO.FS.writeFile (out / "members.json") (witness.pretty ++ "\n")

def membersChanged (m : Manifest) (members : Array Member) : Manifest :=
  { m with members, membersRoot := membersRootOf members }

def mutate (bytes : ByteArray) (offset : Nat) (value : UInt8) : ByteArray :=
  ⟨bytes.data.set! offset value⟩

end CompilatrixTests.IxonV3.CatalogFixtures
