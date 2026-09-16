import Compilatrix.Ixon.V3.Env

/-! Catalog-v2 data at the pinned ix source boundary. The manifest's scope
is object format 3 and erased-lean-v1 (validator 1), not a resource claim. -/

namespace Compilatrix.Ixon.V3.Catalog

def magic : ByteArray := "IXC".toUTF8 ++ ⟨#[0, 0, 0, 0, 0]⟩

structure Member where
  envRoot : Address
  constCount : UInt64
  label : String
  toolchain : String
  sourcePin : String
  deps : Array UInt32
  preimage : Option Address
  deriving BEq, Repr, Inhabited

structure FatPiece where
  fileHash : Address
  fileBytes : UInt64
  deriving BEq, Repr, Inhabited

structure Chunk where
  chunkRoot : Address
  fileHash : Address
  fileBytes : UInt64
  owner : UInt32
  deriving BEq, Repr, Inhabited

inductive Storage where
  | fat (pieces : Array FatPiece)
  | chunked (chunks : Array Chunk)
  deriving BEq, Repr, Inhabited

structure Manifest where
  version : UInt32
  objectFormat : UInt8
  validator : UInt8
  membersRoot : Address
  contentRoot : Address
  members : Array Member
  storage : Storage
  /-- Committed by the manifest bytes, but not interpreted as evidence. -/
  trailing : ByteArray := .empty
  deriving BEq, Inhabited

def Manifest.scopeMatches (m : Manifest) : Bool :=
  m.version == 2 && m.objectFormat == 3 && m.validator == 1

structure Limits where
  manifestBytes : Nat := 1024 * 1024
  members : Nat := 4096
  dependencyEdges : Nat := 65536
  storageUnits : Nat := 16384
  pieceBytes : Nat := 16 * 1024 * 1024
  totalPieceBytes : Nat := 64 * 1024 * 1024
  constantEntries : Nat := 65536
  blobEntries : Nat := 65536
  assumptions : Nat := 65536
  hints : Nat := 65536
  unionConstants : Nat := 16384
  unionBlobs : Nat := 16384
  memberEntries : Nat := 131072
  deriving BEq, Repr

inductive Error where
  | syntax (message : String)
  | limit (name : String) (actual maximum : Nat)
  | scope (version : UInt32) (objectFormat validator : UInt8)
  | manifest (message : String)
  | piece (index : Nat) (message : String)
  | coverage (message : String)
  | typing (message : String)
  deriving BEq, Repr

def requireLimit (name : String) (actual maximum : Nat) : Except Error Unit :=
  if actual ≤ maximum then .ok () else .error (.limit name actual maximum)

def membersRootOf (members : Array Member) : Address :=
  Merkle.rootCanonical (members.map (·.envRoot))

def validLabel (s : String) : Bool :=
  !s.isEmpty && s != "." && s != ".." &&
    !s.any (fun c => c == '/' || c == '\\' || c == '\x00')

structure PieceSpec where
  filename : String
  fileHash : Address
  fileBytes : UInt64
  root : Address
  owner : Nat
  deriving BEq, Repr, Inhabited

/-- Manifest parsing validates all indices and filename stems first. -/
def pieceSpecs (m : Manifest) : Array PieceSpec := Id.run do
  match m.storage with
  | .fat rows =>
    return rows.mapIdx fun i row =>
      { filename := s!"{m.members[i]!.label}.ixe"
        fileHash := row.fileHash, fileBytes := row.fileBytes
        root := m.members[i]!.envRoot, owner := i }
  | .chunked rows =>
    return rows.mapIdx fun i row =>
      { filename := s!"{m.members[row.owner.toNat]!.label}.chunk{i}.ixe"
        fileHash := row.fileHash, fileBytes := row.fileBytes
        root := row.chunkRoot, owner := row.owner.toNat }

/-- Full original member sets, not just the addresses first owned by them.
They are witnesses authenticated against each member's root and count. -/
abbrev MemberSets := Array (Array Address)

structure Stats where
  pieceBytes : Nat := 0
  constantEntries : Nat := 0
  blobEntries : Nat := 0
  assumptions : Nat := 0
  hints : Nat := 0
  memberEntries : Nat := 0
  deriving BEq, Repr

structure Loaded where
  manifest : Manifest
  pieces : Array Env
  memberSets : MemberSets
  /-- Exact raw-byte union, with min-merged hints and no external assumptions. -/
  env : Env
  stats : Stats

end Compilatrix.Ixon.V3.Catalog
