/-
  `Ix.Catalog`: the Lean mirror of the `.ixc` catalog manifest
  (`crates/ixon/src/catalog.rs` is the Rust source of truth; the
  `catalog` suite pins byte-level parity between the two).

  A catalog is semantically ONE anonymous env — the union of its
  members' constant sets — committed by two roots:

  - `membersRoot`: canonical merkle root over member ENV ROOTS (the
    membership commitment);
  - `contentRoot`: canonical root over the union's constant addresses
    — the env root of the virtual union env, never materialized.

  Anonymous Ixon is conflict-free (§2 is content-addressed; a key
  collision implies byte-equal values), so catalog identity involves
  no names, no qualification, and no union import anywhere. The union
  loader that used to live here — streaming qualified import, staging
  copies, kernel replay, audit — is deleted; per-member pieces are
  compiled in separate processes and meet only in this manifest.
  Replay planning survives in `Ix.Replay` (shared with `import_ixe`).

  On disk a `.ixc` is a self-contained DIRECTORY: the binary manifest
  this module mirrors lives at `<name>.ixc/manifest`, with the piece
  files (`<label>.ixe`) next to it — no separate pieces dir, no
  report side-files (the manifest IS the machine-readable record).

  This mirror covers the wire format and the load-time invariants
  (`membersRoot` recomputed on parse, deps topo-ordered, labels
  filename-safe, unknown flags rejected). Piece-file operations —
  assemble, verify, merge — live Rust-side behind `ix catalog` /
  `ix merge` (`Ix/Cli/CatalogCmd.lean`, `Ix/Cli/MergeCmd.lean`).
-/
module

public import Ix.Ixon
public import Ix.Merkle

public section

namespace Ix.Catalog

open Ixon (PutM GetM putU8 getU8 putBytes getBytes runPut runGet)

/-- Magic bytes at the head of every `.ixc` file. -/
def MAGIC : ByteArray := String.toUTF8 "IXC" ++ ⟨#[0, 0, 0, 0, 0]⟩

/-- `.ixc` format version. -/
def VERSION : UInt32 := 1

/-- Storage-profile flag: bit0 of the header `flags` word. -/
def FLAG_CHUNKED : UInt32 := 1

/-- One catalog member: the anon env root (semantic identity) plus
    catalog-level metadata — where "consistent naming" now lives. -/
structure Member where
  envRoot : Address
  constCount : UInt64
  /-- Qualifier, e.g. `"Mathlib"`; doubles as the piece filename stem
      (`<label>.ixe`), so it must be a bare name. -/
  label : String
  toolchain : String
  sourcePin : String
  /-- Member indices, all strictly before this member (topo order). -/
  deps : Array UInt32
  /-- Store key of the member's const-set `AssumptionTree` (the
      `ix tree env` object), when persisted. -/
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

structure Catalog where
  membersRoot : Address
  contentRoot : Address
  members : Array Member
  storage : Storage
  /-- Bytes after the storage section, preserved verbatim (future
      trailing sections; opaque to this version). -/
  trailing : ByteArray
  deriving Inhabited

instance : BEq Catalog where
  beq a b := a.membersRoot == b.membersRoot
    && a.contentRoot == b.contentRoot
    && a.members == b.members
    && a.storage == b.storage
    && a.trailing == b.trailing

/-- Canonical root over the entries' env roots. -/
def membersRootOf (members : Array Member) : Address :=
  Ix.Merkle.merkleRootCanonical (members.map (·.envRoot))
    |>.getD Ix.Merkle.zeroAddress

/-- A label doubles as a filename stem; reject anything that could
    escape a pieces dir (mirrors the Rust `validate_label`). -/
def validateLabel (label : String) : Except String Unit := do
  if label.isEmpty then
    throw "catalog: empty member label"
  if label.any (fun c => c == '/' || c == '\\' || c == '\x00')
      || label == "." || label == ".." then
    throw s!"catalog: label `{label}` is not a bare filename"

/-! ## Wire format (fixed-width LE, the `.ixes` convention) -/

private def putU16LE (x : UInt16) : PutM Unit := do
  putU8 x.toUInt8
  putU8 (x >>> 8).toUInt8

private def getU16LE : GetM UInt16 := do
  let a ← getU8
  let b ← getU8
  return a.toUInt16 ||| (b.toUInt16 <<< 8)

private def putU32LE (x : UInt32) : PutM Unit := do
  putU8 x.toUInt8
  putU8 (x >>> 8).toUInt8
  putU8 (x >>> 16).toUInt8
  putU8 (x >>> 24).toUInt8

private def getU32LE : GetM UInt32 := do
  let a ← getU8
  let b ← getU8
  let c ← getU8
  let d ← getU8
  return a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16)
    ||| (d.toUInt32 <<< 24)

private def putU64LEr (x : UInt64) : PutM Unit := do
  putU32LE x.toUInt32
  putU32LE (x >>> 32).toUInt32

private def getU64LEr : GetM UInt64 := do
  let lo ← getU32LE
  let hi ← getU32LE
  return lo.toUInt64 ||| (hi.toUInt64 <<< 32)

private def putStr16 (s : String) : PutM Unit := do
  let bytes := s.toUTF8
  putU16LE bytes.size.toUInt16
  putBytes bytes

private def getStr16 : GetM String := do
  let len ← getU16LE
  let bytes ← getBytes len.toNat
  match String.fromUTF8? bytes with
  | some s => return s
  | none => throw "invalid utf8 string in .ixc"

private def putAddr (a : Address) : PutM Unit := putBytes a.hash

private def getAddr : GetM Address := do
  let bytes ← getBytes 32
  return ⟨bytes⟩

def putMember (m : Member) : PutM Unit := do
  putAddr m.envRoot
  putU64LEr m.constCount
  putStr16 m.label
  putStr16 m.toolchain
  putStr16 m.sourcePin
  putU32LE m.deps.size.toUInt32
  for d in m.deps do putU32LE d
  match m.preimage with
  | some a => putU8 1; putAddr a
  | none => putU8 0

def ser (c : Catalog) : ByteArray := runPut do
  putBytes MAGIC
  putU32LE VERSION
  putU32LE (match c.storage with
    | .chunked _ => FLAG_CHUNKED
    | .fat _ => 0)
  putAddr c.membersRoot
  putAddr c.contentRoot
  putU32LE c.members.size.toUInt32
  for m in c.members do putMember m
  match c.storage with
  | .fat pieces =>
    for p in pieces do
      putAddr p.fileHash
      putU64LEr p.fileBytes
  | .chunked chunks =>
    putU32LE chunks.size.toUInt32
    for ch in chunks do
      putAddr ch.chunkRoot
      putAddr ch.fileHash
      putU64LEr ch.fileBytes
      putU32LE ch.owner
  putBytes c.trailing

private def getMember (idx : Nat) : GetM Member := do
  let envRoot ← getAddr
  let constCount ← getU64LEr
  let label ← getStr16
  match validateLabel label with
  | .ok () => pure ()
  | .error e => throw e
  let toolchain ← getStr16
  let sourcePin ← getStr16
  let depCount ← getU32LE
  let mut deps : Array UInt32 := #[]
  for _ in [0:depCount.toNat] do
    let d ← getU32LE
    if d.toNat ≥ idx then
      throw s!"catalog: member {idx} ({label}) depends on member {d}, \
which is not strictly before it — members are topo-ordered, deps first"
    deps := deps.push d
  let preimage ← do
    if (← getU8) == 1 then pure (some (← getAddr)) else pure none
  return { envRoot, constCount, label, toolchain, sourcePin, deps, preimage }

/-- Parse and structurally validate, `membersRoot` recomputed from the
    entries (a mismatch is rejected on load — the `.ixe` root
    discipline one level up). `contentRoot` needs the storage bytes;
    `ix catalog verify` binds it. Mirrors the Rust `from_bytes`. -/
def de (bytes : ByteArray) : Except String Catalog := do
  let (catalog, consumed) ← runGetPrefix bytes
  -- Trailing bytes are future sections, preserved opaquely.
  return { catalog with
    trailing := bytes.extract consumed bytes.size }
where
  runGetPrefix (bytes : ByteArray) : Except String (Catalog × Nat) := do
    let core : GetM (Catalog × Nat) := do
      let magic ← getBytes 8
      unless magic == MAGIC do
        throw "not an .ixc file (bad magic)"
      let version ← getU32LE
      unless version == VERSION do
        throw s!"unsupported .ixc version {version} (expected {VERSION})"
      let flags ← getU32LE
      if flags &&& (~~~FLAG_CHUNKED) != 0 then
        throw s!"unknown .ixc flags {flags}"
      let membersRoot ← getAddr
      let contentRoot ← getAddr
      let memberCount ← getU32LE
      let mut members : Array Member := #[]
      for i in [0:memberCount.toNat] do
        members := members.push (← getMember i)
      let storage ← do
        if flags &&& FLAG_CHUNKED == 0 then
          let mut pieces : Array FatPiece := #[]
          for _ in [0:memberCount.toNat] do
            let fileHash ← getAddr
            let fileBytes ← getU64LEr
            pieces := pieces.push { fileHash, fileBytes }
          pure (Storage.fat pieces)
        else
          let chunkCount ← getU32LE
          let mut chunks : Array Chunk := #[]
          for _ in [0:chunkCount.toNat] do
            let chunkRoot ← getAddr
            let fileHash ← getAddr
            let fileBytes ← getU64LEr
            let owner ← getU32LE
            if owner.toNat ≥ memberCount.toNat then
              throw s!"catalog: chunk owner {owner} out of range \
({memberCount} members)"
            chunks := chunks.push { chunkRoot, fileHash, fileBytes, owner }
          pure (Storage.chunked chunks)
      let recomputed := membersRootOf members
      unless recomputed == membersRoot do
        throw s!"catalog: members_root mismatch — stored \
{membersRoot}, recomputed {recomputed} from the member entries"
      let consumed := (← get).idx
      return ({ membersRoot, contentRoot, members, storage,
                trailing := .empty }, consumed)
    Ixon.runGet core bytes

end Ix.Catalog

end
