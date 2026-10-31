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
  filename-safe, no two members with one env root or label, a strict
  preimage tag, unknown flags and trailing bytes rejected). The writer
  refuses lengths the format cannot carry, as the Rust writer does.
  Piece-file operations — assemble, verify, merge — live Rust-side
  behind `ix catalog` / `ix merge` (`Ix/Cli/CatalogCmd.lean`,
  `Ix/Cli/MergeCmd.lean`).
-/
module

public import Ix.Claim
public import Ix.Ixon
public import Ix.Merkle

public section

namespace Ix.Catalog

open Ixon (PutM GetM putU8 getU8 putBytes getBytes runPut runGet)

/-- Magic bytes at the head of every `.ixc` file. -/
def MAGIC : ByteArray := String.toUTF8 "IXC" ++ ⟨#[0, 0, 0, 0, 0]⟩

/-- Manifest v3 binds the Ixon object format (`Ixon.Env.OBJECT_FORMAT`)
    and erased-lean-v2 catalog claims (`Ix.Claim.VALIDATOR_ERASED_LEAN`). -/
def VERSION : UInt32 := 3

/-- Storage-profile flag: bit0 of the header `flags` word. -/
def FLAG_CHUNKED : UInt32 := 1

/-- One catalog member: the anon env root (semantic identity) plus
    catalog-level metadata — where "consistent naming" now lives. -/
structure Member where
  envRoot : Address
  /-- The piece's role binding hash (`Ixon.RoleBinding.address`): which
      constants play the checker's roles in this member. Members compiled on
      different Lean toolchains have different bindings; `ix catalog verify`
      checks it against the piece. -/
  binding : Address
  constCount : UInt64
  /-- Qualifier, e.g. `"Mathlib"`; doubles as the piece filename stem
      (`<label>.ixe`), so it must be a bare name. -/
  label : String
  /-- The Lean toolchain the member was elaborated with. Members may span
      toolchains. -/
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
  deriving BEq, Inhabited

/-- Canonical root over the entries' env roots. Canonical-set semantics:
    duplicates collapse, which is why a manifest with duplicate members is
    refused on load. -/
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

/-- Reject two members with one env root or one label: the members root is
    a set root, so a repeated env root would vanish from it, and a label is a
    filename stem, so a repeated label would name one piece twice. Mirrors the
    Rust `check_unique`. -/
def checkUnique (members : Array Member) : Except String Unit := do
  let mut roots : Std.HashSet Address := {}
  let mut labels : Std.HashSet String := {}
  for m in members do
    if roots.contains m.envRoot then
      throw s!"catalog: duplicate member env root {m.envRoot} ({m.label})"
    if labels.contains m.label then
      throw s!"catalog: duplicate member label `{m.label}`"
    roots := roots.insert m.envRoot
    labels := labels.insert m.label

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
  putAddr m.binding
  putU64LEr m.constCount
  putStr16 m.label
  putStr16 m.toolchain
  putStr16 m.sourcePin
  putU32LE m.deps.size.toUInt32
  for d in m.deps do putU32LE d
  match m.preimage with
  | some a => putU8 1; putAddr a
  | none => putU8 0

/-- The lengths the wire format carries: strings of at most 65,535 bytes,
    counts below 2^32, and one fat storage row per member. The Rust writer
    refuses the same. -/
def checkWire (c : Catalog) : Except String Unit := do
  let u32Max := 0xFFFFFFFF
  let str16 (what s : String) : Except String Unit :=
    unless s.utf8ByteSize ≤ 0xFFFF do
      throw s!"catalog: {what} over 64 KiB: {s.take 40}…"
  unless c.members.size ≤ u32Max do throw "catalog: over u32::MAX members"
  for m in c.members do
    str16 "label" m.label
    str16 "toolchain" m.toolchain
    str16 "source pin" m.sourcePin
    unless m.deps.size ≤ u32Max do throw "catalog: over u32::MAX deps"
  match c.storage with
  | .fat pieces =>
    unless pieces.size == c.members.size do
      throw s!"catalog: fat profile carries {pieces.size} storage rows for \
{c.members.size} members"
  | .chunked chunks =>
    unless chunks.size ≤ u32Max do throw "catalog: over u32::MAX chunks"

private def put (c : Catalog) : PutM Unit := do
  putBytes MAGIC
  putU32LE VERSION
  putU32LE (match c.storage with
    | .chunked _ => FLAG_CHUNKED
    | .fat _ => 0)
  putU8 Ixon.Env.OBJECT_FORMAT
  putU8 Ix.Claim.VALIDATOR_ERASED_LEAN
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

/-- Serialize, refusing what `checkWire` refuses. -/
def ser (c : Catalog) : Except String ByteArray := do
  checkWire c
  return runPut (put c)

private def getMember (idx : Nat) : GetM Member := do
  let envRoot ← getAddr
  let binding ← getAddr
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
  let preimage ← match ← getU8 with
    | 0 => pure none
    | 1 => pure (some (← getAddr))
    | tag => throw s!"catalog: member {idx} ({label}): bad preimage tag {tag}"
  return { envRoot, binding, constCount, label, toolchain, sourcePin, deps, preimage }

/-- Parse and structurally validate, `membersRoot` recomputed from the
    entries (a mismatch is rejected on load — the `.ixe` root
    discipline one level up). `contentRoot` needs the storage bytes;
    `ix catalog verify` binds it. Mirrors the Rust `from_bytes`. -/
def de (bytes : ByteArray) : Except String Catalog := do
  let core : GetM Catalog := do
    let magic ← getBytes 8
    unless magic == MAGIC do
      throw "not an .ixc file (bad magic)"
    let version ← getU32LE
    unless version == VERSION do
      throw s!"unsupported .ixc version {version} (expected {VERSION})"
    let flags ← getU32LE
    if flags &&& (~~~FLAG_CHUNKED) != 0 then
      throw s!"unknown .ixc flags {flags}"
    let format ← getU8
    unless format == Ixon.Env.OBJECT_FORMAT do
      throw s!"catalog: unsupported object format {format}, expected \
        {Ixon.Env.OBJECT_FORMAT} — regenerate the catalog"
    unless (← getU8) == Ix.Claim.VALIDATOR_ERASED_LEAN do
      throw "catalog: wrong validator identity"
    let membersRoot ← getAddr
    let contentRoot ← getAddr
    let memberCount ← getU32LE
    let mut members : Array Member := #[]
    for i in [0:memberCount.toNat] do
      members := members.push (← getMember i)
    match checkUnique members with
    | .ok () => pure ()
    | .error e => throw e
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
    let rest := bytes.size - (← get).idx
    unless rest == 0 do
      throw s!"catalog: {rest} trailing bytes after the storage section"
    let recomputed := membersRootOf members
    unless recomputed == membersRoot do
      throw s!"catalog: members_root mismatch — stored \
{membersRoot}, recomputed {recomputed} from the member entries"
    return { membersRoot, contentRoot, members, storage }
  Ixon.runGet core bytes

end Ix.Catalog

end
