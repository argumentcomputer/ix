import Compilatrix.Ixon.V3.Catalog
import Compilatrix.Tools.Check

namespace Compilatrix.Tools.IxonV3Catalog

open Compilatrix.Ixon Compilatrix.Ixon.V3 Catalog

/-- Read at most the configured limit plus one byte, even if the file grows.
Leaf symlinks and nonregular files are not catalog storage units. -/
def readBounded (path : System.FilePath) (limit : Nat) : IO ByteArray := do
  unless (← path.symlinkMetadata).type == .file do
    throw (IO.userError s!"not a regular file: {path}")
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    for _ in [:limit + 1] do
      let chunk ← handle.read (min 65536 (limit + 1 - bytes.size)).toUSize
      if chunk.isEmpty then return bytes
      bytes := bytes ++ chunk
      if bytes.size > limit then throw (IO.userError s!"byte budget exceeded: {path}")
    throw (IO.userError s!"byte budget exceeded: {path}")

def memberSetsFromJson (limits : Limits) (json : Lean.Json) : Except String MemberSets := do
  let members ← json.getArr?
  if members.size > limits.members then throw "too many member lists"
  let mut result := #[]
  let mut total := 0
  for member in members do
    let entries ← member.getArr?
    total := total + entries.size
    if total > limits.memberEntries then throw "too many member addresses"
    let mut addresses := #[]
    for entry in entries do
      let text ← entry.getStr?
      unless text.utf8ByteSize == 64 do throw "member address must have 64 hex digits"
      let bytes ← Check.unhex text
      let some address := Address.ofBytes? bytes | throw "invalid member address"
      addresses := addresses.push address
    result := result.push addresses
  return result

/-- Bound shape, counts and string lengths before the general JSON parser.
Only two array levels and literal ASCII hex strings belong to this witness
format, so arbitrary JSON nesting/numbers cannot consume parser resources. -/
def checkWitnessSyntax (limits : Limits) (raw : ByteArray) : Except String Unit := do
  let mut depth := 0
  let mut quoted := false
  let mut digits := 0
  let mut members := 0
  let mut addresses := 0
  for byte in raw.data do
    if quoted then
      if byte == 34 then
        unless digits == 64 do throw "member address must have 64 literal hex digits"
        quoted := false
      else
        unless (48 ≤ byte && byte ≤ 57) || (65 ≤ byte && byte ≤ 70) ||
            (97 ≤ byte && byte ≤ 102) do throw "invalid literal hex address"
        digits := digits + 1
        if digits > 64 then throw "member address exceeds 64 digits"
    else if byte == 91 then
      if depth ≥ 2 then throw "member lists exceed two array levels"
      depth := depth + 1
      if depth == 2 then
        members := members + 1
        if members > limits.members then throw "too many member lists"
    else if byte == 93 then
      if depth == 0 then throw "unexpected closing bracket"
      depth := depth - 1
    else if byte == 34 then
      unless depth == 2 do throw "address outside a member list"
      addresses := addresses + 1
      if addresses > limits.memberEntries then throw "too many member addresses"
      digits := 0
      quoted := true
    else unless byte == 44 || byte == 32 || byte == 9 || byte == 10 || byte == 13 do
      throw "invalid member-list token"
  if quoted || depth != 0 then throw "truncated member lists"

/-- The supplemental witness format is a bounded array of arrays of literal
hex addresses, authenticated by the manifest's member roots. -/
def readMemberSets (limits : Limits) (path : System.FilePath) : IO MemberSets := do
  let raw ← readBounded path (limits.memberEntries * 70 + limits.members * 4 + 1024)
  IO.ofExcept (checkWitnessSyntax limits raw)
  let some text := String.fromUTF8? raw | throw (IO.userError "invalid UTF-8 member lists")
  IO.ofExcept (Lean.Json.parse text >>= memberSetsFromJson limits)

def readPieces (limits : Limits) (directory : System.FilePath) (m : Manifest) :
    IO (Array ByteArray) := do
  IO.ofExcept ((checkStorageBudget limits m).mapError reprStr)
  let mut pieces := #[]
  let mut total := 0
  for spec in pieceSpecs m do
    let raw ← readBounded (directory / spec.filename)
      (min spec.fileBytes.toNat (limits.totalPieceBytes - total))
    total := total + raw.size
    pieces := pieces.push raw
  return pieces

def run (args : List String) : IO UInt32 := do
  try
    let (directory, membersFile) ← match args with
      | [directory] => pure (System.FilePath.mk directory, none)
      | [directory, members] => pure (System.FilePath.mk directory, some members)
      | _ => throw (IO.userError "usage: check-ixon-v3-catalog CATALOG.ixc [MEMBERS.json]")
    let limits : Limits := {}
    let raw ← readBounded (directory / "manifest") limits.manifestBytes
    let manifest ← IO.ofExcept ((decodeManifestWith limits raw).mapError reprStr)
    let supplied ← membersFile.mapM (readMemberSets limits ∘ System.FilePath.mk)
    let pieces ← readPieces limits directory manifest
    let input ← IO.ofExcept ((admitWith limits raw pieces supplied).mapError reprStr)
    IO.println s!"ixon-v3 catalog validated: validator=erased-lean-v1 manifest={Address.blake3 raw} content={input.loaded.env.root} members={manifest.members.size} constants={input.loaded.env.consts.size}"
    return 0
  catch error =>
    IO.eprintln s!"ixon-v3 catalog rejected: {error}"
    return 1

end Compilatrix.Tools.IxonV3Catalog
