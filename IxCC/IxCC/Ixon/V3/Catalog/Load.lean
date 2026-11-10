import IxCC.Ixon.V3.Catalog.Manifest
import IxCC.Ixon.V3.Catalog.Coverage

namespace IxCC.Ixon.V3.Catalog

private def countPiece (limits : Limits) (stats : Stats) (env : Env) : Except Error Stats := do
  let stats := { stats with
    constantEntries := stats.constantEntries + env.consts.size
    blobEntries := stats.blobEntries + env.blobs.size
    assumptions := stats.assumptions + env.assumptions.size
    hints := stats.hints + env.hints.size }
  requireLimit "constant entries" stats.constantEntries limits.constantEntries
  requireLimit "blob entries" stats.blobEntries limits.blobEntries
  requireLimit "assumptions" stats.assumptions limits.assumptions
  requireLimit "hints" stats.hints limits.hints
  return stats

/-- Check advertised budgets before reading or decoding piece contents. -/
def checkStorageBudget (limits : Limits) (m : Manifest) : Except Error Unit := do
  let mut total := 0
  for spec in pieceSpecs m do
    requireLimit "piece bytes" spec.fileBytes.toNat limits.pieceBytes
    total := total + spec.fileBytes.toNat
    requireLimit "total piece bytes" total limits.totalPieceBytes
  let mut members := 0
  for member in m.members do
    members := members + member.constCount.toNat
    requireLimit "member entries" members limits.memberEntries

private def mergeTable (name : String) (unique : Bool) (maximum : Nat)
    (into source : Std.HashMap Address ByteArray) : Except Error (Std.HashMap Address ByteArray) := do
  let mut table := into
  for (address, raw) in source do
    if let some prior := table[address]? then
      if unique then throw (.coverage s!"{name}: address redeclared across chunks")
      unless prior == raw do throw (.coverage s!"{name}: inconsistent bytes for shared address")
    else
      requireLimit s!"union {name}" (table.size + 1) maximum
      table := table.insert address raw
  return table

/-- Load the exact supplied bytes. File hashes bind hints, assumptions and
opaque metadata as well as the addressed object tables. No cached materialized
environment is accepted as a replacement for a piece. -/
def loadWith (limits : Limits) (manifestBytes : ByteArray) (pieceBytes : Array ByteArray)
    (supplied : Option MemberSets := none) : Except Error Loaded := do
  let manifest ← decodeManifestWith limits manifestBytes
  let specs := pieceSpecs manifest
  unless pieceBytes.size == specs.size do throw (.manifest "piece count differs from storage rows")
  checkStorageBudget limits manifest
  let chunked := match manifest.storage with | .fat _ => false | .chunked _ => true
  let mut stats : Stats := {}
  -- Account for actual bytes before any piece is parsed, even if the
  -- advertised sizes are false.
  for raw in pieceBytes do
    requireLimit "piece bytes" raw.size limits.pieceBytes
    stats := { stats with pieceBytes := stats.pieceBytes + raw.size }
    requireLimit "total piece bytes" stats.pieceBytes limits.totalPieceBytes
  let mut pieces := #[]
  let mut env : Env := {}
  let mut hints : Std.HashMap Address UInt64 := {}
  let mut mains : Std.HashSet Address := {}
  for i in [:pieceBytes.size] do
    let raw := pieceBytes[i]!
    let spec := specs[i]!
    unless raw.size == spec.fileBytes.toNat do throw (.piece i "file size differs")
    unless Address.blake3 raw == spec.fileHash do throw (.piece i "file hash differs")
    let piece ← (decodeAnonymousEnv raw limits.pieceBytes).mapError (Error.piece i)
    -- A catalog's union carries no role binding, so its pieces are unbound.
    if piece.isBound then throw (.piece i "a catalog piece must be an unbound environment")
    unless piece.root == spec.root do throw (.piece i "environment root differs")
    if !chunked && !piece.assumptions.isEmpty then
      throw (.piece i "fat member carries external assumptions")
    stats ← countPiece limits stats piece
    let consts ← mergeTable "constants" chunked limits.unionConstants env.consts piece.consts
    let blobs ← mergeTable "blobs" false limits.unionBlobs env.blobs piece.blobs
    env := { env with consts, blobs }
    for (address, hint) in piece.hints do
      hints := hints.insert address (min hint (hints[address]?.getD hint))
    if let some main := piece.main then mains := mains.insert main
    pieces := pieces.push piece
  let root := Merkle.rootCanonical (constantAddresses env)
  unless root == manifest.contentRoot do throw (.manifest "union root differs from content_root")
  for piece in pieces do
    for assumption in piece.assumptions do
      unless env.consts.contains assumption || env.blobs.contains assumption do
        throw (.coverage "unresolved external assumption in catalog union")
  env := { env with
    root := root
    main := if mains.size == 1 then mains.toArray[0]? else none
    hints := hints.toArray.qsort (fun a b => Merkle.addressLT a.1 b.1) }
  let (memberSets, entries) ← checkCoverage limits manifest pieces env supplied
  return { manifest, pieces, memberSets, env, stats := { stats with memberEntries := entries } }

def load (manifestBytes : ByteArray) (pieceBytes : Array ByteArray)
    (supplied : Option MemberSets := none) : Except Error Loaded :=
  loadWith {} manifestBytes pieceBytes supplied

end IxCC.Ixon.V3.Catalog
