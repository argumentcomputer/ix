import CompilatrixTests.IxonV3.Catalog.Admission

namespace CompilatrixTests.IxonV3.CatalogTests

open Compilatrix.Ixon Compilatrix.Ixon.V3 Catalog CatalogFixtures TypingFixtures

def wire : IO Nat := do
  let (env, a) := base
  let raws := #[envBytes env]
  let m ← IO.ofExcept (fat raws)
  let raw := manifestBytes m
  for length in [:raw.size] do
    expect s!"manifest prefix {length}" (decodeManifest (raw.extract 0 length)) false
  let mutations : Array (String × Nat × UInt8) := #[("magic", 0, 0), ("version", 8, 1),
      ("flags", 12, 2), ("object format", 16, 2), ("validator", 17, 2),
      ("members root", 18, raw[18]! ^^^ 1), ("UTF8", 128, 255),
      ("preimage tag", 138, 2)]
  for (label, offset, byte) in mutations do
    expect label (decodeManifest (mutate raw offset byte)) false
  expect "oversized count before allocation" (decodeManifest
    (raw.extract 0 82 ++ ⟨#[255, 255, 255, 255]⟩)) false
  for label in #["", ".", "..", "a/b", "a\\b", "a\x00b"] do
    expect s!"unsafe label {reprStr label}" (decodeManifest (manifestBytes
      (membersChanged m #[{ m.members[0]! with label }]))) false
  let duplicates := membersChanged m #[m.members[0]!, m.members[0]!]
  expect "duplicate label" (decodeManifest (manifestBytes duplicates)) false
  let futureDep := membersChanged m #[{ m.members[0]! with deps := #[0] }]
  expect "non-topological dependency" (decodeManifest (manifestBytes futureDep)) false
  let wrongCount := membersChanged m #[{ m.members[0]! with constCount := 2 }]
  expect "fat member count" (load (manifestBytes wrongCount) raws) false
  let wrongRoot := membersChanged m #[{ m.members[0]! with envRoot := a }]
  expect "fat piece root" (load (manifestBytes wrongRoot) raws) false
  expect "content root" (load (manifestBytes { m with contentRoot := a }) raws) false
  expect "missing piece" (load raw #[]) false
  expect "extra piece" (load raw (raws.push raws[0]!)) false
  let .fat rows := m.storage | throw (IO.userError "expected fat")
  let badSize := { m with storage := .fat #[{ rows[0]! with fileBytes := rows[0]!.fileBytes + 1 }] }
  expect "file size" (load (manifestBytes badSize) raws) false
  let badHash := { m with storage := .fat #[{ rows[0]! with fileHash := a }] }
  expect "file hash" (load (manifestBytes badHash) raws) false
  let metadataManifest := membersChanged m #[{ m.members[0]! with
    preimage := some a
    toolchain := "toolchain metadata", sourcePin := "source metadata" }]
  let tail : ByteArray := ⟨#[1, 255, 3, 0]⟩
  let decoded ← checked (decodeManifest (manifestBytes { metadataManifest with trailing := tail }))
  require (decoded.trailing == tail && decoded.members[0]!.preimage == some a &&
    decoded.members[0]!.toolchain == "toolchain metadata" &&
    decoded.members[0]!.sourcePin == "source metadata") "retained uninterpreted fields"
  let chunks ← IO.ofExcept (chunked m.members #[(raws[0]!, 0)])
  let .chunked chunkRows := chunks.storage | throw (IO.userError "expected chunks")
  let badOwner := { chunks with storage := .chunked #[{ chunkRows[0]! with owner := 1 }] }
  expect "owner bounds" (decodeManifest (manifestBytes badOwner)) false
  let badChunkRoot := { chunks with storage := .chunked #[{ chunkRows[0]! with chunkRoot := a }] }
  expect "chunk root" (load (manifestBytes badChunkRoot) raws (some #[#[a]])) false
  -- An object can be corrupted while its enclosing file hash is rebound.
  let corrupted := mutate raws[0]! 72 (raws[0]![72]! ^^^ 1)
  let rebound := { m with storage := .fat #[⟨Address.blake3 corrupted, corrupted.size.toUInt64⟩] }
  expect "constant hash after file rebinding" (load (manifestBytes rebound) #[corrupted]) false
  let triple ← IO.ofExcept (fat #[raws[0]!, raws[0]!, raws[0]!])
  let triple := membersChanged triple #[triple.members[0]!,
    { triple.members[1]! with deps := #[0] }, { triple.members[2]! with deps := #[0] }]
  expect "exact aggregate dependency budget"
    (decodeManifestWith { dependencyEdges := 2 } (manifestBytes triple)) true
  expect "aggregate dependency overflow"
    (decodeManifestWith { dependencyEdges := 1 } (manifestBytes triple)) false
  return raw.size + 30

def budgets : IO Nat := do
  let (left, a) := base
  let (right, b) := store left (identity a)
  let blob := "catalog budget blob".toUTF8
  let address := Address.blake3 blob
  let left := { left with blobs := left.blobs.insert address blob, hints := #[(a, 0)] }
  let thin : Env := { right with
    consts := right.consts.erase a
    assumptions := Merkle.sortAddresses #[a, address], hints := #[(b, 1)] }
  let raws := #[envBytes left, envBytes thin]
  let members := #[member left 0, { member right 1 with deps := #[0] }]
  let m ← IO.ofExcept (chunked members #[(raws[0]!, 0), (raws[1]!, 1)])
  let raw := manifestBytes m
  let sets := some #[constantAddresses left, constantAddresses right]
  let exact : Limits := {
    manifestBytes := raw.size, members := 2, dependencyEdges := 1, storageUnits := 2
    pieceBytes := max raws[0]!.size raws[1]!.size
    totalPieceBytes := raws[0]!.size + raws[1]!.size
    constantEntries := 2, blobEntries := 1, assumptions := 2, hints := 2
    unionConstants := 2, unionBlobs := 1, memberEntries := 3 }
  let loaded ← checked (loadWith exact raw raws sets)
  expect "exact budgets admit" (admitWith exact raw raws sets) true
  require (loaded.stats.constantEntries == 2 && loaded.stats.blobEntries == 1 &&
    loaded.stats.assumptions == 2 && loaded.stats.hints == 2 &&
    loaded.stats.memberEntries == 3 && loaded.stats.pieceBytes == exact.totalPieceBytes)
    "aggregate accounting"
  let cases : Array (String × Limits) := #[
    ("manifest bytes", { exact with manifestBytes := raw.size - 1 }),
    ("members", { exact with members := 1 }),
    ("dependencies", { exact with dependencyEdges := 0 }),
    ("storage units", { exact with storageUnits := 1 }),
    ("piece bytes", { exact with pieceBytes := exact.pieceBytes - 1 }),
    ("total piece bytes", { exact with totalPieceBytes := exact.totalPieceBytes - 1 }),
    ("constant entries", { exact with constantEntries := 1 }),
    ("blob entries", { exact with blobEntries := 0 }),
    ("assumptions", { exact with assumptions := 1 }),
    ("hints", { exact with hints := 1 }),
    ("union constants", { exact with unionConstants := 1 }),
    ("union blobs", { exact with unionBlobs := 0 }),
    ("member entries", { exact with memberEntries := 2 })]
  for (label, limits) in cases do expect label (loadWith limits raw raws sets) false
  let huge := membersChanged m #[{ m.members[0]! with constCount := 18446744073709551615 }, m.members[1]!]
  expect "advertised member count cannot overflow" (load (manifestBytes huge) raws sets) false
  let .chunked rows := m.storage | throw (IO.userError "expected chunks")
  let large := { m with storage := .chunked (rows.set! 0 { rows[0]! with fileBytes := 18446744073709551615 }) }
  expect "advertised byte count cannot overflow" (load (manifestBytes large) raws sets) false
  return cases.size + 4

end CompilatrixTests.IxonV3.CatalogTests
