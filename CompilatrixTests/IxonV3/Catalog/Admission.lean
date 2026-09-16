import CompilatrixTests.IxonV3.Catalog.Fixtures

namespace CompilatrixTests.IxonV3.CatalogTests

open Compilatrix.Ixon Compilatrix.Ixon.V3 Catalog CatalogFixtures TypingFixtures

def require (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError s!"v3 catalog: {label}")

def expect (label : String) (result : Except Catalog.Error α) (accepted : Bool) : IO Unit :=
  unless result.toOption.isSome == accepted do
    let detail := match result with | .ok _ => "accepted" | .error e => reprStr e
    throw (IO.userError s!"v3 catalog {label}: expected {accepted}, got {detail}")

def checked (result : Except Catalog.Error α) : IO α := IO.ofExcept (result.mapError reprStr)

def admission (root : System.FilePath) : IO Nat := do
  let (aEnv, a) := base
  let (abEnv, b) := store aEnv (identity a)
  let blob := "catalog blob".toUTF8
  let blobAddr := Address.blake3 blob
  let left : Env := { aEnv with
    blobs := aEnv.blobs.insert blobAddr blob
    hints := #[(a, 12)], main := some a, metadata := ⟨#[250, 251]⟩ }
  let right : Env := { abEnv with
    blobs := abEnv.blobs.insert blobAddr blob
    hints := #[(a, 1), (b, 3)], main := some b }
  let raws := #[envBytes left, envBytes right]
  let m ← IO.ofExcept (fat raws)
  let input ← checked (admit (manifestBytes m) raws)
  let union := input.loaded.env
  require (union.consts.size == 2 && union.blobs.size == 1 && union.main.isNone &&
    union.assumptions.isEmpty && union.hints.contains (a, 1)) "fat union accounting and hint minimum"
  require (input.loaded.pieces[0]!.metadata == left.metadata && union.metadata.isEmpty)
    "original metadata retained outside anonymous union"
  expect "fat cannot accept supplemental membership" (load (manifestBytes m) raws (some input.loaded.memberSets)) false
  let sameMains := #[envBytes left, envBytes { right with main := some a }]
  let same ← checked (admit (manifestBytes (← IO.ofExcept (fat sameMains))) sameMains)
  require (same.loaded.env.main == some a) "unique main survives union"
  let opaquePieces := #[envBytes left, envBytes { right with hints := #[(a, 0)] }]
  let op ← checked (admit (manifestBytes (← IO.ofExcept (fat opaquePieces))) opaquePieces)
  require (op.loaded.env.hints.contains (a, 0)) "opaque hint wins min merge"
  let reversed := raws.reverse
  let reversedInput ← checked (admit (manifestBytes (← IO.ofExcept (fat reversed))) reversed)
  require (reversedInput.loaded.env.root == union.root &&
    reversedInput.loaded.env.hints == union.hints && reversedInput.loaded.env.main == union.main)
    "fat merge is independent of piece order"
  let malformed : C := ⟨.defn ⟨.defn, .safe, 0, .sort 0, .var 0⟩, #[], #[], #[.zero]⟩
  let badRaw := #[envBytes (store aEnv malformed).1]
  let badM ← IO.ofExcept (fat badRaw)
  expect "ill-typed catalog is structurally valid" (load (manifestBytes badM) badRaw) true
  expect "ill-typed catalog fails admission" (admit (manifestBytes badM) badRaw) false
  let escaped ← IO.FS.readBinFile (root / "handoff/rejected-local-escape.ixe")
  let escapedM ← IO.ofExcept (fat #[escaped])
  let escapedInput ← checked (admit (manifestBytes escapedM) #[escaped])
  let profileRaw ← IO.FS.readBinFile (root / "handoff/profile.bin")
  let profile ← IO.ofExcept (Resource.Profile.ofBytes profileRaw)
  require ((Resource.Addressed.checkResources escapedInput.loaded.env profile).toOption.isNone)
    "erased catalog typing does not confer resource admission"
  -- The second original member overlaps the first, but its chunk carries
  -- only b. A union-only check would not authenticate this relationship.
  let thin : Env := { right with
    consts := right.consts.erase a
    hints := #[(b, 3)], assumptions := Merkle.sortAddresses #[a, blobAddr] }
  let chunks := #[envBytes left, envBytes thin]
  let cm ← IO.ofExcept (chunked m.members #[(chunks[0]!, 0), (chunks[1]!, 1)])
  let sets := input.loaded.memberSets
  let chunkInput ← checked (admit (manifestBytes cm) chunks (some sets))
  require (chunkInput.loaded.env.root == union.root && chunkInput.loaded.env.assumptions.isEmpty)
    "overlap witnesses and cross-chunk assumptions resolve"
  expect "missing chunk witness" (admit (manifestBytes cm) chunks) false
  expect "missing member witness" (admit (manifestBytes cm) chunks (some #[sets[0]!])) false
  expect "owner slice is not original member" (admit (manifestBytes cm) chunks (some #[#[a], #[b]])) false
  expect "unsorted member" (admit (manifestBytes cm) chunks (some #[#[a], sets[1]!.reverse])) false
  expect "duplicate member key" (admit (manifestBytes cm) chunks (some #[#[a], #[a, a]])) false
  expect "absent member key" (admit (manifestBytes cm) chunks (some #[#[a], Merkle.sortAddresses #[a, Address.replicate 99]])) false
  let .chunked rows := cm.storage | throw (IO.userError "expected chunks")
  let badOwner := { cm with storage := .chunked (rows.set! 1 { rows[1]! with owner := 0 }) }
  expect "wrong first owner" (admit (manifestBytes badOwner) chunks (some sets)) false
  let dupChunks := #[envBytes left, envBytes right]
  let dupM ← IO.ofExcept (chunked m.members #[(dupChunks[0]!, 0), (dupChunks[1]!, 1)])
  expect "constant duplicated across chunks" (admit (manifestBytes dupM) dupChunks (some sets)) false
  let missingM := membersChanged cm #[m.members[0]!, { m.members[1]! with
    envRoot := m.members[0]!.envRoot, constCount := 1 }]
  expect "uncovered union constant" (admit (manifestBytes missingM) chunks (some #[#[a], #[a]])) false
  let missingRef : Env := { thin with assumptions := #[Address.replicate 77] }
  let missingRaws := #[envBytes left, envBytes missingRef]
  let missingRefs ← IO.ofExcept (chunked m.members #[(missingRaws[0]!, 0), (missingRaws[1]!, 1)])
  expect "unresolved external assumption" (admit (manifestBytes missingRefs) missingRaws (some sets)) false
  let fatThin := #[envBytes { right with assumptions := #[a] }]
  expect "fat forbids assumptions even if present" (admit (manifestBytes (← IO.ofExcept (fat fatThin))) fatThin) false
  let noRefRaws := #[envBytes { thin with assumptions := #[] }]
  expect "undeclared missing reference fails typing"
    (admit (manifestBytes (← IO.ofExcept (fat noRefRaws))) noRefRaws) false
  let noBlob : C := ⟨.defn ⟨.defn, .safe, 0, .ref 0 #[], .nat 1⟩, #[], #[a, blobAddr], #[]⟩
  let noBlobRaws := #[envBytes (store aEnv noBlob).1]
  expect "missing literal blob fails typing"
    (admit (manifestBytes (← IO.ofExcept (fat noBlobRaws))) noBlobRaws) false
  -- Every byte is covered by the advertised file hash, including opaque
  -- metadata. Rebinding a malformed object still must fail its own hash gate.
  for i in [:raws[0]!.size] do
    let corrupt := raws.set! 0 (mutate raws[0]! i (raws[0]![i]! ^^^ 1))
    expect s!"file byte {i}" (load (manifestBytes m) corrupt) false
  let mixed := raws.set! 0 (mutate raws[0]! 0 0xE2)
  let .fat fatRows := m.storage | throw (IO.userError "expected fat")
  let mixedM := { m with storage := .fat (fatRows.set! 0
    ⟨Address.blake3 mixed[0]!, mixed[0]!.size.toUInt64⟩) }
  expect "v2 piece in v3 catalog" (load (manifestBytes mixedM) mixed) false
  let emptyM ← IO.ofExcept (fat #[])
  expect "empty catalog" (admit (manifestBytes emptyM) #[]) true
  return 25 + raws[0]!.size

end CompilatrixTests.IxonV3.CatalogTests
