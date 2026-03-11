/-
  FFI lifecycle tests: non-roundtrip code paths focused on memory management.
  Exercises external objects, serialization pipelines, and hash FFI.
-/
module

public import LSpec
public import Ix.Keccak
public import Tests.Sha256
public import Ix.Ixon
public import Tests.Gen.Ixon
public import Tests.FFI.Ixon

open LSpec SlimCheck Gen Ixon
open Tests.Gen.Ixon
open Tests.FFI.Ixon (rawEnvEq)

namespace Tests.FFI.Lifecycle

/-! ## Keccak external object lifecycle tests -/

/-- Basic hash lifecycle: init → update → finalize -/
def keccakBasicTests : TestSeq :=
  -- Known test vector: SHA3-256 of [0]
  let input : ByteArray := ⟨#[0]⟩
  let expected : ByteArray := ⟨#[
    188, 54, 120, 158, 122, 30, 40, 20, 54, 70, 66, 41, 130, 143, 129, 125,
    102, 18, 247, 180, 119, 214, 101, 145, 255, 150, 169, 224, 100, 188, 201, 138
  ]⟩
  let result := Keccak.hash input
  test "Keccak basic hash [0]" (result == expected) ++
  -- Empty input
  let emptyResult := Keccak.hash ByteArray.empty
  test "Keccak empty input produces 32 bytes" (emptyResult.size == 32) ++
  -- Determinism: same input twice
  let result2 := Keccak.hash input
  test "Keccak deterministic" (result == result2)

/-- Multi-update lifecycle: init → update × N → finalize
    Creates N+1 external Hasher objects, exercising the destructor path. -/
def keccakMultiUpdateTests : TestSeq :=
  -- Multi-update should produce same result as single update of concatenated input
  let chunk1 : ByteArray := ⟨#[1, 2, 3]⟩
  let chunk2 : ByteArray := ⟨#[4, 5, 6]⟩
  let chunk3 : ByteArray := ⟨#[7, 8, 9]⟩
  let combined : ByteArray := ⟨#[1, 2, 3, 4, 5, 6, 7, 8, 9]⟩
  let singleHash := Keccak.hash combined
  let multiHash :=
    let h := Keccak.Hasher.init ()
    let h := h.update chunk1
    let h := h.update chunk2
    let h := h.update chunk3
    h.finalize
  test "Keccak multi-update == single" (singleHash == multiHash) ++
  -- Many updates to stress the external object destructor
  let manyHash := Id.run do
    let mut h := Keccak.Hasher.init ()
    for i in [:20] do
      h := h.update ⟨#[i.toUInt8]⟩
    return h.finalize
  test "Keccak 20 updates produces 32 bytes" (manyHash.size == 32)

/-- Large input to exercise large ByteArray across FFI boundary -/
def keccakLargeInputTests : TestSeq :=
  let large : ByteArray := ⟨Array.range 4096 |>.map Nat.toUInt8⟩
  let result := Keccak.hash large
  test "Keccak large input (4096 bytes)" (result.size == 32) ++
  -- Verify determinism on large input
  let result2 := Keccak.hash large
  test "Keccak large input deterministic" (result == result2)

/-! ## SHA256 hashing tests -/

def sha256Tests : TestSeq :=
  -- Empty input: SHA-256("") = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
  let emptyHash := Sha256.hash ByteArray.empty
  let expectedEmpty : ByteArray := ⟨#[
    0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
    0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55
  ]⟩
  test "SHA256 empty" (emptyHash == expectedEmpty) ++
  -- "abc": SHA-256("abc") = ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
  let abcHash := Sha256.hash ⟨#[0x61, 0x62, 0x63]⟩
  let expectedAbc : ByteArray := ⟨#[
    0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
    0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad
  ]⟩
  test "SHA256 abc" (abcHash == expectedAbc) ++
  -- Determinism: hash same input twice
  let hash1 := Sha256.hash ⟨#[1, 2, 3]⟩
  let hash2 := Sha256.hash ⟨#[1, 2, 3]⟩
  test "SHA256 deterministic" (hash1 == hash2) ++
  test "SHA256 produces 32 bytes" (hash1.size == 32)

/-! ## Ixon serialization roundtrip tests (ser_env → de_env) -/

/-- Compare RawEnv after serde: only check consts, named, comms.
    The serde pipeline normalizes the names table and may add string blobs
    for name components, so names and blobs are not compared structurally. -/
private def serdeEnvEq (a b : RawEnv) : Bool :=
  a.consts.size == b.consts.size &&
  a.named.size == b.named.size &&
  a.comms.size == b.comms.size &&
  a.consts.all fun rc =>
    b.consts.any fun rc' => rc.addr == rc'.addr &&
      rc.const.info == rc'.const.info &&
      rc.const.sharing.size == rc'.const.sharing.size &&
      rc.const.refs.size == rc'.const.refs.size &&
      rc.const.univs.size == rc'.const.univs.size

def serdeTests : TestSeq :=
  -- Empty RawEnv
  let empty : RawEnv := { consts := #[], named := #[], blobs := #[], comms := #[] }
  let emptyBytes := rsSerEnvFFI empty
  let emptyResult := rsDeEnvFFI emptyBytes
  .individualIO "serde empty RawEnv" none (do
    match emptyResult with
    | .ok decoded => pure (serdeEnvEq decoded empty, 0, 0, if serdeEnvEq decoded empty then none else some "mismatch")
    | .error e => pure (false, 0, 0, some s!"deserialization failed: {e}")) .done ++
  -- RawEnv with data (include name entries for all referenced addresses)
  let testAddr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  let testExpr : Expr := .sort 0
  let testDef : Definition := {
    kind := .defn, safety := .safe, lvls := 0,
    typ := testExpr, value := testExpr
  }
  let testConst : Constant := {
    info := .defn testDef, sharing := #[], refs := #[], univs := #[]
  }
  let testRawConst : RawConst := { addr := testAddr, const := testConst }
  let testComm : Comm := { secret := testAddr, payload := testAddr }
  let testRawComm : RawComm := { addr := testAddr, comm := testComm }
  let testRawBlob : RawBlob := { addr := testAddr, bytes := ByteArray.mk #[1, 2, 3] }
  let testName := Ix.Name.mkStr Ix.Name.mkAnon "test"
  let testRawNamed : RawNamed := {
    name := testName, addr := testAddr, constMeta := .empty
  }
  let testNameEntry : RawNameEntry := { addr := testAddr, name := testName }
  let withData : RawEnv := {
    consts := #[testRawConst],
    named := #[testRawNamed],
    blobs := #[testRawBlob],
    comms := #[testRawComm],
    names := #[testNameEntry]
  }
  let dataBytes := rsSerEnvFFI withData
  let dataResult := rsDeEnvFFI dataBytes
  .individualIO "serde RawEnv with data" none (do
    match dataResult with
    | .ok decoded => pure (serdeEnvEq decoded withData, 0, 0, if serdeEnvEq decoded withData then none else some "mismatch")
    | .error e => pure (false, 0, 0, some s!"deserialization failed: {e}")) .done

/-- Generate a ConstantInfo without embedded Address fields.
    Projections contain Addresses that would need name entries;
    these simpler variants only contain Expr/Univ/Nat fields. -/
private def genSimpleConstantInfo : Gen ConstantInfo :=
  frequency [
    (10, .defn <$> genDefinition),
    (5, .recr <$> genRecursor),
    (10, .axio <$> genAxiom),
    (10, .quot <$> genQuotient),
  ]

/-- Generate a well-formed RawEnv where every address has a name entry.
    The serde pipeline requires all addresses to be resolvable in the
    name table; random RawEnvs almost always violate this. -/
private def genSerdeRawEnv : Gen RawEnv := do
  -- Build a pool of (address, name) pairs; all addresses used below come from here
  let poolSize ← Gen.choose Nat 2 8
  let mut pool : Array (Address × Ix.Name) := #[]
  for i in [:poolSize] do
    let addr ← genAddress
    pool := pool.push (addr, Ix.Name.mkNat Ix.Name.mkAnon i)
  let pickAddr : Gen Address := do
    let idx ← Gen.choose Nat 0 (pool.size - 1)
    pure pool[idx]!.1
  -- Name entries for every address in the pool
  let names : Array RawNameEntry := pool.map fun (addr, name) => { addr, name }
  -- Consts: pool addresses, empty refs/sharing/univs (no extra address lookups)
  let numConsts ← Gen.choose Nat 0 3
  let mut consts : Array RawConst := #[]
  for _ in [:numConsts] do
    let addr ← pickAddr
    let info ← genSimpleConstantInfo
    consts := consts.push { addr, const := { info, sharing := #[], refs := #[], univs := #[] } }
  -- Named: pool addresses with empty metadata
  let numNamed ← Gen.choose Nat 0 3
  let mut named : Array RawNamed := #[]
  for _ in [:numNamed] do
    let idx ← Gen.choose Nat 0 (pool.size - 1)
    let (addr, name) := pool[idx]!
    named := named.push { name, addr, constMeta := .empty }
  -- Blobs: pool addresses
  let numBlobs ← Gen.choose Nat 0 3
  let mut blobs : Array RawBlob := #[]
  for _ in [:numBlobs] do
    let addr ← pickAddr
    let bytes ← Tests.Gen.Ixon.genByteArray
    blobs := blobs.push { addr, bytes }
  -- Comms: pool addresses
  let numComms ← Gen.choose Nat 0 2
  let mut comms : Array RawComm := #[]
  for _ in [:numComms] do
    let addr ← pickAddr
    let secret ← pickAddr
    let payload ← pickAddr
    comms := comms.push { addr, comm := { secret, payload } }
  -- Deduplicate by key: the Rust side uses HashMaps, so duplicates collapse
  let consts' := consts.foldl (init := (#[] : Array RawConst)) fun acc x =>
    if acc.any (·.addr == x.addr) then acc else acc.push x
  let named' := named.foldl (init := (#[] : Array RawNamed)) fun acc x =>
    if acc.any (·.name == x.name) then acc else acc.push x
  let blobs' := blobs.foldl (init := (#[] : Array RawBlob)) fun acc x =>
    if acc.any (·.addr == x.addr) then acc else acc.push x
  let comms' := comms.foldl (init := (#[] : Array RawComm)) fun acc x =>
    if acc.any (·.addr == x.addr) then acc else acc.push x
  pure { consts := consts', named := named', blobs := blobs', comms := comms', names }

/-- Wrapper so we can give well-formed RawEnvs their own SampleableExt instance. -/
private structure serdeRawEnv where
  env : RawEnv

private instance : Repr serdeRawEnv where
  reprPrec e n := reprPrec e.env n

private instance : Shrinkable serdeRawEnv where
  shrink _ := []

private instance : SampleableExt serdeRawEnv :=
  SampleableExt.mkSelfContained (serdeRawEnv.mk <$> genSerdeRawEnv)

/-- Check that serialize → deserialize roundtrips for a well-formed RawEnv. -/
def serdeRoundtripOk (env : RawEnv) : Bool :=
  match rsDeEnvFFI (rsSerEnvFFI env) with
  | .ok decoded => serdeEnvEq decoded env
  | .error _ => false

/-- Property test: random well-formed RawEnv → serialize → deserialize → compare -/
def serdePropertyTest : TestSeq :=
  checkIO "serde RawEnv roundtrip" (∀ e : serdeRawEnv, serdeRoundtripOk e.env)

/-! ## Test Suite -/

public def suite : List TestSeq := [
  keccakBasicTests,
  keccakMultiUpdateTests,
  keccakLargeInputTests,
  sha256Tests,
  serdeTests,
  serdePropertyTest,
]

end Tests.FFI.Lifecycle
