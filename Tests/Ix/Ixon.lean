module
public import Ix.Ixon
public import Tests.Gen.Ixon
public import Tests.FFI.Ixon
public import Tests.Ix.OriginalData
public import Tests.Ix.RoleBinding
public import Tests.Ix.RolePublication
public import Tests.Ix.RoleGeneration
public import Tests.Ix.RoleArtifactConsumer

open LSpec SlimCheck Gen Ixon
open Tests.FFI.Ixon (rsEqUnivSerialization rsEqExprSerialization rsEqConstantSerialization rsEqEnvSerialization)

/-!
## Roundtrip Tests for New Format Types
-/

def univSerde (u : Univ) : Bool :=
  let bytes := serUniv u
  match deUniv bytes with
  | .ok u' => u == u'
  | .error _ => false

def exprSerde (e : Expr) : Bool :=
  let bytes := serExpr e
  match deExpr bytes with
  | .ok e' => e == e'
  | .error _ => false

def constantSerde (c : Constant) : Bool :=
  let bytes := serConstant c
  match deConstant bytes with
  | .ok c' => c == c'
  | .error _ => false

def commSerde (c : Comm) : Bool :=
  let bytes := serComm c
  match deComm bytes with
  | .ok c' => c == c'
  | .error _ => false

def envSerde (raw : RawEnv) : Bool :=
  let env := raw.toEnv
  match serEnv env with
  | .error _ => false
  | .ok bytes1 =>
    match deEnv bytes1 with
    | .ok env' =>
      -- Byte-level equality after roundtrip
      match serEnv env' with
      | .ok bytes2 => bytes1 == bytes2
      | .error _ => false
    | .error _ => false

/-!
## Unit Tests for New Format Types
-/

def univUnits : TestSeq :=
  let cases : List Univ := [
    .zero,
    .var 0,
    .var 31,
    .var 32,
    .var 42,
    .var 0x100,
    .var 0xffffffffffffffff,
    .succ .zero,
    .succ (.succ .zero),
    .succ (.succ (.succ .zero)),  -- Test telescope compression
    Univ.addSucc 31 .zero,
    Univ.addSucc 32 .zero,         -- 32 successors: TagN f=2 rung 2
    .max .zero (.var 0),
    .imax (.var 1) .zero,
    .max (.succ .zero) (.succ (.succ .zero)),
  ]
  cases.foldl (init := .done) fun acc u =>
    acc ++ test s!"Univ roundtrip: {repr u}" (univSerde u) ++
      test s!"Univ Lean==Rust bytes: {repr u}"
        (rsEqUnivSerialization u (serUniv u))

def univPrefixAccepts (bytes : ByteArray) : Bool :=
  match runGet getUniv bytes with
  | .ok .zero => true
  | _ => false

def univExactRejects (bytes : ByteArray) : Bool :=
  match deUniv bytes with
  | .error _ => true
  | .ok _ => false

def univExactUnits : TestSeq :=
  let bytes := serUniv Univ.zero ++ [0].toByteArray
  test "Univ prefix runner may leave trailing bytes"
      (univPrefixAccepts bytes) ++
    test "Univ full-buffer decoder rejects trailing bytes"
      (univExactRejects bytes)

def exprUnits : TestSeq :=
  let cases : List Expr := [
    .sort 0,
    .var 0,
    .var 42,
    .ref 0 #[],
    .ref 1 #[0, 1, 2],
    .recur 0 #[],
    .recur 2 #[1],
    .str 5,
    .nat 10,
    .share 0,
    .app (.var 0) (.var 1),
    .app (.app (.var 0) (.var 1)) (.var 2),  -- Nested apps (telescope)
    .lam .erased (.sort 0) (.var 0),
    .lam .affine (.sort 0) (.lam .linear (.sort 1) (.var 0)),  -- Nested lams (telescope)
    .all .many .shared (.sort 0) (.var 0),
    .all .linear .unique (.sort 0)
      (.all .erased .shared (.sort 1) (.var 0)),  -- Nested alls (telescope)
    .letE (.lean true) (.sort 0) (.var 0) (.var 1),
    .letE (.lean false) (.sort 0) (.var 0) (.var 1),
    .prj 0 1 (.var 0),
  ]
  cases.foldl (init := .done) fun acc e =>
    acc ++ test s!"Expr roundtrip: {repr e}" (exprSerde e) ++
      test s!"Expr Lean==Rust bytes: {repr e}"
        (rsEqExprSerialization e (serExpr e))

def exprPrefixAccepts (bytes : ByteArray) : Bool :=
  match runGet getExpr bytes with
  | .ok (.sort 0) => true
  | _ => false

def exprExactRejects (bytes : ByteArray) : Bool :=
  match deExpr bytes with
  | .error _ => true
  | .ok _ => false

def exprExactUnits : TestSeq :=
  let bytes := serExpr (.sort 0) ++ [0].toByteArray
  test "Expr prefix runner may leave trailing bytes"
      (exprPrefixAccepts bytes) ++
    test "Expr full-buffer decoder rejects trailing bytes"
      (exprExactRejects bytes)

def exprRejects (bytes : Array UInt8) : Bool :=
  match deExpr (ByteArray.mk bytes) with
  | .error _ => true
  | .ok _ => false

/-- Directed malformed vectors for the maximal-telescope grammar. Reserved
    binder, forall and let codes are covered by `Tests.IxonV4.rejectedExprCases`. -/
def strictExprUnits : TestSeq :=
  test "rejects empty app spine" (exprRejects #[0x70]) ++
  test "rejects nested app base"
    (exprRejects #[0x71, 0x71, 0x10, 0x11, 0x12]) ++
  test "rejects nested lambda body"
    (exprRejects #[0x81, 0x03, 0x00, 0x81, 0x03, 0x00, 0x10]) ++
  test "rejects nested forall codomain"
    (exprRejects #[0x91, 0x07, 0x00, 0x91, 0x07, 0x00, 0x10])

/-! ## TagN integer code -/

/-- Rung boundary values for an `f`-bit flag, plus the `UInt64` extremes. -/
def tagNBoundaries (f : Nat) : List Nat :=
  let ends := [tagNEnd1 f, tagNEnd2 f, tagNEnd3 f, tagNEnd4 f, tagNEnd5 f]
  [0, 1, 2 ^ 64 - 1] ++ ends.flatMap fun e => [e - 1, e, e + 1]

/-- Encode, check the width, decode exactly. -/
def tagNRoundtrip (f : Nat) (flag : UInt8) (v : Nat) : Bool :=
  let t : TagN := ⟨flag, v.toUInt64⟩
  let bytes := runPut (putTagN f flag v.toUInt64)
  bytes.size == tagNByteWidth f v &&
    match runGetExact (getTagN f) bytes with
    | .ok t' => t' == t
    | .error _ => false

def tagNEncodes (f : Nat) (flag : UInt8) (v : Nat) (expected : Array UInt8) : Bool :=
  runPut (putTagN f flag v.toUInt64) == ByteArray.mk expected

def tagNRejects (f : Nat) (bytes : Array UInt8) : Bool :=
  match runGetExact (getTagN f) (ByteArray.mk bytes) with
  | .error _ => true
  | .ok _ => false

/-- Every byte string of length 1 or 2 that decodes exactly re-encodes to
itself (no value has two encodings within these lengths). -/
def tagNShortCanonical (f : Nat) : Bool := Id.run do
  for a in [0:256] do
    let one := ByteArray.mk #[a.toUInt8]
    if let .ok t := runGetExact (getTagN f) one then
      if runPut (putTagN f t.flag t.value) != one then return false
    for b in [0:256] do
      let two := ByteArray.mk #[a.toUInt8, b.toUInt8]
      if let .ok t := runGetExact (getTagN f) two then
        if runPut (putTagN f t.flag t.value) != two then return false
  return true

def tagNUnits : TestSeq :=
  let perF (f : Nat) : TestSeq :=
    let flags : List UInt8 := [0, (2 ^ f - 1).toUInt8]
    let cases := flags.flatMap fun flag => (tagNBoundaries f).map (flag, ·)
    cases.foldl (init := .done) fun acc (flag, v) =>
      acc ++ test s!"TagN f={f} flag={flag} value={v}: width and roundtrip"
        (tagNRoundtrip f flag v)
  perF 0 ++ perF 2 ++ perF 4 ++
  test "TagN rung ends f=0" ([tagNEnd1 0, tagNEnd2 0, tagNEnd3 0, tagNEnd4 0, tagNEnd5 0]
    == [128, 16512, 82048, 16859264, 4311826560]) ++
  test "TagN rung ends f=2" ([tagNEnd1 2, tagNEnd2 2, tagNEnd3 2, tagNEnd4 2, tagNEnd5 2]
    == [32, 4128, 69664, 16846880, 4311814176]) ++
  test "TagN rung ends f=4" ([tagNEnd1 4, tagNEnd2 4, tagNEnd3 4, tagNEnd4 4, tagNEnd5 4]
    == [8, 1032, 66568, 16843784, 4311811080]) ++
  test "TagN f=4 bytes: 7" (tagNEncodes 4 0xA 7 #[0xA7]) ++
  test "TagN f=4 bytes: 8" (tagNEncodes 4 0xA 8 #[0xA8, 0x00]) ++
  test "TagN f=4 bytes: 1031" (tagNEncodes 4 0x1 1031 #[0x1B, 0xFF]) ++
  test "TagN f=4 bytes: 1032" (tagNEncodes 4 0 1032 #[0x0C, 0x00, 0x00]) ++
  test "TagN f=4 bytes: 66567" (tagNEncodes 4 0 66567 #[0x0C, 0xFF, 0xFF]) ++
  test "TagN f=4 bytes: 66568" (tagNEncodes 4 0 66568 #[0x0D, 0, 0, 0]) ++
  test "TagN f=4 bytes: 16843783" (tagNEncodes 4 0 16843783 #[0x0D, 0xFF, 0xFF, 0xFF]) ++
  test "TagN f=4 bytes: 16843784" (tagNEncodes 4 0 16843784 #[0x0E, 0, 0, 0, 0]) ++
  test "TagN f=4 bytes: 4311811079"
    (tagNEncodes 4 0 4311811079 #[0x0E, 0xFF, 0xFF, 0xFF, 0xFF]) ++
  test "TagN f=4 bytes: 4311811080"
    (tagNEncodes 4 0 4311811080 #[0x0F, 0, 0, 0, 0, 0, 0, 0, 0]) ++
  test "TagN f=0 bytes: 127" (tagNEncodes 0 0 127 #[0x7F]) ++
  test "TagN f=0 bytes: 128" (tagNEncodes 0 0 128 #[0x80, 0x00]) ++
  test "TagN f=0 bytes: 16512" (tagNEncodes 0 0 16512 #[0xC0, 0x00, 0x00]) ++
  test "TagN f=0 bytes: 82047" (tagNEncodes 0 0 82047 #[0xC0, 0xFF, 0xFF]) ++
  test "TagN f=0 bytes: 82048" (tagNEncodes 0 0 82048 #[0xC1, 0, 0, 0]) ++
  test "TagN f=0 bytes: 16859263" (tagNEncodes 0 0 16859263 #[0xC1, 0xFF, 0xFF, 0xFF]) ++
  test "TagN f=0 bytes: 16859264" (tagNEncodes 0 0 16859264 #[0xC2, 0, 0, 0, 0]) ++
  test "TagN f=0 bytes: 4311826560"
    (tagNEncodes 0 0 4311826560 #[0xC3, 0, 0, 0, 0, 0, 0, 0, 0]) ++
  test "TagN f=0 bytes: 2^64 - 1"
    (tagNEncodes 0 0 (2 ^ 64 - 1) #[0xC3, 0x7F, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]) ++
  test "TagN f=2 bytes: 32" (tagNEncodes 2 3 32 #[0xE0, 0x00]) ++
  test "TagN f=2 bytes: 4128" (tagNEncodes 2 3 4128 #[0xF0, 0x00, 0x00]) ++
  test "TagN f=2 bytes: 69663" (tagNEncodes 2 3 69663 #[0xF0, 0xFF, 0xFF]) ++
  test "TagN f=2 bytes: 69664" (tagNEncodes 2 3 69664 #[0xF1, 0, 0, 0]) ++
  test "TagN f=2 bytes: 16846879" (tagNEncodes 2 3 16846879 #[0xF1, 0xFF, 0xFF, 0xFF]) ++
  test "TagN f=2 bytes: 16846880" (tagNEncodes 2 3 16846880 #[0xF2, 0, 0, 0, 0]) ++
  test "TagN f=2 bytes: 4311814176"
    (tagNEncodes 2 3 4311814176 #[0xF3, 0, 0, 0, 0, 0, 0, 0, 0]) ++
  test "TagN f=2 rejects code 4" (tagNRejects 2 #[0x34]) ++
  test "TagN f=2 rejects code 15" (tagNRejects 2 #[0x3F]) ++
  test "TagN f=0 rejects code 4" (tagNRejects 0 #[0xC4]) ++
  test "TagN f=0 rejects code 63" (tagNRejects 0 #[0xFF]) ++
  test "TagN f=4 rejects overflow"
    (tagNRejects 4 #[0x0F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]) ++
  test "TagN f=0 rejects overflow"
    (tagNRejects 0 #[0xC3, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]) ++
  -- The smallest overflowing rung-6 payloads: 2^64 - R5 for each f, one past
  -- the payload of 2^64 - 1 (R5 = 0x1_0101_4080, 0x1_0101_1020, 0x1_0101_0408).
  test "TagN f=0 rejects the smallest overflow"
    (tagNRejects 0 #[0xC3, 0x80, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]) ++
  test "TagN f=2 accepts 2^64 - 1"
    (tagNEncodes 2 0 (2 ^ 64 - 1) #[0x33, 0xDF, 0xEF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]) ++
  test "TagN f=2 rejects the smallest overflow"
    (tagNRejects 2 #[0x33, 0xE0, 0xEF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]) ++
  test "TagN f=4 accepts 2^64 - 1"
    (tagNEncodes 4 0 (2 ^ 64 - 1) #[0x0F, 0xF7, 0xFB, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]) ++
  test "TagN f=4 rejects the smallest overflow"
    (tagNRejects 4 #[0x0F, 0xF8, 0xFB, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]) ++
  -- An invalid code followed by as many bytes as a valid rung would read:
  -- a reader that kept only the low two code bits would accept these.
  test "TagN f=0 rejects code 4 with two following bytes" (tagNRejects 0 #[0xC4, 0x00, 0x00]) ++
  test "TagN f=2 rejects code 4 with two following bytes" (tagNRejects 2 #[0x34, 0x00, 0x00]) ++
  test "TagN rejects truncated rung 2" (tagNRejects 4 #[0x08]) ++
  test "TagN rejects truncated rung 4" (tagNRejects 4 #[0x0D, 0x00, 0x00]) ++
  test "TagN rejects truncated rung 5" (tagNRejects 4 #[0x0E, 0x00, 0x00, 0x00]) ++
  test "TagN rejects truncated rung 6" (tagNRejects 4 #[0x0F, 0x00, 0x00, 0x00]) ++
  test "TagN rejects trailing byte" (tagNRejects 4 #[0x07, 0x00]) ++
  test "TagN f=0 short strings canonical" (tagNShortCanonical 0) ++
  test "TagN f=2 short strings canonical" (tagNShortCanonical 2) ++
  test "TagN f=4 short strings canonical" (tagNShortCanonical 4)

/-! ## ExprMeta arena wire format

Directed byte vectors for the arena encoding (implicit post-order children,
explicit TagN backward deltas); the same vectors are pinned in Rust
(`ixon::metadata::tests::arena_vector_*`). Name indices are 0 and 1 (one
byte in every integer code). -/

def arenaVecNames : Address × Address × NameIndex × NameReverseIndex :=
  let a := Address.blake3 (ByteArray.mk #[1])
  let b := Address.blake3 (ByteArray.mk #[2])
  (a, b, (({} : NameIndex).insert a 0).insert b 1, #[a, b])

def arenaBytes (arena : ExprMetaArena) : ByteArray :=
  runPut (putExprMetaArenaIndexed arena arenaVecNames.2.2.1)

def arenaFrom (bytes : Array UInt8) : Except String ExprMetaArena :=
  runGetExact (getExprMetaArenaIndexed arenaVecNames.2.2.2) (ByteArray.mk bytes)

/-- The arena writes exactly `bytes`, and `bytes` read back to the arena. -/
def arenaVector (arena : ExprMetaArena) (bytes : Array UInt8) : Bool :=
  arenaBytes arena == ByteArray.mk bytes &&
    match arenaFrom bytes with
    | .ok a => a == arena
    | .error _ => false

def arenaRejects (bytes : Array UInt8) : Bool :=
  match arenaFrom bytes with
  | .error _ => true
  | .ok _ => false

def exprMetaArenaUnits : TestSeq :=
  let a := arenaVecNames.1
  let b := arenaVecNames.2.1
  -- `fun (x : T) => f x` in post-order: every child implicit.
  let tree : ExprMetaArena := { nodes := #[
    .ref b, .ref a, .leaf, .app 1 2, .binder a .default 0 3] }
  -- Shared nodes: explicit backward deltas next to implicit slots.
  let dag : ExprMetaArena := { nodes := #[
    .leaf, .app 0 0, .letBinder a 0 1 0, .prj b 1, .mdata #[] 3] }
  -- A forward reference wraps.
  let forward : ExprMetaArena := { nodes := #[.leaf, .leaf, .leaf, .prj a 7] }
  test "arena: a post-order tree writes no references"
    (arenaVector tree #[0x05, 0x38, 0x01, 0x38, 0x00, 0x00, 0x0B, 0x13, 0x00]) ++
  test "arena: shared nodes are explicit backward deltas"
    (arenaVector dag #[0x05, 0x00, 0x0A, 0x00, 0x32, 0x00, 0x01, 0x01, 0x40,
      0x01, 0x01, 0x49, 0x00]) ++
  test "arena: a forward reference wraps"
    (arenaVector forward #[0x04, 0x00, 0x00, 0x00,
      0x40, 0x00, 0xC3, 0x7B, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]) ++
  test "arena: rejects the retired call-site kinds 10 and 11 (CQ3.6)"
    (arenaRejects #[0x01, 0x50, 0x00, 0x00, 0x00, 0x00, 0x00] &&
      arenaRejects #[0x01, 0x58, 0x00, 0x00, 0x00, 0x00, 0x00]) ++
  test "arena: rejects an explicit slot at the implicit position"
    (arenaRejects #[0x02, 0x00, 0x08, 0x00, 0x00]) ++
  test "arena: rejects an implicit slot with no preceding node"
    (arenaRejects #[0x01, 0x09, 0x00]) ++
  test "arena: rejects mask bits beyond the kind's slots"
    (arenaRejects #[0x01, 0x01] && arenaRejects #[0x02, 0x00, 0x0C] &&
      arenaRejects #[0x01, 0x39, 0x00]) ++
  test "arena: rejects unknown kinds" (arenaRejects #[0x01, 0x60]) ++
  test "arena: rejects every truncation"
    (let bytes : Array UInt8 := #[0x05, 0x38, 0x01, 0x38, 0x00, 0x00, 0x0B, 0x13, 0x00]
     (List.range bytes.size).all fun n => arenaRejects (bytes.extract 0 n)) ++
  test "arena: the canonical form of a rejected vector is accepted"
    (arenaVector { nodes := #[.leaf, .app 0 0] } #[0x02, 0x00, 0x0A, 0x00])

def constantUnits : TestSeq :=
  let defn := Definition.mk .defn .safe 0 (.sort 0) (.var 0)
  let c := Constant.mk
    (.defn defn)
    #[.var 0, .sort 1]  -- sharing
    #[⟨(Blake3.Rust.hash "ref".toUTF8).val⟩]  -- refs
    #[.zero, .succ .zero]  -- univs
  test "Constant roundtrip" (constantSerde c)

def commUnits : TestSeq :=
  let addr1 : Address := ⟨(Blake3.Rust.hash "secret".toUTF8).val⟩
  let addr2 : Address := ⟨(Blake3.Rust.hash "payload".toUTF8).val⟩
  let c := Comm.mk addr1 addr2
  test "Comm roundtrip" (commSerde c)

/-! ## Env Unit Tests -/

def envSerdeUnit (env : Env) : Bool :=
  match serEnv env with
  | .error _ => false
  | .ok bytes1 =>
    match deEnv bytes1 with
    | .ok env' =>
      match serEnv env' with
      | .ok bytes2 => bytes1 == bytes2
      | .error _ => false
    | .error _ => false

def envUnitTests : TestSeq :=
  -- Test 1: Empty env
  let emptyEnv : Env := {}
  -- Test 2: Env with only a blob. Blob addresses must be the content
  -- hash of the bytes — readers verify per entry.
  let blobBytes := ByteArray.mk #[4, 5, 6]
  let blobAddr := Address.blake3 blobBytes
  let envWithBlob : Env := { blobs := ({} : Std.HashMap _ _).insert blobAddr blobBytes }
  -- Test 3: Env with a simple name (no named entry)
  let testName := Ix.Name.mkStr Ix.Name.mkAnon "test"
  let testNameAddr := testName.getHash
  let envWithName : Env := { names := ({} : Std.HashMap _ _).insert testNameAddr testName }
  -- Test 4: Env with named entry and empty metadata. §5 keys the
  -- entry's constant by §2 rank, so the target must be a stored
  -- constant (content-addressed — readers verify per entry).
  let namedDef : Definition := {
    kind := .defn, safety := .safe, lvls := 0, typ := .sort 0, value := .sort 0
  }
  let namedConst : Constant := {
    info := .defn namedDef, sharing := #[], refs := #[], univs := #[]
  }
  let constAddr := Address.blake3 (serConstant namedConst)
  let envWithNamed : Env := Id.run do
    let mut env : Env := {}
    env := env.storeConst constAddr namedConst
    env := { env with names := RawEnv.addNameComponents env.names testName }
    env := env.registerName testName { addr := constAddr, constMeta := .empty }
    return env
  -- Test 5: Env with nested name and named entry, plus an `original`
  -- edge whose address is deliberately NOT a stored constant — the §5
  -- original address stays raw on the wire (it may reference an
  -- assumed constant), so this must roundtrip.
  let nestedName := Ix.Name.mkStr (Ix.Name.mkNat testName 42) "bar"
  let envWithNestedName : Env := Id.run do
    let mut env : Env := {}
    env := env.storeConst constAddr namedConst
    env := { env with names := RawEnv.addNameComponents env.names nestedName }
    env := env.registerName nestedName
      { addr := constAddr, constMeta := .empty,
        original := some (Address.blake3 (ByteArray.mk #[99]), .empty) }
    return env
  -- Test 6: Env with blob and comm
  let secretAddr := Address.blake3 (ByteArray.mk #[10, 11, 12])
  let payloadAddr := Address.blake3 (ByteArray.mk #[13, 14, 15])
  let commAddr := Address.blake3 (ByteArray.mk #[16, 17, 18])
  let envWithBlobAndComm : Env := {
    blobs := ({} : Std.HashMap _ _).insert blobAddr blobBytes,
    comms := ({} : Std.HashMap _ _).insert commAddr (Comm.mk secretAddr payloadAddr)
  }
  -- Test 7: Bundle env — main + assumptions + anonHints exercise the
  -- bundle header and §3.
  let bundleDef : Definition := {
    kind := .defn, safety := .safe, lvls := 0, typ := .sort 0, value := .sort 0
  }
  let bundleConst : Constant := {
    info := .defn bundleDef, sharing := #[], refs := #[], univs := #[]
  }
  let bundleConstAddr := Address.blake3 (serConstant bundleConst)
  let bundleEnv : Env := Id.run do
    let mut env : Env := {}
    env := env.storeConst bundleConstAddr bundleConst
    return { env with
      main := some bundleConstAddr
      assumptions := ({} : Std.HashSet Address)
        |>.insert (Address.blake3 (ByteArray.mk #[42]))
        |>.insert (Address.blake3 (ByteArray.mk #[43]))
      anonHints := ({} : Std.HashMap _ _).insert bundleConstAddr (.regular 5) }
  test "Empty env roundtrip" (envSerdeUnit emptyEnv) ++
  test "Env with blob roundtrip" (envSerdeUnit envWithBlob) ++
  test "Env with name roundtrip" (envSerdeUnit envWithName) ++
  test "Env with named (empty meta) roundtrip" (envSerdeUnit envWithNamed) ++
  test "Env with nested name roundtrip" (envSerdeUnit envWithNestedName) ++
  test "Env with blob+comm roundtrip" (envSerdeUnit envWithBlobAndComm) ++
  test "Bundle env (main/assumptions/hints) roundtrip" (envSerdeUnit bundleEnv)

/-! ## Cross-implementation serialization comparison tests -/

def univSerializationMatches (u : Univ) : Bool :=
  rsEqUnivSerialization u (serUniv u)

def exprSerializationMatches (e : Expr) : Bool :=
  rsEqExprSerialization e (serExpr e)

def constantSerializationMatches (c : Constant) : Bool :=
  rsEqConstantSerialization c (serConstant c)

def envSerializationMatches (raw : RawEnv) : Bool :=
  match serEnv raw.toEnv with
  | .ok bytes => rsEqEnvSerialization raw bytes
  | .error _ => false

/-- Strict byte equality between the pure-Lean writer and the Rust
    writer over the same RawEnv (a stronger check than
    `rsEqEnvSerialization`'s content comparison). -/
def envBytesMatchRust (raw : RawEnv) : Bool :=
  match serEnv raw.toEnv with
  | .ok bytes => match rsSerEnvFFI raw with
    | .ok rustBytes => bytes == rustBytes
    | .error _ => false
  | .error _ => false

/-- Unit tests for Lean==Rust serialization comparison -/
def envSerializationUnitTests : TestSeq :=
  -- Test 1: Empty env
  let emptyRaw : RawEnv := { consts := #[], named := #[], blobs := #[], comms := #[] }
  -- Test 2: Env with one blob (content-addressed: readers verify).
  let blobBytes := ByteArray.mk #[4, 5, 6]
  let blobAddr := Address.blake3 blobBytes
  let blobRaw : RawEnv := {
    consts := #[], named := #[],
    blobs := #[{ addr := blobAddr, bytes := blobBytes }],
    comms := #[]
  }
  -- Test 3: Env with one comm
  let commAddr := Address.blake3 (ByteArray.mk #[7, 8, 9])
  let secretAddr := Address.blake3 (ByteArray.mk #[10, 11, 12])
  let payloadAddr := Address.blake3 (ByteArray.mk #[13, 14, 15])
  let commRaw : RawEnv := {
    consts := #[], named := #[],
    blobs := #[],
    comms := #[{ addr := commAddr, comm := Comm.mk secretAddr payloadAddr }]
  }
  -- Test 4: Env with blob + comm
  let blobCommRaw : RawEnv := {
    consts := #[], named := #[],
    blobs := #[{ addr := blobAddr, bytes := blobBytes }],
    comms := #[{ addr := commAddr, comm := Comm.mk secretAddr payloadAddr }]
  }
  -- Test 5: Bundle env — the directed cross-language vector for the
  -- bundle header (main/assumptions) and §3 anon_hints.
  let bundleDef : Definition := {
    kind := .defn, safety := .safe, lvls := 0, typ := .sort 0, value := .sort 0
  }
  let bundleConst : Constant := {
    info := .defn bundleDef, sharing := #[], refs := #[], univs := #[]
  }
  let bundleConstAddr := Address.blake3 (serConstant bundleConst)
  let bundleRaw : RawEnv := {
    consts := #[{ addr := bundleConstAddr, const := bundleConst }],
    named := #[], blobs := #[], comms := #[],
    main := some bundleConstAddr,
    assumptions := #[
      Address.blake3 (ByteArray.mk #[42]),
      Address.blake3 (ByteArray.mk #[43])],
    anonHints := #[(bundleConstAddr, .regular 5)]
  }
  -- Test 6: Named entry + hints — the directed cross-language vector
  -- for the index-keyed §5 (name §4-index + const §2 rank) and §3
  -- (delta-coded ranks + fused hints). Unlike `RawEnv.toEnv`, the Rust
  -- FFI side does not auto-add name components for named entries, so
  -- `names` carries the leaf explicitly (ancestors are emitted by both
  -- topological sorts from the parent chain).
  let namedName := Ix.Name.mkStr Ix.Name.mkAnon "MyDef"
  let namedRaw : RawEnv := {
    consts := #[{ addr := bundleConstAddr, const := bundleConst }],
    named := #[{ name := namedName, addr := bundleConstAddr,
                 constMeta := .empty, hints := some (.regular 7) }],
    blobs := #[], comms := #[],
    names := #[{ addr := namedName.getHash, name := namedName }],
    anonHints := #[(bundleConstAddr, .abbrev)]
  }
  -- Test 7: Metadata-bearing named entries — the directed cross-language
  -- byte vector for the FULL metadata wire grammar: an arena over the
  -- kinds 0-9 (indexed names, binder info, an app, a ref, mdata), the
  -- extension tables (sharing exprs, raw refs, univs, univ patches), and
  -- a muts entry with the nested-aux `auxLayout` sidecar. Every indexed
  -- name address is a registered name component. (Before CQ3.6 the arena
  -- also carried a call-site surgery node, kinds 10/11, now retired.)
  let surgName := Ix.Name.mkStr Ix.Name.mkAnon "surg"
  let blkName := Ix.Name.mkStr Ix.Name.mkAnon "blk"
  let anonAddr := Ix.Name.mkAnon.getHash
  let surgArena : ExprMetaArena := { nodes := #[
    .leaf,
    .binder anonAddr .implicit 0 0,
    .ref surgName.getHash,
    .app 2 1,
    .mdata #[#[(blkName.getHash, .ofName surgName.getHash)]] 3
  ] }
  let surgMeta : ConstantMeta := {
    info := .defn surgName.getHash #[anonAddr] #[surgName.getHash] #[]
      surgArena 0 4,
    metaSharing := #[.app (.share 1) (.var 2), .sort 0],
    metaRefs := #[bundleConstAddr],
    metaUnivs := #[.succ (.var 0), .max .zero (.var 1)],
    univPatches := #[⟨1, #[0, 2]⟩, ⟨4, #[3]⟩]
  }
  let mutsMeta : ConstantMeta := .new
    (.muts #[#[surgName.getHash], #[blkName.getHash]]
      (some { perm := #[1, 0], sourceCtorCounts := #[2, 3],
              evaporated := #[0, 0] }))
  let metaRaw : RawEnv := {
    consts := #[{ addr := bundleConstAddr, const := bundleConst }],
    named := #[
      { name := surgName, addr := bundleConstAddr, constMeta := surgMeta,
        hints := some (.regular 3) },
      { name := blkName, addr := bundleConstAddr, constMeta := mutsMeta }],
    blobs := #[], comms := #[],
    names := #[
      { addr := surgName.getHash, name := surgName },
      { addr := blkName.getHash, name := blkName }]
  }
  test "Empty env Lean==Rust" (envSerializationMatches emptyRaw) ++
  test "Blob env Lean==Rust" (envSerializationMatches blobRaw) ++
  test "Comm env Lean==Rust" (envSerializationMatches commRaw) ++
  test "Blob+Comm env Lean==Rust" (envSerializationMatches blobCommRaw) ++
  test "Bundle env Lean==Rust" (envSerializationMatches bundleRaw) ++
  test "Named env Lean==Rust" (envSerializationMatches namedRaw) ++
  test "Empty env bytes Lean==Rust" (envBytesMatchRust emptyRaw) ++
  test "Blob env bytes Lean==Rust" (envBytesMatchRust blobRaw) ++
  test "Bundle env bytes Lean==Rust" (envBytesMatchRust bundleRaw) ++
  test "Named env bytes Lean==Rust" (envBytesMatchRust namedRaw) ++
  test "Metadata env bytes Lean==Rust" (envBytesMatchRust metaRaw) ++
  test "Metadata env pure serde" (envSerde metaRaw)

/-! ## Canonical env merkle root: Lean vs. Rust agreement -/

def envMerkleRootMatches (raw : RawEnv) : Bool :=
  let env := raw.toEnv
  raw.merkleRoot == rsEnvMerkleRoot env

/-- Both pure-Lean and Rust FFI agree on the merkle root over the env's
    consts addresses. Distinct tests for various const-set shapes. -/
def envMerkleRootUnitTests : TestSeq :=
  -- Empty env: no root.
  let emptyRaw : RawEnv :=
    { consts := #[], named := #[], blobs := #[], comms := #[] }
  -- Single-const env.
  let constAddr := Address.blake3 (ByteArray.mk #[42])
  let oneConst : Constant :=
    { info := .axio { isUnsafe := false, lvls := 0, typ := .sort 0 },
      sharing := #[], refs := #[], univs := #[] }
  let singleRaw : RawEnv :=
    { consts := #[{ addr := constAddr, const := oneConst }],
      named := #[], blobs := #[], comms := #[] }
  -- Two-const env, inserted in different orders to check sort invariance.
  let addrA := Address.blake3 "a".toUTF8
  let addrB := Address.blake3 "b".toUTF8
  let raw_ab : RawEnv :=
    { consts := #[{ addr := addrA, const := oneConst },
                  { addr := addrB, const := oneConst }],
      named := #[], blobs := #[], comms := #[] }
  let raw_ba : RawEnv :=
    { consts := #[{ addr := addrB, const := oneConst },
                  { addr := addrA, const := oneConst }],
      named := #[], blobs := #[], comms := #[] }
  test "empty env merkle root is none" (emptyRaw.merkleRoot == none) ++
  test "empty env: Lean==Rust" (envMerkleRootMatches emptyRaw) ++
  test "single const: Lean==Rust" (envMerkleRootMatches singleRaw) ++
  test "two consts (a,b): Lean==Rust" (envMerkleRootMatches raw_ab) ++
  test "two consts (b,a): Lean==Rust" (envMerkleRootMatches raw_ba) ++
  test "(a,b) and (b,a) same root"
    (raw_ab.merkleRoot == raw_ba.merkleRoot)

/-! ## Checked format 4 and versioned storage envelopes -/

/-- The empty env's bytes, with the header byte replaced by `header`. -/
private def emptyEnvWithHeader (header : UInt8) : ByteArray :=
  match serEnv ({} : Env) with
  | .ok bytes => bytes.set! 0 header
  | .error _ => .empty

/-- `r` failed with the readers' format-version error for version `got`. -/
private def versionRejected {α : Type} (r : Except String α) (got : Nat) : Bool :=
  match r with
  | .ok _ => false
  | .error e =>
    (e.splitOn s!"unsupported .ixe envelope version {got}").length > 1

def envHeaderUnits : TestSeq :=
  let bytes := match serEnv ({} : Env) with | .ok b => b | .error _ => .empty
  test "env header is TagN(4, 0xE, 4) = 0xE4" (bytes.data[0]? == some 0xE4)
  ++ test "wireFormatId is ixon-v4" (wireFormatId == "ixon-v4")
  ++ test "checked object-format byte remains 4" (Env.OBJECT_FORMAT == 4)
  ++ test "Lean reader accepts the version 4 header" ((deEnv bytes).toOption.isSome)
  ++ test "Lean reader rejects a version 3 header"
      (versionRejected (deEnv (emptyEnvWithHeader 0xE3)) 3)
  ++ test "Lean streaming reader rejects a version 3 header"
      (versionRejected (deEnvVerifiedLazy (emptyEnvWithHeader 0xE3)) 3)
  ++ test "Rust reader rejects a version 3 header"
      (versionRejected (deEnvAnon (emptyEnvWithHeader 0xE3)) 3)

/-! ## Separate original-data storage (M6D) -/

private def originalCheck (label : String) (ok : Bool) : Except String Unit :=
  if ok then .ok () else .error label

private def originalReadersRefuse (bytes : ByteArray) : Bool :=
  (deEnv bytes).toOption.isNone && (deEnvVerifiedLazy bytes).toOption.isNone &&
    (rsDeEnv bytes).toOption.isNone && (deEnvAnon bytes).toOption.isNone

/-- Construct adversarial trailers independently of the validating writer. -/
private def originalWire (base : ByteArray) (rows : Array RawBlob)
    (hints : Array (UInt64 × Option Lean.ReducibilityHints)) : ByteArray :=
  (base.set! 0 0xE5) ++ runPut do
    putTagN 0 0 rows.size.toUInt64
    for row in rows do
      Serialize.put row.addr
      putTagN 0 0 row.bytes.size.toUInt64
      putBytes row.bytes
    putTagN 0 0 hints.size.toUInt64
    for (idx, hint) in hints do
      putTagN 0 0 idx
      putFusedOptHint hint

private def originalDataChecks (definition : Definition) : Except String Unit := do
  let c : Constant := {
    info := .defn definition, sharing := #[], refs := #[], univs := #[] }
  let a : Constant := { c with info := .quot { kind := .type, lvls := 0, typ := .sort 0 } }
  let b : Constant := { c with info := .quot { kind := .ctor, lvls := 0, typ := .sort 0 } }
  let ca := Address.blake3 (serConstant c)
  let oa : RawBlob := { addr := Address.blake3 (serConstant a), bytes := serConstant a }
  let ob : RawBlob := { addr := Address.blake3 (serConstant b), bytes := serConstant b }
  originalCheck "fixture addresses must be distinct" (ca != oa.addr && ca != ob.addr && oa.addr != ob.addr)
  let n := Ix.Name.mkStr Ix.Name.mkAnon "OriginalA"
  let clear := Ix.Name.mkStr Ix.Name.mkAnon "OriginalClear"
  let absent := Ix.Name.mkStr Ix.Name.mkAnon "OriginalAbsent"
  let raw : RawEnv := {
    consts := #[{ addr := ca, const := c }], blobs := #[], comms := #[],
    named := #[n, clear, absent].map (fun name =>
      { name, addr := ca, constMeta := .empty, original := some (oa.addr, .empty),
        hints := some Lean.ReducibilityHints.abbrev }),
    names := #[n, clear, absent].map (fun name => { addr := name.getHash, name }),
    originals := #[oa, ob],
    originalHintOverrides := #[(n, some (.regular 37)), (clear, none)] }
  let env ← raw.toEnvChecked
  let bytes ← serEnv env
  originalCheck "v5 bytes agree across writers" (bytes == (← rsSerEnvFFI raw) && bytes.data[0]? == some 0xE5)
  let legacy := { env with originals := {}, originalHintOverrides := {} }
  let base ← serEnv legacy
  let baseRead ← deEnv base
  originalCheck "v5 changes only the header before its trailer"
    (base.data[0]? == some 0xE4 && bytes.extract 1 base.size == base.extract 1 base.size)
  let goldenEmpty := runPut do
    putU8 0xE4
    Serialize.put Ix.Merkle.zeroAddress
    putBytes (ByteArray.mk #[0, 0, 0, 0, 0, 1])
    Serialize.put Ix.Name.mkAnon.getHash
    putBytes (ByteArray.mk #[0, 0, 0])
  originalCheck "empty v4 bytes retain the legacy layout" ((← serEnv {}) == goldenEmpty)
  let full ← deEnv bytes
  let rust ← rsDeEnv bytes
  let parts ← deEnvVerifiedLazy bytes
  let named ← parts.materializeAllNamed
  let cached ← parts.materializeAll
  for loaded in [full, rust, named, cached] do
    originalCheck "full/lazy original tables roundtrip" ((← serEnv loaded) == bytes)
    originalCheck "original hints preserve some, explicit none, and absence"
      (loaded.originalHintOverrides[n]? == some (some (.regular 37)) &&
       loaded.originalHintOverrides[clear]? == some none && loaded.originalHintOverrides[absent]? == none)
    originalCheck "original payloads stay raw and outside canonical lookup"
      (loaded.originals.size == 2 && loaded.originals.toList.all (fun (_, lc) => lc.cache.isNone) &&
       (loaded.getConst? oa.addr).isNone)
    originalCheck "canonical name lookup does not switch to original addresses"
      ((loaded.addrToName[ca]?).any (fun name => (loaded.named[name]?).any (·.addr == ca)) &&
       loaded.addrToName[oa.addr]? == none)
  originalCheck "the trailer preserves the Lean reader's canonical alias choice"
    (full.addrToName[ca]? == baseRead.addrToName[ca]? && named.addrToName[ca]? == baseRead.addrToName[ca]?)
  originalCheck "verified lazy originals retain backing windows"
    (parts.env.originals.toList.all fun (_, lc) => lc.off > 0 && lc.buf.size == bytes.size)
  let anon ← deEnvAnon bytes
  let prefixEnv ← rsDeEnvAnon bytes
  for view in [anon, prefixEnv] do
    originalCheck "anonymous views omit both original-data tables"
      (view.originals.isEmpty && view.originalHintOverrides.isEmpty && view.consts.size == 1)
  let (s1, s2, s3, s4, s5, s6, trailer) := envSectionSizes env
  originalCheck "v5 size accounting includes exactly its trailer"
    (35 + s1 + s2 + s3 + s4 + s5 + s6 + trailer == bytes.size && trailer == bytes.size - base.size)
  let (v1, v2, v3, v4, v5, v6, emptyTrailer) := envSectionSizes legacy
  originalCheck "v4 size accounting matches its bytes with no trailer"
    (35 + v1 + v2 + v3 + v4 + v5 + v6 == base.size && emptyTrailer == 0)
  for only in [{ raw with originals := #[] }, { raw with originalHintOverrides := #[] }] do
    let emitted ← serEnv (← only.toEnvChecked)
    originalCheck "either nonempty table selects v5"
      (emitted.data[0]? == some 0xE5 && emitted == (← rsSerEnvFFI only))
    originalCheck "single-table v5 roundtrips" ((← serEnv (← deEnv emitted)) == emitted)
  for duplicate in [
      { raw with originals := raw.originals.push oa },
      { raw with originals := raw.originals.push { oa with bytes := ob.bytes } },
      { raw with originalHintOverrides := raw.originalHintOverrides.push (n, some (.regular 37)) },
      { raw with originalHintOverrides := raw.originalHintOverrides.push (n, none) }] do
    for refusal in [(duplicate.toEnvChecked >>= serEnv), rsSerEnvFFI duplicate] do
      match refusal with
      | .ok _ => throw "duplicate original-data key was silently folded"
      | .error e => originalCheck "duplicate evidence is checked before folding" ((e.splitOn "duplicate").length > 1)
  let malformed : RawBlob := {
    addr := Address.blake3 (ByteArray.mk #[0xff, 0, 1]), bytes := ByteArray.mk #[0xff, 0, 1] }
  let rawBad := { raw with originals := #[malformed] }
  originalCheck "raw FFI transfer preserves malformed bytes"
    (Tests.FFI.Ixon.rawEnvEq (Tests.FFI.Ixon.roundtripRawEnv rawBad) rawBad)
  originalCheck "Merkle roots ignore unchecked original data"
    (raw.merkleRoot == rawBad.merkleRoot && rsEnvMerkleRootFFI raw == rsEnvMerkleRootFFI rawBad)
  for bad in [rawBad,
      { raw with originals := #[{ addr := ca, bytes := serConstant c }] },
      { raw with
        consts := #[{ addr := oa.addr, const := c }], named := #[], names := #[], originalHintOverrides := #[] },
      { raw with originalHintOverrides := #[(Ix.Name.mkAnon, none)] },
      { raw with named := raw.named.map (fun row => { row with original := none }) }] do
    originalCheck "writers refuse malformed, overlapping or unbound original data"
      ((bad.toEnvChecked >>= serEnv).toOption.isNone && (rsSerEnvFFI bad).toOption.isNone)
  let sorted := Env.topologicalSortNames env.names
  let idx ← match sorted.findIdx? (fun (_, name) => name == n) with
    | some i => pure i.toUInt64
    | none => throw "fixture name missing from index"
  let clearIdx ← match sorted.findIdx? (fun (_, name) => name == clear) with
    | some i => pure i.toUInt64
    | none => throw "fixture clear-name missing from index"
  originalCheck "fixture hint indices differ" (idx != clearIdx)
  let descending := if idx < clearIdx then #[(clearIdx, none), (idx, none)]
    else #[(idx, none), (clearIdx, none)]
  let noncanonical := oa.bytes.push 0
  for bad in [base ++ ByteArray.mk #[0], bytes.push 0, bytes.extract 0 (bytes.size - 1),
      bytes.set! 0 0xE6, originalWire base #[] #[],
      originalWire base #[oa, oa] #[],
      originalWire base (#[oa, ob].qsort fun a b => addrLt b.addr a.addr) #[],
      originalWire base #[malformed] #[],
      originalWire base #[{ oa with bytes := ob.bytes }] #[],
      originalWire base #[{ addr := Address.blake3 noncanonical, bytes := noncanonical }] #[],
      originalWire base #[{ addr := ca, bytes := serConstant c }] #[],
      originalWire base #[oa] #[(idx, none), (idx, some Lean.ReducibilityHints.opaque)],
      originalWire base #[oa] descending,
      originalWire base #[oa] #[(sorted.size.toUInt64, none)],
      originalWire base #[oa] #[(0, none)]] do
    originalCheck "full and verified-lazy readers refuse malformed original trailers" (originalReadersRefuse bad)

/-- Keep the fixture as a parameter so the compiler cannot initialize the
entire closed FFI computation before the selected test runs. -/
private def originalDataUnits (definition : Definition) : TestSeq :=
  .individualIO "original data: v4/v5, exact FFI, lazy retention and malformed controls" none (do
    let result ← IO.lazyPure fun _ => originalDataChecks definition
    return match result with
      | .ok _ => (true, 0, 0, none)
      | .error e => (false, 0, 0, some e)) .done

/-! ## Test Suite (property-based) -/

public def Tests.Ixon.suite : List TestSeq := [
  envHeaderUnits,
  Tests.Ix.RoleGeneration.units .natDiv,
  Tests.Ix.RoleGeneration.artifactUnits .natDiv,
  Tests.Ix.RoleArtifactConsumer.units,
  Tests.Ix.RoleBinding.units {
    sharing := #[], refs := #[], univs := #[.zero], info := .defn {
      kind := .defn, safety := .safe, lvls := 0, typ := .sort 0, value := .sort 0 } },
  Tests.Ix.RolePublication.units {
    sharing := #[], refs := #[], univs := #[.zero], info := .defn {
      kind := .defn, safety := .safe, lvls := 0, typ := .sort 0, value := .sort 0 } },
  Tests.Ix.OriginalData.units Ix.Merkle.zeroAddress,
  originalDataUnits {
    kind := .defn, safety := .safe, lvls := 0, typ := .sort 0, value := .sort 0 },
  univExactUnits,
  univUnits,
  exprExactUnits,
  exprUnits,
  strictExprUnits,
  tagNUnits,
  exprMetaArenaUnits,
  -- Env unit tests (for debugging serialization)
  envUnitTests,
  -- Env serialization comparison unit tests
  envSerializationUnitTests,
  -- Env merkle root agreement (Lean vs. Rust FFI)
  envMerkleRootUnitTests,
  -- Pure Lean serde roundtrips
  checkIO "Univ serde roundtrips" (∀ u : Univ, univSerde u),
  checkIO "Expr serde roundtrips" (∀ e : Expr, exprSerde e),
  checkIO "Constant serde roundtrips" (∀ c : Constant, constantSerde c),
  checkIO "Comm serde roundtrips" (∀ c : Comm, commSerde c),
  checkIO "Env serde roundtrips" (∀ raw : RawEnv, envSerde raw),
  -- Cross-implementation serialization comparison (Lean == Rust)
  checkIO "Univ serialization Lean==Rust" (∀ u : Univ, univSerializationMatches u),
  checkIO "Expr serialization Lean==Rust" (∀ e : Expr, exprSerializationMatches e),
  checkIO "Constant serialization Lean==Rust" (∀ c : Constant, constantSerializationMatches c),
  checkIO "Env serialization Lean==Rust" (∀ raw : RawEnv, envSerializationMatches raw),
  -- Strict byte equality between the two writers over generated envs —
  -- generated named entries carry full metadata (arena nodes,
  -- extension tables, auxLayout), so this is the generator-driven gate
  -- that the metadata wire format stays in sync.
  checkIO "Env bytes Lean==Rust" (∀ raw : RawEnv, envBytesMatchRust raw),
]
