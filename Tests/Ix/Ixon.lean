module
public import Ix.Ixon
public import Ix.Sharing
public import Tests.Gen.Ixon
public import Tests.FFI.Ixon

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
    .var 42,
    .succ .zero,
    .succ (.succ .zero),
    .succ (.succ (.succ .zero)),  -- Test telescope compression
    .max .zero (.var 0),
    .imax (.var 1) .zero,
    .max (.succ .zero) (.succ (.succ .zero)),
  ]
  cases.foldl (init := .done) fun acc u =>
    acc ++ test s!"Univ roundtrip: {repr u}" (univSerde u)

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
    .lam (.sort 0) (.var 0),
    .lam (.sort 0) (.lam (.sort 1) (.var 0)),  -- Nested lams (telescope)
    .all (.sort 0) (.var 0),
    .all (.sort 0) (.all (.sort 1) (.var 0)),  -- Nested alls (telescope)
    .letE true (.sort 0) (.var 0) (.var 1),
    .letE false (.sort 0) (.var 0) (.var 1),
    .prj 0 1 (.var 0),
  ]
  cases.foldl (init := .done) fun acc e =>
    acc ++ test s!"Expr roundtrip: {repr e}" (exprSerde e)

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

/-!
## Sharing Analysis Tests
-/

def sharingTest1 : Bool :=
  let e1 := Expr.app (.var 0) (.var 1)
  let (rewritten1, sharing1) := Ix.Sharing.applySharing #[e1]
  sharing1.isEmpty && rewritten1[0]! == e1

def sharingTest2 : Bool :=
  let ty := Expr.sort 0
  let e2 := Expr.app (.lam ty (.var 0)) (.lam ty (.var 1))
  let (_, sharing2) := Ix.Sharing.applySharing #[e2]
  sharing2.size == 1

def sharingTest3 : Bool :=
  let var0 := Expr.var 0
  let e3a := Expr.app var0 var0
  let e3b := Expr.app var0 (.var 1)
  let e3c := Expr.app var0 (.var 2)
  let (_, sharing3) := Ix.Sharing.applySharing #[e3a, e3b, e3c]
  sharing3.size >= 1

def sharingTest4 : Bool :=
  let e4 := Expr.lam (.sort 0) (.app (.var 0) (.var 0))
  let (rewritten4, _) := Ix.Sharing.applySharing #[e4]
  let serialized := serExpr rewritten4[0]!
  match deExpr serialized with
  | .ok e => e == rewritten4[0]!
  | .error _ => false

def sharingUnits : TestSeq :=
  test "no sharing for unique subterms" sharingTest1
  ++ test "shares repeated sort 0" sharingTest2
  ++ test "analyzes multiple expressions" sharingTest3
  ++ test "roundtrip after sharing" sharingTest4

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
  | .ok bytes => bytes == rsSerEnvFFI raw
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
  -- byte vector for the FULL metadata wire grammar: arena with a
  -- call-site surgery node (indexed names, kept/collapsed entries,
  -- canonMeta, origHead), surgery extension tables (sharing exprs, raw
  -- refs, univs), and a muts entry with the nested-aux `auxLayout`
  -- sidecar. Every indexed name address is a registered name component.
  let surgName := Ix.Name.mkStr Ix.Name.mkAnon "surg"
  let blkName := Ix.Name.mkStr Ix.Name.mkAnon "blk"
  let anonAddr := Ix.Name.mkAnon.getHash
  let surgArena : ExprMetaArena := { nodes := #[
    .leaf,
    .binder anonAddr .implicit 0 0,
    .callSite surgName.getHash
      #[.kept 0 1, .collapsed 0 0, .kept 2 1]
      #[1, 0]
      (some (1, 0)),
    .mdata #[#[(blkName.getHash, .ofName surgName.getHash)]] 2
  ] }
  let surgMeta : ConstantMeta := {
    info := .defn surgName.getHash #[anonAddr] #[surgName.getHash] #[]
      surgArena 0 3,
    metaSharing := #[.app (.share 1) (.var 2), .sort 0],
    metaRefs := #[bundleConstAddr],
    metaUnivs := #[.succ (.var 0), .max .zero (.var 1)]
  }
  let mutsMeta : ConstantMeta := .new
    (.muts #[#[surgName.getHash], #[blkName.getHash]]
      (some { perm := #[1, 0], sourceCtorCounts := #[2, 3] }))
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
  test "Surgery metadata env bytes Lean==Rust" (envBytesMatchRust metaRaw) ++
  test "Surgery metadata env pure serde" (envSerde metaRaw)

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

/-! ## Test Suite (property-based) -/

public def Tests.Ixon.suite : List TestSeq := [
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
  -- generated named entries carry full metadata (call-site surgery,
  -- extension tables, auxLayout), so this is the generator-driven gate
  -- that the metadata wire format stays in sync.
  checkIO "Env bytes Lean==Rust" (∀ raw : RawEnv, envBytesMatchRust raw),
]
