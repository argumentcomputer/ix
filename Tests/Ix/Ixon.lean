/-
  Pure Lean serialization tests for Ixon types.
  Generators have been moved to Tests/Gen/Ixon.lean.
-/

import Ix.Ixon
import Ix.Sharing
import Tests.Gen.Ixon
import Tests.FFI.Ixon

open LSpec SlimCheck Gen Ixon
open Tests.FFI.Ixon (rsEqUnivSerialization rsEqExprSerialization rsEqConstantSerialization rsEqEnvSerialization)

/-!
## Roundtrip Tests for New Format Types
-/

def univSerde (u : Univ) : Bool :=
  let bytes := serUniv u
  match desUniv bytes with
  | .ok u' => u == u'
  | .error _ => false

def exprSerde (e : Expr) : Bool :=
  let bytes := serExpr e
  match desExpr bytes with
  | .ok e' => e == e'
  | .error _ => false

def constantSerde (c : Constant) : Bool :=
  let bytes := serConstant c
  match desConstant bytes with
  | .ok c' => c == c'
  | .error _ => false

def commSerde (c : Comm) : Bool :=
  let bytes := serComm c
  match desComm bytes with
  | .ok c' => c == c'
  | .error _ => false

def envSerde (raw : RawEnv) : Bool :=
  let env := raw.toEnv
  let bytes1 := serEnv env
  match desEnv bytes1 with
  | .ok env' =>
    let bytes2 := serEnv env'
    bytes1 == bytes2  -- Byte-level equality after roundtrip
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
    #[⟨(Blake3.hash "ref".toUTF8).val⟩]  -- refs
    #[.zero, .succ .zero]  -- univs
  test "Constant roundtrip" (constantSerde c)

def commUnits : TestSeq :=
  let addr1 : Address := ⟨(Blake3.hash "secret".toUTF8).val⟩
  let addr2 : Address := ⟨(Blake3.hash "payload".toUTF8).val⟩
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
  match desExpr serialized with
  | .ok e => e == rewritten4[0]!
  | .error _ => false

def sharingUnits : TestSeq :=
  test "no sharing for unique subterms" sharingTest1
  ++ test "shares repeated sort 0" sharingTest2
  ++ test "analyzes multiple expressions" sharingTest3
  ++ test "roundtrip after sharing" sharingTest4

/-! ## Env Unit Tests -/

def envSerdeUnit (env : Env) : Bool :=
  let bytes1 := serEnv env
  match desEnv bytes1 with
  | .ok env' =>
    let bytes2 := serEnv env'
    bytes1 == bytes2
  | .error _ => false

def envUnitTests : TestSeq :=
  -- Test 1: Empty env
  let emptyEnv : Env := {}
  -- Test 2: Env with only a blob
  let blobAddr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  let envWithBlob : Env := { blobs := ({} : Std.HashMap _ _).insert blobAddr (ByteArray.mk #[4, 5, 6]) }
  -- Test 3: Env with a simple name (no named entry)
  let testName := Ix.Name.mkStr Ix.Name.mkAnon "test"
  let testNameAddr := testName.getHash
  let envWithName : Env := { names := ({} : Std.HashMap _ _).insert testNameAddr testName }
  -- Test 4: Env with named entry and empty metadata
  let constAddr := Address.blake3 (ByteArray.mk #[7, 8, 9])
  let envWithNamed : Env := Id.run do
    let mut env : Env := {}
    env := { env with names := RawEnv.addNameComponents env.names testName }
    env := env.registerName testName { addr := constAddr, constMeta := .empty }
    return env
  -- Test 5: Env with nested name and named entry
  let nestedName := Ix.Name.mkStr (Ix.Name.mkNat testName 42) "bar"
  let envWithNestedName : Env := Id.run do
    let mut env : Env := {}
    env := { env with names := RawEnv.addNameComponents env.names nestedName }
    env := env.registerName nestedName { addr := constAddr, constMeta := .empty }
    return env
  -- Test 6: Env with blob and comm
  let secretAddr := Address.blake3 (ByteArray.mk #[10, 11, 12])
  let payloadAddr := Address.blake3 (ByteArray.mk #[13, 14, 15])
  let commAddr := Address.blake3 (ByteArray.mk #[16, 17, 18])
  let envWithBlobAndComm : Env := {
    blobs := ({} : Std.HashMap _ _).insert blobAddr (ByteArray.mk #[4, 5, 6]),
    comms := ({} : Std.HashMap _ _).insert commAddr (Comm.mk secretAddr payloadAddr)
  }
  test "Empty env roundtrip" (envSerdeUnit emptyEnv) ++
  test "Env with blob roundtrip" (envSerdeUnit envWithBlob) ++
  test "Env with name roundtrip" (envSerdeUnit envWithName) ++
  test "Env with named (empty meta) roundtrip" (envSerdeUnit envWithNamed) ++
  test "Env with nested name roundtrip" (envSerdeUnit envWithNestedName) ++
  test "Env with blob+comm roundtrip" (envSerdeUnit envWithBlobAndComm)

/-! ## Cross-implementation serialization comparison tests -/

def univSerializationMatches (u : Univ) : Bool :=
  rsEqUnivSerialization u (serUniv u)

def exprSerializationMatches (e : Expr) : Bool :=
  rsEqExprSerialization e (serExpr e)

def constantSerializationMatches (c : Constant) : Bool :=
  rsEqConstantSerialization c (serConstant c)

def envSerializationMatches (raw : RawEnv) : Bool :=
  let env := raw.toEnv
  rsEqEnvSerialization raw (serEnv env)

/-- Unit tests for Lean==Rust serialization comparison -/
def envSerializationUnitTests : TestSeq :=
  -- Test 1: Empty env
  let emptyRaw : RawEnv := { consts := #[], named := #[], blobs := #[], comms := #[] }
  -- Test 2: Env with one blob
  let blobAddr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  let blobRaw : RawEnv := {
    consts := #[], named := #[],
    blobs := #[{ addr := blobAddr, bytes := ByteArray.mk #[4, 5, 6] }],
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
    blobs := #[{ addr := blobAddr, bytes := ByteArray.mk #[4, 5, 6] }],
    comms := #[{ addr := commAddr, comm := Comm.mk secretAddr payloadAddr }]
  }
  test "Empty env Lean==Rust" (envSerializationMatches emptyRaw) ++
  test "Blob env Lean==Rust" (envSerializationMatches blobRaw) ++
  test "Comm env Lean==Rust" (envSerializationMatches commRaw) ++
  test "Blob+Comm env Lean==Rust" (envSerializationMatches blobCommRaw)

/-! ## Test Suite (property-based) -/

def Tests.Ixon.suite : List TestSeq := [
  -- Env unit tests (for debugging serialization)
  envUnitTests,
  -- Env serialization comparison unit tests
  envSerializationUnitTests,
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
]
