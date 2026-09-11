import Ix.Compiler

/-!
Runtime test executable: everything that must *execute* FFI (blake3)
lives here, compiled and linked against the static lib — elaboration-
time `#guard`s can't run FFI (no dynlib in the interpreter). Run by the
flake's `tests` check; prints `tests-ok` on success.
-/

open Ix.Compiler.Ixon

/-- The universal BLAKE3 empty-input test vector:
`af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262`. -/
def expectedEmptyBlake3 : List Nat :=
  [0xaf, 0x13, 0x49, 0xb9, 0xf5, 0xf9, 0xa1, 0xa6,
   0xa0, 0x40, 0x4d, 0xea, 0x36, 0xdc, 0xc9, 0x49,
   0x9b, 0xcb, 0x25, 0xc9, 0xad, 0xc1, 0x12, 0xb7,
   0xcc, 0x9a, 0x93, 0xca, 0xe4, 0x1f, 0x32, 0x62]

/-! Exact ix-side capture at `Sharing.ixParityRevision`. The clean archived
source tree was `c09cfe3df1ee6ff92009672cc9077b4b7e2db63a`; the revision itself is
single-sourced in `Sharing.ixParityRevision`. These are external golden
artifacts, deliberately independent of the local serializer definitions. -/

namespace IxRebaseline

def sourceTree : String := "c09cfe3df1ee6ff92009672cc9077b4b7e2db63a"
def wireFormat : String := "ixon-v2"

def sampleAxiomBytes : ByteArray := ByteArray.mk #[210, 0, 1, 3, 0, 0, 1, 0]

def sampleAxiomAddress : List Nat :=
  [175, 190, 20, 2, 194, 88, 190, 182, 79, 114, 28, 108, 112, 136,
   43, 71, 254, 192, 235, 145, 134, 231, 227, 179, 11, 181, 74, 208,
   29, 62, 109, 135]

def goldenV2Bytes : ByteArray := ByteArray.mk #[
  208, 1, 128, 128, 148, 0, 0, 5, 8, 31, 2, 8, 32, 7, 8, 128,
  3, 132, 0, 0, 1, 8, 31, 2, 8, 32, 3, 8, 128, 120, 8, 40,
  8, 0, 0, 1, 2, 3, 4, 0, 1, 2, 19, 18, 17, 16, 176, 176,
  80, 9, 0, 1, 1, 114, 49, 0, 4, 65, 0, 16, 16, 1, 171, 171,
  171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171,
  171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171, 171,
  171, 171, 5, 0, 1, 0, 64, 192, 1, 193, 128, 194, 64, 0, 195, 225,
  0, 1]

def goldenV2Address : List Nat :=
  [238, 16, 204, 23, 76, 138, 70, 122, 24, 3, 187, 143, 106, 4,
   178, 63, 183, 235, 146, 24, 170, 118, 219, 68, 149, 59, 34, 171,
   73, 90, 205, 116]

structure SharingCapture where
  name : String
  input : ByteArray
  output : ByteArray

def sharingCaptures : List SharingCapture := [
  { name := "simple"
    input := ByteArray.mk #[1, 148, 7, 32, 0, 7, 32, 0, 7, 32, 0, 7, 32, 0, 1]
    output := ByteArray.mk #[1, 148, 7, 176, 7, 176, 7, 176, 7, 176, 1, 1, 32, 0] },
  { name := "content-hash"
    input := ByteArray.mk #[3, 145, 7, 32, 0, 0, 145, 7, 32, 0, 1,
      145, 7, 32, 0, 2]
    output := ByteArray.mk #[3, 145, 7, 176, 0, 145, 7, 176, 1,
      145, 7, 176, 2, 1, 32, 0] },
  { name := "recursor"
    input := ByteArray.mk #[4, 149, 7, 145, 7, 32, 0, 1, 7, 113, 17, 32,
      1, 7, 113, 18, 32, 2, 7, 113, 19, 32, 3, 7, 32, 0, 113, 17, 16,
      17, 18, 19]
    output := ByteArray.mk #[4, 149, 7, 145, 7, 32, 0, 1, 7, 113, 17,
      32, 1, 7, 113, 18, 32, 2, 7, 113, 19, 32, 3, 7, 32, 0, 113, 17,
      16, 17, 18, 19, 0] },
  { name := "forall-imp-sharing"
    input := ByteArray.mk #[2, 146, 7, 19, 7, 113, 18, 17, 113, 18, 16,
      146, 7, 19, 7, 113, 18, 16, 113, 18, 17]
    output := ByteArray.mk #[2, 146, 7, 19, 7, 176, 177, 146, 7, 19, 7,
      177, 176, 2, 113, 18, 17, 113, 18, 16] },
  { name := "forall-imp-real"
    input := ByteArray.mk #[2, 150, 7, 0, 7, 145, 7, 16, 1, 7, 145, 7,
      17, 1, 7, 146, 7, 18, 7, 113, 18, 16, 113, 18, 17, 7, 145, 7, 19,
      113, 19, 16, 7, 20, 113, 19, 16, 134, 3, 0, 3, 145, 7, 16, 1, 3,
      145, 7, 17, 1, 3, 146, 7, 18, 7, 113, 18, 16, 113, 18, 17, 3, 145,
      7, 19, 113, 19, 16, 3, 20, 114, 18, 16, 113, 17, 16]
    output := ByteArray.mk #[2, 150, 7, 0, 7, 183, 7, 179, 7, 182, 7,
      178, 7, 20, 177, 134, 3, 0, 3, 183, 3, 179, 3, 182, 3, 178, 3, 20,
      113, 180, 113, 17, 16, 8, 113, 18, 17, 113, 19, 16, 145, 7, 19,
      177, 145, 7, 17, 1, 113, 18, 16, 145, 7, 180, 176, 145, 7, 18,
      181, 145, 7, 16, 1] },
  { name := "flip"
    input := ByteArray.mk #[2, 150, 7, 0, 7, 1, 7, 2, 7, 146, 7, 18, 7,
      18, 18, 7, 18, 7, 20, 19, 134, 3, 0, 3, 1, 3, 2, 3, 146, 7, 18,
      7, 18, 18, 3, 18, 3, 20, 114, 18, 16, 17]
    output := ByteArray.mk #[2, 150, 7, 0, 7, 1, 7, 2, 7, 177, 7, 18, 7,
      20, 19, 134, 3, 0, 3, 1, 3, 2, 3, 177, 3, 18, 3, 20, 114, 18, 16,
      17, 2, 145, 7, 18, 18, 145, 7, 18, 176] }
]

def sharingCapture? (name : String) : Option SharingCapture :=
  sharingCaptures.find? fun capture => capture.name == name

end IxRebaseline

def hashNats (a : Address) : List Nat :=
  a.hash.data.toList.map (fun (b : UInt8) => b.toNat)

/-- Deterministic distinct addresses for the compiled environment-index smoke
test. The first three bytes are a little-endian natural; the remaining bytes
are zero. -/
def indexedAddress (n : Nat) : Address :=
  Address.ofFn fun index =>
    if index.val == 0 then n.toUInt8
    else if index.val == 1 then (n / 256).toUInt8
    else if index.val == 2 then (n / (256 * 256)).toUInt8
    else 0

namespace IxIRAddressFixtures

def ir0Decl : Ix.Compiler.IxIR0.Decl :=
  .recursor 2 false #[
    ⟨0, .lit (.nat 128)⟩,
    ⟨1, .app (.var 1) (.lit (.str "x"))⟩]

def ir1Decl : Ix.Compiler.IxIR1.Decl :=
  .fn ⟨2, .unique, false,
    .letOp
      (.alloc .unique
        ⟨Address.replicate 0x2a, 1, 2⟩
        #[.var 1, .lit (.nat 128)])
      (.case (.var 0) true #[
        .mk 2 1 (.ret (.lit (.str "x")))])⟩

def expectedIr0Bytes : ByteArray := ByteArray.mk #[
  99, 111, 109, 112, 105, 108, 97, 116, 114, 105, 120, 47, 105, 120,
  105, 114, 48, 47, 100, 101, 99, 108, 47, 49, 0, 2, 2, 0, 2, 0, 6,
  0, 128, 1, 1, 2, 0, 1, 6, 1, 1, 120]

def expectedIr0Hash : List Nat :=
  [87, 159, 186, 175, 104, 210, 117, 212, 187, 180, 242, 170, 245,
   247, 102, 207, 47, 63, 157, 187, 179, 63, 228, 86, 156, 71, 29,
   197, 105, 126, 184, 124]

def expectedIr1Bytes : ByteArray := ByteArray.mk #[
  99, 111, 109, 112, 105, 108, 97, 116, 114, 105, 120, 47, 105, 120,
  105, 114, 49, 47, 100, 101, 99, 108, 47, 50, 0, 0, 2, 0, 0, 1, 1, 0,
  42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42,
  42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42,
  1, 2, 2, 0, 1, 1, 0, 128, 1, 2, 0, 0, 1, 1, 2, 1, 0, 1, 1, 1,
  120]

def expectedIr1Hash : List Nat :=
  [168, 15, 142, 42, 202, 39, 215, 3, 84, 101, 26, 27, 100, 29, 247,
   9, 29, 165, 55, 137, 160, 249, 47, 228, 54, 229, 201, 244, 99, 5,
   108, 71]

private def rejected {alpha : Type} : Except String alpha → Bool
  | .error _ => true
  | .ok _ => false

def ir0DecodeOk : Bool :=
  match Ix.Compiler.IxIR0.Decl.decodePreimage expectedIr0Bytes with
  | .ok declaration => declaration.preimage == expectedIr0Bytes
  | .error _ => false

def ir1DecodeOk : Bool :=
  match Ix.Compiler.IxIR1.Decl.decodePreimage expectedIr1Bytes with
  | .ok declaration => declaration.preimage == expectedIr1Bytes
  | .error _ => false

/-- Malformed framing, tags, LEB128, UTF-8, and truncation must all fail
closed. The nonminimal LEB128 fixture parses as zero at the raw-reader layer
and is rejected by the canonical re-encoding check. -/
def ir0Malformed : List (String × ByteArray) := [
  ("trailing byte", expectedIr0Bytes.push 0),
  ("wrong domain", expectedIr0Bytes.set! 0 0),
  ("invalid declaration tag", expectedIr0Bytes.set! 25 0xff),
  ("nonminimal LEB128",
    Ix.Compiler.IxIR0.Decl.addressDomain ++ ByteArray.mk #[3, 128, 0]),
  ("invalid nested UTF-8",
    Ix.Compiler.IxIR0.Decl.addressDomain ++
      ByteArray.mk #[0, 0, 6, 1, 1, 0xff]),
  ("truncated declaration",
    expectedIr0Bytes.extract 0 (expectedIr0Bytes.size - 1))]

def ir1Malformed : List (String × ByteArray) := [
  ("trailing byte", expectedIr1Bytes.push 0),
  ("wrong domain", expectedIr1Bytes.set! 0 0),
  ("invalid declaration tag", expectedIr1Bytes.set! 25 0xff),
  ("nonminimal LEB128",
    Ix.Compiler.IxIR1.Decl.addressDomain ++ ByteArray.mk #[1, 128, 0]),
  ("invalid nested UTF-8",
    Ix.Compiler.IxIR1.Decl.addressDomain ++
      ByteArray.mk #[0, 0, 0, 0, 0, 1, 1, 1, 0xff]),
  ("truncated declaration",
    expectedIr1Bytes.extract 0 (expectedIr1Bytes.size - 1))]

def ir0Rejects (bytes : ByteArray) : Bool :=
  rejected (Ix.Compiler.IxIR0.Decl.decodePreimage bytes)

def ir1Rejects (bytes : ByteArray) : Bool :=
  rejected (Ix.Compiler.IxIR1.Decl.decodePreimage bytes)

end IxIRAddressFixtures

namespace IxIRReaddressFixtures

open Ix.Compiler.IxIR1

def oldLeaf : Address := Address.replicate 0xfa
def oldParent : Address := Address.replicate 0xfb
def sourceKey : Address := Address.replicate 0x11

def leaf : Decl :=
  .fn ⟨0, .shared, true, .ret (.lit (.nat 7))⟩

def parent : Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call oldLeaf #[]) (.ret (.var 0))⟩

def sourceDeclaration : Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call oldParent #[])
      (.letOp (.papp oldLeaf #[]) (.ret (.var 0)))⟩

def mainCode : Code :=
  .letOp (.call oldParent #[]) (.ret (.var 0))

def chain : Except String Readdress.Result :=
  Readdress.run [(sourceKey, sourceDeclaration)]
    [(oldParent, parent), (oldLeaf, leaf)] mainCode

def chainRuntimeAgrees (result : Readdress.Result) : Bool :=
  let ctx : Ctx :=
    { decls := Env.ofList result.declarations,
      oracle := Ix.Compiler.IxIR1.Lower.tgtOracle }
  match runMain ctx result.main with
  | .ok (_, .lit (.nat 7)) => true
  | _ => false

def contentHexes (result : Readdress.Result) : List String :=
  result.addressMap.map fun entry => Address.toHex entry.2

def expectedChainContent : List String :=
  ["bffd28385492968a674f7090824348301087119dfa377a6b682bff177ede78d1",
   "571f9c86b9289add35eda891c1f019c0da121f6e7738a1767193da7948261ff9"]

def chainOk (result : Readdress.Result) : Bool :=
  let mapAddress := Readdress.Renaming.apply result.addressMap
  let expectedParent := Readdress.Decl.mapAddresses mapAddress parent
  match result.generated with
  | [(leafAddress, emittedLeaf), (parentAddress, emittedParent)] =>
      result.addressMap.lookup oldLeaf == some leafAddress &&
      result.addressMap.lookup oldParent == some parentAddress &&
      leafAddress == leaf.address &&
      parentAddress == expectedParent.address &&
      emittedLeaf.preimage == leaf.preimage &&
      emittedParent.preimage == expectedParent.preimage &&
      result.source.flatMap (fun entry =>
        Readdress.Decl.references entry.2) == [parentAddress, leafAddress] &&
      Readdress.Code.references result.main == [parentAddress] &&
      contentHexes result == expectedChainContent &&
      result.noTransientKeys && result.noTransientReferences &&
      result.generatedAreAddressed &&
      result.semanticAudit
        ([(sourceKey, sourceDeclaration)] ++
          [(oldParent, parent), (oldLeaf, leaf)]) mainCode &&
      chainRuntimeAgrees result
  | _ => false

def oldDuplicateA : Address := Address.replicate 0xfc
def oldDuplicateB : Address := Address.replicate 0xfd

def deduplicate : Except String Readdress.Result :=
  Readdress.run [] [(oldDuplicateA, leaf), (oldDuplicateB, leaf)]
    (.letOp (.call oldDuplicateA #[])
      (.letOp (.call oldDuplicateB #[]) (.ret (.var 0))))

def expectedDeduplicatedContent : List String :=
  ["bffd28385492968a674f7090824348301087119dfa377a6b682bff177ede78d1",
   "bffd28385492968a674f7090824348301087119dfa377a6b682bff177ede78d1"]

def deduplicateOk (result : Readdress.Result) : Bool :=
  match result.generated with
  | [(address, declaration)] =>
      result.addressMap.lookup oldDuplicateA == some address &&
      result.addressMap.lookup oldDuplicateB == some address &&
      declaration.preimage == leaf.preimage &&
      Readdress.Code.references result.main == [address, address] &&
      contentHexes result == expectedDeduplicatedContent &&
      result.noTransientKeys && result.noTransientReferences &&
      result.generatedAreAddressed &&
      result.semanticAudit
        [(oldDuplicateA, leaf), (oldDuplicateB, leaf)]
        (.letOp (.call oldDuplicateA #[])
          (.letOp (.call oldDuplicateB #[]) (.ret (.var 0))))
  | _ => false

def cycleA : Address := Address.replicate 0xf1
def cycleB : Address := Address.replicate 0xf2

def cycleDeclA : Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call cycleB #[]) (.ret (.var 0))⟩

def cycleDeclB : Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call cycleA #[]) (.ret (.var 0))⟩

def cycleRejected : Bool :=
  match Readdress.run [] [(cycleA, cycleDeclA), (cycleB, cycleDeclB)]
      (.ret .erased) with
  | .error message =>
      message == "generated declaration address dependency cycle"
  | .ok _ => false

def overlapRejected : Bool :=
  match Readdress.run [(oldLeaf, .extern 0)] [(oldLeaf, leaf)]
      (.ret .erased) with
  | .error message =>
      message == s!"generated temporary address overlaps source declaration {Address.toHex oldLeaf}"
  | .ok _ => false

def sourceKeyCollisionRejected : Bool :=
  let address := leaf.address
  match Readdress.run [(address, .extern 0)] [(oldLeaf, leaf)]
      (.ret .erased) with
  | .error message =>
      message == s!"generated content address collides with source declaration key {Address.toHex address}"
  | .ok _ => false

def contentTemporaryOverlapRejected : Bool :=
  let address := leaf.address
  match Readdress.run [] [(address, leaf)] (.ret .erased) with
  | .error message =>
      message == s!"generated content address overlaps temporary namespace {Address.toHex address}"
  | .ok _ => false

def nestedExpression : Ix.Compiler.IxIR0.Expr :=
  .app
    (.lam .many
      (.app (.lam .many (.var 1))
        (Ix.Compiler.IxIR0.Examples.natE 2)))
    (Ix.Compiler.IxIR0.Examples.natE 3)

def nestedLowering : Except String Readdress.Result :=
  Ix.Compiler.IxIR1.Lower.lowerAllIndexedAddressed
    Ix.Compiler.IxIR0.Examples.declList nestedExpression

def loweringAudits (source : List (Address × Ix.Compiler.IxIR0.Decl))
    (main : Ix.Compiler.IxIR0.Expr) (result : Readdress.Result) : Bool :=
  match (Ix.Compiler.IxIR1.Lower.lowerAllIndexedAction source main
      .shared 10000).run {} with
  | .ok (raw, rawMain) _ =>
      result.semanticAudit raw rawMain &&
        result.protects (source.map Prod.fst)
  | .error _ _ => false

def expectedNestedContent : List String :=
  ["acdd7ed6dd2ff0f364ea7697b85c32098d843b7ff3daa1f62b4ec2e0dc6d9fc5",
   "04374cf03ca115a555c4cc2b3fccac7009b405ae83d6df238e1f05b533c72f0c",
   "5a51d499b2f13429d9a04cf59d8f20a2e5b5def8d27a454bc821e8d0d7508393",
   "df504cb4ec73814775bb8d0cae6f3f360d01972a66df694b9ca0c0d1ee7e2fa6",
   "ca360f51322575138a9b9025f245bd18117a2c48c9286ce763ceeccd635e8976"]

def nestedLoweringOk (result : Readdress.Result) : Bool :=
  let ctx : Ctx :=
    { decls := Env.ofList result.declarations,
      oracle := Ix.Compiler.IxIR1.Lower.tgtOracle }
  -- The corpus declarations themselves contribute three wrappers/lifts;
  -- the nested expression contributes its inner and outer lifted functions.
  result.addressMap.length == 5 && result.generated.length == 5 &&
    contentHexes result == expectedNestedContent &&
    result.noTransientKeys && result.noTransientReferences &&
    result.generatedAreAddressed &&
    loweringAudits Ix.Compiler.IxIR0.Examples.declList nestedExpression
      result &&
    match runMain ctx result.main with
    | .ok (store, value) =>
        (Ix.Compiler.IxIR1.Lower.treeOfR store 1000 value).bind
          Ix.Compiler.IxIR1.Lower.natT? == some 3
    | .error _ => false

def wrapperExpression : Ix.Compiler.IxIR0.Expr :=
  .app (.ref Ix.Compiler.IxIR0.Examples.pairMk)
    (Ix.Compiler.IxIR0.Examples.natE 1)

def wrapperLowering : Except String Readdress.Result :=
  Ix.Compiler.IxIR1.Lower.lowerAllIndexedAddressed
    Ix.Compiler.IxIR0.Examples.declList wrapperExpression

def expectedWrapperContent : List String :=
  ["2ff8127bf306efa22913c6c3c44ba3f560e1aedf94a94b85939f0f772aa97138",
   "5a51d499b2f13429d9a04cf59d8f20a2e5b5def8d27a454bc821e8d0d7508393",
   "df504cb4ec73814775bb8d0cae6f3f360d01972a66df694b9ca0c0d1ee7e2fa6",
   "ca360f51322575138a9b9025f245bd18117a2c48c9286ce763ceeccd635e8976"]

def wrapperLoweringOk (result : Readdress.Result) : Bool :=
  -- Three generated declarations come from the corpus; this partial
  -- constructor application contributes the fourth wrapper.
  result.addressMap.length == 4 && result.generated.length == 4 &&
    contentHexes result == expectedWrapperContent &&
    result.noTransientKeys && result.noTransientReferences &&
    result.generatedAreAddressed &&
    loweringAudits Ix.Compiler.IxIR0.Examples.declList wrapperExpression
      result

/-- A constructor address is a source identity even though constructors emit
no raw IxIR₁ declaration.  Deliberately collide it with the first transient
lambda key and ensure the production boundary rejects the would-be rewrite. -/
def protectedCtorKey : Address :=
  Ix.Compiler.IxIR1.Lower.synthAddr 0

def protectedSourceIdentityRejected : Bool :=
  let source : List (Address × Ix.Compiler.IxIR0.Decl) :=
    [(protectedCtorKey, .ctor 0 0)]
  let expression : Ix.Compiler.IxIR0.Expr :=
    .app (.lam .many (.var 0)) (.ref protectedCtorKey)
  match Ix.Compiler.IxIR1.Lower.lowerAllIndexedAddressed source expression with
  | .error message =>
      message == "generated address map rewrites a protected source identity"
  | .ok _ => false

end IxIRReaddressFixtures

namespace IxIR1ReaddressAllFixtures

open Ix.Compiler.IxIR1
open Ix.Compiler.IxIR1.ReaddressAll

def oldRoot : Address := Address.replicate 0xd0
def oldA : Address := Address.replicate 0xd1
def oldB : Address := Address.replicate 0xd2
def oldLeaf : Address := Address.replicate 0xd3
def external : Address := Address.replicate 0xd4

def leaf : Decl := .extern 1

def declarationA : Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call oldB #[])
      (.letOp (.call oldLeaf #[]) (.ret .erased))⟩

def declarationB : Decl :=
  .fn ⟨0, .unique, false,
    .letOp (.papp oldA #[])
      (.letOp (.extern external #[]) (.ret .erased))⟩

def root : Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call oldA #[]) (.ret (.var 0))⟩

/-- Source order deliberately opposes dependency order. -/
def raw : List (Address × Decl) :=
  [(oldRoot, root), (oldA, declarationA), (oldB, declarationB),
   (oldLeaf, leaf)]

def mainCode : Code :=
  .letOp (.call oldRoot #[]) (.ret (.var 0))

def built : Except String ReaddressAll.Result :=
  ReaddressAll.run [external] raw mainCode

def expectedTargetHexes : List String :=
  ["d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3",
   "9f879169042641be6111442a373d7799aa1aa34b44ea6aca2b303013815b2287",
   "eded0797fe0dc6c8f382111845bfefc7d83eef1bfe3813d65d5b268774deed05",
   "c86d1f0cbfa5eb1ad35d6990f7582ef4c872663779143f732a41c53cbd46075c"]

def expectedBlockHex : String :=
  "fac32ac632054612f912abec284c37b0a331f84e4ebe72ec09e16f4966f1cddd"

def componentsOk : Bool :=
  (ReaddressAll.discoverComponents raw).map Component.keys ==
    [[oldRoot], [oldA, oldB], [oldLeaf]]

/-- The public SCC boundary must remain iterative on a dependency chain large
enough to expose accidental native-stack recursion. -/
def longChainLength : Nat := 8192

def longChainRaw : List (Address × Decl) :=
  (List.range longChainLength).map fun index =>
    let address := Ix.Compiler.IxIR1.Lower.synthAddr index
    let body :=
      if index + 1 < longChainLength then
        .letOp (.call (Ix.Compiler.IxIR1.Lower.synthAddr (index + 1)) #[])
          (.ret .erased)
      else
        .ret .erased
    (address, .fn ⟨0, .shared, true, body⟩)

def longChainComponentsOk : Bool :=
  let components := ReaddressAll.discoverComponents longChainRaw
  components.length == longChainLength &&
    components.all fun component => component.members.length == 1

def builtOk (result : ReaddressAll.Result) : Bool :=
  let targets := result.addressMap.map fun entry => Address.toHex entry.2
  match result.artifacts, result.blocks, result.stable, result.ordinary,
      result.addressMap.lookup oldLeaf, result.addressMap.lookup oldA,
      result.addressMap.lookup oldB, result.addressMap.lookup oldRoot with
  | [.stable leafAddress emittedLeaf, .mutual block,
        .ordinary rootAddress emittedRoot], [onlyBlock],
      [(stableLeaf, _)], [(ordinaryRoot, _)],
      some mappedLeaf, some mappedA, some mappedB, some mappedRoot =>
      targets == expectedTargetHexes &&
        Address.toHex block.blockAddress == expectedBlockHex &&
        onlyBlock.blockAddress == block.blockAddress &&
        leafAddress == mappedLeaf && rootAddress == mappedRoot &&
        stableLeaf == leafAddress && ordinaryRoot == rootAddress &&
        emittedLeaf.preimage == leaf.preimage &&
        emittedRoot.address == rootAddress &&
        block.derivedAddresses == [mappedA, mappedB] &&
        (result.declarations.map fun entry =>
          (Readdress.Decl.references entry.2).map Address.toHex) ==
            [[], [Address.toHex mappedB, Address.toHex mappedLeaf],
              [Address.toHex mappedA, Address.toHex external],
              [Address.toHex mappedA]] &&
        (Readdress.Code.references result.main).map Address.toHex ==
          [Address.toHex mappedRoot] &&
        result.addressMap.length == raw.length &&
        result.declarations.length == raw.length &&
        result.contentAddressed && result.noTransientKeys &&
        result.noTransientReferences && result.semanticAudit raw mainCode &&
        result.rebuildSemanticAudit raw mainCode
  | _, _, _, _, _, _, _, _ => false

def newRoot : Address := Address.replicate 0xe0
def newA : Address := Address.replicate 0xe1
def newB : Address := Address.replicate 0xe2
def renamedRaw : List (Address × Decl) :=
  [(newRoot,
      .fn ⟨0, .shared, true,
        .letOp (.call newA #[]) (.ret (.var 0))⟩),
   (newA,
    .fn ⟨0, .shared, true,
      .letOp (.call newB #[])
          (.letOp (.call oldLeaf #[]) (.ret .erased))⟩),
   (newB,
      .fn ⟨0, .unique, false,
        .letOp (.papp newA #[])
          (.letOp (.extern external #[]) (.ret .erased))⟩),
   (oldLeaf, leaf)]

def renamedMain : Code :=
  .letOp (.call newRoot #[]) (.ret (.var 0))

def transientSpellingIndependent : Bool :=
  match built, ReaddressAll.run [external] renamedRaw renamedMain with
  | .ok original, .ok renamed =>
      original.finalAddresses == renamed.finalAddresses &&
        original.blockAddresses == renamed.blockAddresses &&
        original.declarations.map (fun entry => entry.2.preimage) ==
          renamed.declarations.map (fun entry => entry.2.preimage)
  | _, _ => false

def memberOrderSensitive : Bool :=
  let reordered : List (Address × Decl) :=
    [(oldRoot, root), (oldB, declarationB), (oldA, declarationA),
     (oldLeaf, leaf)]
  match built, ReaddressAll.run [external] reordered mainCode with
  | .ok original, .ok changed =>
      original.blockAddresses != changed.blockAddresses &&
        original.finalAddresses != changed.finalAddresses
  | _, _ => false

def duplicateA : Address := Address.replicate 0xf0
def duplicateB : Address := Address.replicate 0xf1

def plainLeaf : Decl :=
  .fn ⟨0, .shared, true, .ret (.lit (.nat 7))⟩

def ordinaryDeduplicates : Bool :=
  match ReaddressAll.run []
      [(duplicateA, plainLeaf), (duplicateB, plainLeaf)]
      (.ret .erased) with
  | .ok result =>
      match result.addressMap.lookup duplicateA,
          result.addressMap.lookup duplicateB with
      | some addressA, some addressB =>
          addressA == addressB && result.artifacts.length == 1 &&
            result.declarations.length == 1 &&
            result.semanticAudit
              [(duplicateA, plainLeaf), (duplicateB, plainLeaf)]
              (.ret .erased)
      | _, _ => false
  | .error _ => false

def selfKey : Address := Address.replicate 0xf2

def explicitSelfUsesBlock : Bool :=
  let declaration : Decl :=
    .fn ⟨0, .shared, true,
      .letOp (.call selfKey #[]) (.ret .erased)⟩
  match ReaddressAll.run [] [(selfKey, declaration)] (.ret .erased) with
  | .ok result => result.blocks.length == 1 && result.ordinary.isEmpty
  | .error _ => false

def callSelfUsesOrdinaryHash : Bool :=
  let declaration : Decl :=
    .fn ⟨0, .shared, true,
      .letOp (.callSelf #[]) (.ret .erased)⟩
  match ReaddressAll.run [] [(selfKey, declaration)] (.ret .erased) with
  | .ok result => result.blocks.isEmpty && result.ordinary.length == 1
  | .error _ => false

def emptyOk : Bool :=
  match ReaddressAll.run [] [] (.ret .erased) with
  | .ok result =>
      result.artifacts.isEmpty && result.addressMap.isEmpty &&
        result.semanticAudit [] (.ret .erased)
  | .error _ => false

def rejectsDuplicateProducer : Bool :=
  match ReaddressAll.run [] [(oldLeaf, leaf), (oldLeaf, .extern 2)]
      (.ret .erased) with
  | .error message =>
      message == s!"duplicate IxIR1 declaration producer key {Address.toHex oldLeaf}"
  | .ok _ => false

def rejectsReservedProducer : Bool :=
  match ReaddressAll.run [oldLeaf] [(oldLeaf, leaf)] (.ret .erased) with
  | .error message =>
      message == s!"IxIR1 declaration producer key overlaps reserved identity {Address.toHex oldLeaf}"
  | .ok _ => false

def rejectsProtectedContent : Bool :=
  let content := plainLeaf.address
  match ReaddressAll.run [content] [(oldLeaf, plainLeaf)] (.ret .erased) with
  | .error message =>
      message == s!"IxIR1 content address collides with protected identity {Address.toHex content}"
  | .ok _ => false

def rejectsContentInTransientNamespace : Bool :=
  let content := plainLeaf.address
  match ReaddressAll.run [] [(content, plainLeaf)] (.ret .erased) with
  | .error message =>
      message == s!"IxIR1 content address overlaps transient namespace {Address.toHex content}"
  | .ok _ => false

def fullyNested : Except String ReaddressAll.Result :=
  Ix.Compiler.IxIR1.Lower.lowerAllIndexedFullyAddressed
    Ix.Compiler.IxIR0.Examples.declList
    IxIRReaddressFixtures.nestedExpression

def expectedFullyNestedTargets : List String :=
  ["4982c3a7b9dedd44f9319e71e6f1c9f3a283bdf9ea756f7e0222f46384992fdf",
   "b09b67046ea7c5f432aaf8d9a0ad364f275859425285e2f0d13b1ff2a4ce745b",
   "b23ea729574d305094e1a192cd98fb9f4c6ac6c3b426e64d17149cb2330c2a9c",
   "93b0f7191ee298a04c041218a2c31b2a6d47e716c9f06adabf6b4ffa52aa59b5",
   "4040404040404040404040404040404040404040404040404040404040404040",
   "acdd7ed6dd2ff0f364ea7697b85c32098d843b7ff3daa1f62b4ec2e0dc6d9fc5",
   "04374cf03ca115a555c4cc2b3fccac7009b405ae83d6df238e1f05b533c72f0c",
   "5a51d499b2f13429d9a04cf59d8f20a2e5b5def8d27a454bc821e8d0d7508393",
   "33c1a0b2b85fab57e9310cc224469ae678bfea3771bc40cf29da7286d590f008",
   "df504cb4ec73814775bb8d0cae6f3f360d01972a66df694b9ca0c0d1ee7e2fa6",
   "5cddf5abadbb430a64d074bee0c0580ac0001429265aacc5d844139d0714e5ed",
   "ca360f51322575138a9b9025f245bd18117a2c48c9286ce763ceeccd635e8976",
   "9193adfb5265d9d0db333d02918ac51134c8dff437538e09b82f30414079ddd9"]

def fullyLoweredAudit
    (source : List (Address × Ix.Compiler.IxIR0.Decl))
    (main : Ix.Compiler.IxIR0.Expr)
    (result : ReaddressAll.Result) : Bool :=
  match (Ix.Compiler.IxIR1.Lower.lowerAllIndexedAction source main
      .shared 10000).run {} with
  | .error _ _ => false
  | .ok (rawTarget, rawMain) _ =>
      let functionProducers := rawTarget.filterMap fun
        | (address, .fn _) => some address
        | _ => none
      let externProducers := rawTarget.filterMap fun
        | (address, .extern _) => some address
        | _ => none
      result.semanticAudit rawTarget rawMain &&
        !result.finalAddresses.any functionProducers.contains &&
        result.stable.length == externProducers.length &&
        (result.stable.all fun entry => externProducers.contains entry.1) &&
        (Ix.Compiler.IxIR1.Lower.constructorIdentities source).all fun address =>
          Readdress.Renaming.apply result.addressMap address == address

def fullyNestedOk (result : ReaddressAll.Result) : Bool :=
  let ctx := result.addressedCtx Ix.Compiler.IxIR1.Lower.tgtOracle
  result.addressMap.map (fun entry => Address.toHex entry.2) ==
      expectedFullyNestedTargets && result.blocks.isEmpty &&
    result.noTransientKeys && result.noTransientReferences &&
    result.contentAddressed &&
    fullyLoweredAudit Ix.Compiler.IxIR0.Examples.declList
      IxIRReaddressFixtures.nestedExpression result &&
    match runMain ctx result.main with
    | .ok (store, value) =>
        (Ix.Compiler.IxIR1.Lower.treeOfR store 1000 value).bind
          Ix.Compiler.IxIR1.Lower.natT? == some 3
    | .error _ => false

def cyclicSourceKey : Address := Address.replicate 0xb7

/-- Lowering this definition emits a closure whose body refers back to the
source function, while the source function body refers to that closure. -/
def cyclicSourceDeclaration : Ix.Compiler.IxIR0.Decl :=
  .defn .shared
    (.lam .many
      (.app (.lam .many (.ref cyclicSourceKey)) (.var 0)))

def fullyCyclicLowering : Except String ReaddressAll.Result :=
  Ix.Compiler.IxIR1.Lower.lowerAllIndexedFullyAddressed
    [(cyclicSourceKey, cyclicSourceDeclaration)]
    (.ref cyclicSourceKey)

def expectedFullyCyclicTargets : List String :=
  ["82bf8557e67293e4a0e19784fb206c0bc0d7a7e38f2ad34d4df6b3cc4da86a9a",
   "d9699af86a4c4726934dae674b3e420c4376bbfaf30a1d08eff073fa37681c7b"]

def expectedFullyCyclicBlock : String :=
  "28cb53ac21a976d278cb1294be05a273214bbab09768afb32b221044896106c5"

def fullyCyclicLoweringOk (result : ReaddressAll.Result) : Bool :=
  fullyLoweredAudit [(cyclicSourceKey, cyclicSourceDeclaration)]
      (.ref cyclicSourceKey) result &&
    result.addressMap.map (fun entry => Address.toHex entry.2) ==
      expectedFullyCyclicTargets &&
    result.blocks.length == 1 &&
    match result.blocks with
    | [block] =>
        Address.toHex block.blockAddress == expectedFullyCyclicBlock &&
          block.derivedAddresses.map Address.toHex ==
            expectedFullyCyclicTargets && block.members.length == 2
    | _ => false

def fullyProtectedSourceIdentityRejected : Bool :=
  let source : List (Address × Ix.Compiler.IxIR0.Decl) :=
    [(Ix.Compiler.IxIR1.Lower.synthAddr 0, .ctor 0 0)]
  let expression : Ix.Compiler.IxIR0.Expr :=
    .app (.lam .many (.var 0))
      (.ref (Ix.Compiler.IxIR1.Lower.synthAddr 0))
  match Ix.Compiler.IxIR1.Lower.lowerAllIndexedFullyAddressed
      source expression with
  | .error message =>
      message == s!"IxIR1 declaration producer key overlaps reserved identity {Address.toHex (Ix.Compiler.IxIR1.Lower.synthAddr 0)}"
  | .ok _ => false

end IxIR1ReaddressAllFixtures

namespace IxIRMutualBlockFixtures

open Ix.Compiler.IxIR0
open Ix.Compiler.IxIR0.MutualBlock

def oldA : Address := Address.replicate 0xf1
def oldB : Address := Address.replicate 0xf2
def external : Address := Address.replicate 0x42

/-- A genuine local cycle: the definition points to the recursor and one
recursor rule points back to the definition.  The extra external edge checks
that only block-local names are abstracted. -/
def raw : List (Address × Ix.Compiler.IxIR0.Decl) :=
  [(oldA,
      .defn .shared
        (.lam .many (.app (.ref oldB) (.ref external)))),
   (oldB,
      .recursor 0 false #[⟨0, .app (.ref oldA) (.var 0)⟩])]

def symbolic : List MutualBlock.Decl := abstractMembers raw

def expectedBlockBytes : ByteArray := ByteArray.mk #[
  99, 111, 109, 112, 105, 108, 97, 116, 114, 105, 120, 47, 105, 120,
  105, 114, 48, 47, 109, 117, 116, 117, 97, 108, 45, 98, 108, 111,
  99, 107, 47, 49, 0, 2, 0, 1, 3, 3, 2, 1, 0, 1, 1, 1,
  66, 66, 66, 66, 66, 66, 66, 66,
  66, 66, 66, 66, 66, 66, 66, 66,
  66, 66, 66, 66, 66, 66, 66, 66,
  66, 66, 66, 66, 66, 66, 66, 66, 2,
  0, 0, 1, 0, 2, 1, 0, 0, 0, 0]

def expectedBlockHex : String :=
  "5ea95e2ae3fda21872339a280eb713a33a8f4452a3746c7c5dd05e29e34e6fdb"

def expectedMemberHexes : List String :=
  ["d0cf65a4d9b4ee7bbe57e56db69b52a7e5b2468482655b03411334a496e3201d",
   "3f2c1b81c862e5a85d73391021af6a1910bf27ae6ba6f2a424bfd035be7204dd"]

def built : Except String MutualBlock.Result := MutualBlock.run [] raw

def decodeOk : Bool :=
  match Block.decodePreimage expectedBlockBytes with
  | .error _ => false
  | .ok decoded =>
      decoded == symbolic &&
        match Block.decodeMaterialized [] expectedBlockBytes, built with
        | .ok artifact, .ok result =>
            artifact.blockAddress == result.blockAddress &&
              artifact.blockMembers == result.blockMembers &&
              artifact.members == result.members && artifact.audit
        | _, _ => false

def malformed : List (String × ByteArray) := [
  ("trailing byte", expectedBlockBytes.push 0),
  ("wrong domain", expectedBlockBytes.set! 0 0),
  ("invalid local-reference tag", expectedBlockBytes.set! 40 0xff),
  ("nonminimal member count",
    Block.addressDomain ++ ByteArray.mk #[130, 0] ++
      expectedBlockBytes.extract 34 expectedBlockBytes.size),
  ("out-of-range local reference", expectedBlockBytes.set! 41 2),
  ("truncated block",
    expectedBlockBytes.extract 0 (expectedBlockBytes.size - 1)),
  ("empty block", Block.addressDomain ++ ByteArray.mk #[0])]

def rejectsArtifactBytes (bytes : ByteArray) : Bool :=
  match Block.decodeArtifact bytes with
  | .error _ => true
  | .ok _ => false

def concreteShape (result : MutualBlock.Result) : Bool :=
  match result.members with
  | [(addressA,
        .defn .shared
          (.lam .many (.app (.ref targetB) (.ref foundExternal)))),
     (addressB,
        .recursor 0 false rules)] =>
      rules == #[⟨0, .app (.ref addressA) (.var 0)⟩] &&
      targetB == addressB && foundExternal == external &&
      result.addressMap.lookup oldA == some addressA &&
      result.addressMap.lookup oldB == some addressB
  | _ => false

def expectedRenamedRaw (result : MutualBlock.Result) :
    List (Address × Ix.Compiler.IxIR0.Decl) :=
  let rename := MutualBlock.Renaming.apply result.addressMap
  raw.map fun entry =>
    (rename entry.1, MutualBlock.Concrete.Decl.mapAddresses rename entry.2)

def builtOk (result : MutualBlock.Result) : Bool :=
  Block.preimage result.blockMembers == expectedBlockBytes &&
    Address.toHex result.blockAddress == expectedBlockHex &&
    result.derivedAddresses.map Address.toHex == expectedMemberHexes &&
    result.blockMembers == symbolic && result.members == expectedRenamedRaw result &&
    result.memberKeysDerived && result.blockStable &&
    result.noTransientKeys && result.noTransientReferences &&
    result.semanticAudit raw && concreteShape result

/-- Changing only the transient spellings cannot change the symbolic artifact
or its block address. -/
def renamedRaw : List (Address × Ix.Compiler.IxIR0.Decl) :=
  let newA := Address.replicate 0xa1
  let newB := Address.replicate 0xa2
  [(newA,
      .defn .shared
        (.lam .many (.app (.ref newB) (.ref external)))),
   (newB,
      .recursor 0 false #[⟨0, .app (.ref newA) (.var 0)⟩])]

def transientSpellingIndependent : Bool :=
  abstractMembers renamedRaw == symbolic &&
    Block.preimage (abstractMembers renamedRaw) == expectedBlockBytes

/-- Member order is semantic because local indices are order-relative. -/
def orderSensitive : Bool :=
  let reversed := raw.reverse
  Block.preimage (abstractMembers reversed) != expectedBlockBytes &&
    Block.address (abstractMembers reversed) != Block.address symbolic

def rejectsEmpty : Bool :=
  match MutualBlock.run [] [] with
  | .error message => message == "mutual block must contain at least one member"
  | .ok _ => false

def rejectsDuplicateTemporary : Bool :=
  match MutualBlock.run [] [(oldA, .extern 0), (oldA, .extern 1)] with
  | .error message =>
      message == s!"duplicate mutual-block temporary address {Address.toHex oldA}"
  | .ok _ => false

/-- This is the exact alias that makes the old XOR scheme unsafe.  The new
boundary detects it before hashing whenever the surrounding block identity is
protected. -/
def legacyWrapIndex : Nat := 2 ^ 64 - 1

def rejectsLegacyWrapAlias : Bool :=
  let block := Address.replicate 0x7a
  let legacy := Address.memberAddr block legacyWrapIndex
  legacy == block &&
    match MutualBlock.run [block] [(legacy, .extern 0)] with
    | .error message =>
        message == s!"mutual-block temporary address overlaps reserved identity {Address.toHex block}"
    | .ok _ => false

def rejectsDerivedReservedCollision : Bool :=
  match built with
  | .error _ => false
  | .ok result =>
      match MutualBlock.run [result.derivedAddresses.head!] raw with
      | .error message =>
          message == s!"mutual-block member key collides with reserved identity {Address.toHex result.derivedAddresses.head!}"
      | .ok _ => false

end IxIRMutualBlockFixtures

namespace IxIR1MutualBlockFixtures

open Ix.Compiler.IxIR1
open Ix.Compiler.IxIR1.MutualBlock

def oldA : Address := Address.replicate 0xc1
def oldB : Address := Address.replicate 0xc2
def external : Address := Address.replicate 0xc3

/-- A source/generated-style cycle with a stable external oracle edge nested
beneath a case alternative. -/
def declarationA : Ix.Compiler.IxIR1.Decl :=
  .fn ⟨1, .shared, true,
    .letOp (.call oldB #[.var 0]) (.ret (.var 0))⟩

def declarationB : Ix.Compiler.IxIR1.Decl :=
  .fn ⟨0, .unique, false,
    .case .erased false #[.mk 0 0
      (.letOp (.papp oldA #[])
        (.letOp (.extern external #[]) (.ret .erased)))]⟩

def raw : List (Address × Ix.Compiler.IxIR1.Decl) :=
  [(oldA, declarationA), (oldB, declarationB)]

def symbolic : List MutualBlock.Decl := abstractMembers raw

def expectedBlockBytes : ByteArray := ByteArray.mk #[
  99, 111, 109, 112, 105, 108, 97, 116, 114, 105, 120, 47, 105, 120,
  105, 114, 49, 47, 109, 117, 116, 117, 97, 108, 45, 98, 108, 111,
  99, 107, 47, 50, 0, 2,
  0, 1, 1, 1, 1, 8, 0, 1, 1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 2, 2, 0, 1, 0, 0, 1, 10, 0, 0, 0, 1, 12, 1,
  195, 195, 195, 195, 195, 195, 195, 195,
  195, 195, 195, 195, 195, 195, 195, 195,
  195, 195, 195, 195, 195, 195, 195, 195,
  195, 195, 195, 195, 195, 195, 195, 195,
  0, 0, 2]

def expectedBlockHex : String :=
  "200b6f0ff4d00b038d54ac7f9f63801347c14e71f9ffa6cf655c3542e8131e66"

def expectedMemberHexes : List String :=
  ["5f5829956d0ffdafba051bc63ca0f922561e10bbd9782012fcf2d48bf4e2e09f",
   "c8a8aef455e2b56a4d80b41bf9cbb171c428bce2a3d5e16a02d81283be70013e"]

def built : Except String MutualBlock.Result :=
  MutualBlock.run [external] raw

def concreteEntriesEq :
    List (Address × Ix.Compiler.IxIR1.Decl) →
      List (Address × Ix.Compiler.IxIR1.Decl) → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      left.1 == right.1 &&
        Ix.Compiler.IxIR1.Readdress.Decl.structurallyEq left.2 right.2 &&
        concreteEntriesEq leftRest rightRest
  | _, _ => false

def decodeOk : Bool :=
  match Block.decodePreimage expectedBlockBytes with
  | .error _ => false
  | .ok decoded =>
      DeclList.structurallyEq decoded symbolic &&
        match Block.decodeMaterialized [external] expectedBlockBytes, built with
        | .ok artifact, .ok result =>
            artifact.blockAddress == result.blockAddress &&
              DeclList.structurallyEq artifact.blockMembers
                result.blockMembers &&
              concreteEntriesEq artifact.members result.members &&
              artifact.audit
        | _, _ => false

def malformed : List (String × ByteArray) := [
  ("trailing byte", expectedBlockBytes.push 0),
  ("wrong domain", expectedBlockBytes.set! 0 0),
  ("invalid local-reference tag", expectedBlockBytes.set! 40 0xff),
  ("nonminimal member count",
    Block.addressDomain ++ ByteArray.mk #[130, 0] ++
      expectedBlockBytes.extract 34 expectedBlockBytes.size),
  ("out-of-range local reference", expectedBlockBytes.set! 41 2),
  ("truncated block",
    expectedBlockBytes.extract 0 (expectedBlockBytes.size - 1)),
  ("empty block", Block.addressDomain ++ ByteArray.mk #[0])]

def rejectsArtifactBytes (bytes : ByteArray) : Bool :=
  match Block.decodeArtifact bytes with
  | .error _ => true
  | .ok _ => false

def expectedRenamedRaw (result : MutualBlock.Result) :
    List (Address × Ix.Compiler.IxIR1.Decl) :=
  let rename := Ix.Compiler.IxIR1.Readdress.Renaming.apply result.addressMap
  raw.map fun entry =>
    (rename entry.1,
      Ix.Compiler.IxIR1.Readdress.Decl.mapAddresses rename entry.2)

def concreteShape (result : MutualBlock.Result) : Bool :=
  match result.members with
  | [(addressA, declarationA), (addressB, declarationB)] =>
      Ix.Compiler.IxIR1.Readdress.Decl.references declarationA == [addressB] &&
        Ix.Compiler.IxIR1.Readdress.Decl.references declarationB ==
          [addressA, external] &&
        result.addressMap.lookup oldA == some addressA &&
        result.addressMap.lookup oldB == some addressB
  | _ => false

def builtOk (result : MutualBlock.Result) : Bool :=
  Block.preimage result.blockMembers == expectedBlockBytes &&
    Address.toHex result.blockAddress == expectedBlockHex &&
    result.derivedAddresses.map Address.toHex == expectedMemberHexes &&
    DeclList.structurallyEq result.blockMembers symbolic &&
    concreteEntriesEq result.members (expectedRenamedRaw result) &&
    result.memberKeysDerived && result.blockStable &&
    result.noTransientKeys && result.noTransientReferences &&
    result.semanticAudit raw && concreteShape result

def renamedRaw : List (Address × Ix.Compiler.IxIR1.Decl) :=
  let newA := Address.replicate 0xa1
  let newB := Address.replicate 0xa2
  [(newA,
      .fn ⟨1, .shared, true,
        .letOp (.call newB #[.var 0]) (.ret (.var 0))⟩),
   (newB,
      .fn ⟨0, .unique, false,
        .case .erased false #[.mk 0 0
          (.letOp (.papp newA #[])
            (.letOp (.extern external #[]) (.ret .erased)))]⟩)]

def transientSpellingIndependent : Bool :=
  DeclList.structurallyEq (abstractMembers renamedRaw) symbolic &&
    Block.preimage (abstractMembers renamedRaw) == expectedBlockBytes

def orderSensitive : Bool :=
  let reversed := raw.reverse
  Block.preimage (abstractMembers reversed) != expectedBlockBytes &&
    Block.address (abstractMembers reversed) != Block.address symbolic

def rejectsEmpty : Bool :=
  match MutualBlock.run [] [] with
  | .error message =>
      message == "IxIR1 mutual block must contain at least one member"
  | .ok _ => false

def rejectsDuplicateTemporary : Bool :=
  match MutualBlock.run []
      [(oldA, .extern 0), (oldA, .extern 1)] with
  | .error message =>
      message == s!"duplicate IxIR1 mutual-block temporary address {Address.toHex oldA}"
  | .ok _ => false

def rejectsDerivedReservedCollision : Bool :=
  match built with
  | .error _ => false
  | .ok result =>
      match MutualBlock.run [result.derivedAddresses.head!] raw with
      | .error message =>
          message == s!"IxIR1 mutual-block member key collides with reserved identity {Address.toHex result.derivedAddresses.head!}"
      | .ok _ => false

end IxIR1MutualBlockFixtures

namespace RepeatedErasureFixtures

open Ix.Compiler Ix.Compiler.Ixon

def first : Address := Address.replicate 0xc1
def second : Address := Address.replicate 0xc2

def groups : List IxIR0.Readdress.Group :=
  [.mutual [(first, .defn .shared .erased)],
   .mutual [(second, .defn .shared .erased)]]

def mainExpr : IxIR0.Expr :=
  .letE .many (.ref first)
    (.letE .many (.ref second) (.lit (.nat 17)))

def built := IxIR0.Readdress.run [] groups mainExpr

/-- Both erased producers survive, even though their output identities and
declarations coincide. The existing semantic transport theorem still applies. -/
theorem transport (result : IxIR0.Readdress.Result) (hrun : built = .ok result) :
    result.addressedCtx.run result.main 100 =
      IxIR0.Readdress.mapResult
        (IxIR0.MutualBlock.Renaming.apply result.addressMap)
        ((result.preAddressCtx groups).run mainExpr 100) := by
  exact IxIR0.Readdress.run_emptyOracle_of_run_eq_ok hrun 100

def checkedReuse : Bool :=
  match built with
  | .error _ => false
  | .ok result =>
    match result.blocks, result.addressMap with
    | [left, right], [(oldA, newA), (oldB, newB)] =>
      oldA == first && oldB == second && newA == newB &&
        left.blockAddress == right.blockAddress &&
        left.blockMembers == [.defn .shared .erased] &&
        left.members == right.members && left.addressMap != right.addressMap &&
        result.declarations.length == 2 &&
        result.semanticAudit [] groups mainExpr &&
        (match (result.preAddressCtx groups).run mainExpr 100,
            result.addressedCtx.run result.main 100 with
        | .ok (.lit (.nat 17)), .ok (.lit (.nat 17)) => true
        | _, _ => false)
    | _, _ => false

/-- Collision tests inject candidate results into the exact production
comparison. They do not need to discover an actual BLAKE3 collision. -/
def conflictsRejected : Bool :=
  match IxIR0.MutualBlock.run [] [(first, .defn .shared .erased)] with
  | .error _ => false
  | .ok original =>
    let compatible := IxIR0.Readdress.compatibleBlocks original
    let member := original.derivedAddresses.head!
    compatible { original with addressMap := [(second, member)] } &&
      !compatible { original with blockMembers := [.extern 0] } &&
      !compatible { original with members := [(member, .extern 0)] } &&
      !compatible { original with addressMap := [(second, second)] } &&
      !compatible { original with blockAddress := second } &&
      !compatible { original with blockAddress := member } &&
      !compatible { original with
        members := [(original.blockAddress, .defn .shared .erased)]
        addressMap := [(second, original.blockAddress)] }

def protectedNamespaces : Bool :=
  match IxIR0.MutualBlock.run [] [(first, .defn .shared .erased)] with
  | .error _ => false
  | .ok block =>
    let rejects := fun reserved groups main =>
      match IxIR0.Readdress.run reserved groups main with
      | .error _ => true
      | .ok _ => false
    let identities := block.blockAddress :: block.derivedAddresses
    identities.all fun key =>
      rejects [key] groups mainExpr &&
        rejects [] (groups ++ [.stable [(key, .extern 0)]]) mainExpr &&
        rejects [] groups (.ref key)

/-- Alpha-renamed two-member cycles share an entire block, including the
position-sensitive derived member identities and all four producer mappings. -/
def repeatedCycles : Bool :=
  let make := fun a b => IxIR0.Readdress.Group.mutual
    [(a, .defn .shared (.lam .many (.ref b))),
     (b, .defn .shared (.lam .many (.ref a)))]
  let a := Address.replicate 0xb1
  let b := Address.replicate 0xb2
  let groups := [make first second, make a b]
  match IxIR0.Readdress.run [] groups .erased with
  | .error _ => false
  | .ok result =>
    match result.addressMap with
    | [(old0, key0), (old1, key1), (old2, key2), (old3, key3)] =>
      [old0, old1, old2, old3] == [first, second, a, b] &&
        key0 == key2 && key1 == key3 && key0 != key1 &&
        result.blocks.length == 2 && result.declarations.length == 4 &&
        result.semanticAudit [] groups .erased
    | _ => false

end RepeatedErasureFixtures

namespace AddressedErasureFixtures

open Ix.Compiler
open Ix.Compiler.Ixon

def block : Address := Address.replicate 0x66
def projection : Address := Address.replicate 0x67
def result0 : Address := Address.replicate 0x68
def result1 : Address := Address.replicate 0x69

def definition0 : Definition :=
  { kind := .defn, safety := .safe, lvls := 0
    typ := .sort 0
    value := .letE false (.sort 0) (.recur 1 #[]) (.nat 0) }

def definition1 : Definition :=
  { kind := .defn, safety := .safe, lvls := 0
    typ := .sort 0
    value := .letE false (.sort 0)
      (.lam .many (.sort 0) (.recur 0 #[])) (.nat 1) }

def blockConstant : Constant :=
  { info := .muts #[.defn definition0, .defn definition1]
    sharing := #[], refs := #[result0, result1], univs := #[] }

def projectionConstant : Constant :=
  { info := .dPrj { idx := 0, block }
    sharing := #[], refs := #[], univs := #[] }

def constants : List (Address × Constant) :=
  [(block, blockConstant), (projection, projectionConstant)]

def resolve : Address → Option Constant := fun address =>
  (constants.find? fun entry => entry.1 == address).map (·.2)

def eraseCtx : Erase.EraseCtx :=
  { resolve
    blobs := fun address =>
      if address == result0 then some (.natB 71)
      else if address == result1 then some (.natB 72)
      else none }

def old0 : Address := Address.memberAddr block 0
def old1 : Address := Address.memberAddr block 1

def expectedRaw : List (Address × IxIR0.Decl) :=
  [(old0,
      .defn .shared
        (.letE .many (.ref old1) (.lit (.nat 71)))),
   (old1,
      .defn .shared
        (.letE .many (.lam .many (.ref old0)) (.lit (.nat 72)))),
   (projection, .defn .shared (.ref old0))]

def built : Except EraseAddressed.Error EraseAddressed.Result :=
  EraseAddressed.run eraseCtx constants (.ref projection) 200

def expectedBlockHex : String :=
  "6312e058809a62a40401b625ea5c0ded43148db937372bc8c6fa0d4fbd38bce2"
def expectedMemberHexes : List String :=
  ["4fcbdd06089faacd05289a959ad6ce05ac3281e70260f3a820a12f43f0b6c8d2",
   "08618a2f9659ce402c41bdb5237b558318911ac27aa98041208e4d5ca9eda708"]

def runtimeOk (result : EraseAddressed.Result) : Bool :=
  let ctx : IxIR0.Ctx := { env := IxIR0.Env.ofList result.declarations }
  match IxIR0.eval ctx 200 [] result.main with
  | .ok (.lit (.nat 71)) => true
  | _ => false

/-- The certified pre-address context executes the legacy main, and the
emitted context executes its exact address image. -/
def transportRuntimeOk (result : EraseAddressed.Result) : Bool :=
  let before := result.addressed.preAddressCtx result.groups
  let after := result.addressed.addressedCtx
  match before.run (.ref projection) 200, after.run result.main 200 with
  | .ok (.lit (.nat 71)), .ok (.lit (.nat 71)) => true
  | _, _ => false

theorem semanticTransport (result : EraseAddressed.Result)
    (hrun : built = .ok result) :
    (result.addressed.addressedCtx).run result.main 200 =
      IxIR0.Readdress.mapResult
        (IxIR0.MutualBlock.Renaming.apply result.addressMap)
        ((result.addressed.preAddressCtx result.groups).run
          (.ref projection) 200) := by
  exact EraseAddressed.run_emptyOracle_semantics_of_run_eq_ok hrun 200

def builtOk (result : EraseAddressed.Result) : Bool :=
  let map := result.addressMap
  let new0 := map.lookup old0
  let new1 := map.lookup old1
  result.raw == expectedRaw && result.groups.length == 2 &&
    result.addressed.blocks.length == 1 && map.length == 2 &&
    result.addressed.blockAddresses.map Address.toHex == [expectedBlockHex] &&
    result.addressed.derivedAddresses.map Address.toHex == expectedMemberHexes &&
    result.addressed.noTransientKeys &&
    result.addressed.noTransientReferences &&
    result.semanticAudit eraseCtx constants (.ref projection) 200 &&
    (match new0, new1,
        (IxIR0.Env.ofList result.declarations) projection with
      | some address0, some address1,
          some (.defn .shared (.ref projected)) =>
          projected == address0 && address0 != old0 && address1 != old1
      | _, _, _ => false) && runtimeOk result && transportRuntimeOk result

/-- A local edge to another block's transient namespace cannot be given the
meaning of an external stable address. -/
def crossBlockTemporaryRejected : Bool :=
  let tempA := Address.replicate 0xd1
  let tempB := Address.replicate 0xd2
  let groups : List IxIR0.Readdress.Group :=
    [.mutual [(tempA, .defn .shared (.ref tempB))],
     .mutual [(tempB, .defn .shared .erased)]]
  match IxIR0.Readdress.run [] groups .erased with
  | .error message =>
      message == s!"cross-block reference uses another mutual block's temporary address {Address.toHex tempB}"
  | .ok _ => false

/-! The same genuine member cycle must cross the complete executable pipeline,
where it becomes an IxIR₀ block and then a distinct IxIR₁ block. -/

def pipelineDefinition0 : Definition :=
  { kind := .defn, safety := .safe, lvls := 0
    typ := .sort 0
    value := .letE false (.sort 0) (.recur 1 #[]) (.sort 0) }

def pipelineDefinition1 : Definition :=
  { kind := .defn, safety := .safe, lvls := 0
    typ := .sort 0
    value := .letE false (.sort 0) (.recur 0 #[]) (.sort 0) }

def pipelineBlockConstant : Constant :=
  { info := .muts #[.defn pipelineDefinition0, .defn pipelineDefinition1]
    sharing := #[], refs := #[], univs := #[] }

def pipelineConstants : List (Address × Constant) :=
  [(block, pipelineBlockConstant), (projection, projectionConstant)]

/-- An unused, well-formed sharing entry selects the sharing-aware validator
branch without changing erasure or target identity. -/
def sharedPipelineBlockConstant : Constant :=
  { pipelineBlockConstant with sharing := #[.sort 0] }

def sharedPipelineConstants : List (Address × Constant) :=
  [(block, sharedPipelineBlockConstant), (projection, projectionConstant)]

def pipelineBuilt : Except Pipeline.Error Pipeline.Artifact :=
  Pipeline.compile pipelineConstants projection

def validatedPipelineBuilt : Except Pipeline.Error Pipeline.Artifact :=
  Pipeline.compileValidated sharedPipelineConstants projection

/-- The conservative sidecar attachment accepts this constructor-free cyclic
program, validates the resulting IxIR₂ graph, and preserves its observable
control-fuel divergence. -/
def validatedIxIR2AttachmentOk : Bool :=
  match Ix.Compiler.IxIR2.Pipeline.compileValidated
      sharedPipelineConstants projection with
  | .error _ => false
  | .ok attached =>
      let artifact := attached.target.artifact
      let context := Ix.Compiler.IxIR2.Eval.Context.ofProgram
        artifact.program artifact.validationContext.schemas
      attached.sidecars.parameterEntries.length ==
        attached.source.artifact.targetDecls.length &&
        attached.sidecars.sourceNoReuse artifact.trace &&
        attached.sidecars.tracePappsSafe artifact.trace &&
        attached.sidecars.traceExactCaseTargetsMatch artifact.trace &&
        !artifact.trace.positions.isEmpty &&
        match Ix.Compiler.IxIR2.Eval.runMain context .logical
            artifact.program 20 20 with
        | .error .controlFuel => true
        | _ => false

def expectedTargetBlockHex : String :=
  "3ecbe37b727c6fbe939db9fa01c4c9b3dfbbf376b2812d1b045546846a3715cb"

def expectedTargetMapHexes : List String :=
  ["eec1f36398b68ed5b253505079e260a21a8b3d6c148b4766a0cd9a00e93a6d9e",
   "0e400d87105ce7a391d272bc3cb535598242ad2cb65e11dbf921571be985929a",
   "d9fc41365f30d4397fdefd6626449cfae2d744bd21461aff8e3b7a82c482f412"]

def pipelineOk (artifact : Pipeline.Artifact) : Bool :=
  let finalKeys := artifact.targetDecls.map (Prod.fst)
  let targetCtx : IxIR1.Ctx :=
    { decls := (IxIR1.Env.Index.ofList artifact.targetDecls).toEnv }
  match artifact.erasedAddressMap.lookup old0,
      artifact.erasedAddressMap.lookup old1 with
  | some erased0, some erased1 =>
    match artifact.targetAddressMap.lookup erased0,
        artifact.targetAddressMap.lookup erased1,
        artifact.targetAddressMap.lookup projection with
    | some target0, some target1, some targetProjection =>
      artifact.erasedBlocks.length == 1 &&
        artifact.targetBlocks.length == 1 &&
        artifact.targetBlocks.map (Address.toHex ∘ (·.blockAddress)) ==
          [expectedTargetBlockHex] &&
        artifact.targetAddressMap.map (Address.toHex ∘ (·.2)) ==
          expectedTargetMapHexes &&
        artifact.targetAddressMap.length == 3 &&
        artifact.targetDecls.length == 3 && target0 != erased0 &&
        target1 != erased1 && targetProjection != projection &&
        !finalKeys.contains old0 && !finalKeys.contains old1 &&
        !finalKeys.contains erased0 && !finalKeys.contains erased1 &&
        !finalKeys.contains projection &&
        artifact.targetBlocks.any fun block =>
          block.derivedAddresses.contains target0 &&
            block.derivedAddresses.contains target1 &&
        match IxIR1.runMain targetCtx artifact.main 200 with
        | .error .fuel => true
        | _ => false
    | _, _, _ => false
  | _, _ => false

def targetDeclsEq : List (Address × IxIR1.Decl) →
    List (Address × IxIR1.Decl) → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      left.1 == right.1 &&
        IxIR1.Readdress.Decl.structurallyEq left.2 right.2 &&
        targetDeclsEq leftRest rightRest
  | _, _ => false

def validatedPipelineAgrees (direct gated : Pipeline.Artifact) : Bool :=
  direct.rawErasedDecls == gated.rawErasedDecls &&
    direct.erasedDecls == gated.erasedDecls &&
    direct.erasedAddressMap == gated.erasedAddressMap &&
    targetDeclsEq direct.targetDecls gated.targetDecls &&
    direct.targetAddressMap == gated.targetAddressMap &&
    direct.targetBlocks.map (·.blockAddress) ==
      gated.targetBlocks.map (·.blockAddress) &&
    pipelineOk gated

end AddressedErasureFixtures

namespace IxIR1OwnedMainFixtures

open Ix.Compiler
open Ix.Compiler.IxIR1

def constructor : CtorId :=
  { block := Address.replicate 0xc7, indIdx := 0, cidx := 0 }

def uniqueMain : Code :=
  .letOp (.alloc .unique constructor #[]) (.ret (.var 0))

def mismatchedMain : Code :=
  .letOp (.alloc .shared constructor #[]) (.ret (.var 0))

def nestedReuse : Code :=
  .case .erased false #[
    .mk 0 0 (.letOp (.reuse .erased constructor #[]) (.ret (.var 0)))]

/-- `runOwnedMain` both accepts the declared unique result and rejects a live
shared location at that boundary. -/
def ownedBoundaryOk : Bool :=
  let context : Ctx := { decls := Env.empty }
  match runOwnedMain context .unique uniqueMain 4,
      runOwnedMain context .unique mismatchedMain 4 with
  | .ok (store, .loc location),
      .error (.mem "function result ownership mismatch") =>
      match store.get? location with
      | some box => box.world == .unique
      | none => false
  | _, _ => false

/-- The executable no-reuse reflection walk reaches nested case bodies and
finite declaration lists. -/
def noReuseChecksOk : Bool :=
  NoReuse.checkCode uniqueMain && !NoReuse.checkCode nestedReuse &&
    NoReuse.checkDeclarations
      [(Address.replicate 0xc8,
        .fn ⟨0, .unique, false, uniqueMain⟩)] &&
    !NoReuse.checkDeclarations
      [(Address.replicate 0xc9,
        .fn ⟨0, .shared, false, nestedReuse⟩)]

end IxIR1OwnedMainFixtures

namespace IxIR2PipelineFixtures

open Ix.Compiler
open Ix.Compiler.Ixon

def constructorBlockA : Address := Address.replicate 0xb1
def constructorBlockB : Address := Address.replicate 0xb2

def constructorA : IxIR2.CtorId :=
  { block := constructorBlockA, indIdx := 0, cidx := 0 }

def constructorB : IxIR2.CtorId :=
  { block := constructorBlockB, indIdx := 0, cidx := 0 }

def ambiguousInput : IxIR2.Lower.Input :=
  { declarations := []
    main :=
      .letOp (.alloc .shared constructorA #[.lit (.nat 9)])
        (.letOp (.fetch (.var 0) 0) (.ret (.var 1)))
    mainResult := .shared }

def ambiguousSidecars : IxIR2.Pipeline.Sidecars :=
  { input := ambiguousInput
    parameterEntries := []
    constructors :=
      [{ identity := constructorA, arity := 1 },
       { identity := constructorB, arity := 1 }] }

/-- Global constructor ambiguity no longer blocks a projection whose lexical
producer is an exact local allocation. -/
def ambiguousFetchAcceptedByProducerFact : Bool :=
  match IxIR2.Lower.lowerChecked ambiguousSidecars.context ambiguousInput with
  | .error _ => false
  | .ok checked =>
      let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
        checked.artifact.validationContext.schemas
      checked.artifact.trace.fetchCapabilitiesMatch &&
        ambiguousSidecars.traceExactFetchesMatch checked.artifact.trace &&
        match IxIR2.Eval.runMain context .logical checked.artifact.program 8 2 with
        | .ok result =>
            match result.value with
            | .loc _ => result.store.live == 1
            | _ => false
        | .error _ => false

def ambiguousCaseInput : IxIR2.Lower.Input :=
  { declarations := []
    main :=
      .letOp (.alloc .shared constructorA #[.lit (.nat 9)])
        (.case (.var 0) false
          #[.mk 0 1
            (.letOp (.drop (.var 1)) (.ret (.lit (.nat 9))))])
    mainResult := .shared }

def ambiguousCaseSidecars : IxIR2.Pipeline.Sidecars :=
  { ambiguousSidecars with input := ambiguousCaseInput }

/-- Exact path-local HPT provenance also disambiguates a constructor switch.
The independent trace check certifies that the selected identity occurs in
the emitted terminator, and execution takes that branch successfully. -/
def ambiguousCaseAcceptedByProducerFact : Bool :=
  match IxIR2.Lower.lowerChecked ambiguousCaseSidecars.context
      ambiguousCaseInput with
  | .error _ => false
  | .ok checked =>
      let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
        checked.artifact.validationContext.schemas
      ambiguousCaseSidecars.traceExactCaseTargetsMatch
          checked.artifact.trace &&
        match IxIR2.Eval.runMain context .logical checked.artifact.program 16 4 with
        | .ok result =>
            result.value == .lit (.nat 9) && result.store.live == 0
        | .error _ => false

def unresolvedFetcher : Address := Address.replicate 0xba

def unresolvedFetchInput : IxIR2.Lower.Input :=
  { declarations :=
      [(unresolvedFetcher,
        .fn
          { arity := 1
            result := .shared
            papSafe := true
            body :=
              .letOp (.fetch (.var 0) 0) (.ret (.var 0)) })]
    main :=
      .letOp (.alloc .shared constructorA #[.lit (.nat 9)])
        (.letOp (.call unresolvedFetcher #[.var 0]) (.ret (.var 0)))
    mainResult := .shared }

def unresolvedFetchSidecars : IxIR2.Pipeline.Sidecars :=
  { input := unresolvedFetchInput
    parameterEntries := [(unresolvedFetcher, #[.shared])]
    constructors :=
      [{ identity := constructorA, arity := 1 },
       { identity := constructorB, arity := 1 }] }

/-- An unrefined function parameter remains ambiguous and fails closed. -/
def unresolvedFetchRejected : Bool :=
  match IxIR2.Lower.lowerChecked unresolvedFetchSidecars.context
      unresolvedFetchInput with
  | .error (.schema _ _) => true
  | _ => false

def scalarConstructorA : IxIR2.CtorId :=
  { block := Address.replicate 0xbb, indIdx := 0, cidx := 0 }

def scalarConstructorB : IxIR2.CtorId :=
  { block := Address.replicate 0xbc, indIdx := 0, cidx := 0 }

def ambiguousScalarFreeInput : IxIR2.Lower.Input :=
  { declarations := []
    main :=
      .letOp (.alloc .unique scalarConstructorA #[])
        (.letOp (.free (.var 0)) (.ret (.lit (.nat 4))))
    mainResult := .shared }

def ambiguousScalarFreeSidecars : IxIR2.Pipeline.Sidecars :=
  { input := ambiguousScalarFreeInput
    parameterEntries := []
    constructors :=
      [{ identity := scalarConstructorA, arity := 0 },
       { identity := scalarConstructorB, arity := 0 }] }

/-- The same exact-producer rule disambiguates a shallow unique free and the
logical machine observes an empty live heap afterward. -/
def ambiguousScalarFreeAcceptedByProducerFact : Bool :=
  match IxIR2.Lower.lowerChecked ambiguousScalarFreeSidecars.context
      ambiguousScalarFreeInput with
  | .error _ => false
  | .ok checked =>
      let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
        checked.artifact.validationContext.schemas
      ambiguousScalarFreeSidecars.traceScalarLeavesMatch
          checked.artifact.trace &&
        match IxIR2.Eval.runMain context .logical checked.artifact.program 8 2 with
        | .ok result =>
            result.value == .lit (.nat 4) && result.store.live == 0
        | .error _ => false

def pappTarget : Address := Address.replicate 0xbd

def pappInput : IxIR2.Lower.Input :=
  { declarations :=
      [(pappTarget,
        .fn
          { arity := 2
            result := .shared
            papSafe := true
            body :=
              .letOp (.drop (.var 0))
                (.letOp (.drop (.var 2)) (.ret (.lit (.nat 0)))) })]
    main :=
      .letOp (.papp pappTarget #[.lit (.nat 7)]) (.ret (.var 0))
    mainResult := .shared }

def pappSidecars : IxIR2.Pipeline.Sidecars :=
  { input := pappInput
    parameterEntries := [(pappTarget, #[.shared, .shared])]
    constructors := [] }

/-- Checked function-PAP lowering records the exact shared capture transition
and the logical machine retains precisely the fresh PAP owner. -/
def pappCapabilityTransitionAccepted : Bool :=
  match IxIR2.Lower.lowerChecked pappSidecars.context pappInput with
  | .error _ => false
  | .ok checked =>
      let emittedPapp :=
        match checked.artifact.program.main.blocks[0]? with
        | some block =>
            block.instructions[0]? ==
              some (.papp pappTarget #[.lit (.nat 7)])
        | none => false
      let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
        checked.artifact.validationContext.schemas
      emittedPapp &&
        pappSidecars.tracePappsSafe checked.artifact.trace &&
        checked.artifact.trace.allocationCapabilitiesMatch &&
        match IxIR2.Eval.runMain context .logical checked.artifact.program 4 1 with
        | .ok result =>
            match result.value with
            | .loc location =>
                result.store.live == 1 &&
                  match result.store.get? location with
                  | some box =>
                      box.world == .shared && box.rc == 1 &&
                        match box.node with
                        | .papN address arity arguments =>
                            address == pappTarget && arity == 2 &&
                              arguments == #[.lit (.nat 7)]
                        | _ => false
                  | none => false
            | _ => false
        | .error _ => false

def unsafePappInput : IxIR2.Lower.Input :=
  { pappInput with
    declarations :=
      [(pappTarget,
        .fn
          { arity := 2
            result := .shared
            papSafe := false
            body :=
              .letOp (.drop (.var 0))
                (.letOp (.drop (.var 2)) (.ret (.lit (.nat 0)))) })] }

def unsafePappSidecars : IxIR2.Pipeline.Sidecars :=
  { pappSidecars with input := unsafePappInput }

/-- The attachment-side trace check fails closed if the exact declaration
environment no longer marks a retained `papp` target safe. -/
def pappSafetyCheckRejectsUnsafe : Bool :=
  match IxIR2.Lower.lowerChecked pappSidecars.context pappInput with
  | .error _ => false
  | .ok checked =>
      !unsafePappSidecars.tracePappsSafe checked.artifact.trace

def retiredBorrowInput : IxIR2.Lower.Input :=
  { declarations := []
    main :=
      .letOp (.alloc .shared constructorA #[.lit (.nat 9)])
        (.letOp (.fetch (.var 0) 0)
          (.letOp (.drop (.var 1)) (.ret (.lit (.nat 4)))))
    mainResult := .shared }

def retiredBorrowSidecars : IxIR2.Pipeline.Sidecars :=
  { input := retiredBorrowInput
    parameterEntries := []
    constructors := [{ identity := constructorA, arity := 1 }] }

/-- Consuming an owner after its loan's final use retires both the owner and
the validator-dead borrow in the producer continuation. -/
def lenderDestructionRetiresBorrow : Bool :=
  match IxIR2.Lower.lowerChecked retiredBorrowSidecars.context
      retiredBorrowInput with
  | .error _ => false
  | .ok checked =>
      let retired := checked.artifact.trace.positions.any fun position =>
        position.source.owner == IxIR2.Validate.Owner.main &&
          position.source.offset == 3 &&
          position.sourceCapabilities ==
            #[.scalar, .dead, .dead]
      let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
        checked.artifact.validationContext.schemas
      checked.artifact.trace.destructionCapabilitiesMatch && retired &&
        match IxIR2.Eval.runMain context .logical checked.artifact.program 6 2 with
        | .ok result =>
            result.value == .lit (.nat 4) && result.store.live == 0
        | .error _ => false

def recursorOwner : Address := Address.replicate 0xb3
def recursorGroupA : Address := Address.replicate 0xb4
def recursorGroupB : Address := Address.replicate 0xb5

def caseConstructorA : IxIR2.CtorId :=
  { block := Address.replicate 0xb6, indIdx := 0, cidx := 0 }

def caseConstructorB : IxIR2.CtorId :=
  { block := Address.replicate 0xb7, indIdx := 0, cidx := 0 }

def exactRecursorInput : IxIR2.Lower.Input :=
  { declarations :=
      [(recursorOwner,
        .fn
          { arity := 1
            result := .shared
            papSafe := true
            body :=
              .case (.var 0) false #[
                .mk 0 0
                  (.letOp (.drop (.var 0))
                    (.ret (.lit (.nat 3))))] })]
    main :=
      .letOp (.alloc .shared caseConstructorA #[])
        (.letOp (.call recursorOwner #[.var 0]) (.ret (.var 0)))
    mainResult := .shared }

def residualRecursorInput : IxIR2.Lower.Input :=
  { exactRecursorInput with
    main :=
      .letOp (.alloc .shared caseConstructorB #[])
        (.letOp (.call recursorOwner #[.var 0]) (.ret (.var 0))) }

def exactRecursorSidecars : IxIR2.Pipeline.Sidecars :=
  { input := exactRecursorInput
    parameterEntries := [(recursorOwner, #[.shared])]
    constructors :=
      [{ identity := caseConstructorA
         arity := 0
         group := some recursorGroupA },
       { identity := caseConstructorB
         arity := 0
         group := some recursorGroupB }]
    recursorOrigins :=
      [{ owner := recursorOwner, group := recursorGroupA }] }

/-- A recursor parameter whose HPT fact remains ambiguous is lowered with
both producer-known full identities sharing its erased tag/arity.  Executing
the same checked branch with either constructor demonstrates that residual
coverage no longer guesses one mutual-block identity. -/
def exactRecursorCaseAccepted : Bool :=
  let accepts := fun input =>
    let sidecars := { exactRecursorSidecars with input := input }
    match IxIR2.Lower.lowerChecked sidecars.context input with
    | .error _ => false
    | .ok checked =>
        let declaration := checked.artifact.program.declarations.find? fun entry =>
          entry.1 == recursorOwner
        let coveredSwitch := match declaration with
          | some (_, .fn definition) =>
              match definition.blocks[0]? with
              | some block =>
                  match block.terminator with
                  | .switchValue _ constructors _ =>
                      constructors.size == 2 &&
                        constructors.any (fun target =>
                          target.cid == caseConstructorA) &&
                        constructors.any (fun target =>
                          target.cid == caseConstructorB)
                  | _ => false
              | none => false
          | _ => false
        let context := IxIR2.Eval.Context.ofProgram checked.artifact.program
          checked.artifact.validationContext.schemas
        coveredSwitch &&
          sidecars.traceResidualCaseTargetsMatch checked.artifact.trace &&
          sidecars.traceConstructorsKnown checked.artifact.trace &&
          match IxIR2.Eval.runMain context .logical checked.artifact.program
              8 2 with
          | .ok result =>
              result.value == .lit (.nat 3) && result.store.live == 0
          | .error _ => false
  accepts exactRecursorInput && accepts residualRecursorInput

def recursorSourceA : Address := Address.replicate 0xb8
def recursorSourceB : Address := Address.replicate 0xb9

def sourceRecursor : IxIR0.Decl :=
  .recursor 0 false #[{ fields := 0, rhs := .lit (.nat 3) }]

def sourceRecursorFn : IxIR1.Decl :=
  .fn
    { arity := 1
      result := .shared
      papSafe := true
      body :=
        .case (.var 0) false #[
          .mk 0 0
            (.letOp (.drop (.var 0)) (.ret (.lit (.nat 3))))] }

def originBlock (group source constructor : Address) :
    IxIR0.MutualBlock.Result :=
  { blockAddress := group
    blockMembers := []
    members := [(source, sourceRecursor), (constructor, .ctor 0 0)]
    addressMap := [] }

/-- The production extractor follows the complete final owner map, and rejects
two distinct mutual-block origins collapsed onto one IxIR₁ identity. -/
def recursorOriginExtractionOk : Bool :=
  let sourceA :=
    [(recursorSourceA, sourceRecursor),
     (caseConstructorA.block, IxIR0.Decl.ctor 0 0)]
  let blockA := originBlock recursorGroupA recursorSourceA
    caseConstructorA.block
  let exact := IxIR2.Pipeline.deriveRecursorOrigins sourceA [blockA]
    [(recursorSourceA, sourceRecursorFn)]
    [(recursorSourceA, recursorOwner)]
  let sourceBoth := sourceA ++
    [(recursorSourceB, sourceRecursor),
     (caseConstructorB.block, IxIR0.Decl.ctor 0 0)]
  let blockB := originBlock recursorGroupB recursorSourceB
    caseConstructorB.block
  let conflict := IxIR2.Pipeline.deriveRecursorOrigins sourceBoth
    [blockA, blockB]
    [(recursorSourceA, sourceRecursorFn),
     (recursorSourceB, sourceRecursorFn)]
    [(recursorSourceA, recursorOwner),
     (recursorSourceB, recursorOwner)]
  let exactOk := match exact with
    | .ok [origin] =>
        origin.owner == recursorOwner && origin.group == recursorGroupA
    | _ => false
  exactOk &&
    match conflict with
    | .error (.recursorOriginConflict owner) => owner == recursorOwner
    | _ => false

end IxIR2PipelineFixtures

namespace ReaddressOracleFixtures

open Ix.Compiler
open Ix.Compiler.Ixon

def legacyKey : Address := Address.replicate 0xe1
def addressedKey : Address := Address.replicate 0xe2

def mapping : IxIR0.MutualBlock.Renaming :=
  [(legacyKey, addressedKey)]

/-- A representative address-insensitive scalar ABI. Its result depends only
on argument count, so structurally mapping argument values cannot change the
legacy answer. -/
def lengthOracle : IxIR0.Oracle := fun _ arguments =>
  if arguments.length == 2 then some (.lit (.nat 37)) else none

theorem lengthOracle_readdressable :
    IxIR0.Readdress.Oracle.Readdressable mapping lengthOracle := by
  apply IxIR0.Readdress.Oracle.Readdressable.of_key_and_arguments
  · intro address arguments
    rfl
  · intro address arguments
    simp [lengthOracle]

/-- Key-sensitive stand-in for a legacy opaque member. It intentionally knows
only the transient key; the executable adapter supplies the final-key view. -/
def legacyKeyOracle : IxIR0.Oracle := fun address arguments =>
  if address == legacyKey && arguments.length == 2 then
    some (.ctor legacyKey 7 [])
  else none

def adapterOk : Bool :=
  let arguments : List IxIR0.Value := [.erased, .lit (.nat 5)]
  let addressed :=
    IxIR0.Readdress.Oracle.readdress mapping legacyKeyOracle
  match legacyKeyOracle addressedKey arguments,
      addressed addressedKey arguments,
      addressed addressedKey [.erased] with
  | none, some (.ctor resultKey 7 []), none => resultKey == addressedKey
  | _, _, _ => false

/-! A real mutual block whose executable path calls the modeled Nat-add ABI.
The back-edge sits beneath a lambda, so the static graph is cyclic while the
selected call terminates with the contentful ledger answer. -/

def cycleLeft : Address := Address.replicate 0xe6
def cycleRight : Address := Address.replicate 0xe7

def cycleLeftDecl : IxIR0.Decl :=
  .defn .shared (.lam .many
    (.letE .many (.ref cycleRight)
      (.app (.app (.ref IxIR0.Examples.natAddExt) (.lit (.nat 20)))
        (.lit (.nat 22)))))

def cycleRightDecl : IxIR0.Decl :=
  .defn .shared (.lam .many
    (.letE .many (.ref cycleLeft) (.lit (.nat 0))))

def ledgerMembers : List (Address × IxIR0.Decl) :=
  [(cycleLeft, cycleLeftDecl), (cycleRight, cycleRightDecl)]

def ledgerGroups : List IxIR0.Readdress.Group :=
  [.mutual ledgerMembers,
   .stable [(IxIR0.Examples.natAddExt, .extern 2)]]

def ledgerMain : IxIR0.Expr :=
  .app (.ref cycleLeft) .erased

def ledgerBuilt : Except String IxIR0.Readdress.Result :=
  IxIR0.Readdress.run [] ledgerGroups ledgerMain

def expectedLedgerBlock : String :=
  "521738161fb5195ac8a994d6386a6851253d826624abb4b6e3e398979e32a276"

def expectedLedgerMembers : List String :=
  ["f4598bb11abeed019d5dd722ca8f185a6ee2f7f9e6b6ef4c18d06d047f482396",
   "de3b531d467cbdfe5a8ebdd90c2d7a40e3c495fac9241dcf5608862a8b67ee8c"]

theorem ledgerOracleReaddressable (result : IxIR0.Readdress.Result)
    (hrun : ledgerBuilt = .ok result) :
    IxIR0.Readdress.Oracle.Readdressable result.addressMap
      IxIR0.Examples.oracle := by
  apply IxIR0.Readdress.Oracle.Readdressable.examples_of_run_eq_ok
    (by simpa [ledgerBuilt] using hrun)
  simp [IxIR0.Readdress.oracleIdentities, ledgerGroups,
    IxIR0.Readdress.stableKeys]

theorem ledgerCycleTransport (result : IxIR0.Readdress.Result)
    (hrun : ledgerBuilt = .ok result) :
    (result.addressedCtx
        (IxIR0.Readdress.Oracle.readdress result.addressMap
          IxIR0.Examples.oracle)).run result.main 200 =
      IxIR0.Readdress.mapResult
        (IxIR0.MutualBlock.Renaming.apply result.addressMap)
        ((result.preAddressCtx ledgerGroups IxIR0.Examples.oracle).run
          ledgerMain 200) := by
  exact result.run_readdressOracle_of_run_eq_ok
    (by simpa [ledgerBuilt] using hrun) IxIR0.Examples.oracle
    (ledgerOracleReaddressable result hrun) 200

def ledgerCycleOk (result : IxIR0.Readdress.Result) : Bool :=
  let before := result.preAddressCtx ledgerGroups IxIR0.Examples.oracle
  let after := result.addressedCtx
    (IxIR0.Readdress.Oracle.readdress result.addressMap
      IxIR0.Examples.oracle)
  result.blocks.length == 1 && result.addressMap.length == 2 &&
    result.blockAddresses.map Address.toHex == [expectedLedgerBlock] &&
    result.derivedAddresses.map Address.toHex == expectedLedgerMembers &&
    IxIR0.Readdress.Renaming.isolates result.addressMap
      IxIR0.Examples.natAddExt &&
    match before.run ledgerMain 200, after.run result.main 200 with
    | .ok (.lit (.nat 42)), .ok (.lit (.nat 42)) => true
    | _, _ => false

/-- Main-code external identities participate in the same no-capture check as
declaration references. -/
def mainExternalCaptureRejected : Bool :=
  match IxIR0.MutualBlock.run [IxIR0.Examples.natAddExt] ledgerMembers with
  | .error _ => false
  | .ok block =>
    match block.derivedAddresses with
    | captured :: _ =>
      match IxIR0.Readdress.run [IxIR0.Examples.natAddExt]
          [.mutual ledgerMembers] (.ref captured) with
      | .error message =>
        message == s!"derived mutual-member key captures a program external reference {Address.toHex captured}"
      | .ok _ => false
    | [] => false

end ReaddressOracleFixtures

namespace HPTFixtures

open Ix.Compiler
open Ix.Compiler.Ixon

def rawExtern : Address := Address.replicate 0xd0
def rawTarget : Address := Address.replicate 0xd1
def rawCaller : Address := Address.replicate 0xd2
def rawConstructor : Address := Address.replicate 0xd3
def rawCycleLeft : Address := Address.replicate 0xd4
def rawCycleRight : Address := Address.replicate 0xd5
def constructorBlock : Address := Address.replicate 0xda

def constructorId : IxIR1.CtorId := ⟨constructorBlock, 0, 0⟩

def targetDeclaration : IxIR1.Decl :=
  .fn ⟨2, .shared, true, .ret (.lit (.nat 42))⟩

def callerDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.papp rawTarget #[.lit (.nat 20)])
      (.letOp (.apply (.var 0) #[.lit (.nat 22)])
        (.ret (.var 0)))⟩

def constructorDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.alloc .shared constructorId #[.lit (.nat 7)])
      (.ret (.var 0))⟩

def cycleLeftDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call rawCycleRight #[]) (.ret (.var 0))⟩

def cycleRightDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true,
    .case (.lit (.nat 0)) true #[
      .mk 0 0
        (.letOp (.alloc .shared constructorId #[.lit (.nat 7)])
          (.letOp (.fetch (.var 0) 0) (.ret (.var 0)))),
      .mk 1 1 (.letOp (.call rawCycleLeft #[]) (.ret (.var 0)))]⟩

def rawDeclarations : List (Address × IxIR1.Decl) :=
  [(rawCaller, callerDeclaration),
   (rawTarget, targetDeclaration),
   (rawConstructor, constructorDeclaration),
   (rawCycleLeft, cycleLeftDeclaration),
   (rawCycleRight, cycleRightDeclaration),
   (rawExtern, .extern 2)]

def rawMain : IxIR1.Code :=
  .letOp (.call rawCaller #[]) (.ret (.var 0))

def addressed : Except String IxIR1.ReaddressAll.Result :=
  IxIR1.ReaddressAll.run [constructorBlock] rawDeclarations rawMain

def finalAddress (result : IxIR1.ReaddressAll.Result)
    (raw : Address) : Address :=
  IxIR1.Readdress.Renaming.apply result.addressMap raw

def programIdentity : IxIR1.ReaddressAll.Artifact → Address
  | .stable address _ | .ordinary address _ => address
  | .mutual block => block.blockAddress

def detailedConstructorFact : IxIR1.HPT.Fact :=
  IxIR1.HPT.Fact.heap
    (.ctor constructorId (some [IxIR1.HPT.FieldFact.scalar]))

def factFor (result : IxIR1.ReaddressAll.Result)
    (targetFact callerFact : IxIR1.HPT.Fact)
    (address : Address) : IxIR1.HPT.Fact :=
  if address == finalAddress result rawTarget then
    targetFact
  else if address == finalAddress result rawCaller then
    callerFact
  else if address == finalAddress result rawConstructor then
    detailedConstructorFact
  else
    IxIR1.HPT.Fact.scalar

def certificate (result : IxIR1.ReaddressAll.Result)
    (targetFact callerFact : IxIR1.HPT.Fact) : IxIR1.HPT.Certificate :=
  ⟨result.artifacts.map fun artifact =>
    { programIdentity := programIdentity artifact
      members := artifact.declarations.map fun member =>
        (member.1, factFor result targetFact callerFact member.1) }⟩

def preciseCertificate (result : IxIR1.ReaddressAll.Result) :
    IxIR1.HPT.Certificate :=
  certificate result .scalar .scalar

def widenedCertificate (result : IxIR1.ReaddressAll.Result) :
    IxIR1.HPT.Certificate :=
  certificate result .top .top

def precise (result : IxIR1.ReaddressAll.Result) :
    Except String IxIR1.HPT.Result :=
  IxIR1.HPT.run result.artifacts (preciseCertificate result)

def widened (result : IxIR1.ReaddressAll.Result) :
    Except String IxIR1.HPT.Result :=
  IxIR1.HPT.run result.artifacts (widenedCertificate result)

def expectedCacheKeys : List String :=
  ["aa0edd4e751dcf06272bc2732dececb251cbfe069f938cfc2714e3954699692d",
   "e25e2f1ac5d876e00bb1a500896fcc6c9f08a463c2a116b847e759c9ea66e6cd",
   "0425d4800a33f31155d461ebb7c42fd1c5f98ba7a13ef22012236c779ef841c3",
   "49e96f64307e0b092fcf7d0d80ebc8b3954fcf7394bb4d6183962bf6c5df7e7a",
   "b3545b3b84a80b48985948ce2cf695100997782b53b9ee6047f2a7fdc02e10f5"]

def expectedSummaryAddresses : List String :=
  ["e63bfc3574ff2dcc567f40c08742b392872cff5727191ab69bd21e312b2c26d8",
   "0440bda2b04538bf529aacced15dcdd26251d749476daef6f03a63d88fc7cc5c",
   "9e0beee98136479c7a2c8d2389210fd6087659790709963646dd1a9a519ac164",
   "8c2eae674fa8fe6efab7f98d5f94462e7c678fd76298a87f2b379a95e1cdca8b",
   "ce6e76ed9c44e92f8a659583dfb8461241f8e9dd6d937a30fc1b9d5a96d18994"]

def findSummary (analysis : IxIR1.HPT.Result) (function : Address) :
    Option IxIR1.HPT.Artifact :=
  analysis.artifacts.find? fun artifact =>
    artifact.members.any fun member => member.1 == function

def cacheConeOk (program : IxIR1.ReaddressAll.Result)
    (preciseResult widenedResult : IxIR1.HPT.Result) : Bool :=
  let target := finalAddress program rawTarget
  let caller := finalAddress program rawCaller
  let constructor := finalAddress program rawConstructor
  match findSummary preciseResult target, findSummary widenedResult target,
      findSummary preciseResult caller, findSummary widenedResult caller,
      findSummary preciseResult constructor,
      findSummary widenedResult constructor with
  | some preciseTarget, some widenedTarget,
      some preciseCaller, some widenedCaller,
      some preciseConstructor, some widenedConstructor =>
      preciseTarget.cacheKey == widenedTarget.cacheKey &&
        preciseTarget.address != widenedTarget.address &&
        preciseCaller.cacheKey != widenedCaller.cacheKey &&
        preciseCaller.dependencies.contains preciseTarget.address &&
        widenedCaller.dependencies.contains widenedTarget.address &&
        preciseConstructor.cacheKey == widenedConstructor.cacheKey &&
        preciseConstructor.address == widenedConstructor.address &&
        preciseResult.artifacts.filter (fun artifact =>
          artifact.kind == .mutual) ==
          widenedResult.artifacts.filter (fun artifact =>
            artifact.kind == .mutual)
  | _, _, _, _, _, _ => false

def cacheBytes (store : IxIR1.HPT.Cache.Store) : Nat :=
  store.entries.foldl (fun total entry => total + entry.2.size) 0

def cacheMaxEntryBytes (store : IxIR1.HPT.Cache.Store) : Nat :=
  store.entries.foldl (fun largest entry => max largest entry.2.size) 0

def cacheIsError {ε α : Type} : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

def cacheCodecOk (analysis : IxIR1.HPT.Result) : Bool :=
  analysis.artifacts.all fun artifact =>
    match IxIR1.HPT.Cache.decodeArtifact
        (IxIR1.HPT.Cache.encodeArtifact artifact) with
    | .ok decoded => decoded == artifact
    | .error _ => false

private def cacheStoreEntryBytes (entry : Address × ByteArray) : ByteArray :=
  IxIR.Encoding.address entry.1 ++ IxIR.Encoding.blob entry.2

def cacheStoreCodecOk (analysis : IxIR1.HPT.Result) : Bool :=
  let store := IxIR1.HPT.Cache.Store.ofResult analysis
  let canonical := store.canonicalize
  let encoded := IxIR1.HPT.Cache.encodeStore store
  let bytes := cacheBytes store
  let limits : IxIR1.HPT.Cache.Limits :=
    { maxEntries := store.entries.length
      maxEntryBytes := cacheMaxEntryBytes store
      maxBytes := bytes
      maxWriteBytes := bytes
      maxStoreBytes := encoded.size }
  let reversedBytes := IxIR1.HPT.Cache.storeDomain ++
    IxIR.Encoding.list cacheStoreEntryBytes canonical.entries.reverse
  match IxIR1.HPT.Cache.prepareStoreWith limits store,
      IxIR1.HPT.Cache.encodeStoreWith limits store,
      IxIR1.HPT.Cache.decodeStoreWith limits encoded with
  | .ok prepared, .ok checkedBytes, .ok decoded =>
      prepared == canonical &&
        prepared.framedSize == encoded.size &&
        checkedBytes == encoded &&
        decoded == canonical &&
        IxIR1.HPT.Cache.encodeStore ⟨store.entries.reverse⟩ == encoded &&
        cacheIsError (IxIR1.HPT.Cache.decodeStoreWith limits
          (encoded ++ ByteArray.mk #[0])) &&
        cacheIsError (IxIR1.HPT.Cache.decodeStoreWith limits reversedBytes) &&
        cacheIsError (IxIR1.HPT.Cache.encodeStoreWith
          { limits with maxEntryBytes := limits.maxEntryBytes - 1 } store) &&
        cacheIsError (IxIR1.HPT.Cache.decodeStoreWith
          { limits with maxStoreBytes := encoded.size - 1 } encoded)
  | _, _, _ => false

/-- Count and coordinate numerals are rejected at their bounded canonical
width, before the generic decoder could construct an oversized `Nat`. -/
def cacheBoundedNumeralOk (analysis : IxIR1.HPT.Result) : Bool :=
  let overlongStoreCount := IxIR1.HPT.Cache.storeDomain ++
    ByteArray.mk #[128, 0]
  let countLimits : IxIR1.HPT.Cache.Limits := { maxEntries := 0 }
  let coordinateLimits : IxIR1.HPT.Cache.Limits :=
    { producer := { checker := { maxShapeIndex := 0 } } }
  cacheIsError (IxIR1.HPT.Cache.decodeStoreWith countLimits
      overlongStoreCount) &&
    match analysis.artifacts with
    | [] => false
    | artifact :: _ =>
        match artifact.members with
        | [] => false
        | member :: members =>
            let fact : IxIR1.HPT.Fact :=
              { mayScalar := false
                unknownHeap := false
                shapes := [.pap member.1 1] }
            let oversized : IxIR1.HPT.Artifact :=
              { artifact with members := (member.1, fact) :: members }
            cacheIsError (IxIR1.HPT.Cache.decodeArtifactWith
              coordinateLimits (IxIR1.HPT.Cache.encodeArtifact oversized))

/-- Cold production, exact warm hits, malformed-record recovery, and a
dependency-cone rekey all cross the persistent-cache scheduler. -/
def persistentCacheOk (program : IxIR1.ReaddressAll.Result)
    (preciseResult widenedResult : IxIR1.HPT.Result) : Bool :=
  let empty : IxIR1.HPT.Cache.Store := ⟨[]⟩
  match IxIR1.HPT.Cache.run program.artifacts empty with
  | .error _ => false
  | .ok cold =>
      let store := cold.completeStore
      let bytes := cacheBytes store
      let target := finalAddress program rawTarget
      let constructor := finalAddress program rawConstructor
      match IxIR1.HPT.Cache.run program.artifacts store,
          findSummary preciseResult target, findSummary widenedResult target,
          findSummary preciseResult constructor with
      | .ok warm, some preciseTarget, some widenedTarget,
          some constructorSummary =>
          let corrupted := store.applyWrites
            [(constructorSummary.cacheKey,
              IxIR1.HPT.Cache.encodeArtifact constructorSummary ++
                ByteArray.mk #[0])]
          let mixed := store.applyWrites
            [(preciseTarget.cacheKey,
              IxIR1.HPT.Cache.encodeArtifact widenedTarget)]
          match IxIR1.HPT.Cache.run program.artifacts corrupted,
              IxIR1.HPT.Cache.run program.artifacts mixed with
          | .ok repaired, .ok mixedRun =>
              let updated := mixed.applyWrites mixedRun.writes
              match IxIR1.HPT.Cache.run program.artifacts updated with
              | .ok rewarmed =>
                  cacheCodecOk preciseResult &&
                    cacheStoreCodecOk preciseResult &&
                    cacheBoundedNumeralOk preciseResult &&
                    cold.certificate == preciseCertificate program &&
                    cold.result == preciseResult &&
                    cold.stats ==
                      { ingressEntries := 0
                        ingressBytes := 0
                        hits := 0
                        misses := 5
                        rejected := 0
                        rounds := 9
                        widenedArtifacts := 0
                        writes := 5
                        writeBytes := bytes } &&
                    empty.applyWrites cold.writes == store &&
                    warm.certificate == preciseCertificate program &&
                    warm.result == preciseResult &&
                    warm.stats ==
                      { ingressEntries := 5
                        ingressBytes := bytes
                        hits := 5
                        misses := 0
                        rejected := 0
                        rounds := 0
                        widenedArtifacts := 0
                        writes := 0
                        writeBytes := 0 } &&
                    repaired.result == preciseResult &&
                    repaired.stats.hits == 4 &&
                    repaired.stats.misses == 1 &&
                    repaired.stats.rejected == 1 &&
                    repaired.stats.writes == 1 &&
                    repaired.rejections.length == 1 &&
                    mixedRun.result == widenedResult &&
                    mixedRun.stats.hits == 4 &&
                    mixedRun.stats.misses == 1 &&
                    mixedRun.stats.rejected == 0 &&
                    mixedRun.stats.writes == 1 &&
                    rewarmed.result == widenedResult &&
                    rewarmed.stats.hits == 5 &&
                    rewarmed.stats.misses == 0 &&
                    rewarmed.stats.rejected == 0
              | .error _ => false
          | _, _ => false
      | _, _, _, _ => false

def persistentCacheBudgetsOk (program : IxIR1.ReaddressAll.Result)
    (analysis : IxIR1.HPT.Result) : Bool :=
  let store := IxIR1.HPT.Cache.Store.ofResult analysis
  let bytes := cacheBytes store
  let largest := cacheMaxEntryBytes store
  let exact : IxIR1.HPT.Cache.Limits :=
    { maxEntries := store.entries.length
      maxEntryBytes := largest
      maxBytes := bytes
      maxWriteBytes := bytes }
  let duplicate := match store.entries with
    | entry :: entries => (⟨entry :: entry :: entries⟩ : IxIR1.HPT.Cache.Store)
    | [] => store
  match IxIR1.HPT.Cache.runWith exact program.artifacts store,
      IxIR1.HPT.Cache.runWith exact program.artifacts ⟨[]⟩ with
  | .ok warm, .ok cold =>
      warm.stats.hits == store.entries.length &&
        warm.stats.misses == 0 &&
        cold.stats.misses == store.entries.length &&
        cold.stats.writeBytes == bytes &&
        cacheIsError (IxIR1.HPT.Cache.runWith
          { exact with maxEntries := store.entries.length - 1 }
          program.artifacts store) &&
        cacheIsError (IxIR1.HPT.Cache.runWith
          { exact with maxBytes := bytes - 1 }
          program.artifacts store) &&
        cacheIsError (IxIR1.HPT.Cache.runWith
          { exact with maxEntryBytes := largest - 1 }
          program.artifacts store) &&
        cacheIsError (IxIR1.HPT.Cache.runWith
          { exact with maxWriteBytes := bytes - 1 }
          program.artifacts ⟨[]⟩) &&
        cacheIsError (IxIR1.HPT.Cache.runWith exact program.artifacts duplicate)
  | _, _ => false

def preciseOk (program : IxIR1.ReaddressAll.Result)
    (analysis : IxIR1.HPT.Result) : Bool :=
  analysis.semanticAudit &&
    analysis.artifacts.length == program.artifacts.length &&
    analysis.cacheKeys.map Address.toHex == expectedCacheKeys &&
    analysis.addresses.map Address.toHex == expectedSummaryAddresses &&
    analysis.artifacts.any (fun artifact =>
      artifact.kind == .mutual && artifact.members.length == 2) &&
    match findSummary analysis (finalAddress program rawConstructor) with
    | some artifact =>
        artifact.members ==
          [(finalAddress program rawConstructor,
            detailedConstructorFact)]
    | none => false

/-- The first field-sensitive HPT slice records the allocated scalar field,
projects it back to a root fact, and agrees with both concrete fixture paths. -/
def fieldSensitiveOk (program : IxIR1.ReaddressAll.Result)
    (analysis : IxIR1.HPT.Result) : Bool :=
  let constructor := finalAddress program rawConstructor
  let cycleRight := finalAddress program rawCycleRight
  let declarations := IxIR1.HPT.programDeclEnv program.artifacts
  let ctx : IxIR1.Ctx := { decls := declarations }
  detailedConstructorFact.exactConstructor? == some constructorId &&
    IxIR1.HPT.Fact.top.exactConstructor? == none &&
    (IxIR1.HPT.Fact.heap (.pap constructor 0)).exactConstructor? == none &&
    detailedConstructorFact.fetch 0 == IxIR1.HPT.Fact.scalar &&
    detailedConstructorFact.fetch 1 == IxIR1.HPT.Fact.bottom &&
    (IxIR1.HPT.Fact.heap (.ctor constructorId none)).fetch 0 ==
      IxIR1.HPT.Fact.top &&
    match findSummary analysis constructor, findSummary analysis cycleRight,
        IxIR1.invoke ctx 16 constructor [] {},
        IxIR1.invoke ctx 32 cycleRight [] {} with
    | some constructorSummary, some cycleSummary,
        .ok (constructorStore, .loc location),
        .ok (_, .lit (.nat 7)) =>
        constructorSummary.members == [(constructor, detailedConstructorFact)] &&
          cycleSummary.members.contains (cycleRight, IxIR1.HPT.Fact.scalar) &&
          match constructorStore.get? location with
          | some box =>
              box.node == .ctorN constructorId #[.lit (.nat 7)]
          | none => false
    | _, _, _, _ => false

/-! Case-binder field recovery fixture.  Keep it separate from the frozen
five-artifact cache graph so improving the transfer does not silently rewrite
the cache identity vectors used above. -/

def rawCaseBinder : Address := Address.replicate 0xde

def caseBinderDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call rawConstructor #[])
      (.case (.var 0) false #[
        .mk 0 1 (.ret (.var 0))])⟩

def caseBinderRawDeclarations : List (Address × IxIR1.Decl) :=
  [(rawCaseBinder, caseBinderDeclaration),
   (rawConstructor, constructorDeclaration)]

def caseBinderRawMain : IxIR1.Code :=
  .letOp (.call rawCaseBinder #[]) (.ret (.var 0))

def caseBinderAddressed : Except String IxIR1.ReaddressAll.Result :=
  IxIR1.ReaddressAll.run [constructorBlock]
    caseBinderRawDeclarations caseBinderRawMain

/-- The checked interpreter and deterministic producer both recover a scalar
result through a constructor case binder.  The local vectors also pin tag
filtering, source-to-de-Bruijn reversal, multi-shape joins, identity-only and
unknown widening, Nat peeling, and alias-forgotten field identities. -/
def caseBinderFieldOk : Bool :=
  let otherIdentity : IxIR1.CtorId := ⟨constructorBlock, 0, 1⟩
  let nestedField := IxIR1.HPT.FieldFact.heap
    (.ctor otherIdentity none)
  let twoFields := IxIR1.HPT.Fact.heap
    (.ctor constructorId
      (some [IxIR1.HPT.FieldFact.scalar, nestedField]))
  let alternateField := IxIR1.HPT.Fact.heap
    (.ctor constructorId (some [nestedField]))
  let joinedFields := detailedConstructorFact.join alternateField
  let joinedExpected := IxIR1.HPT.Fact.scalar.join
    (IxIR1.HPT.Fact.heap (.ctor otherIdentity none))
  let wrongTag := detailedConstructorFact.join
    (IxIR1.HPT.Fact.heap (.ctor otherIdentity none))
  let forgottenField : IxIR1.HPT.FieldFact := ⟨false, true, []⟩
  let forgottenOuter := IxIR1.HPT.Fact.heap
    (.ctor constructorId (some [forgottenField]))
  detailedConstructorFact.caseFields false 0 1 ==
      [IxIR1.HPT.Fact.scalar] &&
    twoFields.caseFields false 0 2 ==
      [IxIR1.HPT.Fact.heap (.ctor otherIdentity none),
       IxIR1.HPT.Fact.scalar] &&
    joinedFields.caseFields false 0 1 == [joinedExpected] &&
    wrongTag.caseFields false 0 1 == [IxIR1.HPT.Fact.scalar] &&
    (IxIR1.HPT.Fact.heap (.ctor constructorId none)).caseFields
      false 0 1 == [IxIR1.HPT.Fact.top] &&
    IxIR1.HPT.Fact.top.caseFields false 0 1 ==
      [IxIR1.HPT.Fact.top] &&
    forgottenOuter.caseFields false 0 1 ==
      [⟨false, true, []⟩] &&
    IxIR1.HPT.Fact.scalar.caseFields true 1 1 ==
      [IxIR1.HPT.Fact.scalar] &&
    match caseBinderAddressed with
    | .error _ => false
    | .ok program =>
        let candidate := preciseCertificate program
        let binder := finalAddress program rawCaseBinder
        let declarations := IxIR1.HPT.programDeclEnv program.artifacts
        let ctx : IxIR1.Ctx := { decls := declarations }
        match IxIR1.HPT.run program.artifacts candidate,
            IxIR1.HPT.produce program.artifacts,
            IxIR1.Env.ofList program.declarations binder,
            IxIR1.invoke ctx 32 binder [] {} with
        | .ok analysis, .ok production, some (.fn function),
            .ok (store, .lit (.nat 7)) =>
            analysis.semanticAudit && production.result.semanticAudit &&
              candidate.summaryEnv binder == some IxIR1.HPT.Fact.scalar &&
              production.certificate.summaryEnv binder ==
                some IxIR1.HPT.Fact.scalar &&
              match IxIR1.HPT.inferFunction declarations
                  candidate.summaryEnv binder function with
              | .ok inferred => inferred == IxIR1.HPT.Fact.scalar &&
                  store.allocs == 1 && store.live == 1
              | .error _ => false
        | _, _, _, _ => false

/-! Recursive field-refinement fixture.  This stays outside the frozen
five-artifact cache graph above while exercising the complete depth-two path:
allocation, projection, case binders, producer widening, and cache ingress. -/

def rawDeepConstructor : Address := Address.replicate 0xe1
def rawDeepFetch : Address := Address.replicate 0xe2
def rawDeepCase : Address := Address.replicate 0xe3

def deepInnerId : IxIR1.CtorId := ⟨constructorBlock, 0, 0⟩
def deepOuterId : IxIR1.CtorId := ⟨constructorBlock, 0, 1⟩

def deepConstructorDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.alloc .shared deepInnerId #[.lit (.nat 11)])
      (.letOp (.alloc .shared deepOuterId #[.var 0])
        (.ret (.var 0)))⟩

def deepFetchDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call rawDeepConstructor #[])
      (.letOp (.fetch (.var 0) 0)
        (.letOp (.fetch (.var 0) 0)
          (.ret (.var 0))))⟩

def deepCaseDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call rawDeepConstructor #[])
      (.case (.var 0) false #[
        .mk 1 1
          (.case (.var 0) false #[
            .mk 0 1 (.ret (.var 0))])])⟩

def deepRawDeclarations : List (Address × IxIR1.Decl) :=
  [(rawDeepFetch, deepFetchDeclaration),
   (rawDeepCase, deepCaseDeclaration),
   (rawDeepConstructor, deepConstructorDeclaration)]

def deepRawMain : IxIR1.Code :=
  .letOp (.call rawDeepCase #[]) (.ret (.var 0))

def deepAddressed : Except String IxIR1.ReaddressAll.Result :=
  IxIR1.ReaddressAll.run [constructorBlock] deepRawDeclarations deepRawMain

def deepInnerFact : IxIR1.HPT.Fact :=
  IxIR1.HPT.Fact.heap
    (.ctor deepInnerId (some [IxIR1.HPT.FieldFact.scalar]))

def deepConstructorFact : IxIR1.HPT.Fact :=
  IxIR1.HPT.Fact.heap
    (.ctor deepOuterId
      (some [IxIR1.HPT.FieldFact.heap
        (.ctor deepInnerId (some [IxIR1.HPT.FieldFact.scalar]))]))

/-- Recursive facts survive both transfer paths and strict cache decoding.
The checker admits depth two exactly and rejects depth one; the deterministic
producer shares that boundary and falls back conservatively when configured
one level below it. -/
def recursiveFieldOk : Bool :=
  deepConstructorFact.fetch 0 == deepInnerFact &&
    (deepConstructorFact.fetch 0).fetch 0 == IxIR1.HPT.Fact.scalar &&
    deepConstructorFact.caseFields false 1 1 == [deepInnerFact] &&
    deepInnerFact.caseFields false 0 1 == [IxIR1.HPT.Fact.scalar] &&
    match deepAddressed with
    | .error _ => false
    | .ok program =>
        let constructor := finalAddress program rawDeepConstructor
        let fetch := finalAddress program rawDeepFetch
        let deepCase := finalAddress program rawDeepCase
        let declarations := IxIR1.HPT.programDeclEnv program.artifacts
        let ctx : IxIR1.Ctx := { decls := declarations }
        let exactChecker :=
          { IxIR1.HPT.defaultLimits with maxFieldDepth := 2 }
        let shallowChecker :=
          { IxIR1.HPT.defaultLimits with maxFieldDepth := 1 }
        let shallowProducer : IxIR1.HPT.ProducerLimits :=
          { checker := shallowChecker }
        let exactCache : IxIR1.HPT.Cache.Limits :=
          { producer := { checker := exactChecker } }
        let shallowCache : IxIR1.HPT.Cache.Limits :=
          { producer := { checker := shallowChecker } }
        match IxIR1.HPT.produce program.artifacts,
            IxIR1.HPT.produceWith shallowProducer program.artifacts,
            IxIR1.invoke ctx 64 fetch [] {},
            IxIR1.invoke ctx 64 deepCase [] {} with
        | .ok production, .ok widened,
            .ok (fetchStore, .lit (.nat 11)),
            .ok (caseStore, .lit (.nat 11)) =>
            match findSummary production.result constructor,
                IxIR1.HPT.preflight exactChecker program.artifacts
                  production.certificate,
                IxIR1.HPT.runWith exactChecker program.artifacts
                  production.certificate with
            | some constructorSummary, .ok stats, .ok checked =>
                let encoded :=
                  IxIR1.HPT.Cache.encodeArtifact constructorSummary
                match IxIR1.HPT.Cache.decodeArtifactWith exactCache encoded with
                | .ok decoded =>
                    production.result.semanticAudit &&
                      checked == production.result &&
                      production.certificate.summaryEnv constructor ==
                        some deepConstructorFact &&
                      production.certificate.summaryEnv fetch ==
                        some IxIR1.HPT.Fact.scalar &&
                      production.certificate.summaryEnv deepCase ==
                        some IxIR1.HPT.Fact.scalar &&
                      stats.shapes == 2 && stats.fields == 2 &&
                      stats.fieldDepth == 2 &&
                      fetchStore.allocs == 2 && fetchStore.live == 2 &&
                      caseStore.allocs == 2 && caseStore.live == 2 &&
                      cacheCodecOk production.result &&
                      cacheStoreCodecOk production.result &&
                      decoded == constructorSummary &&
                      cacheIsError
                        (IxIR1.HPT.preflight shallowChecker program.artifacts
                          production.certificate) &&
                      cacheIsError
                        (IxIR1.HPT.runWith shallowChecker program.artifacts
                          production.certificate) &&
                      cacheIsError
                        (IxIR1.HPT.Cache.decodeArtifactWith shallowCache encoded) &&
                      widened.certificate.postFixpoint program.artifacts &&
                      widened.result.semanticAudit &&
                      widened.stats.widenedArtifacts != 0
                | .error _ => false
            | _, _, _ => false
        | _, _, _, _ => false

/-- A non-degenerate root redex for the first checked HPT consumer.  The
called function can only return constructor index zero; the second alternative
is therefore unreachable under the precise certificate. -/
def casePruneInput (program : IxIR1.ReaddressAll.Result) : IxIR1.Code :=
  .letOp (.call (finalAddress program rawConstructor) #[])
    (.case (.var 0) false #[
      .mk 0 1 (.ret (.lit (.nat 41))),
      .mk 1 0 (.ret (.lit (.nat 99)))])

private def rootCallCaseIndices : IxIR1.Code → Option (List Nat)
  | .letOp (.call _ _) (.case (.var 0) _ alternatives) =>
      some (alternatives.toList.map (fun alternative => alternative.cidx))
  | _ => none

private def rootCallHasUnaryFetch : IxIR1.Code → Bool
  | .letOp (.call _ _)
      (.letOp (.fetch (.var 0) 0) _) => true
  | _ => false

private def casePruneExecutionOk :
    Except IxIR1.Err (IxIR1.Store × IxIR1.RVal) → Bool
  | .ok (store, .lit (.nat 41)) =>
      store.nodes.size == 1 && store.allocs == 1 && store.reuses == 0 &&
        store.frees == 0 && store.rcops == 0 && store.live == 1 &&
        match store.get? 0 with
        | some box =>
            box.world == .shared && box.rc == 1 &&
              box.node == .ctorN constructorId #[.lit (.nat 7)]
        | none => false
  | _ => false

/-- The precise checked row removes one impossible constructor branch,
collapses the remaining unary case to a checked fetch, and preserves concrete
execution. Conservative facts and duplicate matches remain pruning-only. -/
def casePruneOk (program : IxIR1.ReaddressAll.Result) : Bool :=
  let preciseCandidate := preciseCertificate program
  let topCandidate := IxIR1.HPT.Certificate.top program.artifacts
  match IxIR1.HPT.run program.artifacts preciseCandidate,
      IxIR1.HPT.run program.artifacts topCandidate with
  | .ok preciseAnalysis, .ok topAnalysis =>
      let declarations := IxIR1.HPT.programDeclEnv program.artifacts
      let input := casePruneInput program
      let pruned := IxIR1.HPT.CasePrune.run declarations
        preciseCandidate.summaryEnv input
      let conservative := IxIR1.HPT.CasePrune.run declarations
        topCandidate.summaryEnv input
      let constructor := finalAddress program rawConstructor
      let identityOnlyFact :=
        IxIR1.HPT.Fact.heap (.ctor constructorId none)
      let exactUnaryFact :=
        IxIR1.HPT.Fact.heap
          (.ctor constructorId (some [IxIR1.HPT.FieldFact.scalar]))
      let nullaryFact :=
        IxIR1.HPT.Fact.heap (.ctor constructorId (some []))
      let binaryFact :=
        IxIR1.HPT.Fact.heap
          (.ctor constructorId
            (some [IxIR1.HPT.FieldFact.scalar,
              IxIR1.HPT.FieldFact.scalar]))
      let identityOnlySummary : IxIR1.HPT.SummaryEnv := fun address =>
        if address == constructor then some identityOnlyFact else none
      let exactUnarySummary : IxIR1.HPT.SummaryEnv := fun address =>
        if address == constructor then some exactUnaryFact else none
      let identityOnly := IxIR1.HPT.CasePrune.run declarations
        identityOnlySummary input
      let singletonInput : IxIR1.Code :=
        .letOp (.call constructor #[])
          (.case (.var 0) false #[
            .mk 0 1 (.ret (.lit (.nat 41)))])
      let singleton := IxIR1.HPT.CasePrune.run declarations
        exactUnarySummary singletonInput
      let duplicateInput : IxIR1.Code :=
        .letOp (.call constructor #[])
          (.case (.var 0) false #[
            .mk 0 1 (.ret (.lit (.nat 41))),
            .mk 0 1 (.ret (.lit (.nat 42))),
            .mk 1 0 (.ret (.lit (.nat 99)))])
      let duplicate := IxIR1.HPT.CasePrune.run declarations
        exactUnarySummary duplicateInput
      let ctx : IxIR1.Ctx := { decls := declarations }
      -- `runCode_run_eq` deliberately holds the current frame fixed; this
      -- fixture contains no `callSelf`, so that boundary is explicit here.
      let current : IxIR1.FnDef := ⟨0, .shared, false, input⟩
      preciseAnalysis.semanticAudit && topAnalysis.semanticAudit &&
        pruned.removedAlternatives == 1 &&
        pruned.collapsedCases == 1 &&
        pruned.materializedFetches == 1 &&
        conservative.removedAlternatives == 0 &&
        conservative.collapsedCases == 0 &&
        conservative.materializedFetches == 0 &&
        rootCallCaseIndices input == some [0, 1] &&
        rootCallHasUnaryFetch pruned.code &&
        rootCallCaseIndices conservative.code == some [0, 1] &&
        identityOnly.removedAlternatives == 1 &&
        identityOnly.collapsedCases == 0 &&
        identityOnly.materializedFetches == 0 &&
        rootCallCaseIndices identityOnly.code == some [0] &&
        singleton.removedAlternatives == 0 &&
        singleton.collapsedCases == 1 &&
        singleton.materializedFetches == 1 &&
        rootCallHasUnaryFetch singleton.code &&
        duplicate.removedAlternatives == 1 &&
        duplicate.collapsedCases == 0 &&
        duplicate.materializedFetches == 0 &&
        rootCallCaseIndices duplicate.code == some [0, 0] &&
        IxIR1.HPT.CasePrune.exactUnaryConstructor? exactUnaryFact ==
          some constructorId &&
        IxIR1.HPT.CasePrune.exactUnaryConstructor? identityOnlyFact == none &&
        IxIR1.HPT.CasePrune.exactUnaryConstructor? nullaryFact == none &&
        IxIR1.HPT.CasePrune.exactUnaryConstructor? binaryFact == none &&
        casePruneExecutionOk
          (IxIR1.runCode ctx 64 current {} [] input) &&
        casePruneExecutionOk
          (IxIR1.runCode ctx 64 current {} [] pruned.code)
  | _, _ => false

/-- Two eligible redexes nested in separate case alternatives.  Only the
first alternative executes, while structural checks ensure traversal reaches
both bodies. -/
def recursiveCasePruneInput
    (program : IxIR1.ReaddressAll.Result) : IxIR1.Code :=
  .case (.lit (.nat 0)) true #[
    .mk 0 0 (casePruneInput program),
    .mk 1 1 (casePruneInput program)]

private def alternativeRootCallCaseIndices : IxIR1.Alt → Option (List Nat)
  | .mk _ _ body => rootCallCaseIndices body

private def caseAlternativeRootIndices : IxIR1.Code →
    Option (List (Option (List Nat)))
  | .case _ _ alternatives =>
      some (alternatives.toList.map alternativeRootCallCaseIndices)
  | _ => none

private def alternativeRootCallHasUnaryFetch : IxIR1.Alt → Bool
  | .mk _ _ body => rootCallHasUnaryFetch body

private def caseAlternativeRootUnaryFetches : IxIR1.Code →
    Option (List Bool)
  | .case _ _ alternatives =>
      some (alternatives.toList.map alternativeRootCallHasUnaryFetch)
  | _ => none

/-- Recursive simplification reaches every alternative body, sums all pass
counters, preserves concrete execution, and remains conservative for a
checked top certificate. The one-root API leaves this input untouched. -/
def recursiveCasePruneOk (program : IxIR1.ReaddressAll.Result) : Bool :=
  let preciseCandidate := preciseCertificate program
  let topCandidate := IxIR1.HPT.Certificate.top program.artifacts
  match IxIR1.HPT.run program.artifacts preciseCandidate,
      IxIR1.HPT.run program.artifacts topCandidate with
  | .ok preciseAnalysis, .ok topAnalysis =>
      let declarations := IxIR1.HPT.programDeclEnv program.artifacts
      let input := recursiveCasePruneInput program
      let rootOnly := IxIR1.HPT.CasePrune.run declarations
        preciseCandidate.summaryEnv input
      let pruned := IxIR1.HPT.CasePrune.runRecursive declarations
        preciseCandidate.summaryEnv input
      let conservative := IxIR1.HPT.CasePrune.runRecursive declarations
        topCandidate.summaryEnv input
      let ctx : IxIR1.Ctx := { decls := declarations }
      let current : IxIR1.FnDef := ⟨0, .shared, false, input⟩
      preciseAnalysis.semanticAudit && topAnalysis.semanticAudit &&
        rootOnly.removedAlternatives == 0 &&
        rootOnly.collapsedCases == 0 &&
        rootOnly.materializedFetches == 0 &&
        pruned.removedAlternatives == 2 &&
        pruned.collapsedCases == 2 &&
        pruned.materializedFetches == 2 &&
        conservative.removedAlternatives == 0 &&
        conservative.collapsedCases == 0 &&
        conservative.materializedFetches == 0 &&
        caseAlternativeRootIndices rootOnly.code ==
          some [some [0, 1], some [0, 1]] &&
        caseAlternativeRootIndices pruned.code ==
          some [none, none] &&
        caseAlternativeRootUnaryFetches pruned.code == some [true, true] &&
        caseAlternativeRootIndices conservative.code ==
          some [some [0, 1], some [0, 1]] &&
        casePruneExecutionOk
          (IxIR1.runCode ctx 64 current {} [] input) &&
        casePruneExecutionOk
          (IxIR1.runCode ctx 64 current {} [] pruned.code)
  | _, _ => false

/-- A one-argument current body recursively peels a Nat with `callSelf`; its
zero branch contains the checked call-result case redex. -/
def callSelfCasePruneInput
    (program : IxIR1.ReaddressAll.Result) : IxIR1.Code :=
  .case (.var 0) true #[
    .mk 0 0 (casePruneInput program),
    .mk 1 1
      (.letOp (.callSelf #[.var 0])
        (.ret (.var 0)))]

/-- Rewriting both the supplied body and the dynamic current frame preserves
a terminating recursive execution.  Three self calls reach the rewritten
zero branch, whose impossible constructor alternative is absent. -/
def callSelfCasePruneOk (program : IxIR1.ReaddressAll.Result) : Bool :=
  let candidate := preciseCertificate program
  match IxIR1.HPT.run program.artifacts candidate with
  | .error _ => false
  | .ok analysis =>
      let declarations := IxIR1.HPT.programDeclEnv program.artifacts
      let input := callSelfCasePruneInput program
      let pruned := IxIR1.HPT.CasePrune.runRecursive declarations
        candidate.summaryEnv input
      let current : IxIR1.FnDef := ⟨1, .shared, false, input⟩
      let rewritten := IxIR1.HPT.CasePrune.rewriteCurrent declarations
        candidate.summaryEnv current
      let ctx : IxIR1.Ctx := { decls := declarations }
      analysis.semanticAudit &&
        pruned.removedAlternatives == 1 &&
        pruned.collapsedCases == 1 &&
        pruned.materializedFetches == 1 &&
        caseAlternativeRootIndices input == some [some [0, 1], none] &&
        caseAlternativeRootIndices pruned.code == some [none, none] &&
        caseAlternativeRootUnaryFetches pruned.code == some [true, false] &&
        caseAlternativeRootIndices rewritten.body == some [none, none] &&
        caseAlternativeRootUnaryFetches rewritten.body == some [true, false] &&
        casePruneExecutionOk
          (IxIR1.runCode ctx 128 current {} [.lit (.nat 3)] input) &&
        casePruneExecutionOk
          (IxIR1.runCode ctx 128 rewritten {} [.lit (.nat 3)] pruned.code)

/-- A zero-argument artifact main that dynamically re-enters itself after the
eligible redex. Finite evaluator fuel makes the observable result exact and
bounded. -/
def callSelfMainPruneInput
    (program : IxIR1.ReaddressAll.Result) : IxIR1.Code :=
  .letOp (.call (finalAddress program rawConstructor) #[])
    (.case (.var 0) false #[
      .mk 0 1
        (.letOp (.callSelf #[])
          (.ret (.var 0))),
      .mk 1 0 (.ret (.lit (.nat 99)))])

private def artifactWithMain (program : IxIR1.ReaddressAll.Result)
    (main : IxIR1.Code) : Pipeline.Artifact :=
  { rawErasedDecls := []
    erasedDecls := []
    erasedBlocks := []
    erasedAddressMap := []
    targetArtifacts := program.artifacts
    main := main
    targetAddressMap := program.addressMap }

private def isFuelError : Except IxIR1.Err (IxIR1.Store × IxIR1.RVal) → Bool
  | .error .fuel => true
  | _ => false

/-- The checked pipeline main API simplifies the artifact main and preserves
an actual zero-argument `callSelf` loop's exact finite-fuel error. -/
def pipelineCallSelfMainPruneOk
    (program : IxIR1.ReaddressAll.Result) : Bool :=
  let input := callSelfMainPruneInput program
  let artifact := artifactWithMain program input
  let candidate := preciseCertificate program
  match artifact.checkAndPruneMain candidate with
  | .error _ => false
  | .ok (analysis, pruned) =>
      let ctx : IxIR1.Ctx := { decls := artifact.targetDeclEnv }
      analysis.semanticAudit &&
        pruned.removedAlternatives == 1 &&
        pruned.collapsedCases == 1 &&
        pruned.materializedFetches == 1 &&
        rootCallCaseIndices input == some [0, 1] &&
        rootCallHasUnaryFetch pruned.code &&
        isFuelError (IxIR1.runMain ctx input 64) &&
        isFuelError (IxIR1.runMain ctx pruned.code 64)

/-! Complete declaration-graph consumer fixture. -/

def graphRawCaller : Address := Address.replicate 0xdb

def graphCallerBody : IxIR1.Code :=
  .letOp (.call rawConstructor #[])
    (.letOp (.pure (.var 0))
      (.case (.var 0) false #[
        .mk 0 1 (.ret (.lit (.nat 41))),
        .mk 1 0 (.ret (.lit (.nat 99))) ]))

def graphCallerDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true, graphCallerBody⟩

def graphRawDeclarations : List (Address × IxIR1.Decl) :=
  [(graphRawCaller, graphCallerDeclaration),
   (rawConstructor, constructorDeclaration)]

def graphRawMain : IxIR1.Code :=
  .letOp (.call graphRawCaller #[]) (.ret (.var 0))

private def rootCallTarget : IxIR1.Code → Option Address
  | .letOp (.call function _) _ => some function
  | _ => none

private def rootCallAliasHasUnaryFetch : IxIR1.Code → Bool
  | .letOp (.call _ _)
      (.letOp (.pure (.var 0))
        (.letOp (.fetch (.var 0) 0) _)) => true
  | _ => false

/-- Complete checked simplification propagates a call fact through an alias,
rewrites the stored function body, changes its content address, rewrites the
main edge, preserves execution, and composes the pipeline's original producer
map through the rebuild. -/
def declarationGraphCasePruneOk : Bool :=
  match IxIR1.ReaddressAll.run [constructorBlock]
      graphRawDeclarations graphRawMain with
  | .error _ => false
  | .ok program =>
      let artifact := artifactWithMain program program.main
      let candidate := preciseCertificate program
      match artifact.checkAndPruneProgram candidate with
      | .error _ => false
      | .ok (analysis, outcome) =>
          let oldCaller := finalAddress program graphRawCaller
          let newCaller := IxIR1.Readdress.Renaming.apply
            outcome.result.addressMap oldCaller
          let installed := artifact.installPrunedProgram outcome
          let oldCtx : IxIR1.Ctx := { decls := artifact.targetDeclEnv }
          let newCtx := outcome.result.addressedCtx (fun _ _ => none)
          analysis.semanticAudit &&
            outcome.removedAlternatives == 1 &&
            outcome.collapsedCases == 1 &&
            outcome.materializedFetches == 1 &&
            oldCaller != newCaller &&
            outcome.result.semanticAudit
              (artifact.prunedTargetEntries candidate.summaryEnv)
              (IxIR1.HPT.CasePrune.runRecursive artifact.targetDeclEnv
                candidate.summaryEnv artifact.main).code &&
            outcome.result.rebuildSemanticAudit
              (artifact.prunedTargetEntries candidate.summaryEnv)
              (IxIR1.HPT.CasePrune.runRecursive artifact.targetDeclEnv
                candidate.summaryEnv artifact.main).code &&
            outcome.result.contentAddressed &&
            outcome.result.noTransientKeys &&
            outcome.result.noTransientReferences &&
            rootCallTarget outcome.result.main == some newCaller &&
            IxIR1.Readdress.Renaming.apply installed.targetAddressMap
              graphRawCaller == newCaller &&
            match IxIR1.Env.ofList outcome.result.declarations newCaller with
            | some (.fn function) =>
                rootCallAliasHasUnaryFetch function.body &&
                  casePruneExecutionOk
                    (IxIR1.runMain oldCtx artifact.main 64) &&
                  casePruneExecutionOk
                    (IxIR1.runMain newCtx outcome.result.main 64)
            | _ => false

/-- The optimizer harness observes a non-degenerate whole-program rewrite,
composes the rebuilt addresses into the pipeline artifact, reproduces the same
report on an independent run, skips deterministically under explicit controls,
and reaches a structural fixed point after recomputing HPT on the new root. -/
def optimizerHarnessOk : Bool :=
  match IxIR1.ReaddressAll.run [constructorBlock]
      graphRawDeclarations graphRawMain with
  | .error _ => false
  | .ok program =>
      let artifact := artifactWithMain program program.main
      match artifact.produceHPT with
      | .error _ => false
      | .ok production =>
          let (firstArtifact, firstReport) :=
            artifact.optimizeWithProducedHPT
              IxIR1.Optimizer.defaultPolicy production
          let (repeatArtifact, repeatReport) :=
            artifact.optimizeWithProducedHPT
              IxIR1.Optimizer.defaultPolicy production
          let disabledPolicy : IxIR1.Optimizer.Policy :=
            { casePrune := { enabled := false }
              fetchForward := { enabled := false }
              destruction := { enabled := false }
              papFuse := { enabled := false }
              reachability := { enabled := false } }
          let disabled := IxIR1.Optimizer.runWithProducedHPT disabledPolicy
            artifact.targetArtifacts artifact.main production
          let budgetPolicy : IxIR1.Optimizer.Policy :=
            { casePrune :=
                { budget := { maxInputInstructions := 0 } } }
          let budgeted := IxIR1.Optimizer.runWithProducedHPT budgetPolicy
            artifact.targetArtifacts artifact.main production
          let newCaller := IxIR1.Readdress.Renaming.apply
            firstArtifact.targetAddressMap graphRawCaller
          let firstRoot := IxIR1.Optimizer.graphRoot
            firstArtifact.targetArtifacts firstArtifact.main
          let repeatRoot := IxIR1.Optimizer.graphRoot
            repeatArtifact.targetArtifacts repeatArtifact.main
          let firstChecks :=
            firstReport.disposition == .changed &&
              firstReport.removedAlternatives == 1 &&
              firstReport.collapsedCases == 1 &&
              firstReport.materializedFetches == 1 &&
              firstReport.forwardedFetches == 0 &&
              firstReport.removedDeclarations == 0 &&
              firstReport.inputRoot != firstReport.outputRoot &&
              firstReport.outputRoot == firstRoot &&
              firstReport.before.counts.alternatives ==
                firstReport.after.counts.alternatives + 2 &&
              firstReport.before.counts.cases ==
                firstReport.after.counts.cases + 1 &&
              firstReport.after.counts.fetches ==
                firstReport.before.counts.fetches + 1 &&
              firstReport.after.codeBytes < firstReport.before.codeBytes &&
              firstReport.after == IxIR1.Optimizer.observe
                firstArtifact.targetArtifacts firstArtifact.main &&
              firstRoot == repeatRoot &&
              firstReport.bytes == repeatReport.bytes &&
              firstReport.address == repeatReport.address &&
              rootCallTarget firstArtifact.main == some newCaller &&
              (match firstArtifact.targetDeclEnv newCaller with
               | some (.fn function) =>
                   rootCallAliasHasUnaryFetch function.body
               | _ => false) &&
              disabled.rebuilt.isNone &&
              disabled.report.disposition ==
                .skipped IxIR1.Optimizer.SkipReason.disabled &&
              disabled.report.inputRoot == disabled.report.outputRoot &&
              budgeted.rebuilt.isNone &&
              budgeted.report.disposition ==
                .skipped (.instructionBudget
                  firstReport.before.counts.instructions 0)
          firstChecks &&
            match firstArtifact.produceHPT with
            | .error _ => false
            | .ok secondProduction =>
                let (secondArtifact, secondReport) :=
                  firstArtifact.optimizeWithProducedHPT
                    IxIR1.Optimizer.defaultPolicy secondProduction
                secondReport.disposition == .unchanged &&
                  secondReport.removedAlternatives == 0 &&
                  secondReport.collapsedCases == 0 &&
                  secondReport.materializedFetches == 0 &&
                  secondReport.forwardedFetches == 0 &&
                  secondReport.removedDeclarations == 0 &&
                  secondReport.inputRoot == firstReport.outputRoot &&
                  secondReport.outputRoot == firstReport.outputRoot &&
                  secondReport.before == secondReport.after &&
                  IxIR1.Optimizer.graphRoot secondArtifact.targetArtifacts
                    secondArtifact.main == firstReport.outputRoot

/-! Checked rooted declaration reachability fixture. -/

def reachRawLeaf : Address := Address.replicate 0xf1
def reachRawMiddle : Address := Address.replicate 0xf2
def reachRawDeadLeft : Address := Address.replicate 0xf3
def reachRawDeadRight : Address := Address.replicate 0xf4

def reachLeafDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true, .ret (.lit (.nat 42))⟩

def reachMiddleDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call reachRawLeaf #[]) (.ret (.var 0))⟩

def reachDeadLeftDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call reachRawDeadRight #[]) (.ret (.var 0))⟩

def reachDeadRightDeclaration : IxIR1.Decl :=
  .fn ⟨0, .shared, true,
    .letOp (.call reachRawDeadLeft #[]) (.ret (.var 0))⟩

def reachRawDeclarations : List (Address × IxIR1.Decl) :=
  [(reachRawMiddle, reachMiddleDeclaration),
   (reachRawLeaf, reachLeafDeclaration),
   (reachRawDeadLeft, reachDeadLeftDeclaration),
   (reachRawDeadRight, reachDeadRightDeclaration)]

def reachRawMain : IxIR1.Code :=
  .letOp (.call reachRawMiddle #[]) (.ret (.var 0))

private def isReachabilityResult :
    Except IxIR1.Err (IxIR1.Store × IxIR1.RVal) → Bool
  | .ok (store, .lit (.nat 42)) => store.live == 0
  | _ => false

/-- The untrusted producer and small checker agree on a direct-call closure,
retain a rooted SCC as a unit, follow PAP edges, and fall back to the complete
world for dynamic apply or an invalid configured root.  Stale identities,
root substitution, and a canonical-but-not-closed retained set are rejected;
filtering preserves the concrete result. -/
def reachabilityCertificateOk : Bool :=
  match IxIR1.ReaddressAll.run [] reachRawDeclarations reachRawMain with
  | .error _ => false
  | .ok program =>
      let entries := program.declarations
      let leaf := finalAddress program reachRawLeaf
      let middle := finalAddress program reachRawMiddle
      let deadLeft := finalAddress program reachRawDeadLeft
      let deadRight := finalAddress program reachRawDeadRight
      let outcome := IxIR1.Reachability.run [] entries program.main
      let rooted := IxIR1.Reachability.run [deadLeft] entries program.main
      let papMain : IxIR1.Code :=
        .letOp (.papp leaf #[]) (.ret (.var 0))
      let pap := IxIR1.Reachability.run [] entries papMain
      let applyMain : IxIR1.Code :=
        .letOp (.papp leaf #[])
          (.letOp (.apply (.var 0) #[]) (.ret (.var 0)))
      let dynamic := IxIR1.Reachability.run [] entries applyMain
      let absent := Address.replicate 0xf5
      let invalidRoot := IxIR1.Reachability.run [absent] entries program.main
      let stale : IxIR1.Reachability.Certificate :=
        { outcome.certificate with inputRoot := Address.replicate 0xf6 }
      let notClosed : IxIR1.Reachability.Certificate :=
        { outcome.certificate with
          retained := (entries.map (fun entry => entry.1)).filter
            (fun address => address != leaf) }
      let entryKeys := entries.map (fun entry => entry.1)
      let retainedKeys := outcome.entries.map (fun entry => entry.1)
      let oldCtx : IxIR1.Ctx := { decls := IxIR1.Env.ofList entries }
      let filteredCtx : IxIR1.Ctx :=
        { decls := IxIR1.Env.ofList outcome.entries }
      outcome.accepted && outcome.removedDeclarations == 2 &&
        outcome.entries.length == 2 && retainedKeys.contains middle &&
        retainedKeys.contains leaf && !retainedKeys.contains deadLeft &&
        !retainedKeys.contains deadRight &&
        rooted.accepted && rooted.removedDeclarations == 0 &&
        rooted.entries.map (fun entry => entry.1) == entryKeys && pap.accepted &&
        pap.certificate.retained.contains leaf &&
        pap.removedDeclarations == 3 && dynamic.accepted &&
        dynamic.removedDeclarations == 0 &&
        dynamic.entries.map (fun entry => entry.1) == entryKeys &&
        !invalidRoot.accepted &&
        invalidRoot.entries.map (fun entry => entry.1) == entryKeys &&
        !IxIR1.Reachability.validate entries program.main [] stale &&
        !IxIR1.Reachability.validate entries program.main [deadLeft]
          outcome.certificate &&
        !IxIR1.Reachability.validate entries program.main [] notClosed &&
        (match IxIR1.Reachability.check entries program.main []
            outcome.certificate with
         | .ok _ => true
         | .error _ => false) &&
        isReachabilityResult (IxIR1.runMain oldCtx program.main 64) &&
        isReachabilityResult (IxIR1.runMain filteredCtx program.main 64)

/-- The public optimizer removes the unreachable mutual component before its
single rebuild, reports the exact declaration delta, preserves execution and
content addressing, honors an exported root, and rejects an unsupported pass
schema fail-softly. -/
def reachabilityHarnessOk : Bool :=
  match IxIR1.ReaddressAll.run [] reachRawDeclarations reachRawMain with
  | .error _ => false
  | .ok program =>
      let artifact := artifactWithMain program program.main
      match artifact.produceHPT with
      | .error _ => false
      | .ok production =>
          let outcome := IxIR1.Optimizer.runWithProducedHPT
            IxIR1.Optimizer.defaultPolicy program.artifacts program.main
            production
          let deadLeft := finalAddress program reachRawDeadLeft
          let rootedPolicy : IxIR1.Optimizer.Policy :=
            { reachability := { roots := [deadLeft] } }
          let rooted := IxIR1.Optimizer.runWithProducedHPT rootedPolicy
            program.artifacts program.main production
          let unsupportedPolicy : IxIR1.Optimizer.Policy :=
            { reachability := { version := 0 } }
          let unsupported := IxIR1.Optimizer.runWithProducedHPT
            unsupportedPolicy program.artifacts program.main production
          let oldCtx : IxIR1.Ctx :=
            { decls := IxIR1.HPT.programDeclEnv program.artifacts }
          outcome.report.disposition == .changed &&
            outcome.report.removedDeclarations == 2 &&
            outcome.report.before.functions == 4 &&
            outcome.report.after.functions == 2 &&
            (match outcome.rebuilt with
             | none => false
             | some result =>
                 result.declarations.length == 2 &&
                   result.contentAddressed && result.noTransientKeys &&
                   result.noTransientReferences &&
                   isReachabilityResult
                     (IxIR1.runMain oldCtx program.main 64) &&
                   isReachabilityResult
                     (IxIR1.runMain
                       (result.addressedCtx (fun _ _ => none)) result.main 64)) &&
            rooted.report.removedDeclarations == 0 &&
            rooted.report.after.functions == 4 &&
            unsupported.rebuilt.isNone &&
            unsupported.report.disposition ==
              .skipped (.unsupportedReachabilityVersion 0
                IxIR1.Optimizer.currentReachabilityVersion)

/-! Local PAP/application fusion fixture. -/

def papRawScalarTarget : Address := Address.replicate 0xe0
def papRawMaker : Address := Address.replicate 0xe1
def papRawUnary : Address := Address.replicate 0xe2

def papScalarTargetDeclaration : IxIR1.Decl :=
  .fn ⟨2, .shared, true, .ret (.lit (.nat 42))⟩

def papUnaryDeclaration : IxIR1.Decl :=
  .fn ⟨1, .shared, true, .ret (.lit (.nat 99))⟩

def papMakerDeclaration : IxIR1.Decl :=
  .fn ⟨2, .shared, true,
    .letOp (.papp papRawUnary #[]) (.ret (.var 0))⟩

def papFusionRawDeclarations : List (Address × IxIR1.Decl) :=
  [(papRawScalarTarget, papScalarTargetDeclaration),
   (papRawMaker, papMakerDeclaration),
   (papRawUnary, papUnaryDeclaration)]

/-- The first pair remains under-saturated and is explicitly released; the
second saturates exactly; the third over-saturates a function which returns a
unary PAP.  Literal captures make the scalar certificate independent of the
entry environment. -/
def papFusionRawMain : IxIR1.Code :=
  .letOp (.papp papRawScalarTarget #[.lit (.nat 10)])
    (.letOp (.apply (.var 0) #[])
      (.letOp (.drop (.var 0))
        (.letOp (.papp papRawScalarTarget #[.lit (.nat 20)])
          (.letOp (.apply (.var 0) #[.lit (.nat 22)])
            (.letOp (.papp papRawMaker #[.lit (.nat 1)])
              (.letOp (.apply (.var 0)
                  #[.lit (.nat 2), .lit (.nat 3)])
                (.ret (.var 0))))))))

private def hasFusedPAPShape : IxIR1.Code → Bool
  | .letOp (.papp _ under)
      (.letOp (.pure (.var 0))
        (.letOp (.drop (.var 0))
          (.letOp (.call _ exact)
            (.letOp (.pure (.var 0))
              (.letOp (.call _ saturated)
                (.letOp (.apply (.var 0) residual) (.ret (.var 0)))))))) =>
      under.size == 1 && exact.size == 2 && saturated.size == 2 &&
        residual.size == 1
  | _ => false

private def isPapFusionResult :
    Except IxIR1.Err (IxIR1.Store × IxIR1.RVal) → Bool
  | .ok (store, .lit (.nat 99)) => store.live == 0
  | _ => false

/-- The versioned harness fuses all saturation classes through one rebuild,
reports the operation delta, preserves the scalar result with no live heap,
rejects every unsupported local shape, and reaches a fixed point after HPT is
recomputed on the rewritten graph. -/
def papFusionHarnessOk : Bool :=
  match IxIR1.ReaddressAll.run [] papFusionRawDeclarations papFusionRawMain with
  | .error _ => false
  | .ok program =>
      let artifact := artifactWithMain program program.main
      match artifact.produceHPT with
      | .error _ => false
      | .ok production =>
          let policy := IxIR1.Optimizer.defaultPolicy
          let (optimized, report) :=
            artifact.optimizeWithProducedHPT policy production
          let oldCtx : IxIR1.Ctx := { decls := artifact.targetDeclEnv }
          let newCtx : IxIR1.Ctx := { decls := optimized.targetDeclEnv }
          let declarations := artifact.targetDeclEnv
          let target := finalAddress program papRawScalarTarget
          let accepted := IxIR1.HPT.PAPFuse.fusePair? declarations [] target
            #[.lit (.nat 1)] #[.lit (.nat 2)] (.ret (.var 0))
          let rejectsHeapCapture :=
            (IxIR1.HPT.PAPFuse.fusePair? declarations [IxIR1.HPT.Fact.top]
              target #[.var 0] #[.lit (.nat 2)] (.ret (.var 0))).isNone
          let rejectsPAPOperand :=
            (IxIR1.HPT.PAPFuse.fusePair? declarations [] target
              #[.lit (.nat 1)] #[.var 0] (.ret (.var 0))).isNone
          let rejectsLiveBinder :=
            (IxIR1.HPT.PAPFuse.fusePair? declarations [] target
              #[.lit (.nat 1)] #[.lit (.nat 2)] (.ret (.var 1))).isNone
          let rejectsSaturatingCapture :=
            (IxIR1.HPT.PAPFuse.fusePair? declarations [] target
              #[.lit (.nat 1), .lit (.nat 2)] #[]
              (.ret (.var 0))).isNone
          report.disposition == .changed &&
            report.removedAlternatives == 0 &&
            report.collapsedCases == 0 &&
            report.materializedFetches == 0 &&
            report.forwardedFetches == 0 &&
            report.fusedPaps == 3 &&
            report.underSaturatedPaps == 1 &&
            report.exactlySaturatedPaps == 1 &&
            report.overSaturatedPaps == 1 &&
            report.before.counts.papAllocations == 4 &&
            report.after.counts.papAllocations == 2 &&
            report.before.counts.applies == 3 &&
            report.after.counts.applies == 1 &&
            report.after.counts.directCalls ==
              report.before.counts.directCalls + 2 &&
            hasFusedPAPShape optimized.main && accepted.isSome &&
            rejectsHeapCapture && rejectsPAPOperand && rejectsLiveBinder &&
            rejectsSaturatingCapture &&
            isPapFusionResult (IxIR1.runMain oldCtx artifact.main 128) &&
            isPapFusionResult (IxIR1.runMain newCtx optimized.main 128) &&
            match optimized.produceHPT with
            | .error _ => false
            | .ok secondProduction =>
                let (fixed, fixedReport) :=
                  optimized.optimizeWithProducedHPT policy secondProduction
                fixedReport.disposition == .unchanged &&
                  fixedReport.forwardedFetches == 0 &&
                  fixedReport.fusedPaps == 0 &&
                  fixedReport.underSaturatedPaps == 0 &&
                  fixedReport.exactlySaturatedPaps == 0 &&
                  fixedReport.overSaturatedPaps == 0 &&
                  fixedReport.inputRoot == report.outputRoot &&
                  fixedReport.outputRoot == report.outputRoot &&
                  IxIR1.Optimizer.graphRoot fixed.targetArtifacts fixed.main ==
                    report.outputRoot

/-! Scalar constructor-fetch forwarding fixture. -/

def fetchForwardConstructorBlock : Address := Address.replicate 0xe3

def fetchForwardCtor : IxIR1.CtorId :=
  ⟨fetchForwardConstructorBlock, 0, 0⟩

/-- One projection follows an in-place reuse and one follows a fresh
allocation.  The second constructor stores the first projected scalar, which
also exercises de Bruijn lifting across the retained allocation binder. -/
def fetchForwardRawMain : IxIR1.Code :=
  .letOp (.alloc .unique fetchForwardCtor #[.lit (.nat 7)])
    (.letOp (.reuse (.var 0) fetchForwardCtor #[.lit (.nat 41)])
      (.letOp (.fetch (.var 0) 0)
        (.letOp (.alloc .unique fetchForwardCtor #[.var 0])
          (.letOp (.fetch (.var 0) 0)
            (.letOp (.free (.var 1))
              (.letOp (.free (.var 4))
                (.ret (.var 2))))))))

private def hasFetchForwardShape : IxIR1.Code → Bool
  | .letOp (.alloc .unique _ #[.lit (.nat 7)])
      (.letOp (.reuse (.var 0) _ #[.lit (.nat 41)])
        (.letOp (.pure (.lit (.nat 41)))
          (.letOp (.alloc .unique _ #[.var 0])
            (.letOp (.pure (.var 1)) _)))) => true
  | _ => false

private def isFetchForwardResult :
    Except IxIR1.Err (IxIR1.Store × IxIR1.RVal) → Bool
  | .ok (store, .lit (.nat 41)) =>
      store.live == 0 && store.allocs == 2 && store.reuses == 1 &&
        store.frees == 2
  | _ => false

/-- The whole-program harness forwards certified scalar fields after both
allocation kinds, rejects heap and out-of-range sources, preserves exact
execution counters/results, and reaches a fixed point after HPT recomputation. -/
def fetchForwardHarnessOk : Bool :=
  match IxIR1.ReaddressAll.run [fetchForwardConstructorBlock] []
      fetchForwardRawMain with
  | .error _ => false
  | .ok program =>
      let artifact := artifactWithMain program program.main
      match artifact.produceHPT with
      | .error _ => false
      | .ok production =>
          let policy := IxIR1.Optimizer.defaultPolicy
          let (optimized, report) :=
            artifact.optimizeWithProducedHPT policy production
          let oldCtx : IxIR1.Ctx := { decls := artifact.targetDeclEnv }
          let newCtx : IxIR1.Ctx := { decls := optimized.targetDeclEnv }
          let rewritten := IxIR1.HPT.OptimizeProgram.rewriteMain {}
            artifact.targetDeclEnv production.certificate.summaryEnv
            artifact.main
          let fetchRest : IxIR1.Code :=
            .letOp (.fetch (.var 0) 0) (.ret (.var 0))
          let rejectsHeapSource :=
            (IxIR1.HPT.FetchForward.forwardHead? [IxIR1.HPT.Fact.top]
              (.alloc .unique fetchForwardCtor #[.var 0]) fetchRest).isNone
          let rejectsMissingField :=
            (IxIR1.HPT.FetchForward.forwardHead? []
              (.alloc .unique fetchForwardCtor #[.lit (.nat 1)])
              (.letOp (.fetch (.var 0) 1) (.ret (.var 0)))).isNone
          let acceptsReuse :=
            match IxIR1.HPT.FetchForward.forwardHead? []
                (.reuse .erased fetchForwardCtor #[.lit (.nat 41)])
                fetchRest with
            | some forwarding =>
                forwarding.kind == .reuse &&
                  forwarding.source == .lit (.nat 41)
            | none => false
          report.disposition == .changed &&
            report.removedAlternatives == 0 &&
            report.collapsedCases == 0 &&
            report.materializedFetches == 0 &&
            report.forwardedFetches == 2 &&
            report.fusedPaps == 0 &&
            report.before.counts.fetches == 2 &&
            report.after.counts.fetches == 0 &&
            report.before.counts.allocations == 2 &&
            report.after.counts.allocations == 2 &&
            report.before.counts.reuses == 1 &&
            report.after.counts.reuses == 1 &&
            rewritten.changes.fetchForward.afterAllocations == 1 &&
            rewritten.changes.fetchForward.afterReuses == 1 &&
            hasFetchForwardShape optimized.main &&
            rejectsHeapSource && rejectsMissingField && acceptsReuse &&
            isFetchForwardResult (IxIR1.runMain oldCtx artifact.main 64) &&
            isFetchForwardResult (IxIR1.runMain newCtx optimized.main 64) &&
            match optimized.produceHPT with
            | .error _ => false
            | .ok secondProduction =>
                let (fixed, fixedReport) :=
                  optimized.optimizeWithProducedHPT policy secondProduction
                fixedReport.disposition == .unchanged &&
                  fixedReport.forwardedFetches == 0 &&
                  fixedReport.inputRoot == report.outputRoot &&
                  fixedReport.outputRoot == report.outputRoot &&
                  fixed.main.bytes == optimized.main.bytes

def underclaimed (result : IxIR1.ReaddressAll.Result) :
    IxIR1.HPT.Certificate :=
  certificate result .bottom .scalar

def noncanonical (result : IxIR1.ReaddressAll.Result) :
    IxIR1.HPT.Certificate :=
  let constructor := finalAddress result rawConstructor
  let duplicate : IxIR1.HPT.Fact :=
    ⟨false, false,
      [.ctor constructorId (some [IxIR1.HPT.FieldFact.scalar]),
       .ctor constructorId (some [IxIR1.HPT.FieldFact.scalar])]⟩
  ⟨(preciseCertificate result).artifacts.map fun artifact =>
    { artifact with members := artifact.members.map fun member =>
        if member.1 == constructor then (member.1, duplicate) else member }⟩

def wrongIdentity (result : IxIR1.ReaddressAll.Result) :
    IxIR1.HPT.Certificate :=
  match (preciseCertificate result).artifacts with
  | [] => preciseCertificate result
  | first :: rest =>
      ⟨{ first with programIdentity := Address.replicate 0xee } :: rest⟩

def excessiveShapeIndex (result : IxIR1.ReaddressAll.Result) :
    IxIR1.HPT.Certificate :=
  let constructor := finalAddress result rawConstructor
  let oversized := IxIR1.HPT.Fact.heap
    (.ctor ⟨constructorBlock, 0, 1⟩ none)
  ⟨(preciseCertificate result).artifacts.map fun artifact =>
    { artifact with members := artifact.members.map fun member =>
        if member.1 == constructor then (member.1, oversized) else member }⟩

def fieldRootShapeCertificate (result : IxIR1.ReaddressAll.Result)
    (identity : IxIR1.CtorId) : IxIR1.HPT.Certificate :=
  let constructor := finalAddress result rawConstructor
  let nested := IxIR1.HPT.Fact.heap
    (.ctor constructorId
      (some [IxIR1.HPT.FieldFact.heap (.ctor identity none)]))
  ⟨(preciseCertificate result).artifacts.map fun artifact =>
    { artifact with members := artifact.members.map fun member =>
        if member.1 == constructor then (member.1, nested) else member }⟩

def exactLimits : IxIR1.HPT.Limits :=
  { maxProgramArtifacts := 5
    maxProgramMembers := 6
    maxCertificateArtifacts := 5
    maxCertificateMembers := 6
    maxShapesPerFact := 1
    maxShapes := 1
    maxFieldsPerShape := 1
    maxFields := 1
    maxFieldDepth := 1
    maxShapeIndex := 0 }

def expectedStats : IxIR1.HPT.Stats :=
  { programArtifacts := 5
    programMembers := 6
    certificateArtifacts := 5
    certificateMembers := 6
    shapes := 1
    fields := 1
    fieldDepth := 1 }

def isError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def resourceBudgetsOk (result : IxIR1.ReaddressAll.Result) : Bool :=
  let candidate := preciseCertificate result
  let fieldRoot := fieldRootShapeCertificate result constructorId
  let excessiveFieldRoot := fieldRootShapeCertificate result
    ⟨constructorBlock, 0, 1⟩
  let fieldRootLimits := { exactLimits with maxShapes := 2 }
  match IxIR1.HPT.preflight exactLimits result.artifacts candidate,
      IxIR1.HPT.runWith exactLimits result.artifacts candidate,
      IxIR1.HPT.preflight fieldRootLimits result.artifacts fieldRoot with
  | .ok stats, .ok analysis, .ok fieldRootStats =>
      stats == expectedStats && analysis.semanticAudit &&
        fieldRootStats == { expectedStats with shapes := 2 } &&
        isError (IxIR1.HPT.runWith
          { exactLimits with maxProgramArtifacts := 4 }
          result.artifacts candidate) &&
        isError (IxIR1.HPT.runWith
          { exactLimits with maxCertificateMembers := 5 }
          result.artifacts candidate) &&
        isError (IxIR1.HPT.runWith
          { exactLimits with maxShapes := 0 }
          result.artifacts candidate) &&
        isError (IxIR1.HPT.runWith
          { exactLimits with maxFieldsPerShape := 0 }
          result.artifacts candidate) &&
        isError (IxIR1.HPT.runWith
          { exactLimits with maxFields := 0 }
          result.artifacts candidate) &&
        isError (IxIR1.HPT.runWith
          { exactLimits with maxFieldDepth := 0 }
          result.artifacts candidate) &&
        isError (IxIR1.HPT.preflight exactLimits result.artifacts fieldRoot) &&
        isError (IxIR1.HPT.preflight fieldRootLimits result.artifacts
          excessiveFieldRoot) &&
        isError (IxIR1.HPT.runWith exactLimits result.artifacts
          (excessiveShapeIndex result))
  | _, _, _ => false

def rejectsBadCertificates (result : IxIR1.ReaddressAll.Result) : Bool :=
  !(underclaimed result).postFixpoint result.artifacts &&
    !(noncanonical result).postFixpoint result.artifacts &&
    !(wrongIdentity result).postFixpoint result.artifacts &&
    !(preciseCertificate result).postFixpoint result.artifacts.reverse &&
    match IxIR1.HPT.run result.artifacts (underclaimed result),
        IxIR1.HPT.run result.artifacts (noncanonical result),
        IxIR1.HPT.run result.artifacts (wrongIdentity result) with
    | .error _, .error _, .error _ => true
    | _, _, _ => false

def pipelineTopOk (artifact : Pipeline.Artifact) : Bool :=
  match artifact.checkHPT
      (IxIR1.HPT.Certificate.top artifact.targetArtifacts) with
  | .ok analysis =>
      analysis.semanticAudit &&
        analysis.artifacts.length == artifact.targetArtifacts.length
  | .error _ => false

def pipelineProducerOk (artifact : Pipeline.Artifact) : Bool :=
  match artifact.produceHPT with
  | .ok production =>
      production.certificate.postFixpoint artifact.targetArtifacts &&
        production.result.semanticAudit
  | .error _ => false

def pipelineCacheOk (artifact : Pipeline.Artifact) : Bool :=
  match artifact.produceHPTCached ⟨[]⟩ with
  | .error _ => false
  | .ok cold =>
      match artifact.produceHPTCached cold.completeStore with
      | .error _ => false
      | .ok warm =>
          cold.certificate.postFixpoint artifact.targetArtifacts &&
            cold.result.semanticAudit &&
            warm.result == cold.result &&
            warm.stats.hits == artifact.targetArtifacts.length &&
            warm.stats.misses == 0

private def cleanupCacheFixture (directory path : System.FilePath) : IO Unit := do
  try IO.FS.removeFile path catch _ => pure ()
  try IO.FS.removeDir path catch _ => pure ()
  try IO.FS.removeDirAll directory catch _ => pure ()

private def cacheTransactionDirsAbsent (directory : System.FilePath) :
    IO Bool := do
  let entries ← directory.readDir
  return !(entries.any fun entry =>
    IxIR1.HPT.CacheIO.isTransactionDirectoryName entry.fileName)

/-- Exercise the production pipeline's absent-file cold start and exact warm
reuse through the bounded filesystem adapter. -/
def pipelineCacheFileOk (artifact : Pipeline.Artifact) : IO Bool := do
  try
    let directory ← IO.FS.createTempDir
    let path := directory / "compilatrix-pipeline-hpt.cache"
    let result ← try
      match ← artifact.produceHPTCachedFile path with
      | .error _ => pure false
      | .ok cold =>
          match ← artifact.produceHPTCachedFile path with
          | .error _ => pure false
          | .ok warm =>
              pure (cold.stats.misses == artifact.targetArtifacts.length &&
                warm.stats.hits == artifact.targetArtifacts.length &&
                warm.stats.misses == 0 && warm.result == cold.result)
      catch _ => pure false
    cleanupCacheFixture directory path
    return result
  catch _ => return false

/-- Exercise the pipeline's metadata-indexed, lazily loaded cache-directory
entry point through an absent-directory cold start and exact warm reuse. -/
def pipelineCacheDirectoryOk (artifact : Pipeline.Artifact) : IO Bool := do
  try
    let parent ← IO.FS.createTempDir
    let directory := parent / "compilatrix-pipeline-hpt-chunks"
    let result ← try
      match ← artifact.produceHPTCachedDirectory directory with
      | .error _ => pure false
      | .ok cold =>
          match ← artifact.produceHPTCachedDirectory directory,
              ← IxIR1.HPT.CacheDirIO.indexDirectory directory with
          | .ok warm, .ok index =>
              pure (cold.stats.misses == artifact.targetArtifacts.length &&
                cold.stats.writes == artifact.targetArtifacts.length &&
                warm.stats.hits == artifact.targetArtifacts.length &&
                warm.stats.misses == 0 && warm.result == cold.result &&
                index.ingress.entries == artifact.targetArtifacts.length)
          | _, _ => pure false
      catch _ => pure false
    cleanupCacheFixture parent directory
    return result
  catch _ => return false

/-- Persist, reload, reject an outer framing corruption, and locally repair a
canonically framed store containing one malformed record. -/
def persistentCacheFileOk (program : IxIR1.ReaddressAll.Result) : IO Bool := do
  try
    let directory ← IO.FS.createTempDir
    let path := directory / "compilatrix-hpt.cache"
    let result ← try
      match ← IxIR1.HPT.CacheIO.refreshFile program.artifacts path with
      | .error _ => pure false
      | .ok cold =>
          match ← IxIR1.HPT.CacheIO.refreshFile program.artifacts path,
              ← IxIR1.HPT.CacheIO.loadFile path with
          | .ok warm, .ok loaded =>
              let durableSyncKinds ←
                match ← (Ix.Compiler.DurableSync.file path).toBaseIO,
                    ← (Ix.Compiler.DurableSync.directory directory).toBaseIO,
                    ← (Ix.Compiler.DurableSync.file directory).toBaseIO,
                    ← (Ix.Compiler.DurableSync.directory path).toBaseIO with
                | .ok (), .ok (), .error _, .error _ => pure true
                | _, _, _, _ => pure false
              let cleanAfterWarm ← cacheTransactionDirsAbsent directory
              let encoded := IxIR1.HPT.Cache.encodeStore loaded
              let persistedBytes ← IO.FS.readBinFile path
              let exactBoundary ←
                match ← IxIR1.HPT.CacheIO.loadFileWith
                    { IxIR1.HPT.Cache.defaultLimits with
                      maxStoreBytes := encoded.size } path with
                | .ok exact => pure (exact == loaded)
                | .error _ => pure false
              let streamedCodecExact :=
                loaded.framedSize == encoded.size && persistedBytes == encoded
              let orphanName :=
                IxIR1.HPT.CacheIO.transactionDirectoryPrefix ++
                  "interrupted" ++
                  IxIR1.HPT.CacheIO.transactionDirectorySuffix
              let orphan := directory / orphanName
              IO.FS.createDir orphan
              IO.FS.writeBinFile (orphan / "store") (ByteArray.mk #[0xde, 0xad])
              let orphanIgnored ←
                match ← IxIR1.HPT.CacheIO.loadFile path with
                | .ok unchanged => pure (unchanged == loaded)
                | .error _ => pure false
              try IO.FS.removeFile (orphan / "store") catch _ => pure ()
              try IO.FS.removeDir orphan catch _ => pure ()
              match loaded.entries with
              | [] => pure false
              | entry :: _ =>
                  let malformed := loaded.applyWrites
                    [(entry.1, entry.2 ++ ByteArray.mk #[0])]
                  match ← IxIR1.HPT.CacheIO.saveFile path malformed with
                  | .error _ => pure false
                  | .ok () =>
                      let replacementCommitted ←
                        match ← IxIR1.HPT.CacheIO.loadFile path with
                        | .ok committed =>
                            pure (committed == malformed.canonicalize)
                        | .error _ => pure false
                      let cleanAfterReplace ←
                        cacheTransactionDirsAbsent directory
                      match ← IxIR1.HPT.CacheIO.refreshFile
                          program.artifacts path with
                      | .error _ => pure false
                      | .ok repaired =>
                          match ← IxIR1.HPT.CacheIO.refreshFile
                              program.artifacts path with
                          | .error _ => pure false
                          | .ok rewarmed =>
                              IO.FS.writeBinFile path
                                (encoded ++ ByteArray.mk #[0])
                              let outerRejected ←
                                IxIR1.HPT.CacheIO.loadFile path
                              let tooSmall ← IxIR1.HPT.CacheIO.loadFileWith
                                { IxIR1.HPT.Cache.defaultLimits with
                                  maxStoreBytes := encoded.size - 1 } path
                              IO.FS.writeBinFile path
                                (IxIR1.HPT.Cache.storeDomain ++
                                  ByteArray.mk #[128, 0])
                              let overlongCount ←
                                IxIR1.HPT.CacheIO.loadFile path
                              IO.FS.writeBinFile path
                                (encoded.extract 0 (encoded.size - 1))
                              let truncatedRecord ←
                                IxIR1.HPT.CacheIO.loadFile path
                              let reversedBytes :=
                                IxIR1.HPT.Cache.storeDomain ++
                                  IxIR.Encoding.list cacheStoreEntryBytes
                                    loaded.entries.reverse
                              IO.FS.writeBinFile path reversedBytes
                              let reversedOrder ←
                                IxIR1.HPT.CacheIO.loadFile path
                              try IO.FS.removeFile path catch _ => pure ()
                              IO.FS.createDir path
                              let nonFileLoad ←
                                IxIR1.HPT.CacheIO.loadFile path
                              let nonFileSave ←
                                IxIR1.HPT.CacheIO.saveFile path loaded
                              pure (cold.stats.misses ==
                                  program.artifacts.length &&
                                warm.stats.hits == program.artifacts.length &&
                                repaired.stats.hits + 1 ==
                                  program.artifacts.length &&
                                repaired.stats.misses == 1 &&
                                repaired.stats.rejected == 1 &&
                                rewarmed.stats.hits == program.artifacts.length &&
                                streamedCodecExact && exactBoundary &&
                                durableSyncKinds &&
                                cleanAfterWarm && orphanIgnored &&
                                replacementCommitted && cleanAfterReplace &&
                                cacheIsError outerRejected &&
                                cacheIsError tooSmall &&
                                cacheIsError overlongCount &&
                                cacheIsError truncatedRecord &&
                                cacheIsError reversedOrder &&
                                cacheIsError nonFileLoad &&
                                cacheIsError nonFileSave)
          | _, _ => pure false
      catch _ => pure false
    cleanupCacheFixture directory path
    return result
  catch _ => return false

/-- Exercise metadata-only indexing, dependency-selected lazy reads, durable
per-record writes, stale-malformed isolation, selected-record repair, and exact
directory/read budgets. -/
def persistentCacheDirectoryOk (program : IxIR1.ReaddressAll.Result) : IO Bool := do
  try
    let parent ← IO.FS.createTempDir
    let directory := parent / "compilatrix-hpt-chunks"
    let result ← try
      match ← IxIR1.HPT.CacheDirIO.refreshDirectory program.artifacts directory with
      | .error _ => pure false
      | .ok cold =>
          match ← IxIR1.HPT.CacheDirIO.refreshDirectory program.artifacts directory,
              ← IxIR1.HPT.CacheDirIO.indexDirectory directory with
          | .ok warm, .ok initialIndex =>
              let cleanAfterWarm ← cacheTransactionDirsAbsent directory
              let staleKey := Ixon.Address.replicate 0xe7
              if cold.writes.any (fun write => write.1 == staleKey) then
                pure false
              else
                let stalePath := directory /
                  IxIR1.HPT.CacheDirIO.recordFileName staleKey
                IO.FS.writeBinFile stalePath (ByteArray.mk #[0xde, 0xad])
                let orphan := directory /
                  (IxIR1.HPT.CacheIO.transactionDirectoryPrefix ++
                    "interrupted" ++
                    IxIR1.HPT.CacheIO.transactionDirectorySuffix)
                IO.FS.createDir orphan
                IO.FS.writeBinFile (orphan / "record")
                  (ByteArray.mk #[0xba, 0xd0])
                match ← IxIR1.HPT.CacheDirIO.refreshDirectory
                    program.artifacts directory,
                    ← IxIR1.HPT.CacheDirIO.indexDirectory directory with
                | .ok staleWarm, .ok indexedWithStale =>
                    try IO.FS.removeFile (orphan / "record") catch _ => pure ()
                    try IO.FS.removeDir orphan catch _ => pure ()
                    let exactIndexLimits :=
                      { IxIR1.HPT.CacheDirIO.defaultLimits with
                        maxIndexEntries := indexedWithStale.ingress.entries
                        maxIndexBytes := indexedWithStale.ingress.bytes }
                    let exactIndex ← IxIR1.HPT.CacheDirIO.indexDirectoryWith
                      exactIndexLimits directory
                    let entryOneBelow ← IxIR1.HPT.CacheDirIO.indexDirectoryWith
                      { exactIndexLimits with
                        maxIndexEntries :=
                          indexedWithStale.ingress.entries - 1 } directory
                    let bytesOneBelow ← IxIR1.HPT.CacheDirIO.indexDirectoryWith
                      { exactIndexLimits with
                        maxIndexBytes := indexedWithStale.ingress.bytes - 1 }
                      directory
                    match cold.writes with
                    | [] => pure false
                    | selected :: _ =>
                        let selectedPath := directory /
                          IxIR1.HPT.CacheDirIO.recordFileName selected.1
                        IO.FS.writeBinFile selectedPath
                          (ByteArray.mk #[0xca, 0xfe])
                        match ← IxIR1.HPT.CacheDirIO.refreshDirectory
                            program.artifacts directory with
                        | .error _ => pure false
                        | .ok repaired =>
                            match ← IxIR1.HPT.CacheDirIO.refreshDirectory
                                program.artifacts directory with
                            | .error _ => pure false
                            | .ok rewarmed =>
                                let payloadBytes := cold.completeStore.entries.foldl
                                  (fun total entry => total + entry.2.size) 0
                                let exactReadLimits :=
                                  { IxIR1.HPT.CacheDirIO.defaultLimits with
                                    maxReadBytes := payloadBytes }
                                let exactRead ←
                                  IxIR1.HPT.CacheDirIO.refreshDirectoryWith
                                    exactReadLimits program.artifacts directory
                                let readOneBelow ←
                                  IxIR1.HPT.CacheDirIO.refreshDirectoryWith
                                    { exactReadLimits with
                                      maxReadBytes := payloadBytes - 1 }
                                    program.artifacts directory
                                let cleanAfterRepair ←
                                  cacheTransactionDirsAbsent directory
                                let canonicalNameOk :=
                                  IxIR1.HPT.CacheDirIO.recordAddress?
                                      (IxIR1.HPT.CacheDirIO.recordFileName
                                        staleKey) == some staleKey &&
                                    (IxIR1.HPT.CacheDirIO.recordAddress?
                                      (staleKey.toHex ++ ".HPT")).isNone
                                let unknownPath := directory / "unexpected"
                                IO.FS.writeBinFile unknownPath
                                  (ByteArray.mk #[0])
                                let unknownRejected ←
                                  IxIR1.HPT.CacheDirIO.indexDirectory directory
                                try IO.FS.removeFile unknownPath catch _ => pure ()
                                pure (cold.stats.misses ==
                                    program.artifacts.length &&
                                  cold.stats.writes == program.artifacts.length &&
                                  warm.stats.hits == program.artifacts.length &&
                                  initialIndex.ingress.entries ==
                                    program.artifacts.length &&
                                  staleWarm.stats.hits ==
                                    program.artifacts.length &&
                                  staleWarm.stats.rejected == 0 &&
                                  indexedWithStale.ingress.entries ==
                                    program.artifacts.length + 1 &&
                                  repaired.stats.hits + 1 ==
                                    program.artifacts.length &&
                                  repaired.stats.misses == 1 &&
                                  repaired.stats.rejected == 1 &&
                                  rewarmed.stats.hits == program.artifacts.length &&
                                  rewarmed.stats.misses == 0 &&
                                  cleanAfterWarm && cleanAfterRepair &&
                                  !cacheIsError exactIndex &&
                                  cacheIsError entryOneBelow &&
                                  cacheIsError bytesOneBelow &&
                                  !cacheIsError exactRead &&
                                  cacheIsError readOneBelow &&
                                  canonicalNameOk &&
                                  cacheIsError unknownRejected)
                | _, _ => pure false
          | _, _ => pure false
      catch _ => pure false
    cleanupCacheFixture parent directory
    return result
  catch _ => return false

def producerExactLimits : IxIR1.HPT.ProducerLimits :=
  { maxRoundsPerArtifact := 3
    maxRounds := 9 }

def producerOneBelowLimits : IxIR1.HPT.ProducerLimits :=
  { maxRoundsPerArtifact := 3
    maxRounds := 8 }

def producerLocalOneBelowLimits : IxIR1.HPT.ProducerLimits :=
  { maxRoundsPerArtifact := 2
    maxRounds := 9 }

def producerShapeFallbackLimits : IxIR1.HPT.ProducerLimits :=
  { checker := { IxIR1.HPT.defaultLimits with
      maxShapesPerFact := 0
      maxShapes := 0 }
    maxRoundsPerArtifact := 3
    maxRounds := 9 }

def producerFieldFallbackLimits : IxIR1.HPT.ProducerLimits :=
  { checker := { IxIR1.HPT.defaultLimits with
      maxFieldsPerShape := 0
      maxFields := 0 }
    maxRoundsPerArtifact := 3
    maxRounds := 9 }

def producerOk (program : IxIR1.ReaddressAll.Result) : Bool :=
  match IxIR1.HPT.produce program.artifacts,
      IxIR1.HPT.produce program.artifacts,
      IxIR1.HPT.produceWith producerExactLimits program.artifacts,
      IxIR1.HPT.produceWith producerOneBelowLimits program.artifacts,
      IxIR1.HPT.produceWith producerLocalOneBelowLimits program.artifacts,
      IxIR1.HPT.produceWith producerShapeFallbackLimits program.artifacts,
      IxIR1.HPT.produceWith producerFieldFallbackLimits program.artifacts with
  | .ok first, .ok second, .ok exact, .ok oneBelow, .ok localOneBelow,
      .ok shapeFallback, .ok fieldFallback =>
      first.certificate == preciseCertificate program &&
        first.result == second.result &&
        first.certificate == second.certificate &&
        first.stats == { rounds := 9, widenedArtifacts := 0 } &&
        exact.certificate == preciseCertificate program &&
        exact.stats == { rounds := 9, widenedArtifacts := 0 } &&
        oneBelow.certificate.postFixpoint program.artifacts &&
        oneBelow.result.semanticAudit &&
        oneBelow.stats == { rounds := 8, widenedArtifacts := 1 } &&
        oneBelow.certificate != preciseCertificate program &&
        localOneBelow.certificate.postFixpoint program.artifacts &&
        localOneBelow.result.semanticAudit &&
        localOneBelow.stats == { rounds := 8, widenedArtifacts := 1 } &&
        localOneBelow.certificate == oneBelow.certificate &&
        shapeFallback.certificate.postFixpoint program.artifacts &&
        shapeFallback.result.semanticAudit &&
        shapeFallback.stats.widenedArtifacts == 1 &&
        fieldFallback.certificate.postFixpoint program.artifacts &&
        fieldFallback.result.semanticAudit &&
        fieldFallback.stats.widenedArtifacts == 1
  | _, _, _, _, _, _, _ => false

/-- The accepted detailed constructor row covers every successful concrete
invocation, including the exact scalar field stored by the fixture. -/
theorem detailedConstructorAcceptedFact_sound
    {result : IxIR1.ReaddressAll.Result} {analysis : IxIR1.HPT.Result}
    {ctx : IxIR1.Ctx} {arguments : List IxIR1.RVal}
    {store outputStore : IxIR1.Store} {outputValue : IxIR1.RVal}
    {fuel : Nat}
    (hcheck : IxIR1.HPT.run result.artifacts
      (preciseCertificate result) = .ok analysis)
    (hctx : ctx.decls = IxIR1.HPT.programDeclEnv result.artifacts)
    (hdeclaration : IxIR1.HPT.programDeclEnv result.artifacts
      (finalAddress result rawConstructor) = some constructorDeclaration)
    (hsummary : (preciseCertificate result).summaryEnv
      (finalAddress result rawConstructor) = some detailedConstructorFact)
    (hinvoke : IxIR1.invoke ctx fuel (finalAddress result rawConstructor)
      arguments store = .ok (outputStore, outputValue)) :
    detailedConstructorFact.Holds
      (IxIR1.HPT.programDeclEnv result.artifacts) outputStore outputValue := by
  exact IxIR1.HPT.functionSummary_sound_of_run_eq_ok hcheck hctx
    hdeclaration hsummary hinvoke

/-- A checked scalar row inferred through a constructor field binder covers
every successful concrete invocation of that addressed caller. -/
theorem caseBinderAcceptedFact_sound
    {result : IxIR1.ReaddressAll.Result} {analysis : IxIR1.HPT.Result}
    {ctx : IxIR1.Ctx} {function : IxIR1.FnDef}
    {arguments : List IxIR1.RVal}
    {store outputStore : IxIR1.Store} {outputValue : IxIR1.RVal}
    {fuel : Nat}
    (hcheck : IxIR1.HPT.run result.artifacts
      (preciseCertificate result) = .ok analysis)
    (hctx : ctx.decls = IxIR1.HPT.programDeclEnv result.artifacts)
    (hdeclaration : IxIR1.HPT.programDeclEnv result.artifacts
      (finalAddress result rawCaseBinder) = some (.fn function))
    (hsummary : (preciseCertificate result).summaryEnv
      (finalAddress result rawCaseBinder) = some IxIR1.HPT.Fact.scalar)
    (hinvoke : IxIR1.invoke ctx fuel (finalAddress result rawCaseBinder)
      arguments store = .ok (outputStore, outputValue)) :
    IxIR1.HPT.Fact.scalar.Holds
      (IxIR1.HPT.programDeclEnv result.artifacts) outputStore outputValue := by
  exact IxIR1.HPT.functionSummary_sound_of_run_eq_ok hcheck hctx
    hdeclaration hsummary hinvoke

/-! Alias safety under in-place reuse.  This intentionally is not well-moded:
`pure` keeps two names for one unique location.  The evaluator nevertheless
executes it, so result-shape soundness cannot retain constructor A on the old
alias after another alias reuses the node as constructor B. -/

def aliasRawFunction : Address := Address.replicate 0xdb
def aliasConstructorBlock : Address := Address.replicate 0xdc

def aliasCtorA : IxIR1.CtorId := ⟨aliasConstructorBlock, 0, 0⟩
def aliasCtorB : IxIR1.CtorId := ⟨aliasConstructorBlock, 0, 1⟩

def aliasReuseDeclaration : IxIR1.Decl :=
  .fn ⟨0, .unique, false,
    .letOp (.alloc .unique aliasCtorA #[])
      (.letOp (.pure (.var 0))
        (.letOp (.reuse (.var 0) aliasCtorB #[])
          (.ret (.var 1))))⟩

def aliasAddressed : Except String IxIR1.ReaddressAll.Result :=
  IxIR1.ReaddressAll.run [aliasConstructorBlock]
    [(aliasRawFunction, aliasReuseDeclaration)]
    (.letOp (.call aliasRawFunction #[]) (.ret (.var 0)))

def aliasFinalFunction (result : IxIR1.ReaddressAll.Result) : Address :=
  IxIR1.Readdress.Renaming.apply result.addressMap aliasRawFunction

def aliasUnknownFact : IxIR1.HPT.Fact := ⟨false, true, []⟩

def aliasCertificate (result : IxIR1.ReaddressAll.Result)
    (claim : IxIR1.HPT.Fact) : IxIR1.HPT.Certificate :=
  ⟨result.artifacts.map fun artifact =>
    { programIdentity := programIdentity artifact
      members := artifact.declarations.map fun member => (member.1, claim) }⟩

def aliasExactCertificate (result : IxIR1.ReaddressAll.Result) :
    IxIR1.HPT.Certificate :=
  aliasCertificate result (IxIR1.HPT.Fact.heap (.ctor aliasCtorA none))

def aliasUnknownCertificate (result : IxIR1.ReaddressAll.Result) :
    IxIR1.HPT.Certificate :=
  aliasCertificate result aliasUnknownFact

def aliasReuseRegressionOk (result : IxIR1.ReaddressAll.Result) : Bool :=
  let exact := aliasExactCertificate result
  let unknown := aliasUnknownCertificate result
  let declarations := IxIR1.HPT.programDeclEnv result.artifacts
  let ctx : IxIR1.Ctx := { decls := declarations }
  !exact.postFixpoint result.artifacts &&
    unknown.postFixpoint result.artifacts &&
    match IxIR1.HPT.run result.artifacts exact,
        IxIR1.HPT.run result.artifacts unknown,
        IxIR1.invoke ctx 16 (aliasFinalFunction result) [] {} with
    | .error _, .ok analysis, .ok (store, .loc location) =>
        analysis.semanticAudit && store.reuses == 1 &&
          match store.get? location with
          | some box => box.node == .ctorN aliasCtorB #[]
          | none => false
    | _, _, _ => false

/-- The accepted unknown-heap row in the alias/reuse fixture covers any
successful concrete result; in particular it cannot retain the overwritten
constructor-A identity. -/
theorem aliasReuseAcceptedFact_sound
    {result : IxIR1.ReaddressAll.Result} {analysis : IxIR1.HPT.Result}
    {ctx : IxIR1.Ctx} {arguments : List IxIR1.RVal}
    {store outputStore : IxIR1.Store} {outputValue : IxIR1.RVal}
    {fuel : Nat}
    (hcheck : IxIR1.HPT.run result.artifacts
      (aliasUnknownCertificate result) = .ok analysis)
    (hctx : ctx.decls = IxIR1.HPT.programDeclEnv result.artifacts)
    (hdeclaration : IxIR1.HPT.programDeclEnv result.artifacts
      (aliasFinalFunction result) = some aliasReuseDeclaration)
    (hsummary : (aliasUnknownCertificate result).summaryEnv
      (aliasFinalFunction result) = some aliasUnknownFact)
    (hinvoke : IxIR1.invoke ctx fuel (aliasFinalFunction result) arguments
      store = .ok (outputStore, outputValue)) :
    aliasUnknownFact.Holds (IxIR1.HPT.programDeclEnv result.artifacts)
      outputStore outputValue := by
  exact IxIR1.HPT.functionSummary_sound_of_run_eq_ok hcheck hctx
    hdeclaration hsummary hinvoke

end HPTFixtures

/-! The six structural cases in ix's pinned Lean/Rust sharing parity suite,
translated mechanically to Ixon v2's `.many`/`.shared` Lean fragment. -/

namespace SharingPolicy

def all (domain body : Expr) : Expr :=
  .all .many .shared domain body

def lam (domain body : Expr) : Expr :=
  .lam .many domain body

def simple : Array Expr :=
  let t := Expr.ref 0 #[]
  let e1 := all t (.sort 1)
  let e2 := all t e1
  let e3 := all t e2
  #[all t e3]

def contentHash : Array Expr := #[
  all (.ref 0 #[]) (.sort 0),
  all (.ref 0 #[]) (.sort 1),
  all (.ref 0 #[]) (.sort 2)]

def recursor : Array Expr :=
  let tRef := Expr.ref 0 #[]
  let target := all tRef (.app (.var 1) (.var 0))
  let withMinor3 := all (.app (.var 3) (.ref 3 #[])) target
  let withMinor2 := all (.app (.var 2) (.ref 2 #[])) withMinor3
  let withMinor1 := all (.app (.var 1) (.ref 1 #[])) withMinor2
  let motiveType := all tRef (.sort 1)
  #[all motiveType withMinor1, .var 1, .var 2, .var 3]

def forallImpReal : Array Expr :=
  let typ := all (.sort 0)
    (all (all (.var 0) (.sort 1))
      (all (all (.var 1) (.sort 1))
        (all
          (all (.var 2)
            (all (.app (.var 2) (.var 0))
                 (.app (.var 2) (.var 1))))
          (all
            (all (.var 3) (.app (.var 3) (.var 0)))
            (all (.var 4) (.app (.var 3) (.var 0)))))))
  let value := lam (.sort 0)
    (lam (all (.var 0) (.sort 1))
      (lam (all (.var 1) (.sort 1))
        (lam
          (all (.var 2)
            (all (.app (.var 2) (.var 0))
                 (.app (.var 2) (.var 1))))
          (lam
            (all (.var 3) (.app (.var 3) (.var 0)))
            (lam (.var 4)
              (.app
                (.app (.var 2) (.var 0))
                (.app (.var 1) (.var 0))))))))
  #[typ, value]

def forallImpSharing : Array Expr :=
  let app21 := Expr.app (.var 2) (.var 1)
  let app20 := Expr.app (.var 2) (.var 0)
  let e1 := all app21 app20
  let e2 := all app20 app21
  #[all (.var 3) e1, all (.var 3) e2]

def flipCase : Array Expr :=
  let innerAll := all (.var 2) (.var 2)
  let funcType := all (.var 2) innerAll
  let resultType := all (.var 2) (all (.var 4) (.var 3))
  let typ := all (.sort 0)
    (all (.sort 1)
      (all (.sort 2) (all funcType resultType)))
  let body := Expr.app (.app (.var 2) (.var 0)) (.var 1)
  let value := lam (.sort 0)
    (lam (.sort 1)
      (lam (.sort 2)
        (lam funcType
          (lam (.var 2) (lam (.var 4) body)))))
  #[typ, value]

def simpleOutput : Sharing.Compression :=
  { bodies := #[all (.share 0)
      (all (.share 0) (all (.share 0) (all (.share 0) (.sort 1))))]
    table := #[.ref 0 #[]] }

def contentHashOutput : Sharing.Compression :=
  { bodies := #[
      all (.share 0) (.sort 0),
      all (.share 0) (.sort 1),
      all (.share 0) (.sort 2)]
    table := #[.ref 0 #[]] }

def recursorOutput : Sharing.Compression :=
  { bodies := recursor, table := #[] }

def forallImpSharingOutput : Sharing.Compression :=
  { bodies := #[
      all (.var 3) (all (.share 0) (.share 1)),
      all (.var 3) (all (.share 1) (.share 0))]
    table := #[
      .app (.var 2) (.var 1),
      .app (.var 2) (.var 0)] }

/-- Exact eight-entry output captured from ix's v2 compressor at
`Sharing.ixParityRevision`. The local exact-byte audit intentionally does not
retain this nested table. -/
def ixForallImpRealOutput : Sharing.Compression :=
  { bodies := #[
      all (.sort 0)
        (all (.share 7)
          (all (.share 3)
            (all (.share 6)
              (all (.share 2) (all (.var 4) (.share 1)))))),
      lam (.sort 0)
        (lam (.share 7)
          (lam (.share 3)
            (lam (.share 6)
              (lam (.share 2)
                (lam (.var 4)
                  (.app (.share 4) (.app (.var 1) (.var 0))))))))]
    table := #[
      .app (.var 2) (.var 1),
      .app (.var 3) (.var 0),
      all (.var 3) (.share 1),
      all (.var 1) (.sort 1),
      .app (.var 2) (.var 0),
      all (.share 4) (.share 0),
      all (.var 2) (.share 5),
      all (.var 0) (.sort 1)] }

/-- Audited v2 output for `forall_imp`: three stale nested entries disappear,
and the surviving mode-bearing representatives have v2 Merkle order. -/
def v2ForallImpRealOutput : Sharing.Compression :=
  { bodies := #[
      all (.sort 0)
        (all (.share 4)
          (all (.share 2)
            (all (.share 3)
              (all (.share 1) (all (.var 4) (.share 0)))))),
      lam (.sort 0)
        (lam (.share 4)
          (lam (.share 2)
            (lam (.share 3)
              (lam (.share 1)
                (lam (.var 4)
                  (.app (.app (.var 2) (.var 0))
                    (.app (.var 1) (.var 0))))))))]
    table := #[
      .app (.var 3) (.var 0),
      all (.var 3) (.share 0),
      all (.var 1) (.sort 1),
      all (.var 2)
        (all (.app (.var 2) (.var 0)) (.app (.var 2) (.var 1))),
      all (.var 0) (.sort 1)] }

/-- Exact two-entry output captured from ix's v2 compressor at
`Sharing.ixParityRevision`. -/
def ixFlipOutput : Sharing.Compression :=
  { bodies := #[
      all (.sort 0)
        (all (.sort 1)
          (all (.sort 2)
            (all (.share 1)
              (all (.var 2) (all (.var 4) (.var 3)))))),
      lam (.sort 0)
        (lam (.sort 1)
          (lam (.sort 2)
            (lam (.share 1)
              (lam (.var 2)
                (lam (.var 4)
                  (.app (.app (.var 2) (.var 0)) (.var 1)))))))]
    table := #[
      all (.var 2) (.var 2),
      all (.var 2) (.share 0)] }

/-- V2 keeps only the maximal two-binder telescope; sharing its inner suffix
would split the canonical `all` run. -/
def v2FlipOutput : Sharing.Compression :=
  { bodies := #[
      all (.sort 0)
        (all (.sort 1)
          (all (.sort 2)
            (all (.share 0)
              (all (.var 2) (all (.var 4) (.var 3)))))),
      lam (.sort 0)
        (lam (.sort 1)
          (lam (.sort 2)
            (lam (.share 0)
              (lam (.var 2)
                (lam (.var 4)
                  (.app (.app (.var 2) (.var 0)) (.var 1)))))))]
    table := #[all (.var 2) (all (.var 2) (.var 2))] }

inductive Relation where
  | exactParity
  | intentionalV2Delta
  deriving BEq, Repr

structure Case where
  name : String
  input : Array Expr
  ixOutput : Sharing.Compression
  v2Output : Sharing.Compression
  relation : Relation

def cases : Array Case := #[
  ⟨"simple", simple, simpleOutput, simpleOutput, .exactParity⟩,
  ⟨"content-hash", contentHash, contentHashOutput, contentHashOutput,
    .exactParity⟩,
  ⟨"recursor", recursor, recursorOutput, recursorOutput, .exactParity⟩,
  ⟨"forall-imp-sharing", forallImpSharing, forallImpSharingOutput,
    forallImpSharingOutput, .exactParity⟩,
  ⟨"forall-imp-real", forallImpReal, ixForallImpRealOutput,
    v2ForallImpRealOutput, .intentionalV2Delta⟩,
  ⟨"flip", flipCase, ixFlipOutput, v2FlipOutput, .intentionalV2Delta⟩]

def putExprArray (exprs : Array Expr) : PutM Unit := do
  putTag0 ⟨exprs.size.toUInt64⟩
  for e in exprs do putExpr e

def putCompression (c : Sharing.Compression) : PutM Unit := do
  putExprArray c.bodies
  putExprArray c.table

/-- Canonically framed transcript of the inputs, pinned ix vectors, intended
v2 vectors, and parity/delta classification. -/
def transcript : ByteArray := runPut do
  putTag0 ⟨cases.size.toUInt64⟩
  for c in cases do
    putU8 (match c.relation with | .exactParity => 0 | .intentionalV2Delta => 1)
    putExprArray c.input
    putCompression c.ixOutput
    putCompression c.v2Output

def fingerprint : Address := .blake3 transcript

/-- `19aa227e6be89cbabef37366bdc3a48fcf1d8f856892054511ae6b6fcf1db4ce`.
Bump only after reviewing both the pinned ix vector and the intended v2
output for every case. -/
def expectedFingerprint : List Nat :=
  [25, 170, 34, 126, 107, 232, 156, 186,
   190, 243, 115, 102, 189, 195, 164, 143,
   207, 29, 143, 133, 104, 146, 5, 69,
   17, 174, 107, 111, 207, 29, 180, 206]

end SharingPolicy

/-! Structured checked-ingress fixtures.  Every malformed constant below is
still valid Ixon syntax, so its exact `DecodeCheck.Error` must come from the
post-decode validator rather than from the raw parser. -/

namespace DecodeCheckFixtures

open DecodeCheck

def address : Address := Address.replicate 0x5a

def axiomConstant (lvls : UInt64) (typ : Expr) (refs : Array Address := #[])
    (univs : Array Univ := #[]) (sharing : Array Expr := #[]) : Constant :=
  { info := .axio { isUnsafe := false, lvls, typ }
    sharing, refs, univs }

def validAxiom : Constant :=
  axiomConstant 1 (.app (.ref 0 #[0]) (.sort 0)) #[address] #[.var 0]

def validShared : Constant :=
  axiomConstant 0 (.app (.share 0) (.share 0)) #[] #[] #[.var 0]

def validUniverse : Constant :=
  axiomConstant 1 (.sort 0) #[]
    #[.imax (.succ (.var 0)) (.max .zero (.var 0))]

def validDefinition : Constant :=
  { info := .defn
      { kind := .thm, safety := .safe, lvls := 0
        typ := .all .many .shared (.var 0) (.var 0)
        value := .lam .many (.var 0)
          (.letE false (.var 0) (.var 0) (.var 0)) }
    sharing := #[], refs := #[], univs := #[] }

def validMutualRecur : Constant :=
  { info := .muts #[.defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .var 0, value := .recur 0 #[] }]
    sharing := #[], refs := #[], univs := #[] }

def invalidMutualRecur : Constant :=
  { validMutualRecur with info := .muts #[.defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .var 0, value := .recur 1 #[] }] }

def recursor (typ : Expr) (rules : Array RecursorRule) : Constant :=
  { info := .recr
      { k := false, isUnsafe := false, lvls := 0
        params := 0, indices := 0, motives := 0, minors := 0
        typ, rules }
    sharing := #[], refs := #[], univs := #[] }

def validRecursor : Constant :=
  recursor
    (.all .many .shared (.var 0) (.var 0))
    #[{ fields := 1, rhs := .lam .many (.var 0) (.var 0) }]

def invalidRecursorType : Constant := recursor (.var 0) #[]

def invalidRecursorRule : Constant :=
  recursor
    (.all .many .shared (.var 0) (.var 0))
    #[{ fields := 1, rhs := .var 0 }]

def allN : Nat → Expr → Expr
  | 0, body => body
  | count + 1, body => .all .many .shared (.var 0) (allN count body)

def lamN : Nat → Expr → Expr
  | 0, body => body
  | count + 1, body => .lam .many (.var 0) (lamN count body)

def validRichRecursor : Constant :=
  { info := .recr
      { k := true, isUnsafe := true, lvls := 0
        params := 1, indices := 2, motives := 3, minors := 4
        typ := allN 11 (.var 0)
        rules := #[{ fields := 5, rhs := lamN 13 (.var 0) }] }
    sharing := #[], refs := #[], univs := #[] }

def validInductiveBlock : Constant :=
  { info := .muts #[.indc
      { isUnsafe := true, lvls := 0, params := 2, indices := 3
        typ := .var 0
        ctors := #[
          { isUnsafe := false, lvls := 0, cidx := 7, params := 2,
            fields := 5, typ := .recur 0 #[] }] }]
    sharing := #[], refs := #[], univs := #[] }

def validQuotient : Constant :=
  { info := .quot { kind := .ind, lvls := 0, typ := .var 0 }
    sharing := #[], refs := #[], univs := #[] }

def validProjections : Array Constant := #[
  { info := .cPrj { idx := 1, cidx := 2, block := address }
    sharing := #[], refs := #[], univs := #[] },
  { info := .rPrj { idx := 3, block := address }
    sharing := #[], refs := #[], univs := #[] },
  { info := .iPrj { idx := 4, block := address }
    sharing := #[], refs := #[], univs := #[] },
  { info := .dPrj { idx := 5, block := address }
    sharing := #[], refs := #[], univs := #[] }
]

/-- A positive corpus spanning every constant-info variant exercised by the
checked decoder.  The fuzz harness mutates the exact encodings of these
values, so it always contains successful inputs as well as malformed ones. -/
def validConstants : Array Constant := #[
  validAxiom,
  validShared,
  validUniverse,
  validDefinition,
  validMutualRecur,
  validRecursor,
  validRichRecursor,
  validInductiveBlock,
  validQuotient
] ++ validProjections

structure Case where
  name : String
  constant : Constant
  expected : Except Error Constant

def axiomSite : Site := ⟨none, .axiomType⟩

def cases : Array Case := #[
  ⟨"last valid ref/universe index", validAxiom, .ok validAxiom⟩,
  ⟨"sharing is checked before inlining", validShared, .ok validShared⟩,
  ⟨"recursive universe forms", validUniverse, .ok validUniverse⟩,
  ⟨"definition and let forms", validDefinition, .ok validDefinition⟩,
  ⟨"last valid mutual self index", validMutualRecur, .ok validMutualRecur⟩,
  ⟨"valid recursor slicing counts", validRecursor, .ok validRecursor⟩,
  ⟨"distinct recursor metadata fields", validRichRecursor,
    .ok validRichRecursor⟩,
  ⟨"inductive/constructor metadata", validInductiveBlock,
    .ok validInductiveBlock⟩,
  ⟨"quotient variant", validQuotient, .ok validQuotient⟩,
  ⟨"constant ref index", axiomConstant 0 (.ref 1 #[]) #[address],
    .error (.refIndex axiomSite .constant 1 1)⟩,
  ⟨"string ref index", axiomConstant 0 (.str 1) #[address],
    .error (.refIndex axiomSite .string 1 1)⟩,
  ⟨"natural ref index", axiomConstant 0 (.nat 1) #[address],
    .error (.refIndex axiomSite .natural 1 1)⟩,
  ⟨"projection type-ref index", axiomConstant 0 (.prj 1 0 (.var 0)) #[address],
    .error (.refIndex axiomSite .projectionType 1 1)⟩,
  ⟨"sort universe index", axiomConstant 0 (.sort 1) #[] #[.zero],
    .error (.universeIndex axiomSite 1 1)⟩,
  ⟨"reference universe-argument index", axiomConstant 0 (.ref 0 #[1])
      #[address] #[.zero],
    .error (.universeIndex axiomSite 1 1)⟩,
  ⟨"universe variable scope", axiomConstant 1 (.sort 0) #[] #[.var 1],
    .error (.universeVariable axiomSite 1 1)⟩,
  ⟨"mutual self index", invalidMutualRecur,
    .error (.recurIndex ⟨some 0, .definitionValue⟩ 1 1)⟩,
  ⟨"recursor type arity", invalidRecursorType,
    .error (.recursorTypeArity ⟨none, .recursorType⟩ 1 0)⟩,
  ⟨"recursor rule arity", invalidRecursorRule,
    .error (.recursorRuleArity ⟨none, .recursorRule 0⟩ 1 0)⟩
]

def allCases : Array Case := cases ++ validProjections.map fun constant =>
  ⟨"projection variant", constant, .ok constant⟩

def resultEq : Except Error Constant → Except Error Constant → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false

def hostileAppCountBytes (count : Nat) : ByteArray := runPut do
  putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩
  putU8 0
  putTag0 ⟨0⟩
  putTag4 ⟨Expr.FLAG_APP, count.toUInt64⟩

def hostileExpressionDepthBytes (depth : Nat) : ByteArray := runPut do
  putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩
  putU8 0
  putTag0 ⟨0⟩
  for _ in [:depth] do
    putTag4 ⟨Expr.FLAG_PRJ, 0⟩
    putTag0 ⟨0⟩

def hostileReferenceCountBytes (count : Nat) : ByteArray := runPut do
  putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩
  putU8 0
  putTag0 ⟨0⟩
  putTag4 ⟨Expr.FLAG_VAR, 0⟩
  putTag0 ⟨0⟩
  putTag0 ⟨count.toUInt64⟩

def hostileUniverseDepthBytes (depth : Nat) : ByteArray := runPut do
  putTag4 ⟨Constant.FLAG, ConstantInfo.CONST_AXIO⟩
  putU8 0
  putTag0 ⟨0⟩
  putTag4 ⟨Expr.FLAG_SORT, 0⟩
  putTag0 ⟨0⟩
  putTag0 ⟨0⟩
  putTag0 ⟨1⟩
  for _ in [:depth] do
    putTag2 ⟨Univ.FLAG_MAX, 0⟩

structure ResourceCase where
  name : String
  bytes : ByteArray
  expected : Error

def resourceCases : Array ResourceCase :=
  let limits := DecodeCheck.defaultLimits
  let tooLong := limits.maxSequenceLength + 1
  #[
    ⟨"flat application count",
      hostileAppCountBytes tooLong,
      .sequenceTooLong .applicationSpine tooLong limits.maxSequenceLength⟩,
    ⟨"flat reference-table count",
      hostileReferenceCountBytes tooLong,
      .sequenceTooLong .references tooLong limits.maxSequenceLength⟩,
    ⟨"expression nesting",
      hostileExpressionDepthBytes limits.maxExpressionDepth,
      .expressionDepth limits.maxExpressionDepth⟩,
    ⟨"universe nesting",
      hostileUniverseDepthBytes limits.maxUniverseDepth,
      .universeDepth limits.maxUniverseDepth⟩
  ]

end DecodeCheckFixtures

/-! Deterministic checked-codec fuzzing.  This deliberately has no external
randomness or fuzzing dependency, so the ordinary flake test reproduces every
case.  Rejection is a valid result; acceptance requires exact canonical bytes
and successful passage through the checked writer. -/

namespace DecodeFuzz

inductive Outcome where
  | rejected
  | accepted
  | roundTripFailure
deriving BEq

def classify (bytes : ByteArray) : Outcome :=
  match DecodeCheck.decodeChecked bytes with
  | .error _ => .rejected
  | .ok constant =>
    if ser constant != bytes then
      .roundTripFailure
    else
      match DecodeCheck.encodeChecked constant with
      | .ok encoded =>
        if encoded == bytes then .accepted else .roundTripFailure
      | .error _ => .roundTripFailure

/-- Original bytes, every strict prefix, every single-byte low-bit flip, and
two trailing-byte mutations. -/
def mutations (bytes : ByteArray) : Array ByteArray :=
  let prefixes := (Array.range bytes.size).map fun size =>
    bytes.extract 0 size
  let flips := (Array.range bytes.size).map fun index =>
    bytes.set! index (bytes.get! index ^^^ (1 : UInt8))
  #[bytes] ++ prefixes ++ flips ++ #[bytes.push 0, bytes.push 0xff]

def nextState (state : UInt64) : UInt64 :=
  state * 6364136223846793005 + 1442695040888963407

def randomBytes (seed : UInt64) (size : Nat) : ByteArray × UInt64 := Id.run do
  let mut state := seed
  let mut bytes : ByteArray := ByteArray.empty
  for _ in [:size] do
    state := nextState state
    bytes := bytes.push state.toUInt8
  return (bytes, state)

def randomCaseCount : Nat := 4096
def maxRandomBytes : Nat := 256

end DecodeFuzz

namespace WorkBudgetFixtures

/-- A tiny valid backward sharing chain whose stored size is linear while its
fully inlined body size doubles at each table entry. -/
def doublingTable (steps : Nat) : Array Expr := Id.run do
  let mut table : Array Expr := #[.sort 0]
  for _ in [:steps] do
    let previous := table.size - 1
    table := table.push (.app (.share previous.toUInt64)
      (.share previous.toUInt64))
  return table

def doublingBodies (table : Array Expr) : Array Expr :=
  let final := table.size - 1
  #[.app (.share final.toUInt64) (.share final.toUInt64)]

end WorkBudgetFixtures

namespace MerkleFixture

/-! Independent ix artifact capture: the 19 member env roots and stored
`members_root` from `Palomar.ix/palomar.ixc/manifest` on 2026-08-25.  Keeping
the leaves as well as the result prevents a local manifest writer and reader
from masking the same Merkle drift. -/

def memberRoots : Array Address := #[
  Address.ofFn fun i => (#[34, 234, 228, 113, 117, 211, 236, 250, 12, 20, 221, 253, 121, 13, 252, 195, 27, 240, 149, 55, 73, 7, 144, 92, 155, 122, 46, 147, 113, 226, 5, 97])[i.val]!,
  Address.ofFn fun i => (#[116, 97, 231, 128, 84, 148, 77, 83, 202, 126, 202, 150, 124, 0, 176, 235, 222, 183, 166, 224, 113, 238, 25, 56, 13, 65, 96, 181, 182, 57, 119, 229])[i.val]!,
  Address.ofFn fun i => (#[178, 247, 193, 242, 219, 45, 196, 228, 122, 118, 69, 100, 245, 136, 74, 92, 136, 86, 221, 152, 221, 79, 234, 103, 78, 74, 238, 176, 138, 27, 92, 106])[i.val]!,
  Address.ofFn fun i => (#[197, 210, 150, 170, 96, 111, 211, 193, 207, 253, 183, 138, 222, 220, 222, 247, 164, 30, 184, 199, 158, 0, 192, 87, 18, 208, 78, 245, 30, 161, 4, 208])[i.val]!,
  Address.ofFn fun i => (#[113, 24, 108, 74, 6, 70, 166, 135, 172, 152, 118, 176, 59, 121, 135, 128, 234, 238, 153, 16, 145, 9, 141, 42, 37, 45, 197, 2, 254, 60, 76, 14])[i.val]!,
  Address.ofFn fun i => (#[67, 233, 29, 165, 155, 181, 250, 65, 95, 83, 213, 85, 21, 66, 190, 24, 249, 255, 96, 99, 118, 74, 59, 235, 185, 33, 23, 128, 50, 60, 161, 23])[i.val]!,
  Address.ofFn fun i => (#[214, 146, 214, 62, 98, 89, 36, 231, 71, 40, 100, 222, 168, 79, 138, 76, 235, 220, 215, 112, 83, 235, 245, 15, 114, 217, 214, 181, 22, 81, 143, 80])[i.val]!,
  Address.ofFn fun i => (#[234, 135, 20, 248, 51, 210, 152, 133, 138, 210, 227, 25, 114, 172, 242, 166, 193, 1, 80, 143, 221, 170, 160, 94, 109, 29, 140, 218, 161, 149, 55, 90])[i.val]!,
  Address.ofFn fun i => (#[15, 124, 132, 78, 214, 243, 93, 39, 51, 53, 88, 135, 122, 178, 188, 204, 21, 225, 138, 112, 175, 10, 166, 85, 198, 167, 171, 38, 142, 182, 33, 247])[i.val]!,
  Address.ofFn fun i => (#[104, 43, 172, 14, 231, 2, 233, 90, 35, 84, 74, 53, 139, 125, 192, 24, 248, 243, 12, 41, 244, 76, 41, 94, 140, 68, 19, 232, 161, 228, 72, 195])[i.val]!,
  Address.ofFn fun i => (#[210, 7, 24, 253, 31, 165, 232, 69, 246, 142, 248, 60, 244, 106, 1, 74, 111, 133, 218, 46, 12, 58, 0, 149, 147, 253, 165, 66, 191, 99, 159, 167])[i.val]!,
  Address.ofFn fun i => (#[119, 83, 141, 120, 37, 67, 242, 190, 143, 237, 20, 18, 67, 237, 49, 133, 131, 127, 229, 206, 100, 241, 62, 189, 140, 61, 199, 43, 154, 68, 243, 225])[i.val]!,
  Address.ofFn fun i => (#[183, 152, 5, 233, 133, 174, 139, 144, 196, 62, 15, 196, 222, 227, 79, 11, 5, 100, 167, 42, 171, 88, 166, 146, 212, 81, 54, 23, 35, 156, 184, 62])[i.val]!,
  Address.ofFn fun i => (#[35, 234, 146, 78, 94, 211, 112, 27, 116, 122, 186, 146, 57, 78, 196, 65, 226, 124, 96, 74, 131, 53, 150, 60, 2, 54, 157, 227, 189, 54, 194, 99])[i.val]!,
  Address.ofFn fun i => (#[180, 90, 29, 76, 86, 71, 8, 189, 92, 197, 78, 85, 64, 190, 142, 172, 202, 89, 154, 26, 98, 188, 116, 17, 20, 119, 104, 192, 53, 135, 230, 34])[i.val]!,
  Address.ofFn fun i => (#[252, 125, 42, 67, 124, 240, 172, 16, 227, 226, 107, 203, 54, 148, 155, 175, 239, 89, 88, 86, 119, 198, 5, 130, 7, 71, 92, 183, 184, 74, 227, 65])[i.val]!,
  Address.ofFn fun i => (#[219, 250, 226, 156, 208, 225, 113, 112, 219, 44, 135, 127, 76, 197, 101, 87, 228, 216, 169, 28, 38, 37, 85, 26, 48, 215, 104, 219, 144, 245, 134, 187])[i.val]!,
  Address.ofFn fun i => (#[66, 225, 49, 195, 52, 228, 129, 12, 82, 120, 164, 31, 84, 71, 0, 25, 22, 103, 200, 130, 69, 165, 23, 39, 95, 181, 243, 241, 53, 230, 47, 40])[i.val]!,
  Address.ofFn fun i => (#[149, 80, 218, 120, 189, 201, 21, 41, 23, 137, 28, 249, 223, 95, 95, 135, 137, 34, 248, 77, 249, 114, 119, 233, 44, 68, 79, 107, 71, 146, 240, 54])[i.val]!
]

def membersRoot : Address :=
  Address.ofFn fun i => (#[131, 134, 112, 180, 85, 1, 141, 183, 156,
    87, 54, 99, 118, 196, 117, 184, 37, 253, 59, 105, 99, 209, 139,
    201, 67, 197, 39, 27, 64, 28, 41, 13])[i.val]!

end MerkleFixture

namespace CatalogFixtures

private def putU16LE (value : UInt16) : PutM Unit :=
  putBytes (u64LEBytes value.toUInt64 2)

private def putU32LE (value : UInt32) : PutM Unit :=
  putBytes (u64LEBytes value.toUInt64 4)

private def putU64LE (value : UInt64) : PutM Unit :=
  putBytes (u64LEBytes value 8)

private def putAddress (address : Address) : PutM Unit :=
  putBytes address.hash

private def putString16 (value : String) : PutM Unit := do
  let bytes := value.toUTF8
  putU16LE bytes.size.toUInt16
  putBytes bytes

private def putMember (member : Catalog.Member) : PutM Unit := do
  putAddress member.envRoot
  putU64LE member.constCount
  putString16 member.label
  putString16 member.toolchain
  putString16 member.sourcePin
  putU32LE member.deps.size.toUInt32
  for dependency in member.deps do
    putU32LE dependency
  match member.preimage with
  | none => putU8 0
  | some address => putU8 1; putAddress address

/-- Test-side exact manifest writer, kept independent of the production
decoder so the loader is exercised from bytes. -/
def manifestBytes (manifest : Catalog.Manifest) : ByteArray := runPut do
  putBytes Catalog.magic
  putU32LE Catalog.version
  putU32LE (match manifest.storage with
    | .fat _ => 0
    | .chunked _ => Catalog.flagChunked)
  putAddress manifest.membersRoot
  putAddress manifest.contentRoot
  putU32LE manifest.members.size.toUInt32
  for member in manifest.members do
    putMember member
  match manifest.storage with
  | .fat pieces =>
    for piece in pieces do
      putAddress piece.fileHash
      putU64LE piece.fileBytes
  | .chunked chunks =>
    putU32LE chunks.size.toUInt32
    for chunk in chunks do
      putAddress chunk.chunkRoot
      putAddress chunk.fileHash
      putU64LE chunk.fileBytes
      putU32LE chunk.owner
  putBytes manifest.trailing

structure PieceArtifact where
  bytes : ByteArray
  envRoot : Address
  addresses : Array Address
  deriving Inhabited

/-- Minimal complete anonymous `.ixe`: the loader consumes through §3 and
retains the three empty metadata-section counts opaquely. -/
def pieceBytes (constants : Array Constant)
    (blobs : Array ByteArray := #[])
    (assumptions : Array Address := #[]) : Except String PieceArtifact := do
  let mut encodedConstants : Array (Address × ByteArray) := #[]
  for constant in constants do
    let address ← match constant.addressChecked with
      | .ok address => pure address
      | .error error => throw s!"unaddressable fixture: {repr error}"
    encodedConstants := encodedConstants.push (address, ser constant)
  encodedConstants := encodedConstants.qsort fun left right =>
    Merkle.addressLT left.1 right.1
  let mut encodedBlobs : Array (Address × ByteArray) := #[]
  for bytes in blobs do
    encodedBlobs := encodedBlobs.push (Address.blake3 bytes, bytes)
  encodedBlobs := encodedBlobs.qsort fun left right =>
    Merkle.addressLT left.1 right.1
  let assumptions := Merkle.dedupSorted (Merkle.sortAddresses assumptions)
  let addresses := encodedConstants.map (·.1)
  let envRoot := Merkle.rootCanonical addresses
  let bytes := runPut do
    putTag4 ⟨Catalog.envFlag, Catalog.envVersion⟩
    putAddress envRoot
    putU8 0
    putTag0 ⟨assumptions.size.toUInt64⟩
    for address in assumptions do putAddress address
    putTag0 ⟨encodedBlobs.size.toUInt64⟩
    for (address, payload) in encodedBlobs do
      putAddress address
      putTag0 ⟨payload.size.toUInt64⟩
      putBytes payload
    putTag0 ⟨encodedConstants.size.toUInt64⟩
    for (address, payload) in encodedConstants do
      putAddress address
      putTag0 ⟨payload.size.toUInt64⟩
      putBytes payload
    putTag0 ⟨0⟩
    -- Empty §4 names, §5 named entries, and §6 comms.  These are opaque to
    -- the anonymous loader but make the fixture a complete `.ixe`.
    putTag0 ⟨0⟩
    putTag0 ⟨0⟩
    putTag0 ⟨0⟩
  return ⟨bytes, envRoot, addresses⟩

def member (label : String) (piece : PieceArtifact)
    (deps : Array UInt32 := #[]) : Catalog.Member :=
  { envRoot := piece.envRoot
    constCount := piece.addresses.size.toUInt64
    label
    toolchain := "lean-4.33.0"
    sourcePin := "catalog-fixture"
    deps
    preimage := none }

def fatManifest (members : Array Catalog.Member)
    (pieces : Array PieceArtifact) : Catalog.Manifest :=
  let allAddresses := pieces.foldl
    (fun addresses piece => addresses.append piece.addresses) #[]
  { membersRoot := Catalog.membersRootOf members
    contentRoot := Merkle.rootCanonical allAddresses
    members
    storage := .fat (pieces.map fun piece =>
      { fileHash := Address.blake3 piece.bytes
        fileBytes := piece.bytes.size.toUInt64 }) }

def chunkedManifest (members : Array Catalog.Member)
    (pieces : Array PieceArtifact) (owners : Array UInt32) :
    Catalog.Manifest :=
  let allAddresses := pieces.foldl
    (fun addresses piece => addresses.append piece.addresses) #[]
  { membersRoot := Catalog.membersRootOf members
    contentRoot := Merkle.rootCanonical allAddresses
    members
    storage := .chunked (pieces.zip owners |>.map fun (piece, owner) =>
      { chunkRoot := piece.envRoot
        fileHash := Address.blake3 piece.bytes
        fileBytes := piece.bytes.size.toUInt64
        owner }) }

def axiomFixture (isUnsafe : Bool) : Constant :=
  { info := .axio { isUnsafe, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[.zero] }

def block (constructorOrdinal : UInt64 := 0) : Constant :=
  { info := .muts #[.indc
      { isUnsafe := false, lvls := 0, params := 0, indices := 0
        typ := .sort 0
        ctors := #[
          { isUnsafe := false, lvls := 0, cidx := constructorOrdinal
            params := 0, fields := 0, typ := .sort 0 }] }]
    sharing := #[], refs := #[], univs := #[.zero] }

def inductiveProjection (blockAddress : Address) (index : UInt64 := 0) :
    Constant :=
  { info := .iPrj { idx := index, block := blockAddress }
    sharing := #[], refs := #[], univs := #[] }

def constructorProjection (blockAddress : Address) (index : UInt64 := 0)
    (ctorIndex : UInt64 := 0) : Constant :=
  { info := .cPrj
      { idx := index
        cidx := ctorIndex
        block := blockAddress }
    sharing := #[], refs := #[], univs := #[] }

structure Input where
  manifest : Catalog.Manifest
  manifestBytes : ByteArray
  pieces : Array PieceArtifact

def inputOf (manifest : Catalog.Manifest) (pieces : Array PieceArtifact) :
    Input :=
  ⟨manifest, manifestBytes manifest, pieces⟩

def validFatInput : Except String Input := do
  let blockConstant := block
  let blockAddress ← match blockConstant.addressChecked with
    | .ok address => pure address
    | .error error => throw s!"block address: {repr error}"
  let sharedAxiom := axiomFixture false
  let pieceA ← pieceBytes #[sharedAxiom, blockConstant,
    inductiveProjection blockAddress,
    constructorProjection blockAddress]
  let pieceB ← pieceBytes #[sharedAxiom, axiomFixture true]
  let members := #[member "Core" pieceA,
    member "Extra" pieceB #[0]]
  let pieces := #[pieceA, pieceB]
  return inputOf (fatManifest members pieces) pieces

def invalidMemberInput : Except String Input := do
  let blockConstant := block
  let blockAddress ← match blockConstant.addressChecked with
    | .ok address => pure address
    | .error error => throw s!"block address: {repr error}"
  let piece ← pieceBytes #[blockConstant,
    inductiveProjection blockAddress 1]
  let pieces := #[piece]
  let members := #[member "BadMember" piece]
  return inputOf (fatManifest members pieces) pieces

def invalidOrdinalInput : Except String Input := do
  let piece ← pieceBytes #[block 7]
  let pieces := #[piece]
  let members := #[member "BadOrdinal" piece]
  return inputOf (fatManifest members pieces) pieces

def duplicateChunkInput : Except String Input := do
  let piece ← pieceBytes #[axiomFixture false]
  let pieces := #[piece, piece]
  let members := #[member "Chunked" piece]
  let manifest := chunkedManifest members pieces #[0, 0]
  return inputOf manifest pieces

def replaceFatBytes (manifest : Catalog.Manifest) (index : Nat)
    (bytes : ByteArray) : Catalog.Manifest :=
  match manifest.storage with
  | .fat rows =>
    let replacement : Catalog.FatPiece :=
      { fileHash := Address.blake3 bytes
        fileBytes := bytes.size.toUInt64 }
    { manifest with storage := .fat (rows.set! index replacement) }
  | .chunked _ => manifest

end CatalogFixtures


def main : IO UInt32 := do
  let mut ok := true

  for check in Ix.Compiler.Pipeline.nativeIntegrationChecks do
    if !check.2 then
      IO.eprintln s!"FAIL: pipeline integration: {check.1}"
      ok := false

  let ir0Bytes := Ix.Compiler.IxIR0.Decl.preimage IxIRAddressFixtures.ir0Decl
  if ir0Bytes != IxIRAddressFixtures.expectedIr0Bytes then
    IO.eprintln s!"FAIL: IxIR₀ declaration preimage drifted: {repr ir0Bytes.data.toList}"
    ok := false
  let ir0Address := Ix.Compiler.IxIR0.Decl.address IxIRAddressFixtures.ir0Decl
  if hashNats ir0Address != IxIRAddressFixtures.expectedIr0Hash then
    IO.eprintln s!"FAIL: IxIR₀ declaration address drifted: {ir0Address}"
    ok := false
  if !IxIRAddressFixtures.ir0DecodeOk then
    IO.eprintln "FAIL: IxIR₀ canonical declaration did not decode"
    ok := false
  for fixture in IxIRAddressFixtures.ir0Malformed do
    if !IxIRAddressFixtures.ir0Rejects fixture.2 then
      IO.eprintln s!"FAIL: IxIR₀ decoder accepted {fixture.1}"
      ok := false

  let ir1Bytes := Ix.Compiler.IxIR1.Decl.preimage IxIRAddressFixtures.ir1Decl
  if ir1Bytes != IxIRAddressFixtures.expectedIr1Bytes then
    IO.eprintln s!"FAIL: IxIR₁ declaration preimage drifted: {repr ir1Bytes.data.toList}"
    ok := false
  let ir1Address := Ix.Compiler.IxIR1.Decl.address IxIRAddressFixtures.ir1Decl
  if hashNats ir1Address != IxIRAddressFixtures.expectedIr1Hash then
    IO.eprintln s!"FAIL: IxIR₁ declaration address drifted: {ir1Address}"
    ok := false
  if !IxIRAddressFixtures.ir1DecodeOk then
    IO.eprintln "FAIL: IxIR₁ canonical declaration did not decode"
    ok := false
  for fixture in IxIRAddressFixtures.ir1Malformed do
    if !IxIRAddressFixtures.ir1Rejects fixture.2 then
      IO.eprintln s!"FAIL: IxIR₁ decoder accepted {fixture.1}"
      ok := false

  if !IxIR1OwnedMainFixtures.ownedBoundaryOk then
    IO.eprintln "FAIL: IxIR₁ owned-main result-world boundary drifted"
    ok := false

  if !IxIR1OwnedMainFixtures.noReuseChecksOk then
    IO.eprintln "FAIL: IxIR₁ executable no-reuse reflection drifted"
    ok := false

  match IxIRMutualBlockFixtures.built with
  | .error message =>
    IO.eprintln s!"FAIL: cycle-safe IxIR₀ mutual block failed: {message}"
    ok := false
  | .ok result =>
    if !IxIRMutualBlockFixtures.builtOk result then
      IO.eprintln s!"FAIL: IxIR₀ mutual-block identity drifted (block={result.blockAddress}, members={repr (result.derivedAddresses.map Address.toHex)}, audit={result.semanticAudit IxIRMutualBlockFixtures.raw})"
      ok := false
  if !IxIRMutualBlockFixtures.decodeOk then
    IO.eprintln "FAIL: canonical mutual block did not decode and materialize identically"
    ok := false
  for fixture in IxIRMutualBlockFixtures.malformed do
    if !IxIRMutualBlockFixtures.rejectsArtifactBytes fixture.2 then
      IO.eprintln s!"FAIL: mutual-block decoder accepted {fixture.1}"
      ok := false
  if !IxIRMutualBlockFixtures.transientSpellingIndependent then
    IO.eprintln "FAIL: mutual-block identity depends on transient member names"
    ok := false
  if !IxIRMutualBlockFixtures.orderSensitive then
    IO.eprintln "FAIL: mutual-block member order did not affect identity"
    ok := false
  if !IxIRMutualBlockFixtures.rejectsEmpty then
    IO.eprintln "FAIL: empty mutual block was accepted"
    ok := false
  if !IxIRMutualBlockFixtures.rejectsDuplicateTemporary then
    IO.eprintln "FAIL: duplicate mutual-block temporary key was accepted"
    ok := false
  if !IxIRMutualBlockFixtures.rejectsLegacyWrapAlias then
    IO.eprintln "FAIL: the legacy 2^64 member-address alias crossed the block boundary"
    ok := false
  if !IxIRMutualBlockFixtures.rejectsDerivedReservedCollision then
    IO.eprintln "FAIL: a derived mutual-member key captured a reserved identity"
    ok := false

  match IxIR1MutualBlockFixtures.built with
  | .error message =>
    IO.eprintln s!"FAIL: cycle-safe IxIR₁ mutual block failed: {message}"
    ok := false
  | .ok result =>
    if !IxIR1MutualBlockFixtures.builtOk result then
      IO.eprintln s!"FAIL: IxIR₁ mutual-block identity drifted (block={result.blockAddress}, members={repr (result.derivedAddresses.map Address.toHex)}, audit={result.semanticAudit IxIR1MutualBlockFixtures.raw})"
      ok := false
  if !IxIR1MutualBlockFixtures.decodeOk then
    IO.eprintln "FAIL: canonical IxIR₁ mutual block did not decode and materialize identically"
    ok := false
  for fixture in IxIR1MutualBlockFixtures.malformed do
    if !IxIR1MutualBlockFixtures.rejectsArtifactBytes fixture.2 then
      IO.eprintln s!"FAIL: IxIR₁ mutual-block decoder accepted {fixture.1}"
      ok := false
  if !IxIR1MutualBlockFixtures.transientSpellingIndependent then
    IO.eprintln "FAIL: IxIR₁ mutual-block identity depends on transient member names"
    ok := false
  if !IxIR1MutualBlockFixtures.orderSensitive then
    IO.eprintln "FAIL: IxIR₁ mutual-block member order did not affect identity"
    ok := false
  if !IxIR1MutualBlockFixtures.rejectsEmpty then
    IO.eprintln "FAIL: empty IxIR₁ mutual block was accepted"
    ok := false
  if !IxIR1MutualBlockFixtures.rejectsDuplicateTemporary then
    IO.eprintln "FAIL: duplicate IxIR₁ mutual-block temporary key was accepted"
    ok := false
  if !IxIR1MutualBlockFixtures.rejectsDerivedReservedCollision then
    IO.eprintln "FAIL: a derived IxIR₁ mutual-member key captured a reserved identity"
    ok := false

  for (label, passed) in [
      ("repeated erased blocks preserve both producers", RepeatedErasureFixtures.checkedReuse),
      ("conflicting block/member identities reject", RepeatedErasureFixtures.conflictsRejected),
      ("repeated blocks preserve protected namespaces", RepeatedErasureFixtures.protectedNamespaces),
      ("repeated cycles preserve ordered member maps", RepeatedErasureFixtures.repeatedCycles)] do
    if !passed then
      IO.eprintln s!"FAIL: {label}"
      ok := false
  match AddressedErasureFixtures.built with
  | .error error =>
    IO.eprintln s!"FAIL: addressed erasure rejected a cyclic program: {repr error}"
    ok := false
  | .ok result =>
    if !AddressedErasureFixtures.builtOk result then
      IO.eprintln s!"FAIL: addressed erasure drifted (blocks={repr (result.addressed.blockAddresses.map Address.toHex)}, members={repr (result.addressed.derivedAddresses.map Address.toHex)}, audit={result.semanticAudit AddressedErasureFixtures.eraseCtx AddressedErasureFixtures.constants (.ref AddressedErasureFixtures.projection) 200})"
      ok := false
  if !AddressedErasureFixtures.crossBlockTemporaryRejected then
    IO.eprintln "FAIL: a cross-block transient reference was accepted"
    ok := false
  match AddressedErasureFixtures.pipelineBuilt with
  | .error error =>
    IO.eprintln s!"FAIL: full pipeline rejected the cyclic definition fixture: {repr error}"
    ok := false
  | .ok artifact =>
    if !AddressedErasureFixtures.pipelineOk artifact then
      IO.eprintln s!"FAIL: full pipeline did not emit the expected IxIR₁ block (blocks={repr (artifact.targetBlocks.map fun block => Address.toHex block.blockAddress)}, map={repr (artifact.targetAddressMap.map fun entry => Address.toHex entry.2)})"
      ok := false
    if !HPTFixtures.pipelineTopOk artifact then
      IO.eprintln "FAIL: the production target artifact rejected the universal checked HPT fallback"
      ok := false
    if !HPTFixtures.pipelineProducerOk artifact then
      IO.eprintln "FAIL: the production target artifact rejected deterministic HPT production"
      ok := false
    if !HPTFixtures.pipelineCacheOk artifact then
      IO.eprintln "FAIL: the production target artifact rejected checked persistent HPT caching"
      ok := false
    if !(← HPTFixtures.pipelineCacheFileOk artifact) then
      IO.eprintln "FAIL: the production target artifact rejected file-backed persistent HPT caching"
      ok := false
    if !(← HPTFixtures.pipelineCacheDirectoryOk artifact) then
      IO.eprintln "FAIL: the production target artifact rejected indexed chunk-directory HPT caching"
      ok := false
  match AddressedErasureFixtures.pipelineBuilt,
      AddressedErasureFixtures.validatedPipelineBuilt with
  | .ok direct, .ok gated =>
    if !AddressedErasureFixtures.validatedPipelineAgrees direct gated then
      IO.eprintln "FAIL: direct and validated cyclic pipelines disagree"
      ok := false
  | _, .error error =>
    IO.eprintln s!"FAIL: validated pipeline rejected the certified cyclic fixture: {repr error}"
    ok := false
  | _, _ =>
    IO.eprintln "FAIL: direct cyclic pipeline failed during agreement check"
    ok := false

  if !AddressedErasureFixtures.validatedIxIR2AttachmentOk then
    IO.eprintln "FAIL: validated IxIR₁ pipeline did not attach and validate the conservative IxIR₂ sidecars"
    ok := false

  for number in [0, 42, 4294967296, UInt64.size - 1] do
    match Ix.Compiler.X86.ValidatedScalar.compile number with
    | .error error =>
        IO.eprintln s!"FAIL: validated Ixon scalar {number} did not compile: {repr error}"
        ok := false
    | .ok compiled =>
        match compiled.observe with
        | .ok _ => pure ()
        | .error message =>
            IO.eprintln s!"FAIL: validated Ixon scalar {number}: {message}"
            ok := false
  if !Ix.Compiler.X86.ValidatedScalar.rejectsBareLiteral 42 then
    IO.eprintln "FAIL: bare unique source literal lost its shared-result freezeNeeded rejection"
    ok := false
  if !Ix.Compiler.X86.ValidatedScalar.rejectsOverflow then
    IO.eprintln "FAIL: validated Ixon scalar above 64 bits lost its selector rejection"
    ok := false

  match Ix.Compiler.Recursion.Examples.runAll with
  | .ok _ => pure ()
  | .error message =>
    IO.eprintln s!"FAIL: Ixon source recursion/reuse: {message}"
    ok := false

  match Ix.Compiler.CallReuse.Examples.runAll with
  | .ok _ => pure ()
  | .error message =>
    IO.eprintln s!"FAIL: Ixon source call reuse: {message}"
    ok := false

  match Ix.Compiler.UniqueReuse.Examples.runAll with
  | .ok _ => pure ()
  | .error message =>
    IO.eprintln s!"FAIL: Ixon source unique reuse: {message}"
    ok := false

  match Ix.Compiler.IxIR2.Reuse.Examples.checkUnaliased with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  match Ix.Compiler.IxIR2.Reuse.Examples.checkAliased with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  for aliased in [false, true] do
    match Ix.Compiler.IxIR2.Reuse.Examples.checkZeroFieldChild aliased with
    | .ok _ => pure ()
    | .error message =>
        IO.eprintln s!"FAIL: {message}"
        ok := false

  for overApplied in [false, true] do
    for aliased in [false, true] do
      match Ix.Compiler.IxIR2.Reuse.Examples.checkPapTailReturn overApplied aliased with
      | .ok _ => pure ()
      | .error message =>
          IO.eprintln s!"FAIL: {message}"
          ok := false

  for underApplied in [false, true] do
    match Ix.Compiler.IxIR2.Reuse.Examples.checkImmediateApplyMore underApplied with
    | .ok _ => pure ()
    | .error message =>
        IO.eprintln s!"FAIL: {message}"
        ok := false

  for fallback in [false, true] do
    match Ix.Compiler.IxIR2.Reuse.Examples.checkProductionSelection fallback with
    | .ok _ => pure ()
    | .error message =>
        IO.eprintln s!"FAIL: {message}"
        ok := false

  match Ix.Compiler.IxIR2.Reuse.Examples.checkProductionSourceRejection with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  match Ix.Compiler.IxIR2.Reuse.Examples.checkIncompatibleLayout with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  match Ix.Compiler.IxIR2.Reuse.Examples.checkGeneralizedShape with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  match Ix.Compiler.IxIR2.Reuse.Examples.checkLateSourceUse with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  match Ix.Compiler.IxIR2.Liveness.Examples.checkSuite with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  if !IxIR2PipelineFixtures.ambiguousFetchAcceptedByProducerFact then
    IO.eprintln "FAIL: exact local HPT producer provenance did not disambiguate an IxIR₂ fetch"
    ok := false

  if !IxIR2PipelineFixtures.ambiguousCaseAcceptedByProducerFact then
    IO.eprintln "FAIL: exact local HPT producer provenance did not disambiguate an IxIR₂ constructor switch"
    ok := false

  if !IxIR2PipelineFixtures.unresolvedFetchRejected then
    IO.eprintln "FAIL: IxIR₂ producer provenance accepted an unresolved fetch parameter"
    ok := false

  if !IxIR2PipelineFixtures.ambiguousScalarFreeAcceptedByProducerFact then
    IO.eprintln "FAIL: exact local HPT producer provenance did not disambiguate an IxIR₂ shallow free"
    ok := false

  if !IxIR2PipelineFixtures.pappCapabilityTransitionAccepted then
    IO.eprintln "FAIL: checked IxIR₂ function-PAP capability transition drifted"
    ok := false

  if !IxIR2PipelineFixtures.pappSafetyCheckRejectsUnsafe then
    IO.eprintln "FAIL: IxIR₂ attachment PAP-safety check accepted an unsafe declaration"
    ok := false

  if !IxIR2PipelineFixtures.lenderDestructionRetiresBorrow then
    IO.eprintln "FAIL: checked IxIR₂ destruction retained a dead lender loan"
    ok := false

  if !IxIR2PipelineFixtures.exactRecursorCaseAccepted then
    IO.eprintln "FAIL: ambiguous recursor case did not cover and execute both full IxIR₂ constructor identities"
    ok := false

  if !IxIR2PipelineFixtures.recursorOriginExtractionOk then
    IO.eprintln "FAIL: recursor-origin extraction lost the final owner map or accepted conflicting blocks"
    ok := false

  if !ReaddressOracleFixtures.adapterOk then
    IO.eprintln "FAIL: the IxIR₀ opaque-oracle adapter did not reverse the call key, preserve scalar arity, and map the result"
    ok := false
  match ReaddressOracleFixtures.ledgerBuilt with
  | .error message =>
    IO.eprintln s!"FAIL: the ledger-oracle mutual-block fixture did not readdress: {message}"
    ok := false
  | .ok result =>
    if !ReaddressOracleFixtures.ledgerCycleOk result then
      IO.eprintln s!"FAIL: the concrete Nat-add oracle lost coherence across the member map (blocks={repr (result.blockAddresses.map Address.toHex)}, members={repr (result.derivedAddresses.map Address.toHex)})"
      ok := false
  if !ReaddressOracleFixtures.mainExternalCaptureRejected then
    IO.eprintln "FAIL: an IxIR₀ member key captured an external identity referenced only by main"
    ok := false

  match IxIRReaddressFixtures.chain with
  | .error message =>
    IO.eprintln s!"FAIL: dependency-ordered IxIR₁ readdressing failed: {message}"
    ok := false
  | .ok result =>
    if !IxIRReaddressFixtures.chainOk result then
      IO.eprintln s!"FAIL: dependency-ordered IxIR₁ readdressing drifted (content={repr (IxIRReaddressFixtures.contentHexes result)})"
      ok := false

  match IxIRReaddressFixtures.deduplicate with
  | .error message =>
    IO.eprintln s!"FAIL: identical IxIR₁ content did not deduplicate: {message}"
    ok := false
  | .ok result =>
    if !IxIRReaddressFixtures.deduplicateOk result then
      IO.eprintln s!"FAIL: IxIR₁ content deduplication drifted (content={repr (IxIRReaddressFixtures.contentHexes result)})"
      ok := false

  if !IxIRReaddressFixtures.cycleRejected then
    IO.eprintln "FAIL: generated IxIR₁ address cycle did not fail closed"
    ok := false
  if !IxIRReaddressFixtures.overlapRejected then
    IO.eprintln "FAIL: generated/source temporary-address overlap was accepted"
    ok := false
  if !IxIRReaddressFixtures.sourceKeyCollisionRejected then
    IO.eprintln "FAIL: generated content/source-key collision was accepted"
    ok := false
  if !IxIRReaddressFixtures.contentTemporaryOverlapRejected then
    IO.eprintln "FAIL: generated content/temporary namespace overlap was accepted"
    ok := false
  if !IxIRReaddressFixtures.protectedSourceIdentityRejected then
    IO.eprintln "FAIL: a transient key rewrote a constructor source identity"
    ok := false

  if !IxIR1ReaddressAllFixtures.componentsOk then
    IO.eprintln "FAIL: IxIR₁ SCC discovery did not preserve deterministic source-member order"
    ok := false
  if !IxIR1ReaddressAllFixtures.longChainComponentsOk then
    IO.eprintln "FAIL: IxIR₁ SCC discovery failed the iterative long-chain guard"
    ok := false
  match IxIR1ReaddressAllFixtures.built with
  | .error message =>
    IO.eprintln s!"FAIL: whole-program IxIR₁ SCC readdressing failed: {message}"
    ok := false
  | .ok result =>
    if !IxIR1ReaddressAllFixtures.builtOk result then
      IO.eprintln s!"FAIL: whole-program IxIR₁ SCC identities or audit drifted (targets={repr (result.addressMap.map fun entry => Address.toHex entry.2)}, blocks={repr (result.blockAddresses.map Address.toHex)}, audit={result.semanticAudit IxIR1ReaddressAllFixtures.raw IxIR1ReaddressAllFixtures.mainCode})"
      ok := false
  if !IxIR1ReaddressAllFixtures.transientSpellingIndependent then
    IO.eprintln "FAIL: whole-program IxIR₁ identities depend on transient producer names"
    ok := false
  if !IxIR1ReaddressAllFixtures.memberOrderSensitive then
    IO.eprintln "FAIL: IxIR₁ SCC member order did not affect block/program identity"
    ok := false
  if !IxIR1ReaddressAllFixtures.ordinaryDeduplicates then
    IO.eprintln "FAIL: whole-program IxIR₁ ordinary content did not deduplicate"
    ok := false
  if !IxIR1ReaddressAllFixtures.explicitSelfUsesBlock then
    IO.eprintln "FAIL: an explicit IxIR₁ self-address edge did not use a block artifact"
    ok := false
  if !IxIR1ReaddressAllFixtures.callSelfUsesOrdinaryHash then
    IO.eprintln "FAIL: address-free IxIR₁ callSelf did not retain the ordinary hash path"
    ok := false
  if !IxIR1ReaddressAllFixtures.emptyOk then
    IO.eprintln "FAIL: empty whole-program IxIR₁ readdressing drifted"
    ok := false
  if !IxIR1ReaddressAllFixtures.rejectsDuplicateProducer then
    IO.eprintln "FAIL: duplicate whole-program IxIR₁ producer key was accepted"
    ok := false
  if !IxIR1ReaddressAllFixtures.rejectsReservedProducer then
    IO.eprintln "FAIL: an IxIR₁ producer key overlapped a reserved identity"
    ok := false
  if !IxIR1ReaddressAllFixtures.rejectsProtectedContent then
    IO.eprintln "FAIL: an IxIR₁ content address captured a protected identity"
    ok := false
  if !IxIR1ReaddressAllFixtures.rejectsContentInTransientNamespace then
    IO.eprintln "FAIL: an IxIR₁ content address overlapped the transient namespace"
    ok := false

  match HPTFixtures.addressed with
  | .error message =>
    IO.eprintln s!"FAIL: HPT fixture did not content-address: {message}"
    ok := false
  | .ok program =>
    match HPTFixtures.precise program, HPTFixtures.widened program with
    | .ok precise, .ok widened =>
      if !HPTFixtures.preciseOk program precise then
        IO.eprintln s!"FAIL: checked HPT facts or SCC materialization drifted (cacheKeys={repr (precise.cacheKeys.map Address.toHex)}, addresses={repr (precise.addresses.map Address.toHex)})"
        ok := false
      if !HPTFixtures.fieldSensitiveOk program precise then
        IO.eprintln "FAIL: field-sensitive HPT allocation/fetch facts disagreed with concrete execution"
        ok := false
      if !HPTFixtures.caseBinderFieldOk then
        IO.eprintln "FAIL: HPT case binders lost field precision, binding order, tag filtering, or conservative widening"
        ok := false
      if !HPTFixtures.recursiveFieldOk then
        IO.eprintln "FAIL: recursive HPT fields lost depth-two projection, case-binder, budget, producer, or cache precision"
        ok := false
      if !HPTFixtures.casePruneOk program then
        IO.eprintln "FAIL: checked HPT case simplification changed execution or crossed a conservative collapse boundary"
        ok := false
      if !HPTFixtures.recursiveCasePruneOk program then
        IO.eprintln "FAIL: recursive checked HPT case simplification missed a nested rewrite or changed execution"
        ok := false
      if !HPTFixtures.callSelfCasePruneOk program then
        IO.eprintln "FAIL: recursive checked HPT case simplification changed a terminating callSelf execution or failed to rewrite its current frame"
        ok := false
      if !HPTFixtures.pipelineCallSelfMainPruneOk program then
        IO.eprintln "FAIL: checked HPT artifact-main pruning changed an exact finite-fuel callSelf result"
        ok := false
      if !HPTFixtures.declarationGraphCasePruneOk then
        IO.eprintln "FAIL: checked HPT declaration-graph simplification failed to readdress a changed body, rewrite its main edge, or preserve execution"
        ok := false
      if !HPTFixtures.optimizerHarnessOk then
        IO.eprintln "FAIL: optimizer policy, observations, deterministic report, fail-soft controls, address transport, or idempotence drifted"
        ok := false
      if !HPTFixtures.reachabilityCertificateOk then
        IO.eprintln "FAIL: rooted reachability production, validation, adversarial rejection, fallback, or exact execution drifted"
        ok := false
      if !HPTFixtures.reachabilityHarnessOk then
        IO.eprintln "FAIL: rooted reachability optimizer reporting, exported roots, one-rebuild content addressing, or execution drifted"
        ok := false
      if !HPTFixtures.papFusionHarnessOk then
        IO.eprintln "FAIL: checked PAP/apply fusion drifted across saturation classes, rejection gates, reporting, execution, or idempotence"
        ok := false
      if !HPTFixtures.fetchForwardHarnessOk then
        IO.eprintln "FAIL: checked scalar fetch forwarding drifted across allocation/reuse, rejection gates, reporting, exact execution, or idempotence"
        ok := false
      if !HPTFixtures.cacheConeOk program precise widened then
        IO.eprintln "FAIL: HPT cache invalidation escaped or missed the dependency cone"
        ok := false
      if !HPTFixtures.persistentCacheOk program precise widened then
        IO.eprintln "FAIL: persistent HPT cache ingress, recovery, or dependency-cone rebuilding drifted"
        ok := false
      if !HPTFixtures.persistentCacheBudgetsOk program precise then
        IO.eprintln "FAIL: persistent HPT cache resource gates drifted at an exact or one-below boundary"
        ok := false
      if !(← HPTFixtures.persistentCacheFileOk program) then
        IO.eprintln "FAIL: persistent HPT cache file ingress, framing rejection, or local repair drifted"
        ok := false
      if !(← HPTFixtures.persistentCacheDirectoryOk program) then
        IO.eprintln "FAIL: indexed HPT chunk caching, lazy repair, or directory budgets drifted"
        ok := false
    | .error message, _ =>
      IO.eprintln s!"FAIL: precise HPT post-fixpoint was rejected: {message}"
      ok := false
    | _, .error message =>
      IO.eprintln s!"FAIL: widened HPT post-fixpoint was rejected: {message}"
      ok := false
    if !HPTFixtures.rejectsBadCertificates program then
      IO.eprintln "FAIL: HPT checker accepted an underclaim, noncanonical fact, wrong identity, or reordered artifact list"
      ok := false
    if !HPTFixtures.resourceBudgetsOk program then
      IO.eprintln "FAIL: HPT structural preflight drifted at an exact or one-below boundary"
      ok := false
    if !HPTFixtures.producerOk program then
      IO.eprintln "FAIL: deterministic HPT production drifted in precision, repeatability, or bounded fallback"
      ok := false

  match HPTFixtures.aliasAddressed with
  | .error message =>
    IO.eprintln s!"FAIL: HPT alias/reuse fixture did not content-address: {message}"
    ok := false
  | .ok program =>
    if !HPTFixtures.aliasReuseRegressionOk program then
      IO.eprintln "FAIL: HPT retained a stale constructor fact across aliased reuse"
      ok := false

  match IxIR1ReaddressAllFixtures.fullyNested with
  | .error message =>
    IO.eprintln s!"FAIL: fully addressed nested IxIR₁ lowering failed: {message}"
    ok := false
  | .ok result =>
    if !IxIR1ReaddressAllFixtures.fullyNestedOk result then
      IO.eprintln s!"FAIL: fully addressed nested IxIR₁ lowering drifted (map={repr (result.addressMap.map fun entry => Address.toHex entry.2)}, blocks={repr (result.blockAddresses.map Address.toHex)}, stable={repr (result.stable.map fun entry => Address.toHex entry.1)})"
      ok := false
  match IxIR1ReaddressAllFixtures.fullyCyclicLowering with
  | .error message =>
    IO.eprintln s!"FAIL: source/lifted IxIR₁ cycle lowering failed: {message}"
    ok := false
  | .ok result =>
    if !IxIR1ReaddressAllFixtures.fullyCyclicLoweringOk result then
      IO.eprintln s!"FAIL: source/lifted IxIR₁ cycle did not become one two-member block (targets={repr (result.addressMap.map fun entry => Address.toHex entry.2)}, blocks={repr (result.blockAddresses.map Address.toHex)}, declarations={result.declarations.length}, audit={IxIR1ReaddressAllFixtures.fullyLoweredAudit [(IxIR1ReaddressAllFixtures.cyclicSourceKey, IxIR1ReaddressAllFixtures.cyclicSourceDeclaration)] (.ref IxIR1ReaddressAllFixtures.cyclicSourceKey) result})"
      ok := false
  if !IxIR1ReaddressAllFixtures.fullyProtectedSourceIdentityRejected then
    IO.eprintln "FAIL: fully addressed lowering allowed a generated key to capture a constructor identity"
    ok := false

  match IxIRReaddressFixtures.nestedLowering with
  | .error message =>
    IO.eprintln s!"FAIL: nested lifted-lambda readdressing failed: {message}"
    ok := false
  | .ok result =>
    if !IxIRReaddressFixtures.nestedLoweringOk result then
      IO.eprintln s!"FAIL: nested lifted-lambda addresses or runtime changed (map={result.addressMap.length}, generated={result.generated.length}, no-transient={result.noTransientReferences}, addressed={result.generatedAreAddressed}, entries={repr result.addressMap})"
      ok := false

  match IxIRReaddressFixtures.wrapperLowering with
  | .error message =>
    IO.eprintln s!"FAIL: constructor-wrapper readdressing failed: {message}"
    ok := false
  | .ok result =>
    if !IxIRReaddressFixtures.wrapperLoweringOk result then
      IO.eprintln s!"FAIL: constructor-wrapper content addressing drifted (map={result.addressMap.length}, generated={result.generated.length}, no-transient={result.noTransientReferences}, addressed={result.generatedAreAddressed}, entries={repr result.addressMap})"
      ok := false

  let generatedSummary := Ix.Compiler.IxIR1.WellModedGen.summarize
  let expectedGeneratedSummary :
      Ix.Compiler.IxIR1.WellModedGen.Summary :=
    { checked := 280
      differential := 180
      expectedRejections := 100
      allKindsSeen := true
      finalState := 1151165198556225096
      fingerprint := 6965325113816880105 }
  if generatedSummary != expectedGeneratedSummary then
    IO.eprintln s!"FAIL: well-moded generator corpus drifted: {repr generatedSummary}"
    ok := false
  match Ix.Compiler.IxIR1.WellModedGen.checkCorpus with
  | none => pure ()
  | some failure =>
    IO.eprintln s!"FAIL: seeded IxIR₀ property case failed: {repr failure}"
    IO.eprintln s!"      original expr: {repr failure.original.template.expr}"
    IO.eprintln s!"      minimized expr: {repr failure.minimized.template.expr}"
    ok := false

  let overlongTrimmed : ByteArray := ⟨Array.replicate 9 0⟩
  match runGet (getU64TrimmedLE 9) overlongTrimmed with
  | .error message =>
    if message != "getU64TrimmedLE: byte length 9 exceeds 8" then
      IO.eprintln s!"FAIL: unexpected overlong u64 error: {message}"
      ok := false
  | .ok value =>
    IO.eprintln s!"FAIL: accepted a nine-byte trimmed u64 as {value}"
    ok := false

  let duplicateKey := indexedAddress 7
  let duplicateIndex := Ix.Compiler.AddressEnv.build
    [(duplicateKey, 11), (duplicateKey, 22), (indexedAddress 8, 33)]
  let duplicateLookup := Ix.Compiler.AddressEnv.lookup duplicateIndex
  if duplicateLookup duplicateKey != some 11 then
    IO.eprintln "FAIL: address index did not preserve first-binding precedence"
    ok := false
  if (duplicateLookup (indexedAddress 9)).isSome then
    IO.eprintln "FAIL: address index returned a value for a missing key"
    ok := false

  let indexSize := 4096
  let indexedEntries := (List.range indexSize).map fun n => (indexedAddress n, n)
  let largeIndex := Ix.Compiler.AddressEnv.build indexedEntries
  let largeLookup := Ix.Compiler.AddressEnv.lookup largeIndex
  for n in [:indexSize] do
    if largeLookup (indexedAddress n) != some n then
      IO.eprintln s!"FAIL: address index lookup disagreed at entry {n}"
      ok := false

  -- This root comes from an actual ix-produced 19-member catalog, not the
  -- local fixture writer.  Reversing the leaves and repeating one also pins
  -- the canonical sort-and-deduplicate policy.
  let artifactLeaves := MerkleFixture.memberRoots.reverse.push
    MerkleFixture.memberRoots[0]!
  if Merkle.rootCanonical artifactLeaves != MerkleFixture.membersRoot then
    IO.eprintln "FAIL: canonical Merkle root drifted from the ix catalog artifact"
    ok := false

  -- Byte-exact production ix contact: a bounded Std closure generated by the
  -- pinned ixon-v2 writer, independently hex-encoded under Tests/Fixtures/Compiler/.
  let contactManifest ← CatalogContactFixture.readHex "manifest.hex"
  let contactPiece ← CatalogContactFixture.readHex
    "CompilatrixStdContact.ixe.hex"
  match contactManifest, contactPiece with
  | .error message, _ | _, .error message =>
    IO.eprintln s!"FAIL: could not read ix contact fixture: {message}"
    ok := false
  | .ok manifestBytes, .ok pieceBytes =>
    if manifestBytes.size != 267 || pieceBytes.size != 14600 then
      IO.eprintln s!"FAIL: ix contact byte sizes changed: manifest={manifestBytes.size}, piece={pieceBytes.size}"
      ok := false
    if toString (Address.blake3 pieceBytes) !=
        CatalogContactFixture.expectedPieceHash then
      IO.eprintln "FAIL: ix contact piece hash changed"
      ok := false
    match Catalog.load manifestBytes #[pieceBytes] with
    | .error error =>
      IO.eprintln s!"FAIL: production ix contact rejected at ingress: {repr error}"
      ok := false
    | .ok loaded =>
      if toString loaded.manifest.membersRoot !=
          CatalogContactFixture.expectedMembersRoot ||
          toString loaded.manifest.contentRoot !=
            CatalogContactFixture.expectedContentRoot then
        IO.eprintln s!"FAIL: ix contact catalog roots changed: members={loaded.manifest.membersRoot}, content={loaded.manifest.contentRoot}"
        ok := false
      if loaded.stats != CatalogContactFixture.expectedStats then
        IO.eprintln s!"FAIL: ix contact stats changed: {repr loaded.stats}"
        ok := false
      match loaded.manifest.members[0]? with
      | none =>
        IO.eprintln "FAIL: ix contact lost its manifest member"
        ok := false
      | some member =>
        if member.label != "CompilatrixStdContact" ||
            member.toolchain != "leanprover/lean4:v4.33.1" ||
            member.sourcePin !=
              "git:ix@6f18ea907b78d06f7dc0917c43beb385561c35f4" ||
            member.constCount != 54 then
          IO.eprintln s!"FAIL: ix contact provenance changed: {repr member}"
          ok := false
      match Ix.Compiler.Pipeline.checkProgram loaded.constants with
      | .error (.usage address .freezeNeeded) =>
        if toString address != CatalogContactFixture.expectedRemainingFreezeAddress then
          IO.eprintln s!"FAIL: ix contact pipeline rejection moved to {address}"
          ok := false
      | .error error =>
        IO.eprintln s!"FAIL: ix contact pipeline outcome changed: {repr error}"
        ok := false
      | .ok _ =>
        IO.eprintln "FAIL: ix contact unexpectedly crossed the current usage-policy gate"
        ok := false

  -- Exact ix `.ixc` + anonymous `.ixe` framing.  The two fat members share
  -- one closure constant: storage work counts six entries while the semantic
  -- union contains five.
  match CatalogFixtures.validFatInput with
  | .error message =>
    IO.eprintln s!"FAIL: could not construct valid catalog fixture: {message}"
    ok := false
  | .ok input =>
    let pieces := input.pieces.map (·.bytes)
    match Catalog.load input.manifestBytes pieces with
    | .error error =>
      IO.eprintln s!"FAIL: valid fat catalog rejected: {repr error}"
      ok := false
    | .ok loaded =>
      if loaded.constants.length != 5 || loaded.stats.constantEntries != 6 ||
          loaded.stats.unionConstants != 5 then
        IO.eprintln s!"FAIL: fat overlap was not deduplicated exactly: \
          entries={loaded.stats.constantEntries}, union={loaded.stats.unionConstants}"
        ok := false
      let stats := loaded.stats
      let exactLimits : Catalog.Limits :=
        { Catalog.defaultLimits with
          maxManifestBytes := stats.manifestBytes
          maxMembers := stats.members
          maxDependencyEdges := stats.dependencyEdges
          maxStorageUnits := stats.storageUnits
          maxPieceBytes := stats.pieceBytes
          maxConstantEntries := stats.constantEntries
          maxConstantBytes := stats.constantBytes
          maxBlobEntries := stats.blobEntries
          maxBlobBytes := stats.blobBytes
          maxAssumptions := stats.assumptions
          maxHints := stats.hints
          maxExpressionUnits := stats.expressionUnits
          maxExpandedExpressionUnits := stats.expandedExpressionUnits
          maxLayer1NodeVisits := stats.layer1NodeVisits
          maxUnionConstants := stats.unionConstants }
      match Catalog.loadWith exactLimits input.manifestBytes pieces with
      | .ok _ => pure ()
      | .error error =>
        IO.eprintln s!"FAIL: exact aggregate catalog limits rejected: {repr error}"
        ok := false
      let tightEntries :=
        { exactLimits with
          maxConstantEntries := stats.constantEntries - 1 }
      match Catalog.loadWith tightEntries input.manifestBytes pieces with
      | .error (.resource exceeded) =>
        let expected : Ix.Compiler.Ixon.Work.Exceeded :=
          ⟨.catalogConstantEntries, stats.constantEntries,
            stats.constantEntries - 1⟩
        if exceeded != expected then
          IO.eprintln s!"FAIL: wrong catalog-entry budget error: {repr exceeded}"
          ok := false
      | .error error =>
        IO.eprintln s!"FAIL: another catalog-entry error surfaced: {repr error}"
        ok := false
      | .ok _ =>
        IO.eprintln "FAIL: catalog crossed its constant-entry budget"
        ok := false
      let tightPieceBytes :=
        { exactLimits with maxPieceBytes := stats.pieceBytes - 1 }
      match Catalog.loadWith tightPieceBytes input.manifestBytes pieces with
      | .error (.resource exceeded) =>
        let expected : Ix.Compiler.Ixon.Work.Exceeded :=
          ⟨.catalogPieceBytes, stats.pieceBytes, stats.pieceBytes - 1⟩
        if exceeded != expected then
          IO.eprintln s!"FAIL: wrong catalog-piece budget error: {repr exceeded}"
          ok := false
      | .error error =>
        IO.eprintln s!"FAIL: another catalog-piece error surfaced: {repr error}"
        ok := false
      | .ok _ =>
        IO.eprintln "FAIL: catalog crossed its aggregate piece-byte budget"
        ok := false

    let truncatedManifest := input.manifestBytes.extract 0
      (input.manifestBytes.size - 1)
    match Catalog.load truncatedManifest pieces with
    | .error (.syntax .manifest _) => pure ()
    | .error error =>
      IO.eprintln s!"FAIL: manifest truncation returned another error: {repr error}"
      ok := false
    | .ok _ =>
      IO.eprintln "FAIL: truncated catalog manifest was accepted"
      ok := false

    let original := pieces[0]!
    let changedFile := original.set! 0 (original[0]! ^^^ (1 : UInt8))
    match Catalog.load input.manifestBytes (pieces.set! 0 changedFile) with
    | .error (.fileHash (.fat 0) _ _) => pure ()
    | .error error =>
      IO.eprintln s!"FAIL: changed piece returned another error: {repr error}"
      ok := false
    | .ok _ =>
      IO.eprintln "FAIL: piece bytes drifted from the manifest hash"
      ok := false

    -- Remove the hint count and all opaque metadata, then bind the shortened
    -- file in a fresh manifest.  This reaches semantic-prefix EOF rather than
    -- stopping at the outer file-size/hash checks.
    let truncatedPiece := original.extract 0 (original.size - 4)
    let truncatedPieceManifest := CatalogFixtures.replaceFatBytes
      input.manifest 0 truncatedPiece
    match Catalog.load (CatalogFixtures.manifestBytes truncatedPieceManifest)
        (pieces.set! 0 truncatedPiece) with
    | .error (.syntax (.piece (.fat 0)) _) => pure ()
    | .error error =>
      IO.eprintln s!"FAIL: semantic piece truncation returned another error: {repr error}"
      ok := false
    | .ok _ =>
      IO.eprintln "FAIL: piece truncated inside the anonymous prefix was accepted"
      ok := false

    -- The final constant payload byte is four bytes before EOF (hint count +
    -- three empty metadata counts follow it). Rebinding only the file hash
    -- must expose the inner constant-address mismatch.
    let payloadIndex := original.size - 5
    let corruptConstant := original.set! payloadIndex
      (original[payloadIndex]! ^^^ (1 : UInt8))
    let corruptManifest := CatalogFixtures.replaceFatBytes
      input.manifest 0 corruptConstant
    match Catalog.load (CatalogFixtures.manifestBytes corruptManifest)
        (pieces.set! 0 corruptConstant) with
    | .error (.constantHash (.fat 0) _ _ _) => pure ()
    | .error error =>
      IO.eprintln s!"FAIL: corrupt constant returned another error: {repr error}"
      ok := false
    | .ok _ =>
      IO.eprintln "FAIL: constant bytes did not bind to their stored address"
      ok := false

  match CatalogFixtures.duplicateChunkInput with
  | .error message =>
    IO.eprintln s!"FAIL: could not construct chunk duplicate fixture: {message}"
    ok := false
  | .ok input =>
    match Catalog.load input.manifestBytes (input.pieces.map (·.bytes)) with
    | .error (.duplicateChunkAddress _ 0 1) => pure ()
    | .error error =>
      IO.eprintln s!"FAIL: chunk duplicate returned another error: {repr error}"
      ok := false
    | .ok _ =>
      IO.eprintln "FAIL: duplicate constant crossed the chunk disjointness gate"
      ok := false

  match CatalogFixtures.invalidMemberInput with
  | .error message =>
    IO.eprintln s!"FAIL: could not construct projection-bound fixture: {message}"
    ok := false
  | .ok input =>
    match Catalog.load input.manifestBytes (input.pieces.map (·.bytes)) with
    | .error (.projectionMemberIndex _ _ 1 1) => pure ()
    | .error error =>
      IO.eprintln s!"FAIL: bad projection member returned another error: {repr error}"
      ok := false
    | .ok _ =>
      IO.eprintln "FAIL: out-of-range projection member crossed store ingress"
      ok := false

  match CatalogFixtures.invalidOrdinalInput with
  | .error message =>
    IO.eprintln s!"FAIL: could not construct constructor-ordinal fixture: {message}"
    ok := false
  | .ok input =>
    match Catalog.load input.manifestBytes (input.pieces.map (·.bytes)) with
    | .error (.constructorOrdinal _ 0 0 7) => pure ()
    | .error error =>
      IO.eprintln s!"FAIL: bad constructor ordinal returned another error: {repr error}"
      ok := false
    | .ok _ =>
      IO.eprintln "FAIL: non-positional constructor cidx crossed store ingress"
      ok := false

  for test in DecodeCheckFixtures.allCases do
    let actual := DecodeCheck.decodeChecked (ser test.constant)
    if !DecodeCheckFixtures.resultEq actual test.expected then
      IO.eprintln s!"FAIL: checked-decode case '{test.name}'"
      IO.eprintln s!"      actual:   {repr actual}"
      IO.eprintln s!"      expected: {repr test.expected}"
      ok := false

  for test in DecodeCheckFixtures.resourceCases do
    let actual := DecodeCheck.decodeChecked test.bytes
    let expected : Except DecodeCheck.Error Constant := .error test.expected
    if !DecodeCheckFixtures.resultEq actual expected then
      IO.eprintln s!"FAIL: checked-decode resource case '{test.name}'"
      IO.eprintln s!"      actual:   {repr actual}"
      IO.eprintln s!"      expected: {repr expected}"
      ok := false

  let mut fuzzCases := 0
  let mut fuzzAccepted := 0
  for constant in DecodeCheckFixtures.validConstants do
    for bytes in DecodeFuzz.mutations (ser constant) do
      match DecodeFuzz.classify bytes with
      | .rejected => pure ()
      | .accepted => fuzzAccepted := fuzzAccepted + 1
      | .roundTripFailure =>
        IO.eprintln s!"FAIL: checked-codec mutation case {fuzzCases} accepted noncanonical bytes (length {bytes.size})"
        ok := false
      fuzzCases := fuzzCases + 1

  let mut fuzzState : UInt64 := 0x6a09e667f3bcc909
  for _ in [:DecodeFuzz.randomCaseCount] do
    fuzzState := DecodeFuzz.nextState fuzzState
    let size := fuzzState.toNat % (DecodeFuzz.maxRandomBytes + 1)
    let (bytes, next) := DecodeFuzz.randomBytes fuzzState size
    fuzzState := next
    match DecodeFuzz.classify bytes with
    | .rejected => pure ()
    | .accepted => fuzzAccepted := fuzzAccepted + 1
    | .roundTripFailure =>
      IO.eprintln s!"FAIL: checked-codec random case {fuzzCases} accepted noncanonical bytes (length {bytes.size})"
      ok := false
    fuzzCases := fuzzCases + 1

  if fuzzAccepted < DecodeCheckFixtures.validConstants.size then
    IO.eprintln s!"FAIL: fuzz harness accepted only {fuzzAccepted} known-valid inputs"
    ok := false

  let boundaryBytes := ser DecodeCheckFixtures.validAxiom
  let boundaryLimits : DecodeCheck.Limits :=
    { maxObjectBytes := boundaryBytes.size
      maxExpressionDepth := 2
      maxUniverseDepth := 1
      maxSequenceLength := 1 }
  let boundaryActual := DecodeCheck.decodeCheckedWith boundaryLimits boundaryBytes
  let boundaryExpected : Except DecodeCheck.Error Constant :=
    .ok DecodeCheckFixtures.validAxiom
  if !DecodeCheckFixtures.resultEq boundaryActual boundaryExpected then
    IO.eprintln s!"FAIL: exact resource boundaries rejected a valid constant: {repr boundaryActual}"
    ok := false

  let objectLimits :=
    { boundaryLimits with maxObjectBytes := boundaryBytes.size - 1 }
  let objectActual := DecodeCheck.decodeCheckedWith objectLimits boundaryBytes
  let objectExpected : Except DecodeCheck.Error Constant :=
    .error (.objectTooLarge boundaryBytes.size (boundaryBytes.size - 1))
  if !DecodeCheckFixtures.resultEq objectActual objectExpected then
    IO.eprintln s!"FAIL: object byte limit was not enforced before decoding: {repr objectActual}"
    ok := false

  let sharedBytes := ser DecodeCheckFixtures.validShared
  let sharedBodies := DecodeCheckFixtures.validShared.info.exprs.toArray
  let sharedLayer1Work := Ix.Compiler.Ixon.Work.layer1NodeVisits
    DecodeCheckFixtures.validShared.sharing sharedBodies
  let exactSharingLimits : DecodeCheck.Limits :=
    { DecodeCheck.defaultLimits with
      maxLayer1NodeVisits := sharedLayer1Work }
  let exactSharingActual := DecodeCheck.decodeCheckedWith exactSharingLimits
    sharedBytes
  let exactSharingExpected : Except DecodeCheck.Error Constant :=
    .ok DecodeCheckFixtures.validShared
  if !DecodeCheckFixtures.resultEq exactSharingActual exactSharingExpected then
    IO.eprintln s!"FAIL: exact layer-1 work boundary rejected a valid constant: {repr exactSharingActual}"
    ok := false
  let tightSharingLimits :=
    { exactSharingLimits with maxLayer1NodeVisits := sharedLayer1Work - 1 }
  let tightSharingActual := DecodeCheck.decodeCheckedWith tightSharingLimits
    sharedBytes
  let tightSharingExpected : Except DecodeCheck.Error Constant :=
    .error (.resource
      ⟨.layer1NodeVisits, sharedLayer1Work, sharedLayer1Work - 1⟩)
  if !DecodeCheckFixtures.resultEq tightSharingActual tightSharingExpected then
    IO.eprintln s!"FAIL: layer-1 work limit returned the wrong failure: {repr tightSharingActual}"
    ok := false

  match DecodeCheck.decodeChecked (ByteArray.mk #[0xff]) with
  | .error (.syntax _) => pure ()
  | actual =>
    IO.eprintln s!"FAIL: raw parser error was not structurally wrapped: {repr actual}"
    ok := false

  let malformedSharing := DecodeCheckFixtures.axiomConstant 0
    (.app (.share 0) (.share 0)) #[] #[] #[]
  if !(match DecodeCheck.checkConstant malformedSharing with
      | .error .sharingInvariant => true
      | _ => false) then
    IO.eprintln "FAIL: direct local validation accepted malformed sharing"
    ok := false

  if Sharing.compressorPolicyId != "compilatrix/ixon-v2-sharing/1" then
    IO.eprintln s!"FAIL: unexpected compressor policy id {Sharing.compressorPolicyId}"
    ok := false
  if Sharing.ixonV2PolicyId !=
      "ix/ixon-v2-sharing@6f18ea907b78d06f7dc0917c43beb385561c35f4" then
    IO.eprintln s!"FAIL: unexpected ixon-v2 policy id {Sharing.ixonV2PolicyId}"
    ok := false
  if wireFormatId != IxRebaseline.wireFormat then
    IO.eprintln s!"FAIL: captured wire id {IxRebaseline.wireFormat} != {wireFormatId}"
    ok := false
  if ser goldenV2 != IxRebaseline.goldenV2Bytes then
    IO.eprintln "FAIL: local goldenV2 bytes differ from the ix capture"
    ok := false
  match (de IxRebaseline.goldenV2Bytes : Except String Constant) with
  | .ok decoded =>
    if decoded != goldenV2 then
      IO.eprintln "FAIL: ix-captured goldenV2 bytes decode to another constant"
      ok := false
  | .error message =>
    IO.eprintln s!"FAIL: ix-captured goldenV2 bytes do not decode: {message}"
    ok := false
  if hashNats (Address.blake3 IxRebaseline.goldenV2Bytes) !=
      IxRebaseline.goldenV2Address then
    IO.eprintln "FAIL: ix-captured goldenV2 bytes hash to another address"
    ok := false
  if IxRebaseline.sharingCaptures.length != SharingPolicy.cases.size then
    IO.eprintln "FAIL: ix sharing capture/case cardinality changed"
    ok := false
  if hashNats SharingPolicy.fingerprint != SharingPolicy.expectedFingerprint then
    IO.eprintln s!"FAIL: sharing policy fingerprint changed: {hashNats SharingPolicy.fingerprint}"
    ok := false

  for c in SharingPolicy.cases do
    match IxRebaseline.sharingCapture? c.name with
    | none =>
      IO.eprintln s!"FAIL: no ix capture artifact for {c.name}"
      ok := false
    | some capture =>
      let inputBytes := runPut (SharingPolicy.putExprArray c.input)
      let outputBytes := runPut (SharingPolicy.putCompression c.ixOutput)
      if inputBytes != capture.input then
        IO.eprintln s!"FAIL: transcribed ix input bytes changed for {c.name}"
        ok := false
      if outputBytes != capture.output then
        IO.eprintln s!"FAIL: transcribed ix output bytes changed for {c.name}"
        ok := false
    let actual := Sharing.compressUnchecked c.input
    if actual != c.v2Output then
      IO.eprintln s!"FAIL: v2 policy vector changed for {c.name}: {repr actual}"
      ok := false
    if c.ixOutput.expanded != c.input then
      IO.eprintln s!"FAIL: transcribed ix vector does not recover {c.name}"
      ok := false
    if c.v2Output.expanded != c.input then
      IO.eprintln s!"FAIL: pinned v2 vector does not recover {c.name}"
      ok := false
    match c.relation with
    | .exactParity =>
      if c.ixOutput != c.v2Output || actual != c.ixOutput then
        IO.eprintln s!"FAIL: common-case ix parity changed for {c.name}"
        ok := false
    | .intentionalV2Delta =>
      if c.ixOutput == c.v2Output then
        IO.eprintln s!"FAIL: declared v2 delta collapsed for {c.name}"
        ok := false
    if Sharing.compress? c.input != some c.v2Output then
      IO.eprintln s!"FAIL: checked compressor diverged from policy vector for {c.name}"
      ok := false
    if Sharing.compressIxonV2? c.input != some c.ixOutput ||
        !Sharing.structuralWF c.ixOutput.table c.ixOutput.bodies ||
        !Sharing.ixonV2Canonical c.ixOutput.bodies c.ixOutput.table then
      IO.eprintln s!"FAIL: pinned ixon-v2 recognizer diverged for {c.name}"
      ok := false
    if !Sharing.layer1WF c.v2Output.table c.v2Output.bodies ||
        !Sharing.deletionLocalOptimal c.v2Output ||
        !Sharing.allEntriesPay c.v2Output ||
        !Sharing.canonical c.v2Output.bodies c.v2Output.table then
      IO.eprintln s!"FAIL: pinned v2 vector violates compressor postconditions for {c.name}"
      ok := false

  let empty := Address.blake3 (ByteArray.mk #[])
  if empty.hash.size != 32 then
    IO.eprintln s!"FAIL: hash size = {empty.hash.size}"
    ok := false
  if hashNats empty != expectedEmptyBlake3 then
    IO.eprintln s!"FAIL: blake3(empty) = {hashNats empty}"
    IO.eprintln s!"      expected       {expectedEmptyBlake3}"
    ok := false

  if !(Address.blake3 (ByteArray.mk #[1, 2, 3])
      == Address.blake3 (ByteArray.mk #[1, 2, 3])) then
    IO.eprintln "FAIL: blake3 nondeterministic"
    ok := false
  if Address.blake3 (ByteArray.mk #[1, 2, 3])
      == Address.blake3 (ByteArray.mk #[1, 2, 4]) then
    IO.eprintln "FAIL: blake3 input-insensitive"
    ok := false

  if Sharing.exprHash (.lam .many (.sort 0) (.var 0)) ==
      Sharing.exprHash (.lam .linear (.sort 0) (.var 0)) then
    IO.eprintln "FAIL: sharing Merkle hash omitted the v2 lambda mode"
    ok := false

  let repeated : Expr := .ref 17 #[0, 1, 2]
  let repeatedInput : Array Expr := #[repeated, repeated, repeated]
  let repeatedUnits := Ix.Compiler.Ixon.Work.exprArrayUnits repeatedInput
  match Sharing.compressWithLimit repeatedUnits repeatedInput with
  | .ok (some _) => pure ()
  | actual =>
    IO.eprintln s!"FAIL: exact compressor work boundary rejected input: {repr actual}"
    ok := false
  match Sharing.compressWithLimit (repeatedUnits - 1) repeatedInput with
  | .error exceeded =>
    if exceeded !=
        (⟨.compressionInputUnits, repeatedUnits, repeatedUnits - 1⟩ :
          Ix.Compiler.Ixon.Work.Exceeded) then
      IO.eprintln s!"FAIL: compressor work limit returned the wrong failure: {repr exceeded}"
      ok := false
  | actual =>
    IO.eprintln s!"FAIL: compressor crossed an over-budget input: {repr actual}"
    ok := false
  match Sharing.compress? repeatedInput with
  | none =>
    IO.eprintln "FAIL: compressor rejected share-free repeated input"
    ok := false
  | some out =>
    let expectedBodies : Array Expr := #[.share 0, .share 0, .share 0]
    let expectedTable : Array Expr := #[repeated]
    if out.bodies != expectedBodies || out.table != expectedTable then
      IO.eprintln s!"FAIL: unexpected canonical compression {repr out}"
      ok := false
    if out.bodies.map (Sharing.inlineExpr out.table) != repeatedInput then
      IO.eprintln "FAIL: inlining compressed roots did not recover input"
      ok := false
    if !Sharing.deletionLocalOptimal out || !Sharing.allEntriesPay out then
      IO.eprintln "FAIL: compressor output failed the exact deletion audit"
      ok := false
    if !Sharing.canonical out.bodies out.table then
      IO.eprintln "FAIL: compressor output was not a recompression fixpoint"
      ok := false

  -- Both the lambda and its repeated domain are initially profitable. Once
  -- the lambda is shared, the domain occurs only once in residual syntax, so
  -- the exact audit must remove that stale nested candidate.
  let nestedLeaf : Expr := .ref 23 #[0, 1, 2]
  let nested : Expr := .lam .many nestedLeaf (.var 0)
  let nestedInput : Array Expr := #[nested, nested, nested]
  match Sharing.compress? nestedInput with
  | none =>
    IO.eprintln "FAIL: compressor rejected nested repeated input"
    ok := false
  | some out =>
    if out.table != #[nested] || out.bodies != #[.share 0, .share 0, .share 0] then
      IO.eprintln s!"FAIL: exact audit retained a stale nested candidate {repr out}"
      ok := false
    if out.bodies.map (Sharing.inlineExpr out.table) != nestedInput then
      IO.eprintln "FAIL: audited nested compression did not inline to input"
      ok := false
    if !Sharing.deletionLocalOptimal out || !Sharing.allEntriesPay out ||
        !Sharing.canonical out.bodies out.table then
      IO.eprintln "FAIL: audited nested compression failed its postconditions"
      ok := false

  let compressionCorpus : Array (Array Expr) := #[
    #[],
    repeatedInput,
    nestedInput,
    #[.sort 0, .var 0, .nat 0],
    #[.ref 130 #[0, 129], .ref 130 #[0, 129], .ref 130 #[0, 129]],
    #[.lam .many (.ref 9 #[0]) (.var 0),
      .lam .many (.ref 9 #[0]) (.var 0),
      .lam .linear (.ref 9 #[0]) (.var 0)],
    #[.letE false (.sort 0) repeated (.app (.var 0) repeated),
      .letE false (.sort 0) repeated (.app (.var 0) repeated)],
    #[.prj 0 1 repeated, .prj 0 1 repeated, .prj 0 1 repeated],
    #[.app (.app (.ref 3 #[]) repeated) repeated,
      .app (.app (.ref 3 #[]) repeated) repeated]
  ]
  for input in compressionCorpus do
    match Sharing.compress? input with
    | none =>
      IO.eprintln s!"FAIL: compressor rejected corpus input {repr input}"
      ok := false
    | some out =>
      let heuristic := Sharing.compressUnchecked input
      if !Sharing.layer1WF heuristic.table heuristic.bodies ||
          !Sharing.allEntriesPay heuristic then
        IO.eprintln s!"FAIL: raw heuristic violated its corpus invariants {repr heuristic}"
        ok := false
      if out != heuristic then
        IO.eprintln s!"FAIL: certified fallback unexpectedly activated {repr input}"
        ok := false
      if Sharing.compress? input != some out then
        IO.eprintln "FAIL: compressor was nondeterministic"
        ok := false
      if !Sharing.layer1WF out.table out.bodies then
        IO.eprintln s!"FAIL: compressor emitted a non-layer-1 table {repr out}"
        ok := false
      if out.bodies.map (Sharing.inlineExpr out.table) != input then
        IO.eprintln s!"FAIL: corpus compression did not inline to input {repr out}"
        ok := false
      if !Sharing.deletionLocalOptimal out || !Sharing.allEntriesPay out then
        IO.eprintln s!"FAIL: corpus compression retained a non-paying entry {repr out}"
        ok := false
      if !Sharing.canonical out.bodies out.table then
        IO.eprintln s!"FAIL: corpus output was not canonical {repr out}"
        ok := false

  let doublingTable := WorkBudgetFixtures.doublingTable 3
  let doublingBodies := WorkBudgetFixtures.doublingBodies doublingTable
  let doublingLayer1 := Ix.Compiler.Ixon.Work.layer1NodeVisits doublingTable
    doublingBodies
  let doublingExpanded :=
    (Ix.Compiler.Ixon.Work.expandedUnits? doublingTable doublingBodies).getD 0
  if doublingExpanded != 31 ||
      !Sharing.layer1WF doublingTable doublingBodies then
    IO.eprintln s!"FAIL: sharing-expansion budget fixture changed (expanded {doublingExpanded})"
    ok := false
  let exactCanonicalLimits : Sharing.ResourceLimits :=
    { maxLayer1NodeVisits := doublingLayer1
      maxCompressionInputUnits := doublingExpanded }
  match Sharing.canonicalWith exactCanonicalLimits doublingBodies doublingTable with
  | .ok _ => pure ()
  | .error exceeded =>
    IO.eprintln s!"FAIL: exact canonicalization work boundary rejected input: {repr exceeded}"
    ok := false
  match Sharing.canonicalWith
      { exactCanonicalLimits with
        maxLayer1NodeVisits := doublingLayer1 - 1 }
      doublingBodies doublingTable with
  | .error exceeded =>
    if exceeded !=
        (⟨.layer1NodeVisits, doublingLayer1, doublingLayer1 - 1⟩ :
          Ix.Compiler.Ixon.Work.Exceeded) then
      IO.eprintln s!"FAIL: canonical layer-1 limit returned the wrong failure: {repr exceeded}"
      ok := false
  | actual =>
    IO.eprintln s!"FAIL: canonicalizer crossed its layer-1 budget: {repr actual}"
    ok := false
  match Sharing.canonicalWith
      { exactCanonicalLimits with
        maxCompressionInputUnits := doublingExpanded - 1 }
      doublingBodies doublingTable with
  | .error exceeded =>
    if exceeded !=
        (⟨.compressionInputUnits, doublingExpanded, doublingExpanded - 1⟩ :
          Ix.Compiler.Ixon.Work.Exceeded) then
      IO.eprintln s!"FAIL: canonical expansion limit returned the wrong failure: {repr exceeded}"
      ok := false
  | actual =>
    IO.eprintln s!"FAIL: canonicalizer materialized an over-budget expansion: {repr actual}"
    ok := false

  let c : Constant :=
    { info := .axio { isUnsafe := false, lvls := 1, typ := .sort 3 }
      sharing := #[], refs := #[], univs := #[.zero] }
  if ser c != IxRebaseline.sampleAxiomBytes then
    IO.eprintln "FAIL: local sample axiom bytes differ from the ix capture"
    ok := false
  match (de IxRebaseline.sampleAxiomBytes : Except String Constant) with
  | .ok decoded =>
    if decoded != c then
      IO.eprintln "FAIL: ix-captured sample bytes decode to another constant"
      ok := false
  | .error message =>
    IO.eprintln s!"FAIL: ix-captured sample bytes do not decode: {message}"
    ok := false
  if hashNats (Address.blake3 IxRebaseline.sampleAxiomBytes) !=
      IxRebaseline.sampleAxiomAddress then
    IO.eprintln "FAIL: ix-captured sample bytes hash to another address"
    ok := false
  -- The upstream codec vectors intentionally contain synthetic out-of-range
  -- table indices. Their raw hashes stay frozen above, but they are not
  -- semantic constants and must not cross the strengthened address gate.
  if c.address?.isSome then
    IO.eprintln "FAIL: locally malformed sample axiom acquired an address"
    ok := false
  if goldenV2.address?.isSome then
    IO.eprintln "FAIL: locally malformed goldenV2 fixture acquired an address"
    ok := false

  let addressable := DecodeCheckFixtures.validAxiom
  match addressable.address? with
  | none =>
    IO.eprintln "FAIL: checked canonical constant was not addressable"
    ok := false
  | some address =>
    if address != Address.blake3 (ser addressable) then
      IO.eprintln "FAIL: checked address gate hashed different bytes"
      ok := false

  let addressBodies := addressable.info.exprs.toArray
  let addressLayer1 := Ix.Compiler.Ixon.Work.layer1NodeVisits
    addressable.sharing addressBodies
  let addressExpanded :=
    (Ix.Compiler.Ixon.Work.expandedUnits? addressable.sharing
      addressBodies).getD 0
  let exactAddressLimits : Constant.AddressLimits :=
    { ingress :=
        { DecodeCheck.defaultLimits with
          maxLayer1NodeVisits := addressLayer1 }
      sharing :=
        { maxLayer1NodeVisits := addressLayer1
          maxCompressionInputUnits := addressExpanded } }
  match addressable.addressCheckedWith exactAddressLimits with
  | .ok address =>
    if address != Address.blake3 (ser addressable) then
      IO.eprintln "FAIL: bounded address gate hashed different bytes"
      ok := false
  | .error error =>
    IO.eprintln s!"FAIL: exact bounded address gate rejected input: {repr error}"
    ok := false
  let tightAddressLimits : Constant.AddressLimits :=
    { exactAddressLimits with sharing :=
        { exactAddressLimits.sharing with
          maxCompressionInputUnits := addressExpanded - 1 } }
  match addressable.addressCheckedWith tightAddressLimits with
  | .error (.resource exceeded) =>
    if exceeded !=
        (⟨.compressionInputUnits, addressExpanded, addressExpanded - 1⟩ :
          Ix.Compiler.Ixon.Work.Exceeded) then
      IO.eprintln s!"FAIL: bounded address gate returned the wrong resource failure: {repr exceeded}"
      ok := false
  | actual =>
    IO.eprintln s!"FAIL: bounded address gate crossed its compressor budget: {repr actual}"
    ok := false

  match DecodeCheck.encodeChecked addressable with
  | .ok bytes =>
    if bytes != ser addressable then
      IO.eprintln "FAIL: checked writer changed canonical bytes"
      ok := false
  | .error error =>
    IO.eprintln s!"FAIL: checked writer rejected valid constant: {repr error}"
    ok := false

  match DecodeCheck.encodeChecked c with
  | .error (.invalid (.universeIndex _ 3 1)) => pure ()
  | .error error =>
    IO.eprintln s!"FAIL: checked writer returned another error: {repr error}"
    ok := false
  | .ok _ =>
    IO.eprintln "FAIL: checked writer accepted the malformed sample"
    ok := false

  let merelyLayer1 : Constant :=
    { info := .axio
        { isUnsafe := false, lvls := 0
          typ := .app (.share 0) (.share 0) }
      sharing := #[.sort 0], refs := #[], univs := #[.zero] }
  if !merelyLayer1.sharingWF then
    IO.eprintln "FAIL: noncanonical identity fixture was not layer-1 valid"
    ok := false
  if merelyLayer1.canonicalSharing then
    IO.eprintln "FAIL: redundant small sharing table passed layer 2"
    ok := false
  if merelyLayer1.address?.isSome then
    IO.eprintln "FAIL: merely layer-1 constant crossed the address boundary"
    ok := false

  if ok then
    IO.println "tests-ok"
    return 0
  else
    return 1
