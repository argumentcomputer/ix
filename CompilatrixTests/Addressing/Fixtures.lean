import CompilatrixTests.Support.Lowering
import CompilatrixTests.Support
import Compilatrix.IxIR0.Examples
import Compilatrix.IxIR0.ReaddressOracleExamples
import Compilatrix.IxIR1.LowerFullyAddressed
import Compilatrix.IxIR1.NoReuseAddressed
import Compilatrix.EraseAddressedSim
import Compilatrix.IxIR2.Pipeline
import Compilatrix.IxIR2.Eval

namespace CompilatrixTests

open Compilatrix.Ixon

namespace IxIRAddressFixtures

def ir0Decl : Compilatrix.IxIR0.Decl :=
  .recursor 2 false #[
    ⟨0, .lit (.nat 128)⟩,
    ⟨1, .app (.var 1) (.lit (.str "x"))⟩]

def ir1Decl : Compilatrix.IxIR1.Decl :=
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
  match Compilatrix.IxIR0.Decl.decodePreimage expectedIr0Bytes with
  | .ok declaration => declaration.preimage == expectedIr0Bytes
  | .error _ => false

def ir1DecodeOk : Bool :=
  match Compilatrix.IxIR1.Decl.decodePreimage expectedIr1Bytes with
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
    Compilatrix.IxIR0.Decl.addressDomain ++ ByteArray.mk #[3, 128, 0]),
  ("invalid nested UTF-8",
    Compilatrix.IxIR0.Decl.addressDomain ++
      ByteArray.mk #[0, 0, 6, 1, 1, 0xff]),
  ("truncated declaration",
    expectedIr0Bytes.extract 0 (expectedIr0Bytes.size - 1))]

def ir1Malformed : List (String × ByteArray) := [
  ("trailing byte", expectedIr1Bytes.push 0),
  ("wrong domain", expectedIr1Bytes.set! 0 0),
  ("invalid declaration tag", expectedIr1Bytes.set! 25 0xff),
  ("nonminimal LEB128",
    Compilatrix.IxIR1.Decl.addressDomain ++ ByteArray.mk #[1, 128, 0]),
  ("invalid nested UTF-8",
    Compilatrix.IxIR1.Decl.addressDomain ++
      ByteArray.mk #[0, 0, 0, 0, 0, 1, 1, 1, 0xff]),
  ("truncated declaration",
    expectedIr1Bytes.extract 0 (expectedIr1Bytes.size - 1))]

def ir0Rejects (bytes : ByteArray) : Bool :=
  rejected (Compilatrix.IxIR0.Decl.decodePreimage bytes)

def ir1Rejects (bytes : ByteArray) : Bool :=
  rejected (Compilatrix.IxIR1.Decl.decodePreimage bytes)

end IxIRAddressFixtures

namespace IxIRReaddressFixtures

open Compilatrix.IxIR1

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
      oracle := Compilatrix.IxIR1.Lower.tgtOracle }
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

def nestedExpression : Compilatrix.IxIR0.Expr :=
  .app
    (.lam .many
      (.app (.lam .many (.var 1))
        (Compilatrix.IxIR0.Examples.natE 2)))
    (Compilatrix.IxIR0.Examples.natE 3)

def nestedLowering : Except String Readdress.Result :=
  Compilatrix.IxIR1.Lower.lowerAllIndexedAddressed
    Compilatrix.IxIR0.Examples.declList nestedExpression

def loweringAudits (source : List (Address × Compilatrix.IxIR0.Decl))
    (main : Compilatrix.IxIR0.Expr) (result : Readdress.Result) : Bool :=
  match (Compilatrix.IxIR1.Lower.lowerAllIndexedAction source main
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
      oracle := Compilatrix.IxIR1.Lower.tgtOracle }
  -- The corpus declarations themselves contribute three wrappers/lifts;
  -- the nested expression contributes its inner and outer lifted functions.
  result.addressMap.length == 5 && result.generated.length == 5 &&
    contentHexes result == expectedNestedContent &&
    result.noTransientKeys && result.noTransientReferences &&
    result.generatedAreAddressed &&
    loweringAudits Compilatrix.IxIR0.Examples.declList nestedExpression
      result &&
    match runMain ctx result.main with
    | .ok (store, value) =>
        (Compilatrix.IxIR1.Lower.treeOfR store 1000 value).bind
          Compilatrix.IxIR1.Lower.natT? == some 3
    | .error _ => false

def wrapperExpression : Compilatrix.IxIR0.Expr :=
  .app (.ref Compilatrix.IxIR0.Examples.pairMk)
    (Compilatrix.IxIR0.Examples.natE 1)

def wrapperLowering : Except String Readdress.Result :=
  Compilatrix.IxIR1.Lower.lowerAllIndexedAddressed
    Compilatrix.IxIR0.Examples.declList wrapperExpression

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
    loweringAudits Compilatrix.IxIR0.Examples.declList wrapperExpression
      result

/-- A constructor address is a source identity even though constructors emit
no raw IxIR₁ declaration.  Deliberately collide it with the first transient
lambda key and ensure the production boundary rejects the would-be rewrite. -/
def protectedCtorKey : Address :=
  Compilatrix.IxIR1.Lower.synthAddr 0

def protectedSourceIdentityRejected : Bool :=
  let source : List (Address × Compilatrix.IxIR0.Decl) :=
    [(protectedCtorKey, .ctor 0 0)]
  let expression : Compilatrix.IxIR0.Expr :=
    .app (.lam .many (.var 0)) (.ref protectedCtorKey)
  match Compilatrix.IxIR1.Lower.lowerAllIndexedAddressed source expression with
  | .error message =>
      message == "generated address map rewrites a protected source identity"
  | .ok _ => false

end IxIRReaddressFixtures

namespace IxIR1ReaddressAllFixtures

open Compilatrix.IxIR1
open Compilatrix.IxIR1.ReaddressAll

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
    let address := Compilatrix.IxIR1.Lower.synthAddr index
    let body :=
      if index + 1 < longChainLength then
        .letOp (.call (Compilatrix.IxIR1.Lower.synthAddr (index + 1)) #[])
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
  Compilatrix.IxIR1.Lower.lowerAllIndexedFullyAddressed
    Compilatrix.IxIR0.Examples.declList
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
    (source : List (Address × Compilatrix.IxIR0.Decl))
    (main : Compilatrix.IxIR0.Expr)
    (result : ReaddressAll.Result) : Bool :=
  match (Compilatrix.IxIR1.Lower.lowerAllIndexedAction source main
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
        (Compilatrix.IxIR1.Lower.constructorIdentities source).all fun address =>
          Readdress.Renaming.apply result.addressMap address == address

def fullyNestedOk (result : ReaddressAll.Result) : Bool :=
  let ctx := result.addressedCtx Compilatrix.IxIR1.Lower.tgtOracle
  result.addressMap.map (fun entry => Address.toHex entry.2) ==
      expectedFullyNestedTargets && result.blocks.isEmpty &&
    result.noTransientKeys && result.noTransientReferences &&
    result.contentAddressed &&
    fullyLoweredAudit Compilatrix.IxIR0.Examples.declList
      IxIRReaddressFixtures.nestedExpression result &&
    match runMain ctx result.main with
    | .ok (store, value) =>
        (Compilatrix.IxIR1.Lower.treeOfR store 1000 value).bind
          Compilatrix.IxIR1.Lower.natT? == some 3
    | .error _ => false

def cyclicSourceKey : Address := Address.replicate 0xb7

/-- Lowering this definition emits a closure whose body refers back to the
source function, while the source function body refers to that closure. -/
def cyclicSourceDeclaration : Compilatrix.IxIR0.Decl :=
  .defn .shared
    (.lam .many
      (.app (.lam .many (.ref cyclicSourceKey)) (.var 0)))

def fullyCyclicLowering : Except String ReaddressAll.Result :=
  Compilatrix.IxIR1.Lower.lowerAllIndexedFullyAddressed
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
  let source : List (Address × Compilatrix.IxIR0.Decl) :=
    [(Compilatrix.IxIR1.Lower.synthAddr 0, .ctor 0 0)]
  let expression : Compilatrix.IxIR0.Expr :=
    .app (.lam .many (.var 0))
      (.ref (Compilatrix.IxIR1.Lower.synthAddr 0))
  match Compilatrix.IxIR1.Lower.lowerAllIndexedFullyAddressed
      source expression with
  | .error message =>
      message == s!"IxIR1 declaration producer key overlaps reserved identity {Address.toHex (Compilatrix.IxIR1.Lower.synthAddr 0)}"
  | .ok _ => false

end IxIR1ReaddressAllFixtures

namespace IxIRMutualBlockFixtures

open Compilatrix.IxIR0
open Compilatrix.IxIR0.MutualBlock

def oldA : Address := Address.replicate 0xf1
def oldB : Address := Address.replicate 0xf2
def external : Address := Address.replicate 0x42

/-- A genuine local cycle: the definition points to the recursor and one
recursor rule points back to the definition.  The extra external edge checks
that only block-local names are abstracted. -/
def raw : List (Address × Compilatrix.IxIR0.Decl) :=
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
    List (Address × Compilatrix.IxIR0.Decl) :=
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
def renamedRaw : List (Address × Compilatrix.IxIR0.Decl) :=
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

open Compilatrix.IxIR1
open Compilatrix.IxIR1.MutualBlock

def oldA : Address := Address.replicate 0xc1
def oldB : Address := Address.replicate 0xc2
def external : Address := Address.replicate 0xc3

/-- A source/generated-style cycle with a stable external oracle edge nested
beneath a case alternative. -/
def declarationA : Compilatrix.IxIR1.Decl :=
  .fn ⟨1, .shared, true,
    .letOp (.call oldB #[.var 0]) (.ret (.var 0))⟩

def declarationB : Compilatrix.IxIR1.Decl :=
  .fn ⟨0, .unique, false,
    .case .erased false #[.mk 0 0
      (.letOp (.papp oldA #[])
        (.letOp (.extern external #[]) (.ret .erased)))]⟩

def raw : List (Address × Compilatrix.IxIR1.Decl) :=
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
    List (Address × Compilatrix.IxIR1.Decl) →
      List (Address × Compilatrix.IxIR1.Decl) → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      left.1 == right.1 &&
        Compilatrix.IxIR1.Readdress.Decl.structurallyEq left.2 right.2 &&
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
    List (Address × Compilatrix.IxIR1.Decl) :=
  let rename := Compilatrix.IxIR1.Readdress.Renaming.apply result.addressMap
  raw.map fun entry =>
    (rename entry.1,
      Compilatrix.IxIR1.Readdress.Decl.mapAddresses rename entry.2)

def concreteShape (result : MutualBlock.Result) : Bool :=
  match result.members with
  | [(addressA, declarationA), (addressB, declarationB)] =>
      Compilatrix.IxIR1.Readdress.Decl.references declarationA == [addressB] &&
        Compilatrix.IxIR1.Readdress.Decl.references declarationB ==
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

def renamedRaw : List (Address × Compilatrix.IxIR1.Decl) :=
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

open Compilatrix Compilatrix.Ixon

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

open Compilatrix
open Compilatrix.Ixon

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
  match Compilatrix.IxIR2.Pipeline.compileValidated
      sharedPipelineConstants projection with
  | .error _ => false
  | .ok attached =>
      let artifact := attached.target.artifact
      let context := Compilatrix.IxIR2.Eval.Context.ofProgram
        artifact.program artifact.validationContext.schemas
      attached.sidecars.parameterEntries.length ==
        attached.source.artifact.targetDecls.length &&
        attached.sidecars.sourceNoReuse artifact.trace &&
        attached.sidecars.tracePappsSafe artifact.trace &&
        attached.sidecars.traceExactCaseTargetsMatch artifact.trace &&
        !artifact.trace.positions.isEmpty &&
        match Compilatrix.IxIR2.Eval.runMain context .logical
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

open Compilatrix
open Compilatrix.IxIR1

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

namespace ReaddressOracleFixtures

open Compilatrix
open Compilatrix.Ixon

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

end CompilatrixTests
