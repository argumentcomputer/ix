import CompilatrixTests.Support
import CompilatrixTests.Addressing.Fixtures
import Compilatrix.IxIR1.HPTCacheDirIO
import Compilatrix.IxIR1.HPTCacheIO
import Compilatrix.IxIR1.HPTPAPFuseProgram
import Compilatrix.IxIR1.HPTFetchForward
import Compilatrix.IxIR1.HPTDestroy
import Compilatrix.IxIR1.Reachability
import Compilatrix.Pipeline

namespace CompilatrixTests

open Compilatrix.Ixon

namespace HPTFixtures

open Compilatrix
open Compilatrix.Ixon

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
                match ← (Compilatrix.DurableSync.file path).toBaseIO,
                    ← (Compilatrix.DurableSync.directory directory).toBaseIO,
                    ← (Compilatrix.DurableSync.file directory).toBaseIO,
                    ← (Compilatrix.DurableSync.directory path).toBaseIO with
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

end CompilatrixTests
