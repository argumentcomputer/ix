import Ix.Compiler.IxIR1.HPTProduce
import Ix.Compiler.IxIR.Decode

/-!
# Persistent checked HPT cache ingress

Cache bytes are untrusted. Each dependency-ordered lookup is keyed by the
current program artifact and the addresses of summaries already accepted in
this run. A hit must decode canonically, reproduce that exact query, pass its
content-address audit, fit the producer/checker resource envelope, and satisfy
the artifact-local post-fixpoint against the current summary environment.

Missing or invalid records rebuild only that artifact with the canonical
producer. Downstream queries then see the accepted/rebuilt summary address, so
the existing dependency cone determines subsequent hits naturally. The final
assembled certificate crosses the ordinary whole-program `runWith` checker;
cache scheduling is not a new trust boundary.
-/

namespace Ix.Compiler.IxIR1.HPT.Cache

open Ix.Compiler.Ixon
open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR

/-- Versioned persistent record framing, independent of summary hash domains. -/
def recordDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir1/hpt-cache-record/2" ++ Encoding.tag 0

/-- Versioned framing for a deterministic collection of keyed records. -/
def storeDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir1/hpt-cache-store/1" ++ Encoding.tag 0

private def memberBytes (member : Address × Fact) : ByteArray :=
  Encoding.address member.1 ++ member.2.bytes

/-- Canonical persistent spelling of one checked summary artifact. -/
def encodeArtifact (artifact : Artifact) : ByteArray :=
  recordDomain ++ Encoding.tag artifact.kind.tag ++
    Encoding.address artifact.programIdentity ++
    Encoding.list Encoding.address artifact.dependencies ++
    Encoding.address artifact.cacheKey ++
    Encoding.list memberBytes artifact.members ++
    Encoding.address artifact.address

/-- Cache-specific byte and entry controls around the producer/checker limits.
Oversized records in an already constructed in-memory store are invalid hits;
persistent ingress and publication reject them before allocation/output. The
aggregate input cap is a hard admission boundary before indexing. -/
structure Limits where
  producer : ProducerLimits := {}
  maxEntries : Nat := 32 * 1024
  maxEntryBytes : Nat := 4 * 1024 * 1024
  maxBytes : Nat := 64 * 1024 * 1024
  maxWriteBytes : Nat := 64 * 1024 * 1024
  /-- Complete framed store-file bytes, including keys and length prefixes. -/
  maxStoreBytes : Nat := 72 * 1024 * 1024
  deriving BEq, Repr

def defaultLimits : Limits := {}

/-- Address-keyed persistent records. Extra stale keys are permitted; duplicate
keys are rejected before lookup so list order cannot choose a winner. -/
structure Store where
  entries : List (Address × ByteArray)
  deriving BEq, Inhabited

private def storeEntryBytes (entry : Address × ByteArray) : ByteArray :=
  Encoding.address entry.1 ++ Encoding.blob entry.2

private def storeEntrySize (entry : Address × ByteArray) : Nat :=
  (Encoding.address entry.1).size +
    (Encoding.nat entry.2.size).size + entry.2.size

/-- Sort lookup keys lexicographically without changing their record bytes.
This makes snapshots independent of insertion and rebuild history. -/
def Store.canonicalize (store : Store) : Store :=
  ⟨(store.entries.toArray.qsort fun left right =>
      Ixon.Merkle.compareAddress left.1 right.1 == .lt).toList⟩

/-- Canonical deterministic spelling of a complete persistent store. -/
def encodeStore (store : Store) : ByteArray :=
  storeDomain ++ Encoding.list storeEntryBytes store.canonicalize.entries

/-- Exact size of the canonical complete-store spelling, computed without
materializing that spelling. Sorting does not affect this sum. Filesystem
adapters use it to enforce the complete-file budget before opening a staging
file. -/
def Store.framedSize (store : Store) : Nat :=
  storeDomain.size + (Encoding.nat store.entries.length).size +
    store.entries.foldl (fun total entry => total + storeEntrySize entry) 0

structure IngressStats where
  entries : Nat := 0
  bytes : Nat := 0
  deriving BEq, Repr, Inhabited

/-- Result of an untrusted cache lookup. Storage adapters may distinguish an
absent key from a present chunk whose outer framing could not be admitted, so
the latter is reported as a local rejection and rebuilt instead of aborting an
otherwise usable cache. -/
inductive LookupResult where
  | missing
  | found (bytes : ByteArray)
  | rejected (reason : String)
  deriving BEq

private def enforce (label : String) (actual limit : Nat) :
    Except String Unit :=
  if actual ≤ limit then .ok ()
  else .error s!"HPT cache {label} budget exceeded: {actual} > {limit}"

/-- Linear aggregate admission scan and duplicate-key rejection. -/
def Store.preflight (limits : Limits) (store : Store) :
    Except String IngressStats := do
  let mut entries := 0
  let mut bytes := 0
  for entry in store.entries do
    entries := entries + 1
    enforce "entry" entries limits.maxEntries
    bytes := bytes + entry.2.size
    enforce "input-byte" bytes limits.maxBytes
  let index := AddressEnv.build (store.entries.map fun entry => (entry.1, ()))
  if index.size != entries then
    throw "HPT cache contains duplicate lookup keys"
  return { entries, bytes }

/-- Validate individual and aggregate payload policy, canonicalize lookup
order, and enforce the exact complete-file budget without constructing the
complete byte array. -/
def prepareStoreWith (limits : Limits) (store : Store) :
    Except String Store := do
  let _ ← store.preflight limits
  for entry in store.entries do
    enforce "record-byte" entry.2.size limits.maxEntryBytes
  let canonical := store.canonicalize
  enforce "store-byte" canonical.framedSize limits.maxStoreBytes
  return canonical

/-- Validate individual/aggregate payload policy and produce the canonical
framed store. -/
def encodeStoreWith (limits : Limits) (store : Store) :
    Except String ByteArray := do
  let canonical ← prepareStoreWith limits store
  return storeDomain ++ Encoding.list storeEntryBytes canonical.entries

private def Store.index (store : Store) : AddressEnv.Index ByteArray :=
  AddressEnv.build store.entries

private def getNatBoundedFuel (label : String) : Nat → Nat → GetM Nat
  | _, 0 => throw s!"HPT cache {label} numeral exceeds its bounded width"
  | limit, fuel + 1 => do
      let byte ← getU8
      let low := byte.toNat % 128
      if byte.toNat < 128 then
        if low ≤ limit then return low
        throw s!"HPT cache {label} value exceeds {limit}"
      let high ← getNatBoundedFuel label (limit / 128) fuel
      let value := low + 128 * high
      if value ≤ limit then return value
      throw s!"HPT cache {label} value exceeds {limit}"

/-- Read no more chunks than the largest canonical numeral permitted by the
policy. Recursive quotients are capped before multiplication, so hostile LEB
input cannot first construct an effectively unbounded `Nat`. -/
private def getNatBounded (label : String) (limit : Nat) : GetM Nat :=
  getNatBoundedFuel label limit (Encoding.nat limit).size

private def getCount (label : String) (limit : Nat) : GetM Nat := do
  getNatBounded s!"{label} count" limit

private def getList (label : String) (limit : Nat) (getOne : GetM α) :
    GetM (List α) := do
  let count ← getCount label limit
  let mut values : Array α := #[]
  for _ in [:count] do
    values := values.push (← getOne)
  return values.toList

private def getCtorId (limits : Limits) : GetM CtorId := do
  let block ← Decode.getAddress
  let indIdx ← getNatBounded "constructor inductive-index"
    limits.producer.checker.maxShapeIndex
  let cidx ← getNatBounded "constructor index"
    limits.producer.checker.maxShapeIndex
  return ⟨block, indIdx, cidx⟩

mutual

private def getFieldShape (limits : Limits) (remainingDepth : Nat) :
    GetM FieldShape := do
  match (← getU8).toNat with
  | 0 =>
      let identity ← getCtorId limits
      match (← getU8).toNat with
      | 0 => return .ctor identity none
      | 1 =>
          let fields ← getList "nested-constructor-field"
            limits.producer.checker.maxFieldsPerShape
            (getFieldFact limits remainingDepth)
          return .ctor identity (some fields)
      | tag => throw s!"HPT cache nested-constructor-field option tag {tag}"
  | 1 =>
      let function ← Decode.getAddress
      let filled ← getNatBounded "PAP fill"
        limits.producer.checker.maxShapeIndex
      return .pap function filled
  | tag => throw s!"HPT cache field-shape tag {tag}"
termination_by 2 * remainingDepth + 1
decreasing_by omega

private def getFieldFact (limits : Limits) : Nat → GetM FieldFact
  | 0 => throw "HPT cache recursive field depth exceeds configured limit"
  | remainingDepth + 1 => do
      let mayScalar ← Decode.getBool
      let unknownHeap ← Decode.getBool
      let shapes ← getList "field-shape"
        limits.producer.checker.maxShapesPerFact
        (getFieldShape limits remainingDepth)
      return ⟨mayScalar, unknownHeap, shapes⟩
termination_by remainingDepth => 2 * remainingDepth
decreasing_by omega

end

private def getHeapShape (limits : Limits) : GetM HeapShape := do
  match (← getU8).toNat with
  | 0 =>
      let identity ← getCtorId limits
      match (← getU8).toNat with
      | 0 => return .ctor identity none
      | 1 =>
          let fields ← getList "constructor-field"
            limits.producer.checker.maxFieldsPerShape
            (getFieldFact limits limits.producer.checker.maxFieldDepth)
          return .ctor identity (some fields)
      | tag => throw s!"HPT cache constructor-field option tag {tag}"
  | 1 =>
      let function ← Decode.getAddress
      let filled ← getNatBounded "PAP fill"
        limits.producer.checker.maxShapeIndex
      return .pap function filled
  | tag => throw s!"HPT cache heap-shape tag {tag}"

private def getFact (limits : Limits) : GetM Fact := do
  let mayScalar ← Decode.getBool
  let unknownHeap ← Decode.getBool
  let shapes ← getList "result-shape"
    limits.producer.checker.maxShapesPerFact (getHeapShape limits)
  return ⟨mayScalar, unknownHeap, shapes⟩

private def getKind : GetM ArtifactKind := do
  match (← getU8).toNat with
  | 0 => return .stable
  | 1 => return .ordinary
  | 2 => return .mutual
  | tag => throw s!"HPT cache artifact-kind tag {tag}"

private def getMember (limits : Limits) : GetM (Address × Fact) := do
  return (← Decode.getAddress, ← getFact limits)

private def getArtifact (limits : Limits) : GetM Artifact := do
  Decode.expectBytes recordDomain
  let kind ← getKind
  let programIdentity ← Decode.getAddress
  let dependencies ← getList "dependency"
    limits.producer.checker.maxProgramArtifacts Decode.getAddress
  let cacheKey ← Decode.getAddress
  let members ← getList "member"
    limits.producer.checker.maxCertificateMembers (getMember limits)
  let address ← Decode.getAddress
  return ⟨kind, programIdentity, members, dependencies, cacheKey, address⟩

private def getStore (limits : Limits) : GetM Store := do
  Decode.expectBytes storeDomain
  let count ← getCount "store-entry" limits.maxEntries
  let mut entries : Array (Address × ByteArray) := #[]
  let mut totalBytes := 0
  for _ in [:count] do
    let key ← Decode.getAddress
    let size ← getNatBounded "record-byte count" limits.maxEntryBytes
    totalBytes := totalBytes + size
    if totalBytes > limits.maxBytes then
      throw s!"HPT cache input-byte count exceeds {limits.maxBytes}"
    let bytes ← getBytes size
    entries := entries.push (key, bytes)
  return ⟨entries.toList⟩

/-- Strict full-consumption, byte-for-byte canonical record decoder. -/
def decodeArtifactWith (limits : Limits) (bytes : ByteArray) :
    Except String Artifact := do
  enforce "record-byte" bytes.size limits.maxEntryBytes
  Decode.runCanonical (getArtifact limits) encodeArtifact bytes

def decodeArtifact (bytes : ByteArray) : Except String Artifact :=
  decodeArtifactWith defaultLimits bytes

/-- Strict, resource-bounded, canonical decoder for a complete store file.
The outer size gate runs before parsing; record lengths and their aggregate are
checked before the corresponding byte arrays are copied. -/
def decodeStoreWith (limits : Limits) (bytes : ByteArray) :
    Except String Store := do
  enforce "store-byte" bytes.size limits.maxStoreBytes
  let store ← Decode.runCanonical (getStore limits) encodeStore bytes
  let _ ← store.preflight limits
  return store

def decodeStore (bytes : ByteArray) : Except String Store :=
  decodeStoreWith defaultLimits bytes

/-- A complete store spelling for a checked result. -/
def Store.ofResult (result : Result) : Store :=
  ⟨result.artifacts.map fun artifact =>
    (artifact.cacheKey, encodeArtifact artifact)⟩

/-- Replace or add rebuilt records. Keys not mentioned by the current program
remain available for other program versions sharing the same store. -/
def Store.applyWrites (store : Store) (writes : List (Address × ByteArray)) :
    Store :=
  let keys := writes.map (·.1)
  ⟨store.entries.filter (fun entry => !keys.contains entry.1) ++ writes⟩

structure Rejection where
  cacheKey : Address
  reason : String
  deriving BEq, Repr

structure Stats where
  ingressEntries : Nat := 0
  ingressBytes : Nat := 0
  hits : Nat := 0
  misses : Nat := 0
  rejected : Nat := 0
  rounds : Nat := 0
  widenedArtifacts : Nat := 0
  writes : Nat := 0
  writeBytes : Nat := 0
  deriving BEq, Repr, Inhabited

/-- Proof-carrying cache schedule result. `writes` contains only missing or
rejected records; `completeStore` can be used for a compact exact snapshot. -/
structure Production (limits : Limits)
    (program : List ReaddressAll.Artifact) where
  certificate : Certificate
  result : Result
  stats : Stats
  rejections : List Rejection
  writes : List (Address × ByteArray)
  checked : runWith limits.producer.checker program certificate = .ok result

namespace Production

def completeStore {limits : Limits} {program : List ReaddressAll.Artifact}
    (production : Production limits program) : Store :=
  Store.ofResult production.result

theorem postFixpoint {limits : Limits} {program : List ReaddressAll.Artifact}
    (production : Production limits program) :
    production.certificate.postFixpoint program = true :=
  postFixpoint_of_runWith_eq_ok production.checked

theorem semanticAudit {limits : Limits} {program : List ReaddressAll.Artifact}
    (production : Production limits program) :
    production.result.semanticAudit = true :=
  semanticAudit_of_runWith_eq_ok production.checked

theorem functionSummary_sound
    {limits : Limits} {program : List ReaddressAll.Artifact}
    (production : Production limits program)
    {ctx : Ctx} {address : Address} {function : FnDef} {claimed : Fact}
    {arguments : List RVal}
    {store outputStore : Ix.Compiler.IxIR1.Store}
    {outputValue : RVal} {fuel : Nat}
    (hctx : ctx.decls = programDeclEnv program)
    (hdeclaration : programDeclEnv program address = some (.fn function))
    (hsummary : production.certificate.summaryEnv address = some claimed)
    (hinvoke : invoke ctx fuel address arguments store =
      .ok (outputStore, outputValue)) :
    claimed.Holds (programDeclEnv program) outputStore outputValue := by
  exact functionSummary_sound_of_runWith_eq_ok production.checked hctx
    hdeclaration hsummary hinvoke

end Production

private structure AcceptedHit where
  candidate : CandidateArtifact
  artifact : Artifact
  summaries : AddressEnv.Index Fact
  totalShapes : Nat
  totalFields : Nat

private structure ScheduleState where
  candidatesRev : List CandidateArtifact := []
  artifactsRev : List Artifact := []
  owners : List (Address × Address) := []
  summaries : AddressEnv.Index Fact := AddressEnv.build []
  totalShapes : Nat := 0
  totalFields : Nat := 0
  rounds : Nat := 0
  remainingRounds : Nat := 0
  widenedArtifacts : Nat := 0
  hits : Nat := 0
  misses : Nat := 0
  rejected : Nat := 0
  rejectionsRev : List Rejection := []
  writesRev : List (Address × ByteArray) := []
  writeBytes : Nat := 0

private def ownersFor (artifact : Artifact) : List (Address × Address) :=
  artifact.members.map fun member => (member.1, artifact.address)

private def validateHit (limits : Limits) (declarations : DeclEnv)
    (state : ScheduleState) (program : ReaddressAll.Artifact)
    (query : Query) (bytes : ByteArray) : Except String AcceptedHit := do
  let artifact ← decodeArtifactWith limits bytes
  unless query.agreesWith artifact do
    throw "record does not match the current cache query"
  unless artifact.semanticAudit do
    throw "record failed its content-address or canonicality audit"
  let candidate : CandidateArtifact :=
    { programIdentity := artifact.programIdentity
      members := artifact.members }
  let summaries := Producer.extendSummaries state.summaries candidate.members
  unless candidate.localPostFixpoint declarations
      (AddressEnv.lookup summaries) program do
    throw "record is not an artifact-local post-fixpoint"
  let (totalShapes, totalFields) ← Producer.validatePayload
    limits.producer.checker state.totalShapes state.totalFields candidate.members
  return ⟨candidate, artifact, summaries, totalShapes, totalFields⟩

private def acceptHit (state : ScheduleState) (hit : AcceptedHit) :
    ScheduleState :=
  { state with
    candidatesRev := hit.candidate :: state.candidatesRev
    artifactsRev := hit.artifact :: state.artifactsRev
    owners := ownersFor hit.artifact ++ state.owners
    summaries := hit.summaries
    totalShapes := hit.totalShapes
    totalFields := hit.totalFields
    hits := state.hits + 1 }

private def rebuild (limits : Limits) (declarations : DeclEnv)
    (state : ScheduleState) (program : ReaddressAll.Artifact)
    (query : Query) (rejection : Option String) : Except String ScheduleState := do
  let produced ← Producer.produceArtifactWith limits.producer declarations
    state.summaries program state.totalShapes state.totalFields
    state.remainingRounds
  let artifact := Artifact.ofQuery query produced.candidate.members
  unless artifact.semanticAudit do
    throw "internal: rebuilt HPT cache artifact failed its semantic audit"
  rejectCollision state.artifactsRev artifact
  let bytes := encodeArtifact artifact
  enforce "record-byte" bytes.size limits.maxEntryBytes
  let writeBytes := state.writeBytes + bytes.size
  enforce "output-byte" writeBytes limits.maxWriteBytes
  let rejected := state.rejected + if rejection.isSome then 1 else 0
  let rejectionsRev := match rejection with
    | some reason => Rejection.mk query.cacheKey reason :: state.rejectionsRev
    | none => state.rejectionsRev
  pure ({ state with
      candidatesRev := produced.candidate :: state.candidatesRev
      artifactsRev := artifact :: state.artifactsRev
      owners := ownersFor artifact ++ state.owners
      summaries := produced.summaries
      totalShapes := produced.totalShapes
      totalFields := produced.totalFields
      rounds := state.rounds + produced.rounds
      remainingRounds := produced.remainingRounds
      widenedArtifacts := state.widenedArtifacts +
        (if produced.widened then 1 else 0)
      misses := state.misses + 1
      rejected := rejected
      rejectionsRev := rejectionsRev
      writesRev := (query.cacheKey, bytes) :: state.writesRev
      writeBytes := writeBytes } : ScheduleState)

/-- Validate effectfully supplied cache hits and rebuild misses one dependency
artifact at a time, then submit the assembled candidate to the ordinary
whole-program checker. The lookup is untrusted: every returned record crosses
the same canonical decoder, exact-query audit, local post-fixpoint check, and
final checker as an in-memory store. -/
def runLookupWithM {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (limits : Limits) (program : List ReaddressAll.Artifact)
    (ingress : IngressStats) (lookup : Address → m LookupResult) :
    m (Production limits program) := do
  let _ ← ofExcept <|
    preflight limits.producer.checker program (Certificate.top program)
  let declarations := programDeclEnv program
  let mut state : ScheduleState :=
    { remainingRounds := limits.producer.maxRounds }
  for programArtifact in program do
    let query ← ofExcept <|
      Query.ofProgram declarations state.owners programArtifact
    match ← lookup query.cacheKey with
    | .missing =>
        state ← ofExcept <|
          rebuild limits declarations state programArtifact query none
    | .rejected reason =>
        state ← ofExcept <|
          rebuild limits declarations state programArtifact query (some reason)
    | .found bytes =>
        match validateHit limits declarations state programArtifact query bytes with
        | .error reason =>
            state ← ofExcept <| rebuild limits declarations state programArtifact
              query (some reason)
        | .ok hit =>
            let _ ← ofExcept <| rejectCollision state.artifactsRev hit.artifact
            state := acceptHit state hit
  let certificate : Certificate := ⟨state.candidatesRev.reverse⟩
  match hrun : HPT.runWith limits.producer.checker program certificate with
  | .error error => throw error
  | .ok result =>
      if result.artifacts != state.artifactsRev.reverse then
        throw "internal: cache schedule and final materialization diverged"
      let stats : Stats :=
        { ingressEntries := ingress.entries
          ingressBytes := ingress.bytes
          hits := state.hits
          misses := state.misses
          rejected := state.rejected
          rounds := state.rounds
          widenedArtifacts := state.widenedArtifacts
          writes := state.writesRev.length
          writeBytes := state.writeBytes }
      pure (⟨certificate, result, stats, state.rejectionsRev.reverse,
        state.writesRev.reverse, hrun⟩ : Production limits program)

/-- In-memory specialization of `runLookupWithM`. Its aggregate admission
statistics cover the complete supplied store, including stale records. -/
def runWith (limits : Limits) (program : List ReaddressAll.Artifact)
    (store : Store) : Except String (Production limits program) := do
  let ingress ← store.preflight limits
  let index := store.index
  runLookupWithM limits program ingress fun key =>
    pure <| match index.get? key with
      | none => .missing
      | some bytes => .found bytes

def run (program : List ReaddressAll.Artifact) (store : Store) :
    Except String (Production defaultLimits program) :=
  runWith defaultLimits program store

end Ix.Compiler.IxIR1.HPT.Cache
