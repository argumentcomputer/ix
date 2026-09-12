import Compilatrix.Modular.Basic

/-!
# Independently checked source units

An imported certificate is transported into the new unit's exact finite
context. Only the owned declarations and mutual members run through the
source validator. The dependency scope is closed when their checked member
packets are assembled. Cached bytes remain ordinary candidates; `checkUnit`
reconstructs kernel evidence for them before they enter the checked cache.
-/

namespace Compilatrix.Modular

open Ixon (Address Constant)
open IxIR

def queryBytes (policy : Policy) (input : Input) (interfaces : List ByteArray) : ByteArray :=
  Encoding.string "compilatrix/source-unit-query/1" ++ policy.bytes ++ input.bytes ++
    Encoding.list Encoding.blob interfaces

structure Record where
  query : ByteArray
  output : TargetEntries
  order : List Address
  deriving DecidableEq

/-- Check syntax and the exact framed size before retaining or comparing
typed evidence. The byte decoder applies these same consumer limits. -/
def Record.preflight (limits : Limits) (record : Record) : Except String Nat := do
  ensure (Bounded.blobFits limits.record record.query &&
    Bounded.countFits limits.record record.output.length &&
    Bounded.countFits limits.record record.order.length) "source record structural limit"
  let mut size := "compilatrix/source-unit-record/1\x00".utf8ByteSize +
    (Encoding.nat record.query.size).size + record.query.size +
    (Encoding.nat record.output.length).size + (Encoding.nat record.order.length).size +
    32 * record.order.length
  ensure (size ≤ limits.record.maxBytes) "source record byte limit"
  for (_, decl) in record.output do
    ensure (declFits limits decl) "source record declaration structural limit"
    let bytes := decl.preimage
    ensure (Bounded.blobFits limits.record bytes) "source record declaration byte limit"
    size := size + 32 + (Encoding.nat bytes.size).size + bytes.size
    ensure (size ≤ limits.record.maxBytes) "source record byte limit"
  return size

/-- Evidence is indexed by its exact finite environment and simultaneous
scope. Proofs are erased by Lean; the runtime cache retains their data. -/
structure CheckedUnit (policy : Policy) where
  input : Input
  interfaces : List ByteArray
  context : Context
  output : TargetEntries
  order : List Address
  erased : Erase.eraseProgram (EraseValidator.eraseCtxOf context.source)
    input.constants policy.eraseFuel = .ok output
  coverage : @EraseValidator.CoverageDB context.scope
    context.source.inlineSharing context.target
  members : @Sim.MemberCoverage context.scope context.source.inlineSharing
    context.target context.scope.plan

def CheckedUnit.query {policy} (unit : CheckedUnit policy) : ByteArray :=
  queryBytes policy unit.input unit.interfaces

def CheckedUnit.key {policy} (unit : CheckedUnit policy) : Address :=
  Address.blake3 unit.query

/-- Every owned raw declaration, including generated mutual members, is part
of the imported interface. The query binds complete source bytes, modes,
literal payloads, policy, and the direct dependency interfaces. -/
def CheckedUnit.interface {policy} (unit : CheckedUnit policy) : ByteArray :=
  Encoding.string "compilatrix/source-unit-interface/1" ++
    Encoding.address unit.key ++
    Encoding.address (Ixon.Merkle.rootCanonical (unit.input.constants.map (·.1)).toArray) ++
    Encoding.list Encoding.address (candidates unit.input.constants) ++
    Encoding.list targetEntryBytes unit.output

def CheckedUnit.record {policy} (unit : CheckedUnit policy) : Record :=
  ⟨unit.query, unit.output, unit.order⟩

def constantDependencies (constant : Constant) : List Address :=
  constant.refs.toList ++ match constant.info with
    | .cPrj projection => [projection.block]
    | .rPrj projection => [projection.block]
    | .iPrj projection => [projection.block]
    | .dPrj projection => [projection.block]
    | _ => []

private def uniqueAddresses (entries : List (Address × α)) : Bool :=
  (entries.map (·.1)).eraseDups.length == entries.length

/-- Preflight precedes serialization, canonicalization, inlining, and
validation. The combined unit charge includes the imported source context. -/
def prepare (limits : Limits) (policy : Policy) (input : Input)
    (imports : List (CheckedUnit policy)) : Except String Context := do
  ensure (!input.name.isEmpty && input.name.utf8ByteSize ≤ 256) "invalid unit name"
  ensure (!input.constants.isEmpty) "empty source unit"
  ensure (input.imports == imports.map (·.input.name)) "missing, stale, or unordered unit imports"
  ensure (input.imports.eraseDups == input.imports && !input.imports.contains input.name)
    "duplicate or cyclic unit import"
  ensure (uniqueAddresses input.constants && uniqueAddresses input.blobs)
    "duplicate owned source or blob binding"
  preflightUnit policy input.constants
  ensure (input.blobs.length ≤ limits.record.maxSequence) "unit blob count limit"
  let mut blobSize := 0
  for (_, blob) in input.blobs do
    let size := match blob with
      | .natB value => value.log2 / 7 + 1
      | .strB value => value.utf8ByteSize
    ensure (size ≤ limits.record.maxBlobBytes) "unit literal payload byte limit"
    blobSize := blobSize + size + 64
    ensure (blobSize ≤ limits.record.maxBlobBytes) "unit literal table byte limit"
  let importedCount := imports.foldl (fun total unit => total + unit.context.constants.length) 0
  let importedBlobs := imports.foldl (fun total unit => total + unit.context.blobs.length) 0
  let importedDecls := imports.foldl (fun total unit => total + unit.context.declarations.length) 0
  ensure (input.constants.length + importedCount + importedBlobs + importedDecls ≤ limits.maxImportBindings)
    "unit import binding limit"
  for unit in imports do
    ensure (input.natBlock == unit.context.natBlock) "incompatible imported Nat identity"
    for (address, _) in input.constants do
      ensure (!(unit.context.constants.any (fun entry => entry.1 == address)))
        "unit owns a source address already owned by an import"
  let constants ← unionEntries (input.constants ++ imports.flatMap (·.context.constants))
  let blobs ← unionEntries (input.blobs ++ imports.flatMap (·.context.blobs))
  let declarations ← unionEntries (imports.flatMap (·.context.declarations))
  let context : Context := { constants, blobs, declarations, natBlock := input.natBlock }
  let contextStats := Ixon.Work.programStats constants
  ensure (contextStats.constants ≤ limits.maxConstants &&
    contextStats.expandedExpressionUnits ≤ limits.maxExpandedUnits) "unit context size limit"
  ensure (proofWork input.constants constants ≤
    policy.unit.maxCertificateSourceNodeWork) "unit certificate source-node work limit"
  let source := context.source
  for (address, constant) in input.constants do
    let actual ← (Constant.addressChecked constant).mapError (fun err => reprStr err)
    ensure (actual == address) "source address does not match its exact canonical constant"
    for dependency in constantDependencies constant do
      ensure ((source.resolve dependency).isSome || (source.blobs dependency).isSome)
        "source reference is absent from the declared dependency closure"
    match Ixon.UsageCheck.checkConstant source.resolve constant policy.checkFuel with
    | .ok _ => pure ()
    | .error err => throw s!"unit usage check: {repr err}"
  -- The input is already finite; these byte caps bound the retained query.
  ensure (input.bytes.size ≤ limits.record.maxBlobBytes) "unit input byte limit"
  return context

structure MemberPacket (context : Context) where
  keys : List Sim.MemberKey
  coverage : @Sim.MemberCoverage context.scope context.source.inlineSharing context.target keys

def memberLookup (context : Context) (key : Sim.MemberKey) :
    List (MemberPacket context) → Option (PLift
      (@Sim.MemberRel context.scope context.source.inlineSharing context.target key))
  | [] => none
  | packet :: rest =>
      if h : key ∈ packet.keys then
        some ⟨@Sim.MemberCoverage.lookup context.scope _ _ _ packet.coverage key h⟩
      else memberLookup context key rest

def closeMembers (context : Context) (packets : List (MemberPacket context)) :
    (keys : List Sim.MemberKey) → Except String (PLift
      (@Sim.MemberCoverage context.scope context.source.inlineSharing context.target keys))
  | [] => .ok ⟨@Sim.MemberCoverage.nil context.scope _ _ context.strict.inlineSharing⟩
  | key :: rest => do
      let some member := memberLookup context key packets
        | throw "unclosed imported mutual-member obligation"
      let tail ← closeMembers context packets rest
      return ⟨@Sim.MemberCoverage.cons context.scope _ _ key rest member.down tail.down⟩

def importedEvidence {policy} (context : Context) (imports : List (CheckedUnit policy)) :
    Except String
      (@EraseValidator.CoverageDB context.scope context.source.inlineSharing context.target ×
        List (MemberPacket context)) := do
  let mut coverage := []
  let mut seen : Std.HashSet Address := {}
  let mut members := []
  for unit in imports do
    let extension ← unit.context.extension context
    let scope ← unit.context.scopeExtension context
    let imported := unit.coverage.extend extension.down.inlineSharing scope.down
    for entry in imported do
      let address := @EraseValidator.CoveredEntry.address context.scope _ _ entry
      if !seen.contains address then
        coverage := entry :: coverage
        seen := seen.insert address
    members := {
      keys := unit.context.scope.plan
      coverage := unit.members.extend extension.down.inlineSharing scope.down } :: members
  return (coverage, members)

private def withOutput (limits : Limits) (context : Context) (output : TargetEntries) :
    Except String Context := do
  ensure (output.length ≤ limits.record.maxSequence && uniqueAddresses output)
    "duplicate or oversized unit output"
  ensure ((Pipeline.firstValidatedExtern? output).isNone) "unit extern ownership ABI rejected"
  let declarations ← unionEntries (output ++ context.declarations)
  ensure (declarations.length ≤ 32768) "unit target context size limit"
  return { context with declarations }

/-- Check supplied evidence against the actual eraser, current imported
certificates, and exact source query. A bad record is rejected, never trusted
because its hash or coverage schedule matches a previous run. -/
def checkUnit (limits : Limits) (policy : Policy) (input : Input)
    (imports : List (CheckedUnit policy)) (record : Record) :
    Except String (CheckedUnit policy) := do
  let _ ← record.preflight limits
  let prepared ← prepare limits policy input imports
  let interfaces := imports.map (·.interface)
  ensure (record.query == queryBytes policy input interfaces) "stale or incompatible source certificate query"
  ensure (record.query.size ≤ limits.record.maxBytes) "source certificate query byte limit"
  let expected := candidates input.constants
  ensure (record.order.length == expected.length && record.order.eraseDups == record.order &&
    record.order.all expected.contains) "malformed source coverage schedule"
  let output ← match erased : Erase.eraseProgram (EraseValidator.eraseCtxOf prepared.source)
      input.constants policy.eraseFuel with
    | .error err => throw s!"unit erasure: {repr err}"
    | .ok actual => pure (⟨actual, erased⟩ : { actual //
        Erase.eraseProgram (EraseValidator.eraseCtxOf prepared.source)
          input.constants policy.eraseFuel = .ok actual })
  if agrees : output.1 = record.output then
    let declarations ← unionEntries (record.output ++ prepared.declarations)
    let context : Context := { prepared with declarations }
    let _ ← withOutput limits prepared record.output
    let (imported, packets) ← importedEvidence context imports
    let coverage ← @EraseValidator.validateCoveragePlan context.scope context.source.inlineSharing
      context.target policy.validateFuel imported record.order
    let ownKeys := Pipeline.programMemberPlan input.constants
    let ownMembers ← @EraseValidator.validateMemberCoverage context.scope context.source.inlineSharing
      context.target coverage policy.validateFuel ownKeys
    let members ← closeMembers context ({ keys := ownKeys, coverage := ownMembers.down } :: packets)
      context.scope.plan
    return {
      input, interfaces, context, output := record.output, order := record.order
      erased := by simpa only [context, Context.source, agrees] using output.2
      coverage, members := members.down }
  else throw "source certificate output differs from the actual eraser"

/-- Coverage discovery is a producer. The resulting record still crosses the
independent checker above, including its exact-output comparison. -/
def produceUnit (limits : Limits) (policy : Policy) (input : Input)
    (imports : List (CheckedUnit policy)) : Except String (CheckedUnit policy) := do
  let prepared ← prepare limits policy input imports
  let output ← (Erase.eraseProgram (EraseValidator.eraseCtxOf prepared.source)
    input.constants policy.eraseFuel).mapError (fun err => s!"unit erasure: {repr err}")
  let context ← withOutput limits prepared output
  let (imported, _) ← importedEvidence context imports
  let expected := candidates input.constants
  let order ← (@Pipeline.coveragePlan context.scope context.source.inlineSharing context.target
    policy.validateFuel (expected.length + 1) imported [] expected).mapError
      (fun (_, message) => s!"unit coverage discovery: {message}")
  checkUnit limits policy input imports {
    query := queryBytes policy input (imports.map (·.interface)), output, order }

end Compilatrix.Modular
