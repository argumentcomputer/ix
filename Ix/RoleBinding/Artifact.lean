module

public import Ix.RoleBinding.Publication
public import Ix.Ixon.Authenticated
public import Ix.KernelCheck.Step

/-! # Certified checking of an artifact's own binding and records

This entry supplies no committed/default table, prelude, evidence or external
assumed records. It checks the complete supplied constant set with the existing
authenticated entry. Its receipt links preparation and checking to the same
artifact. Host claim subjects/assumption roots and Source value preservation are
separate obligations; no result here supplies those claims.
-/

@[expose] public section

namespace Ix.RoleBinding.Artifact

open Ix.Kernel (Role ConstRef)
open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep (RecordStore Hints)

inductive Error where
  | missingBinding
  | binding (error : Ix.Kernel.Admission.BindingError)
  | bytes (error : Ix.Kernel.Admission.ByteError)
  | prelude (message : String)
  | coverage (message : String)
  | admission (error : Ix.Kernel.Admission.Error)

instance : ToString Error where
  toString
    | .missingBinding => "artifact: missing role binding"
    | .binding e => s!"artifact: {Ix.Kernel.Admission.Error.binding e}"
    | .bytes e => s!"artifact: {Ix.Kernel.Admission.Error.ofBytes e}"
    | .prelude e => s!"artifact prelude: {e}"
    | .coverage e => s!"artifact coverage: {e}"
    | .admission e => s!"artifact: {e}"

structure Prepared where
  binding : Ix.Kernel.Admission.Binding
  table : Ix.Kernel.RoleTable
  pre : Prelude .anon
  records : Ix.Kernel.Admission.Records
  blobs : Ix.Kernel.Ingress.Blobs
  hints : Hints

/-- Authenticated records in the exact order supplied to either entry. The
logical and tiered consumers share this byte/binding/prelude boundary. -/
structure PreparedRecords where
  prepared : Prepared
  constants : List (Address × Ixon.Constant)

/-- Every table entry must designate an actual member. Table well-formedness
alone permits unused absent roles, and does not establish this coverage. -/
def checkBindings (table : Ix.Kernel.RoleTable) (store : RecordStore) : Except Error Unit := do
  let mut seen : Std.HashMap (ConstRef Address) Role := {}
  for (role, address) in table.bound do
    let some record := store[address]? | throw (.coverage s!"missing record for {repr role}: {address}")
    let some ref := resolveSource (store[·]?) address record
      | throw (.coverage s!"unresolved member for {repr role}: {address}")
    if let some other := seen[ref]? then
      throw (.coverage s!"{repr role} and {repr other} designate the same member")
    seen := seen.insert ref role
  for (role, entries) in table.evidence do
    for entry in entries do
      if let .proof address := entry then
        unless store.contains address do
          throw (.coverage s!"missing proof record for {repr role}: {address}")

/-- Require all evidence to resolve in the actual prepared reading, even if
an unused operation would otherwise never demand it. Operation evidence gates
run on definitions, so every bound operation must appear as a definition. -/
def checkEvidence (table : Ix.Kernel.RoleTable) (evidence : Ix.Kernel.Evidences .anon)
    (declarations : Array (Ix.Kernel.Declaration .anon)) : Except Error Unit := do
  for (role, entries) in table.evidence do
    let actual := ((evidence.find? (·.1 == role)).map (·.2)).getD []
    unless actual.length == entries.size do
      throw (.coverage s!"not every proof for {repr role} resolves")
    for (expected, observed) in entries.toList.zip actual do
      unless (match expected, observed with | .defeq, .defeq | .proof _, .proof _ => true | _, _ => false) do
        throw (.coverage s!"evidence kind differs for {repr role}")
    unless declarations.any (fun
        | .defnDecl cv _ _ => cv.name == Ix.Kernel.roleKey role
        | _ => false) do
      throw (.coverage s!"bound operation {repr role} is not a definition")

def prepareRecords (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) :
    Except Error PreparedRecords := do
  let some raw := artifact.roleBinding | throw .missingBinding
  let binding : Ix.Kernel.Admission.Binding := ⟨raw.address, raw.bytes⟩
  let rawRecords := (artifact.consts.toArray.map fun (a, c) => (a, c.rawBytes)).qsort
    fun x y => x.1.cmpBytes y.1 == .lt
  let blobs := (artifact.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList
  (Ix.Kernel.Admission.preflight limits rawRecords.toList blobs).mapError .bytes
  (Ix.Kernel.Admission.uniqueKeys rawRecords.toList blobs).mapError .bytes
  (Ix.Kernel.Admission.authenticate Address.admissionHash rawRecords.toList blobs).mapError .bytes
  let table ← (Ix.Kernel.Admission.admitBinding Address.admissionHash binding).mapError .binding
  let constants ← (Ix.Kernel.Admission.decodeRecords limits rawRecords.toList).mapError .bytes
  let store : RecordStore := constants.foldl (fun m (a, c) => m.insert a c) {}
  checkBindings table store
  let preRecords ← (Ix.RoleBinding.preludeRecords table (store[·]?) Ix.Kernel.preludeShape).mapError .prelude
  let pre : Prelude .anon ← (readPrelude table preRecords #[] blobs).mapError .prelude
  (checkPreludeShape pre).mapError .prelude
  (checkFallbackRecursors pre).mapError .prelude
  let order := Ixon.CheckOrder.wholeEnv table pre constants.toArray
  unless order.size == rawRecords.size do throw (.coverage "record order does not cover the artifact")
  let mut seen : Std.HashSet Address := {}
  let mut ordered : Array (Address × ByteArray) := #[]
  let mut decoded : Array (Address × Ixon.Constant) := #[]
  for address in order do
    if seen.contains address then throw (.coverage s!"duplicate ordered record {address}")
    let some record := artifact.consts[address]? | throw (.coverage s!"unknown ordered record {address}")
    let some constant := store[address]? | throw (.coverage s!"unknown decoded record {address}")
    seen := seen.insert address
    ordered := ordered.push (address, record.rawBytes)
    decoded := decoded.push (address, constant)
  let hints := Hints.ofStore store artifact.anonHints
  return { prepared := { binding, table, pre, records := ordered.toList, blobs, hints }
           constants := decoded.toList }

def prepare (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) : Except Error Prepared := do
  let input ← prepareRecords artifact limits
  let p := input.prepared
  let (evidence, declarations) ← (Ix.Kernel.Admission.prepareWith Address.admissionHash p.binding p.pre limits
    p.records p.blobs p.hints.lookup).mapError .admission
  checkEvidence p.table evidence declarations
  return p

/-- This is a receipt of these two actual runs, not an arbitrary stored
verdict. It does not certify a host claim or a relation to a source program. -/
structure Receipt (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) where
  prepared : Prepared
  target : Ix.Kernel.Env .anon
  preparedFrom : prepare artifact limits = .ok prepared
  checked : Ix.Kernel.Admission.checkBytesWith Address.admissionHash prepared.binding prepared.pre
    limits prepared.records prepared.blobs prepared.hints.lookup = .ok target

def check (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) :
    Except Error (Receipt artifact limits) :=
  match fromArtifact : prepare artifact limits with
  | .error e => .error e
  | .ok prepared =>
    match checked : Ix.Kernel.Admission.checkBytesWith Address.admissionHash prepared.binding prepared.pre
        limits prepared.records prepared.blobs prepared.hints.lookup with
    | .error e => .error (.admission e)
    | .ok target => .ok ⟨prepared, target, fromArtifact, checked⟩

end Ix.RoleBinding.Artifact
