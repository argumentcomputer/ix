module

public import Ix.RoleBinding.Publication
public import Ix.Ixon.Authenticated
public import Ix.KernelCheck.Step
public import IxCK.Kernel.Admission.UserAxioms
public import Ix.RoleBinding.RecordDecoding

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

/-- Preserve the requested order and the artifact's actual byte/decoded owners.
The guards and their precedence are shared by default and explicit orders. -/
def materializeOrder (artifact : Ixon.Env) (store : RecordStore) (order : Array Address) :
    Except Error (Ix.Kernel.Admission.Records × List (Address × Ixon.Constant)) := do
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
  return (ordered.toList,decoded.toList)

/-! ## Decoding in parallel

`decodeRecords` is one loop over every record. `decodeRecordsPar` decodes
chunks of the records on parallel tasks, each from its first record's
position, and joins them in order; it is `decodeRecords`, the same value and
the same first failure (`decodeRecordsPar_eq`). -/

section DecodePar

open Ix.Kernel.Admission

theorem decodeLoop_acc (limits : Limits) (position : Nat) (records : Records)
    (reversed : Ix.Kernel.Ingress.Constants) :
    decodeLoop limits position records reversed =
      (decodeLoop limits position records []).map (reversed.reverse ++ ·) := by
  induction records generalizing position reversed with
  | nil => simp [decodeLoop, Except.map]
  | cons pair rest ih =>
    rcases pair with ⟨address, bytes⟩
    cases decoded : Ixon.Canonical.deConstant limits.maxRecordBytes limits.maxRecordUnivNodes bytes with
    | error reason => simp [decodeLoop, decoded, Except.mapError, bind, Except.bind, Except.map]
    | ok constant =>
      simp only [decodeLoop, decoded, Except.mapError, bind, Except.bind]
      rw [ih (position + 1) ((address, constant) :: reversed), ih (position + 1) [(address, constant)]]
      cases decodeLoop limits (position + 1) rest [] <;> simp [Except.map, List.append_assoc]

theorem decodeLoop_append (limits : Limits) (position : Nat) (front back : Records) :
    decodeLoop limits position (front ++ back) [] =
      (decodeLoop limits position front []).bind fun first =>
        (decodeLoop limits (position + front.length) back []).map (first ++ ·) := by
  induction front generalizing position with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero, decodeLoop, List.reverse_nil, Except.bind]
    cases decodeLoop limits position back [] <;> rfl
  | cons pair rest ih =>
    rcases pair with ⟨address, bytes⟩
    cases decoded : Ixon.Canonical.deConstant limits.maxRecordBytes limits.maxRecordUnivNodes bytes with
    | error reason => simp [decodeLoop, decoded, Except.mapError, bind, Except.bind]
    | ok constant =>
      simp only [List.cons_append, decodeLoop, decoded, Except.mapError, bind, Except.bind]
      rw [decodeLoop_acc limits (position + 1) (rest ++ back) [(address, constant)], ih (position + 1),
        decodeLoop_acc limits (position + 1) rest [(address, constant)]]
      have shift : position + (rest.length + 1) = position + 1 + rest.length := by omega
      simp only [List.length_cons, shift]
      cases decodeLoop limits (position + 1) rest [] with
      | error e => simp [Except.bind, Except.map]
      | ok first =>
        cases decodeLoop limits (position + 1 + rest.length) back [] <;>
          simp [Except.bind, Except.map]

/-- One decoding task per chunk of `size + 1` records, each with its first
record's position, all spawned before any is joined. -/
def spawnDecodes (limits : Limits) (size : Nat) (position : Nat) :
    Records → List (Task (Except ByteError Ix.Kernel.Ingress.Constants))
  | [] => []
  | r :: rs =>
    (Task.spawn fun _ => decodeLoop limits position ((r :: rs).take (size + 1)) []) ::
      spawnDecodes limits size (position + (size + 1)) ((r :: rs).drop (size + 1))
termination_by records => records.length
decreasing_by simp; omega

/-- The chunks' decodings joined in order: the first failure, else every
chunk's constants in order. -/
def joinDecodes : List (Task (Except ByteError Ix.Kernel.Ingress.Constants)) →
    Except ByteError Ix.Kernel.Ingress.Constants
  | [] => .ok []
  | t :: ts =>
    match t.get with
    | .error e => .error e
    | .ok first => (joinDecodes ts).map (first ++ ·)

theorem joinDecodes_spawnDecodes (limits : Limits) (size : Nat) :
    (position : Nat) → (records : Records) →
    joinDecodes (spawnDecodes limits size position records) = decodeLoop limits position records []
  | position, [] => by simp [spawnDecodes, joinDecodes, decodeLoop]
  | position, r :: rs => by
    rw [spawnDecodes, joinDecodes]
    rw [joinDecodes_spawnDecodes limits size (position + (size + 1)) ((r :: rs).drop (size + 1))]
    conv => rhs; rw [← List.take_append_drop (size + 1) (r :: rs), decodeLoop_append]
    show (match decodeLoop limits position ((r :: rs).take (size + 1)) [] with
      | .error e => (Except.error e : Except ByteError Ix.Kernel.Ingress.Constants)
      | .ok first => (decodeLoop limits (position + (size + 1)) ((r :: rs).drop (size + 1)) []).map
          (first ++ ·)) = _
    cases decodeLoop limits position ((r :: rs).take (size + 1)) [] with
    | error e => rfl
    | ok first =>
      by_cases fits : size + 1 ≤ (r :: rs).length
      · have least : min size rs.length = size := Nat.min_eq_left (by simp at fits; omega)
        simp [Except.bind, least]
      · have rest : (r :: rs).drop (size + 1) = [] := List.drop_eq_nil_of_le (by omega)
        simp [rest, decodeLoop, Except.bind, Except.map]
termination_by _ records => records.length
decreasing_by simp; omega

/-- `decodeRecords` on chunks of at least 256 records, decoded in parallel. -/
def decodeRecordsPar (limits : Limits) (records : Records) :
    Except ByteError Ix.Kernel.Ingress.Constants :=
  joinDecodes (spawnDecodes limits (Nat.max 255 (records.length / 64)) 0 records)

theorem decodeRecordsPar_eq (limits : Limits) (records : Records) :
    decodeRecordsPar limits records = decodeRecords limits records := by
  simp only [decodeRecordsPar, decodeRecords, joinDecodes_spawnDecodes]

/-- `Ix.Kernel.Admission.decodeWithin` with the decoding in parallel
(`decodeRecordsPar`), the depth scan and the expanded check in parallel too
(`RecordDecoding.scanDepthsParallel`, `expandedDepthsParallel`): the same result. -/
def decodeWithinPar (limits : Limits) (records : Records) :
    Except ByteError Ix.Kernel.Ingress.Constants := do
  Ix.RoleBinding.RecordDecoding.scanDepthsParallel 256 limits records
  let constants ← (decodeRecordsPar limits records).mapError Ix.Kernel.Admission.ByteError.asLimit
  Ix.RoleBinding.RecordDecoding.expandedDepthsParallel 256 limits constants
  pure constants

theorem decodeWithinPar_eq (limits : Limits) (records : Records) :
    decodeWithinPar limits records = Ix.Kernel.Admission.decodeWithin limits records := by
  simp only [decodeWithinPar, Ix.Kernel.Admission.decodeWithin, decodeRecordsPar_eq,
    Ix.RoleBinding.RecordDecoding.scanDepthsParallel_eq,
    Ix.RoleBinding.RecordDecoding.expandedDepthsParallel_eq]

end DecodePar

/-- The order is selected before reading/checking, then subjected to the same
complete artifact coverage, ownership and uniqueness guards. -/
def prepareRecordsFor (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (requested : Option (Array Address)) :
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
  let constants ← (Ix.Kernel.Admission.decodeWithin limits rawRecords.toList).mapError .bytes
  let store : RecordStore := constants.foldl (fun m (a, c) => m.insert a c) {}
  checkBindings table store
  let preRecords ← (Ix.RoleBinding.preludeRecords table (store[·]?) Ix.Kernel.preludeShape).mapError .prelude
  let pre : Prelude .anon ← (readPrelude table preRecords #[] blobs).mapError .prelude
  (checkPreludeShape pre).mapError .prelude
  (checkFallbackRecursors pre).mapError .prelude
  let order := match requested with
    | none => Ixon.CheckOrder.wholeEnv table pre constants.toArray
    | some order => order
  unless order.size == rawRecords.size do throw (.coverage "record order does not cover the artifact")
  let (ordered,decoded) ← materializeOrder artifact store order
  let hints := Hints.ofStore store artifact.anonHints
  return { prepared := { binding, table, pre, records := ordered, blobs, hints }
           constants := decoded }

/-- Existing callers retain the original wholeEnv policy. -/
def prepareRecords (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) : Except Error PreparedRecords :=
  prepareRecordsFor artifact limits none

def prepareRecordsAt (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (order : Array Address) : Except Error PreparedRecords :=
  prepareRecordsFor artifact limits (some order)

/-- `prepareRecordsFor` with the records decoded in parallel
(`decodeRecordsPar`): the same preparation, the same value and the same
first refusal (`prepareRecordsForPar_eq`), for hosts that run it outside
a certified entry. -/
def prepareRecordsForPar (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (requested : Option (Array Address)) :
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
  let constants ← (decodeWithinPar limits rawRecords.toList).mapError .bytes
  let store : RecordStore := constants.foldl (fun m (a, c) => m.insert a c) {}
  checkBindings table store
  let preRecords ← (Ix.RoleBinding.preludeRecords table (store[·]?) Ix.Kernel.preludeShape).mapError .prelude
  let pre : Prelude .anon ← (readPrelude table preRecords #[] blobs).mapError .prelude
  (checkPreludeShape pre).mapError .prelude
  (checkFallbackRecursors pre).mapError .prelude
  let order := match requested with
    | none => Ixon.CheckOrder.wholeEnv table pre constants.toArray
    | some order => order
  unless order.size == rawRecords.size do throw (.coverage "record order does not cover the artifact")
  let (ordered,decoded) ← materializeOrder artifact store order
  let hints := Hints.ofStore store artifact.anonHints
  return { prepared := { binding, table, pre, records := ordered, blobs, hints }
           constants := decoded }

theorem prepareRecordsForPar_eq (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (requested : Option (Array Address)) :
    prepareRecordsForPar artifact limits requested = prepareRecordsFor artifact limits requested := by
  unfold prepareRecordsForPar prepareRecordsFor
  simp only [decodeWithinPar_eq]

/-- `prepareRecords` with the records decoded in parallel
(`prepareRecordsPar_eq`). -/
def prepareRecordsPar (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) :
    Except Error PreparedRecords :=
  prepareRecordsForPar artifact limits none

theorem prepareRecordsPar_eq (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) :
    prepareRecordsPar artifact limits = prepareRecords artifact limits :=
  prepareRecordsForPar_eq artifact limits none

def prepareFor (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (requested : Option (Array Address)) : Except Error Prepared := do
  let input ← prepareRecordsFor artifact limits requested
  let p := input.prepared
  let (evidence, declarations) ← (Ix.Kernel.Admission.prepareWith Address.admissionHash p.binding p.pre limits
    p.records p.blobs p.hints.lookup).mapError .admission
  checkEvidence p.table evidence declarations
  return p

def prepare (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) : Except Error Prepared :=
  prepareFor artifact limits none

def prepareAt (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (order : Array Address) : Except Error Prepared :=
  prepareFor artifact limits (some order)

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

/-- The order is part of this receipt's type. Its target is the result of the
actual chosen-order entry, fixed before any supplied model is quantified. -/
structure OrderedReceipt (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (order : Array Address) where
  prepared : Prepared
  target : Ix.Kernel.Env .anon
  preparedFrom : prepareAt artifact limits order = .ok prepared
  checked : Ix.Kernel.Admission.checkBytesWith Address.admissionHash prepared.binding prepared.pre
    limits prepared.records prepared.blobs prepared.hints.lookup = .ok target

def checkAt (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) (order : Array Address) :
    Except Error (OrderedReceipt artifact limits order) :=
  match fromArtifact : prepareAt artifact limits order with
  | .error e => .error e
  | .ok prepared =>
    match checked : Ix.Kernel.Admission.checkBytesWith Address.admissionHash prepared.binding prepared.pre
        limits prepared.records prepared.blobs prepared.hints.lookup with
    | .error e => .error (.admission e)
    | .ok target => .ok ⟨prepared,target,fromArtifact,checked⟩

/-- A receipt of preparation and of the check that admits user axioms
(`Admission.checkBytesUnder .allowUser`), with the kernel's list of the user
axioms among the declarations it ran over (`axioms`). Its accept holds only
under them: no theorem covers it and no host statement is issued for it,
unless the list is empty, when it is a receipt of the certified entry
(`ReceiptConditional.toReceipt`). -/
structure ReceiptConditional (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) where
  prepared : Prepared
  target : Ix.Kernel.Env .anon
  axioms : List (Ix.Kernel.ConstantVal .anon)
  preparedFrom : prepare artifact limits = .ok prepared
  checked : Ix.Kernel.Admission.checkBytesUnder .allowUser Address.admissionHash prepared.binding
    prepared.pre limits prepared.records prepared.blobs prepared.hints.lookup = .ok (target, axioms)

def checkConditional (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) :
    Except Error (ReceiptConditional artifact limits) :=
  match fromArtifact : prepare artifact limits with
  | .error e => .error e
  | .ok prepared =>
    match checked : Ix.Kernel.Admission.checkBytesUnder .allowUser Address.admissionHash prepared.binding
        prepared.pre limits prepared.records prepared.blobs prepared.hints.lookup with
    | .error e => .error (.admission e)
    | .ok (target, axioms) => .ok ⟨prepared, target, axioms, fromArtifact, checked⟩

/-- **A conditional receipt that lists no user axiom is a receipt of the
certified entry**, with the same preparation and environment (T1,
`Admission.checkBytesUnder_strict_of_nil`). One run of the check that admits
user axioms therefore also gives the certified receipt, and the host statement,
of an artifact that declares none. -/
def ReceiptConditional.toReceipt {artifact : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    (receipt : ReceiptConditional artifact limits) (noAxioms : receipt.axioms = []) :
    Receipt artifact limits where
  prepared := receipt.prepared
  target := receipt.target
  preparedFrom := receipt.preparedFrom
  checked := Ix.Kernel.Admission.checkBytesUnder_strict_of_nil (policy := .allowUser) (by
    rw [← noAxioms]
    exact receipt.checked)

end Ix.RoleBinding.Artifact
