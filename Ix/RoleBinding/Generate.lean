module

public import Ix.RoleBinding.Publication
public import Ix.RoleBinding.Evidence
public import Ix.RoleBinding.RecordDecoding
public import Ix.RoleEvidence
public import Ix.KernelCheck.Step

/-! # Artifact-specific binding and proof-evidence generation

The inputs are the actual compiled artifact and compiled certificate module.
Required roles and prelude groups are explicit; missing publication is an
error, with no default-table fallback. Generation is untrusted. A consumer
must still admit the binding and check the actual declarations and evidence.
This module does not choose compiler support inputs or a certified closure.
-/

@[expose] public section

namespace Ix.RoleBinding

open Ix.Kernel (Role ConstRef RoleTable)
open Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep (RecordStore Hints Setup setup closure)

def byteError (e : Ix.Kernel.Admission.ByteError) : String :=
  toString (Ix.Kernel.Admission.Error.ofBytes e)

/-- Read authenticated canonical bytes, never a materialized cache supplied
beside different bytes. Bounds are supplied by the caller. -/
def recordStore (limits : Ix.Kernel.Admission.Limits) (env : Ixon.Env) :
    Except String RecordStore := do
  let records := (env.consts.toArray.map fun (a, c) => (a, c.rawBytes)).qsort
    fun x y => x.1.cmpBytes y.1 == .lt
  let blobs := (env.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList
  (Ix.Kernel.Admission.preflight limits records.toList blobs).mapError byteError
  (Ix.Kernel.Admission.uniqueKeys records.toList blobs).mapError byteError
  (Ix.Kernel.Admission.authenticate Address.admissionHash records.toList blobs).mapError byteError
  let decoded ← (Ix.Kernel.Admission.decodeRecords limits records.toList).mapError byteError
  return decoded.foldl (fun out (a, c) => out.insert a c) {}

/-- The same store construction with bounded parallel authentication and
canonical decoding. Sorting and each preceding admission phase keep their
original order. -/
def recordStoreParallel (limits : Ix.Kernel.Admission.Limits) (env : Ixon.Env) :
    Except String RecordStore := do
  let records := (env.consts.toArray.map fun (a, c) => (a, c.rawBytes)).qsort
    fun x y => x.1.cmpBytes y.1 == .lt
  let blobs := (env.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList
  (Ix.Kernel.Admission.preflight limits records.toList blobs).mapError byteError
  (Ix.Kernel.Admission.uniqueKeys records.toList blobs).mapError byteError
  (RecordDecoding.authenticateParallel 256 Address.admissionHash records.toList blobs).mapError byteError
  let decoded ← (RecordDecoding.parallel 256 limits records.toList).mapError byteError
  return decoded.foldl (fun out (a, c) => out.insert a c) {}

@[csimp] theorem recordStore_eq_parallel : @recordStore = @recordStoreParallel := by
  funext limits env
  simp only [recordStore, recordStoreParallel, RecordDecoding.authenticateParallel_eq,
    RecordDecoding.parallel_eq]

/-- An authenticated, canonical record store for exactly this environment and
these admission limits. Reusing it cannot substitute records from another
artifact or validation under weaker limits. -/
structure CheckedStore (limits : Ix.Kernel.Admission.Limits) (env : Ixon.Env) where
  records : RecordStore
  checked : recordStore limits env = .ok records

/-- Authenticate and decode an artifact, retaining the association needed to
reuse its record store during generation and emission. -/
def checkedStore (limits : Ix.Kernel.Admission.Limits) (env : Ixon.Env) :
    Except String (CheckedStore limits env) :=
  match checked : recordStore limits env with
  | .error error => .error error
  | .ok records => .ok ⟨records, checked⟩

/-- Structural source spelling for certificate names, including duplicate
spellings that a forged stored Ix.Name hash would otherwise distinguish. -/
def sourceAddresses (env : Ixon.Env) : Except String (Std.HashMap Ix.Kernel.Name Address) := do
  let entries := Ix.Compile.Parallel.map 32
    (fun (name, named) => (Ix.LeanIngress.ingressName name, named.addr))
    env.named.toArray
  let mut out : Std.HashMap Ix.Kernel.Name Address := Std.HashMap.emptyWithCapacity entries.size
  for (key, addr) in entries do
    if out.contains key then throw s!"role generation: duplicate source spelling {key}"
    out := out.insert key addr
  return out

def mergeRecords (left right : RecordStore) : Except String RecordStore := do
  let mut out := left
  for (address, record) in right.toList do
    if let some old := out[address]? then
      unless Ixon.serConstant old == Ixon.serConstant record do
        throw s!"role generation: conflicting record bytes at {address}"
    else out := out.insert address record
  return out

/-- Refuse conflicting certificate bytes anywhere in the artifact, including
outside the support used for evidence generation. Authentication and canonical
decoding remain separate checks; a shared address does not imply equal bytes. -/
def checkCertificateContent (artifact certificates : Ixon.Env) : Except String Unit := do
  for (address, record) in certificates.consts.toList do
    if let some old := artifact.consts[address]? then
      unless old.rawBytes == record.rawBytes do
        throw s!"role generation: conflicting record bytes at {address}"
  for (address, bytes) in certificates.blobs.toList do
    if let some old := artifact.blobs[address]? then
      unless old == bytes do throw s!"role generation: conflicting blob bytes at {address}"

def readDeclarations (s : Setup) (addresses : Array Address) :
    Except String (Array (CDecl .anon)) := do
  let mut state : State .anon := {}
  let mut out : Array (CDecl .anon) := #[]
  for address in addresses do
    let some record := s.store[address]?
      | throw s!"role generation: missing closure record {address}"
    let read ← (readRecord s.cx state address record).mapError
      fun e => s!"role generation: reading {address}: {e}"
    state := state.commit read
    out := out ++ read.decls
  return out

structure Generated where
  publication : Publication
  table : RoleTable
  prelude : Array (Address × Ixon.Constant)
  evidence : Array (Address × Ixon.Constant)
  blobs : Array (Address × ByteArray)
  /-- Ordinary certificate dependencies retained for definition equations.
  Consumers check these declarations before using their theorem evidence. -/
  support : Array (Address × Ixon.Constant) := #[]
  supportBlobs : Array (Address × ByteArray) := #[]
  supportHints : Array (Address × Lean.ReducibilityHints) := #[]
  /-- Retained for independent reader roundtrip verification by the caller. -/
  closed : Std.HashMap Address (CExpr .anon)

/-- Generate evidence for the required, actually published roles. The
certificate module's bound operations must have the artifact's addresses.
Missing proofs, unreadable closure records and noncanonical output refuse.
`store?` carries a checked store for this artifact and these limits when the
caller has already built it. -/
def generate (limits : Ix.Kernel.Admission.Limits) (env certificates : Ixon.Env)
    (required : List Role) (groups : List (List Role))
    (store? : Option (CheckedStore limits env) := none) : Except String Generated := do
  let store ← match store? with
    | some store => pure store.records
    | none => recordStore limits env
  let published ← publication env (store[·]?) required
  let boundOnly := RoleTable.ofEntries Ix.Kernel.specVersion published.bound.toList []
  let preRecords ← preludeRecords boundOnly (store[·]?) groups
  let pre : Prelude .anon ← readPrelude boundOnly preRecords
  let base := setup store (env.blobs[·]?) boundOnly pre (Hints.ofStore store env.anonHints).lookup
  for (role, ref) in published.refs.toList do
    unless (base.cx.memberKey ref).toOption == some (Ix.Kernel.roleKey role) do
      throw s!"role generation: {repr role} is not read under its role key"

  let certRecords ← recordStore limits certificates
  let certNames ← sourceAddresses certificates
  let certStore ← mergeRecords base.store certRecords
  for (role, address) in published.bound do
    if let some certAddress := certNames[role.leanName]? then
      unless address == certAddress do
        throw s!"role generation: shared role addresses differ for {repr role}"
  for (address, bytes) in certificates.blobs.toList do
    if let some old := env.blobs[address]? then
      unless old == bytes do throw s!"role generation: conflicting blob bytes at {address}"
  let selected := Ix.RoleEvidence.allCertTheorems.filter fun (r, _) => required.contains r
  for (role, _) in selected do
    let some address := certNames[role.leanName]?
      | throw s!"role generation: certificate input has no {repr role}"
    unless boundOnly.addressOf? role == some address do
      throw s!"role generation: certificate and artifact addresses differ for {repr role}"
  let cs := setup certStore (fun a => certificates.blobs[a]? <|> env.blobs[a]?) boundOnly pre
    (Hints.ofStore certStore certificates.anonHints).lookup
  let mut certAt : Std.HashMap Lean.Name Address := {}
  let mut roots := preRecords.map (·.1)
  for (role, theorems) in selected do
    let some ref := published.refs[role]?
      | throw s!"role generation: unresolved required operation {repr role}"
    roots := roots.push ref.block
    for name in theorems do
      let some address := certNames[Ix.Kernel.Name.ofLeanName name]?
        | throw s!"role generation: certificate input has no {name}"
      unless certStore.contains address do
        throw s!"role generation: missing certificate record for {name}"
      certAt := certAt.insert name address
      roots := roots.push address
  let declarations ← readDeclarations cs (closure cs.store cs.extra roots)
  let values : Ix.RoleEvidence.Universe .anon := declarations.foldl Ix.RoleEvidence.Universe.add {}
  let lookup := Ix.RoleEvidence.lookupOf declarations
  let mut addrOfName : Std.HashMap (CName .anon) Address := {}
  for (address, _) in cs.store.toArray.qsort (fun x y => x.1.cmpBytes y.1 == .lt) do
    if let .ok key := cs.cx.keyAt address then
      unless addrOfName.contains key do addrOfName := addrOfName.insert key address
  for (role, address) in published.bound do
    addrOfName := addrOfName.insert (Ix.Kernel.roleKey role) address
  let mut keys : Std.HashMap Lean.Name (CName .anon) := {}
  for (name, address) in certAt.toList do
    let key ← (cs.cx.keyAt address).mapError fun e => s!"role generation: {name}: {e}"
    keys := keys.insert name key
  let mut evidence := (Ix.RoleEvidence.defeqRoles.filter required.contains).toArray.map
    (fun r => (r, (Ix.RoleEvidence.defeqEvidence (K := Address) r).toArray)) ++
      (Ix.RoleEvidence.defeqDefinitions (K := Address)).toArray.filter (required.contains ·.1)
  let mut records : Array (Address × Ixon.Constant) := #[]
  let mut blobs : Array (Address × ByteArray) := #[]
  let mut closed : Std.HashMap Address (CExpr .anon) := {}
  for (role, theorems) in selected do
    -- The same closure operations as RoleEvidence.closedProofs, with a
    -- fallible certificate-key lookup instead of its total key function.
    let operation := Ix.Kernel.roleKey (md := .anon) role
    let some operationValue := Ix.RoleEvidence.valueOf declarations operation
      | throw s!"role generation: {repr role} is not a definition here"
    let isOperation := Ix.RoleEvidence.certTheorems.any (·.1 == role)
    let allowed := Ix.RoleEvidence.allowedFor (lookup[·]?) operation operationValue
    -- Capture the computed set: a function-valued conditional causes closure
    -- conversion to repeat the graph walk for every visited proof node.
    let keep : CName .anon → Bool := allowed.contains
    let proofs ← theorems.mapM fun name => do
      let some key := keys[name]? | throw s!"role generation: missing certificate key for {name}"
      let some value := Ix.RoleEvidence.theoremOf declarations key
        | throw s!"role generation: {name} is not a theorem here"
      let proof ← (if isOperation then Ix.RoleEvidence.closeProof values keep value
        else .ok value).mapError
        fun e => s!"role generation: {name}: {e}"
      pure (key, proof)
    let mut entries : Array (Ix.Kernel.Evidence Address) := #[]
    for (key, proof) in proofs do
      let some type := declarations.findSome? (fun
          | .thmDecl cv _ => if cv.name == key then some cv.type else none
          | _ => none)
        | throw s!"role generation: no theorem statement for {key}"
      let (record, extraBlobs) ← Evidence.theoremRecord (addrOfName[·]?) type proof
      let bytes := Ixon.serConstant record
      let decoded ← Ixon.Canonical.deConstant limits.maxRecordBytes limits.maxRecordUnivNodes bytes
      unless Ixon.serConstant decoded == bytes do throw "role generation: noncanonical proof record"
      let address := Address.admissionHash bytes
      records := records.push (address, record)
      closed := closed.insert address proof
      entries := entries.push (.proof address)
      for (a, b) in extraBlobs do
        if let some (_, old) := blobs.find? (·.1 == a) then
          unless old == b do throw s!"role generation: conflicting generated blob at {a}"
        else blobs := blobs.push (a, b)
    evidence := evidence.push (role, Ix.RoleEvidence.evidenceEntries role entries)
  let table := RoleTable.ofEntries Ix.Kernel.specVersion published.bound.toList evidence.toList
  table.check
  unless table.wireWF do throw "role generation: table exceeds the canonical wire domain"
  let bytes := table.toBytes
  let decoded ← (Ix.Kernel.Admission.admitBinding Address.admissionHash
    ⟨Address.admissionHash bytes, bytes⟩).mapError fun e => toString (Ix.Kernel.Admission.Error.binding e)
  unless decoded.toBytes == bytes do throw "role generation: binding does not roundtrip"
  let finalPrelude : Prelude .anon ← readPrelude table preRecords records blobs.toList
  let retained := selected.any fun (role, _) => !Ix.RoleEvidence.certTheorems.any (·.1 == role)
  let support := if retained then certRecords.toArray else #[]
  let supportBlobs := if retained then certificates.blobs.toArray else #[]
  let supportHints := if retained then certificates.anonHints.toArray else #[]
  let finalStore := if retained then certStore else store
  let final := setup finalStore (fun a => env.blobs[a]? <|> certificates.blobs[a]?) table finalPrelude
    (Hints.ofStore finalStore env.anonHints).lookup
  for (role, expected) in table.evidence do
    let actual := ((final.evidence.find? (·.1 == role)).map (·.2)).getD []
    unless actual.length == expected.size do
      throw s!"role generation: evidence for {repr role} does not all read back"
    for (want, got) in expected.toList.zip actual do
      match want, got with
      | .defeq, .defeq => pure ()
      | .proof address, .proof (_, value) =>
        unless closed[address]? == some value do
          throw s!"role generation: proof at {address} does not read back as its closed value"
      | _, _ => throw s!"role generation: evidence kind changed for {repr role}"
  return {
    publication := published, table, prelude := preRecords, evidence := records
    blobs, closed, support, supportBlobs, supportHints }

/-- Insert generated proof records, literal blobs and the exact binding.
This explicitly regenerates a binding: any previous binding is replaced only
after the new table's source publications match this artifact. Existing record
and blob bytes cannot be overwritten. The caller must still check the resulting
artifact at the certified entry; a previous certificate does not transfer.
`store?` carries a checked store for this artifact and these limits (as for
`generate`), so that one artifact is authenticated and decoded once; `roleStore?`
supplies an already-checked role-closure lookup when only the role closure was
decoded ahead of whole-artifact finalization checks. -/
def Generated.emit (generated : Generated) (limits : Ix.Kernel.Admission.Limits)
    (env : Ixon.Env) (store? : Option (CheckedStore limits env) := none)
    (roleStore? : Option Store := none)
    (sourceAddrs? : Option (Std.HashMap Ix.Kernel.Name Address) := none) :
    Except String Ixon.Env := do
  generated.table.check
  unless generated.table.wireWF do throw "role emission: noncanonical binding table"
  let lookup : Store ← match store?, roleStore? with
    | some store, _ => pure (store.records[·]?)
    | none, some s => pure s
    | none, none =>
      let s ← recordStore limits env
      pure (s[·]?)
  let required := generated.table.bound.toList.map (·.1)
  let actual ← match sourceAddrs? with
    | some existing => do
      unless required.Nodup do throw "role publication: a required role occurs twice"
      let mut bound : Array (Role × Address) := #[]
      let mut refs : Std.HashMap Role (ConstRef Address) := {}
      let mut roleOfRef : Std.HashMap (ConstRef Address) Role := {}
      for role in Role.all do
        unless required.contains role do continue
        let some address := existing[role.leanName]?
          | throw s!"role publication: no published constant for {repr role}"
        let some record := lookup address
          | throw s!"role publication: {repr role} has no record at {address}"
        let some ref := resolveSource lookup address record
          | throw s!"role publication: {repr role} at {address} does not resolve"
        if let some other := roleOfRef[ref]? then
          throw s!"role publication: {repr role} and {repr other} resolve to the same member"
        roleOfRef := roleOfRef.insert ref role
        refs := refs.insert role ref
        bound := bound.push (role, address)
      pure { bound, refs }
    | none => Ix.RoleBinding.publication env lookup required
  unless actual.bound == generated.table.bound do
    throw "role emission: binding differs from this artifact's published roles"
  let mut out := env
  for (address, record) in generated.support ++ generated.evidence do
    let bytes := Ixon.serConstant record
    unless Address.admissionHash bytes == address do throw s!"role emission: bad record address {address}"
    let decoded ← Ixon.Canonical.deConstant limits.maxRecordBytes limits.maxRecordUnivNodes bytes
    unless Ixon.serConstant decoded == bytes do throw s!"role emission: noncanonical record at {address}"
    if let some old := out.consts[address]? then
      unless old.rawBytes == bytes do throw s!"role emission: conflicting record at {address}"
    else out := { out with consts := out.consts.insert address { buf := bytes, off := 0, len := bytes.size, cache := some record } }
  for (address, bytes) in generated.supportBlobs ++ generated.blobs do
    unless Address.admissionHash bytes == address do throw s!"role emission: bad blob address {address}"
    if let some old := out.blobs[address]? then
      unless old == bytes do throw s!"role emission: conflicting blob at {address}"
    else out := { out with blobs := out.blobs.insert address bytes }
  for (address, hint) in generated.supportHints do
    match out.anonHints[address]? with
    | some old =>
      unless Ixon.mergeHints old hint == old do
        throw s!"role emission: certificate support would change the original hint at {address}"
    | none => out := { out with anonHints := out.anonHints.insert address hint }
  for (address, record) in generated.support ++ generated.evidence do
    for dependency in record.refs do
      unless out.consts.contains dependency || out.blobs.contains dependency do
        throw s!"role emission: evidence {address} needs unavailable support {dependency}"
  unless out.consts.size ≤ limits.maxRecords do
    throw (byteError (.limit .records))
  unless out.blobs.size ≤ limits.maxBlobs do
    throw (byteError (.limit .blobs))
  let total := out.consts.fold (init := 0) (fun acc _ c => acc + c.len)
  let total := out.blobs.fold (init := total) (fun acc _ b => acc + b.size)
  unless total ≤ limits.maxTotalBytes do
    throw (byteError (.limit .totalBytes))
  let bytes := generated.table.toBytes
  return { out with roleBinding := some ⟨Address.admissionHash bytes, bytes⟩ }

end Ix.RoleBinding
