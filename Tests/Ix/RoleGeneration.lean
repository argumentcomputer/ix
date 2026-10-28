module

public import Ix.RoleBinding.Generate
public import Ix.RoleBinding.Artifact
public import Ix.Resource.Typing
public import LSpec

namespace Tests.Ix.RoleGeneration

open Ixon
open Ix.Kernel (Role RoleTable)

private def need (label : String) (ok : Bool) : Except String Unit :=
  if ok then .ok () else .error label

private def sourceName (role : Role) : Ix.Name :=
  Ix.Name.fromLeanName (Ix.RoleEvidence.toLeanName (Ix.Kernel.roleKey (md := .anon) role))

/-- Actual committed constant/proof bytes are fixtures here. No production
binding is obtained from a default table by the generator under test. -/
private def inputs (operation : Role) (complete : Bool := false) :
    Except String (Env × Env × List Role × Array Address) := do
  let table ← Ix.Kernel.Reader.defaultTable
  let prelude ← Ix.Kernel.Reader.preludeRecords
  let closure ← Ix.Kernel.Reader.decodeCommitted "fixture closure" Ix.Kernel.Reader.RoleData.closure
  let proofs ← Ix.Kernel.Reader.evidenceRecords
  let literals ← Ix.Kernel.Reader.evidenceBlobs
  let closureLiterals ← Ix.Kernel.Reader.RoleData.closureBlobs.toList.mapM fun (hex, bytes) => do
    let some address := Ix.Kernel.Reader.addressOfHex hex | throw "fixture: bad blob address"
    let some value := bytesOfHex bytes | throw "fixture: bad blob bytes"
    pure (address, value)
  let mut env : Env := {}
  for (a, c) in prelude ++ closure do
    env := { env with consts := env.consts.insert a (LazyConstant.ofConstant c) }
  for (a, bytes) in literals ++ closureLiterals do
    env := { env with blobs := env.blobs.insert a bytes }
  let mut required := if complete then table.bound.toList.filterMap
    (fun (role, address) => if env.consts.contains address then some role else none)
    else operation :: Ix.Kernel.preludeShape.flatten
  for _ in [:Role.all.length] do
    required := (required ++ required.flatMap Role.block ++ required.flatMap Role.deps).eraseDups
  required := Role.all.filter required.contains
  for role in required do
    let some address := table.addressOf? role | throw s!"fixture: missing role {repr role}"
    let name := sourceName role
    env := { env with
      named := env.named.insert name { addr := address }
      names := env.names.insert name.getHash name }
  let mut certificates := env
  for (a, c) in proofs do
    certificates := { certificates with consts := certificates.consts.insert a (LazyConstant.ofConstant c) }
  let mut addresses := #[]
  for (role, names) in Ix.RoleEvidence.certTheorems do
    unless required.contains role do continue
    let some (_, evidence) := table.evidence.find? (·.1 == role)
      | throw "fixture: operation has no evidence entries"
    need "fixture: certificate count" (names.length == evidence.size)
    for (name, entry) in names.zip evidence.toList do
      let .proof address := entry | throw "fixture: expected proof evidence"
      let name := Ix.Name.fromLeanName name
      certificates := { certificates with
        named := certificates.named.insert name { addr := address }
        names := certificates.names.insert name.getHash name }
      addresses := addresses.push address
  return (env, certificates, required, addresses)

/-- A complete generated fixture shared with the actual consumer/CLI controls.
The committed bytes remain test inputs, never a production fallback. -/
public def completeArtifact (operation : Role) : Except String (Env × Ix.RoleBinding.Generated) := do
  let (env, certificates, required, _) ← inputs operation true
  let generated ← Ix.RoleBinding.generate Ix.Resource.typingLimits env certificates required Ix.Kernel.preludeShape
  return (← generated.emit Ix.Resource.typingLimits env, generated)

private def checks (operation : Role) : Except String Unit := do
  let (env, certificates, required, proofAddresses) ← inputs operation
  let limits := Ix.Resource.typingLimits
  let generated ← Ix.RoleBinding.generate limits env certificates required Ix.Kernel.preludeShape
  need "every requested role is actually published"
    (generated.publication.bound.size == required.length)
  need "actual proof certificates are generated and read back"
    (generated.evidence.size == proofAddresses.size && !generated.evidence.isEmpty)
  let emitted ← generated.emit limits env
  need "original checked bytes are retained"
    (env.consts.toList.all fun (a, c) => (emitted.consts[a]?).any (·.rawBytes == c.rawBytes))
  need "all generated proof records are emitted with their exact bytes"
    (generated.evidence.all fun (a, c) => (emitted.consts[a]?).any (·.rawBytes == serConstant c))
  let some binding := emitted.roleBinding | throw "binding was not emitted"
  need "binding is the actual generated table"
    (binding.bytes == generated.table.toBytes && binding.address == Address.admissionHash binding.bytes)
  let admitted ← (Ix.Kernel.Admission.admitBinding Address.admissionHash
    ⟨binding.address, binding.bytes⟩).mapError fun e => toString (Ix.Kernel.Admission.Error.binding e)
  need "emitted binding passes real canonical and structural admission"
    (admitted.toBytes == generated.table.toBytes)
  let bytes ← serEnv emitted
  let store ← Ix.RoleBinding.checkedStore limits env
  let cached ← Ix.RoleBinding.generate limits env certificates required Ix.Kernel.preludeShape
    (store? := some store)
  let cachedArtifact ← cached.emit limits env (store? := some store)
  need "reusing authenticated records preserves the complete emitted bytes"
    ((← serEnv cachedArtifact) == bytes)
  let decoded ← deEnv bytes
  need "generated artifact uses v5 and retains its exact binding"
    (bytes.data[0]? == some 0xE5 && decoded.roleBinding == emitted.roleBinding)

  let noRole := { env with named := env.named.erase (sourceName operation) }
  need "missing required source role refuses generation"
    (!(Ix.RoleBinding.generate limits noRole certificates required Ix.Kernel.preludeShape).isOk)
  need "emission cannot reuse a binding after publication changes"
    (!(generated.emit limits noRole).isOk)
  let changedStore ← Ix.RoleBinding.checkedStore limits noRole
  need "checked records do not bypass the generation publication check"
    (!(Ix.RoleBinding.generate limits noRole certificates required Ix.Kernel.preludeShape
      (store? := some changedStore)).isOk)
  need "checked records do not bypass the emission publication check"
    (!(cached.emit limits noRole (store? := some changedStore)).isOk)
  let some zero := env.named[sourceName .natZero]? | throw "fixture has no Nat.zero"
  let otherRole := { certificates with named := certificates.named.insert (sourceName operation) zero }
  need "certificate/artifact operation mismatch refuses generation"
    (!(Ix.RoleBinding.generate limits env otherRole required Ix.Kernel.preludeShape).isOk)
  let some missing := proofAddresses[0]? | throw "fixture has no proof"
  let missingEnv := { env with consts := env.consts.erase missing }
  let missingCert := { certificates with consts := certificates.consts.erase missing }
  need "missing actual certificate record refuses generation"
    (!(Ix.RoleBinding.generate limits missingEnv missingCert required Ix.Kernel.preludeShape).isOk)
  let some (_, record) := generated.evidence[0]? | throw "no generated record"
  let wrong := Address.admissionHash (ByteArray.mk #[8, 9, 10])
  let unauthenticated := { env with consts := env.consts.insert wrong (LazyConstant.ofConstant record) }
  need "raw record authentication precedes generation"
    (!(Ix.RoleBinding.generate limits unauthenticated certificates required Ix.Kernel.preludeShape).isOk)

  -- An empty input cannot make its old records reject before these new-record
  -- limits are tested. This reference-free definition is Prop : Type.
  let small : Constant := {
    sharing := #[], refs := #[], univs := #[.zero, .succ .zero]
    info := .defn { kind := .defn, safety := .safe, lvls := 0, typ := .sort 1, value := .sort 0 }
  }
  let smallBytes := serConstant small
  let smallAddress := Address.admissionHash smallBytes
  let larger := { env with consts := env.consts.insert smallAddress (LazyConstant.ofConstant small) }
  let largerStore ← Ix.RoleBinding.checkedStore limits larger
  let fullGenerated ← Ix.RoleBinding.generate limits larger certificates required Ix.Kernel.preludeShape
    (store? := some largerStore)
  let fullArtifact ← fullGenerated.emit limits larger (store? := some largerStore)
  let closureArtifact ← generated.emit limits larger (store? := some largerStore)
  need "generation over support retains the complete artifact's bytes"
    ((← serEnv closureArtifact) == (← serEnv fullArtifact))
  let malformedBytes := ByteArray.mk #[255]
  let malformedAddress := Address.admissionHash malformedBytes
  let malformed := { larger with consts := larger.consts.insert malformedAddress
    { buf := malformedBytes, len := malformedBytes.size } }
  need "whole-artifact validation refuses an authenticated malformed orphan"
    (!(Ix.RoleBinding.checkedStore limits malformed).isOk)
  let paddedBytes := smallBytes.push 0
  let paddedAddress := Address.admissionHash paddedBytes
  let noncanonical := { larger with consts := larger.consts.insert paddedAddress
    { buf := paddedBytes, len := paddedBytes.size } }
  need "whole-artifact validation refuses an authenticated noncanonical orphan"
    (!(Ix.RoleBinding.checkedStore limits noncanonical).isOk)
  let separate : Ix.RoleBinding.Generated := {
    publication := { bound := #[], refs := {} }
    table := { version := Ix.Kernel.specVersion, bound := #[], evidence := #[] }
    prelude := #[], evidence := #[(smallAddress, small)], blobs := #[], closed := {}
  }
  need "new canonical record emits under sufficient limits" (separate.emit limits {}).isOk
  need "new records obey the emission byte limit"
    (!(separate.emit { limits with maxRecordBytes := smallBytes.size - 1 } {}).isOk)
  need "new records obey the emission universe-node limit"
    (!(separate.emit { limits with maxRecordUnivNodes := 0 } {}).isOk)

public def units (operation : Role) : LSpec.TestSeq :=
  .individualIO "role generation: actual proof records, source bindings, emission and refusals" none (do
    let result ← IO.lazyPure fun _ => checks operation
    return match result with
      | .ok _ => (true, 0, 0, none)
      | .error message => (false, 0, 0, some message)) .done

private def artifactChecks (operation : Role) : Except String Unit := do
  let limits := Ix.Resource.typingLimits
  let (partialEnv, partialCertificates, partialRoles, _) ← inputs operation
  let partialGenerated ← Ix.RoleBinding.generate limits partialEnv partialCertificates partialRoles Ix.Kernel.preludeShape
  let partialArtifact ← partialGenerated.emit limits partialEnv
  need "a generated partial binding does not certify unbound standard axioms in the full record set"
    (!(Ix.RoleBinding.Artifact.check partialArtifact limits).isOk)
  -- Keep the exact same input records, supplying their actual fixture-source
  -- roles and certificates. The original partial fixture is retained above.
  let (env, certificates, required, _) ← inputs operation true
  let generated ← Ix.RoleBinding.generate limits env certificates required Ix.Kernel.preludeShape
  let emitted ← generated.emit limits env
  let receipt ← (Ix.RoleBinding.Artifact.check emitted limits).mapError toString
  need "actual certified fold checks a nonempty generated artifact" (!receipt.target.consts.isEmpty)
  need "receipt uses the exact emitted binding and every actual record"
    (receipt.prepared.binding.bytes == generated.table.toBytes &&
      receipt.prepared.records.length == emitted.consts.size)
  let anonymous := { emitted with named := {}, names := {}, addrToName := {} }
  need "certified artifact entry needs no named metadata" (Ix.RoleBinding.Artifact.check anonymous limits).isOk
  need "missing binding has its own refusal" (match Ix.RoleBinding.Artifact.check
      { emitted with roleBinding := none } limits with
    | .error .missingBinding => true
    | _ => false)
  let some raw := emitted.roleBinding | throw "fixture: no emitted binding"
  let badHash := { raw with address := Address.admissionHash (raw.bytes.push 0) }
  need "binding hash mismatch is refused" (match Ix.RoleBinding.Artifact.check
      { emitted with roleBinding := some badHash } limits with
    | .error (.binding (.mismatch _)) => true
    | _ => false)
  let malformedBytes := raw.bytes.push 0
  let malformed := { emitted with roleBinding := some ⟨Address.admissionHash malformedBytes, malformedBytes⟩ }
  need "rehashing a noncanonical binding cannot bypass decoding" (match Ix.RoleBinding.Artifact.check malformed limits with
    | .error (.binding .decode) => true
    | _ => false)
  let some opAddress := generated.table.addressOf? operation | throw "fixture: no operation"
  need "every bound role needs an actual record, even before the fold" (match Ix.RoleBinding.Artifact.check
      { emitted with consts := emitted.consts.erase opAddress } limits with
    | .error (.coverage _) => true
    | _ => false)
  let some (proofAddress, proofRecord) := generated.evidence[0]? | throw "fixture: no proof record"
  let some proofLazy := emitted.consts[proofAddress]? | throw "fixture: no stored proof"
  let badCache := { proofRecord with refs := #[] }
  need "cache-conflict fixture has different bytes" (serConstant badCache != proofLazy.rawBytes)
  let cached := { emitted with consts := emitted.consts.insert proofAddress { proofLazy with cache := some badCache } }
  need "conflicting materialized cache cannot replace authenticated bytes"
    (Ix.RoleBinding.Artifact.check cached limits).isOk
  let badBytes := { proofLazy with buf := ByteArray.mk #[0], off := 0, len := 1, cache := some proofRecord }
  need "a valid cache cannot rescue unauthenticated raw bytes" (match Ix.RoleBinding.Artifact.check
      { emitted with consts := emitted.consts.insert proofAddress badBytes } limits with
    | .error (.bytes (.mismatch _ _ _)) => true
    | _ => false)
  need "missing proof records cannot be supplied from committed fallback" (match Ix.RoleBinding.Artifact.check
      { emitted with consts := emitted.consts.erase proofAddress } limits with
    | .error (.coverage _) => true
    | _ => false)
  let some natAddress := generated.table.addressOf? .nat | throw "fixture: missing Nat binding"
  let some natRaw := emitted.consts[natAddress]? | throw "fixture: missing Nat record"
  let natRecord ← deConstant natRaw.rawBytes
  let owner := Ixon.CheckOrder.owner natAddress natRecord
  need "fixture has a distinct actual projection owner" (owner != natAddress && emitted.consts.contains owner)
  need "present projection cannot conceal its missing owner" (match Ix.RoleBinding.Artifact.check
      { emitted with consts := emitted.consts.erase owner } limits with
    | .error (.coverage _) => true
    | _ => false)
  let bind := fun (table : RoleTable) =>
    let bytes := table.toBytes
    { emitted with roleBinding := some ⟨Address.admissionHash bytes, bytes⟩ }
  let wrongKindBound := generated.table.bound.map fun (role, address) =>
    (role, if role == operation then proofAddress else address)
  let wrongKind := { generated.table with bound := wrongKindBound }
  need "an operation bound to a theorem does not evade its definition gate"
    (!(Ix.RoleBinding.Artifact.check (bind wrongKind) limits).isOk)
  let wrongPreludeBound := generated.table.bound.map fun (role, address) =>
    (role, if role == .nat then proofAddress else address)
  let wrongPrelude := { generated.table with bound := wrongPreludeBound }
  need "an altered prelude binding cannot use the committed prelude"
    (!(Ix.RoleBinding.Artifact.check (bind wrongPrelude) limits).isOk)
  let .defn original := proofRecord.info | throw "fixture: proof is not a definition record"
  let changed := { proofRecord with info := .defn { original with value := .var 0 } }
  let changedBytes := serConstant changed
  let changedAddress := Address.admissionHash changedBytes
  let changedEvidence := generated.table.evidence.map fun (role, entries) =>
    (role, entries.map fun
      | .proof address => .proof (if address == proofAddress then changedAddress else address)
      | .defeq => .defeq)
  let changedTable := { generated.table with evidence := changedEvidence }
  let changedArtifact := { bind changedTable with
    consts := (emitted.consts.erase proofAddress).insert changedAddress (LazyConstant.ofConstant changed) }
  need "authenticated replacement proof fails the actual certified consumer"
    (!(Ix.RoleBinding.Artifact.check changedArtifact limits).isOk)

public def artifactUnits (operation : Role) : LSpec.TestSeq :=
  .individualIO "artifact consumer: real fold, exact binding, no fallback and evidence refusals" none (do
    let result ← IO.lazyPure fun _ => artifactChecks operation
    return match result with
      | .ok _ => (true, 0, 0, none)
      | .error message => (false, 0, 0, some message)) .done

end Tests.Ix.RoleGeneration
