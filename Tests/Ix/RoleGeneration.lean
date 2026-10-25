module

public import Ix.RoleBinding.Generate
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
private def inputs (operation : Role) : Except String (Env × Env × List Role × Array Address) := do
  let table ← Ix.Kernel.Reader.defaultTable
  let prelude ← Ix.Kernel.Reader.preludeRecords
  let closure ← Ix.Kernel.Reader.decodeCommitted "fixture closure" Ix.Kernel.Reader.RoleData.closure
  let proofs ← Ix.Kernel.Reader.evidenceRecords
  let literals ← Ix.Kernel.Reader.evidenceBlobs
  let closureLiterals ← Ix.Kernel.Reader.RoleData.closureBlobs.toList.mapM fun (hex, bytes) => do
    let some address := Ix.Kernel.Reader.addressOfHex hex | throw "fixture: bad blob address"
    let some value := bytesOfHex bytes | throw "fixture: bad blob bytes"
    pure (address, value)
  let mut required := operation :: Ix.Kernel.preludeShape.flatten
  for _ in [:Role.all.length] do
    required := (required ++ required.flatMap Role.block ++ required.flatMap Role.deps).eraseDups
  required := Role.all.filter required.contains
  let mut env : Env := {}
  for (a, c) in prelude ++ closure do
    env := { env with consts := env.consts.insert a (LazyConstant.ofConstant c) }
  for (a, bytes) in literals ++ closureLiterals do
    env := { env with blobs := env.blobs.insert a bytes }
  for role in required do
    let some address := table.addressOf? role | throw s!"fixture: missing role {repr role}"
    let name := sourceName role
    env := { env with
      named := env.named.insert name { addr := address }
      names := env.names.insert name.getHash name }
  let mut certificates := env
  for (a, c) in proofs do
    certificates := { certificates with consts := certificates.consts.insert a (LazyConstant.ofConstant c) }
  let some (_, names) := Ix.RoleEvidence.certTheorems.find? (·.1 == operation)
    | throw "fixture: operation has no proof certificates"
  let some (_, evidence) := table.evidence.find? (·.1 == operation)
    | throw "fixture: operation has no evidence entries"
  need "fixture: certificate count" (names.length == evidence.size)
  let mut addresses := #[]
  for (name, entry) in names.zip evidence.toList do
    let .proof address := entry | throw "fixture: expected proof evidence"
    let name := Ix.Name.fromLeanName name
    certificates := { certificates with
      named := certificates.named.insert name { addr := address }
      names := certificates.names.insert name.getHash name }
    addresses := addresses.push address
  return (env, certificates, required, addresses)

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
  let decoded ← deEnv bytes
  need "generated artifact uses v6 and retains its exact binding"
    (bytes.data[0]? == some 0xE6 && decoded.roleBinding == emitted.roleBinding)

  let noRole := { env with named := env.named.erase (sourceName operation) }
  need "missing required source role refuses generation"
    (!(Ix.RoleBinding.generate limits noRole certificates required Ix.Kernel.preludeShape).isOk)
  need "emission cannot reuse a binding after publication changes"
    (!(generated.emit limits noRole).isOk)
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

end Tests.Ix.RoleGeneration
