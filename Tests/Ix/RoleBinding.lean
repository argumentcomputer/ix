module
public import Ix.Ixon
public import IxC.Kernel.Admission
public import Tests.FFI.Ixon
public import LSpec

namespace Tests.Ix.RoleBinding
open Ixon
open Ix.Kernel (RoleTable)
open Ix.Kernel.Admission (Binding admitBinding)

private def need (label : String) (ok : Bool) : Except String Unit :=
  if ok then .ok () else .error label

private def raw (bytes : ByteArray) : RoleBinding :=
  ⟨Address.admissionHash bytes, bytes⟩

private def tableBinding (table : RoleTable) : RoleBinding := raw table.toBytes

private def admitted (binding : RoleBinding) :=
  admitBinding Address.admissionHash (⟨binding.address, binding.bytes⟩ : Binding)

private def readers (bytes : ByteArray) : List (Except String Env) :=
  [deEnv bytes, (deEnvVerifiedLazy bytes).map (·.env), rsDeEnv bytes,
    deEnvAnon bytes, rsDeEnvAnon bytes]

private def emptySections : PutM Unit := do
  for _ in [:3] do putTagN 0 0 0
  -- The format always stores the anonymous name at index zero.
  putTagN 0 0 1
  Serialize.put Ix.Name.mkAnon.getHash
  Env.putNameComponent Ix.Name.mkAnon
  putTagN 0 0 0
  putTagN 0 0 0

private def checks (original : Constant) : Except String Unit := do
  let table : RoleTable := { version := Ix.Kernel.specVersion, bound := #[], evidence := #[] }
  let binding := tableBinding table
  need "canonical empty table admits" (admitted binding).isOk
  let legacy : Env := {}
  let legacyBytes ← serEnv legacy
  let independentLegacy := runPut do
    putTagN 4 Env.FLAG 4
    Serialize.put Ix.Merkle.zeroAddress
    putU8 0
    putTagN 0 0 0
    emptySections
  need "empty v4 bytes are unchanged" (legacyBytes == independentLegacy)
  let bound := { legacy with roleBinding := some binding }
  let bytes ← serEnv bound
  let expected := runPut do
    putTagN 4 Env.FLAG 6
    Serialize.put Ix.Merkle.zeroAddress
    putU8 0
    putTagN 0 0 0
    Serialize.put binding.address
    putTagN 0 0 binding.bytes.size.toUInt64
    putBytes binding.bytes
    emptySections
    putTagN 0 0 0
    putTagN 0 0 0
  need "v6 header and empty original trailer have exact layout" (bytes == expected)
  need "Rust writer agrees exactly" ((← rsSerEnv bound) == bytes)
  for parsed in readers bytes do
    let env ← parsed
    need "all full/anonymous/lazy/FFI paths retain binding" (env.roleBinding == bound.roleBinding)
  let roundtrip := Tests.FFI.Ixon.roundtripRawEnv bound.toRawEnv
  need "raw FFI object preserves binding" (roundtrip.roleBinding == some binding)
  need "FFI content comparator sees binding" (Tests.FFI.Ixon.rsEqEnvSerialization bound.toRawEnv bytes)
  let other := raw (binding.bytes.push 0)
  let otherEnv := { bound with roleBinding := some other }
  let otherBytes ← serEnv otherEnv
  need "FFI comparator rejects binding-only changes"
    (!Tests.FFI.Ixon.rsEqEnvSerialization bound.toRawEnv otherBytes)
  for compareMeta in [false, true] do
    let difference ← rsDiffEnvs bytes otherBytes compareMeta
    need "binding-only changes appear in anonymous diff"
      (!difference.isEmpty && difference.roleBindingChanged.isSome &&
        difference.constsOnlyA.isEmpty && difference.constsOnlyB.isEmpty)

  let originalBytes := serConstant original
  let originalAddress := Address.admissionHash originalBytes
  let originals : Std.HashMap Address LazyConstant :=
    ({} : Std.HashMap Address LazyConstant).insert originalAddress (LazyConstant.ofConstant original)
  let withOriginal := { bound with originals }
  let withOriginalBytes ← serEnv withOriginal
  need "bound originals serialize identically" ((← rsSerEnv withOriginal) == withOriginalBytes)
  for parsed in [deEnv withOriginalBytes, (deEnvVerifiedLazy withOriginalBytes).map (·.env),
      rsDeEnv withOriginalBytes] do
    let env ← parsed
    need "v6 retains the exact original bytes"
      (env.roleBinding == bound.roleBinding &&
        (env.originals[originalAddress]?).map LazyConstant.rawBytes == some originalBytes)
  let unboundOriginal := { withOriginal with roleBinding := none }
  let v5 ← serEnv unboundOriginal
  need "unbound originals retain v5" (v5.data[0]? == some 0xE5 && (← rsSerEnv unboundOriginal) == v5)

  let wrong := { binding with address := Address.admissionHash (ByteArray.mk #[1, 2, 3]) }
  need "writer rejects wrong binding hash" (!(serEnv { bound with roleBinding := some wrong }).isOk)
  need "admission distinguishes hash failure" (match admitted wrong with | .error (.mismatch _) => true | _ => false)
  need "admission distinguishes canonical decoding failure" (match admitted other with | .error .decode => true | _ => false)
  let sameAddress := tableBinding { table with bound := #[(.nat, binding.address), (.bool, binding.address)] }
  need "admission distinguishes malformed table" (match admitted sameAddress with | .error (.malformed _) => true | _ => false)
  let duplicate := tableBinding { table with bound := #[(.nat, binding.address), (.nat, wrong.address)] }
  need "duplicate role bytes fail canonical admission" (match admitted duplicate with | .error .decode => true | _ => false)
  let empty := raw .empty
  let presentEmpty ← serEnv { bound with roleBinding := some empty }
  need "present empty payload does not downgrade to absent" (presentEmpty.data[0]? == some 0xE6)
  need "empty payload fails actual role admission" (match admitted empty with | .error .decode => true | _ => false)
  for parsed in readers presentEmpty do
    need "raw loaders preserve malformed payload until admission" ((← parsed).roleBinding == some empty)

  let corrupted := bytes.set! 35 ((bytes.get! 35) ^^^ (1 : UInt8))
  let oversized := (bytes.extract 0 67) ++ runPut (putTagN 0 0 (18446744073709551615 : UInt64))
  for malformed in [bytes.extract 0 35, bytes.extract 0 68, corrupted, oversized] do
    for parsed in readers malformed do
      need "every header reader rejects bad framing or hash" (!parsed.isOk)

/-- The parameter keeps foreign calls out of module initialization. -/
public def units (original : Constant) : LSpec.TestSeq :=
  .individualIO "role binding: exact legacy/v6 bytes, all loaders, FFI and admission boundary" none (do
    let result ← IO.lazyPure fun _ => checks original
    return match result with
      | .ok _ => (true, 0, 0, none)
      | .error message => (false, 0, 0, some message)) .done

end Tests.Ix.RoleBinding

