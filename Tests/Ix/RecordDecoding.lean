module

public import Ix.RoleBinding.Generate
public import LSpec

namespace Tests.Ix.RecordDecoding

open Ixon
open Ix.Kernel.Admission
open Ixon.CheckOrder (RecordStore)

private def need (label : String) (ok : Bool) : Except String Unit :=
  if ok then .ok () else .error label

private instance : BEq ByteError := ⟨fun left right => decide (left = right)⟩

private def sameResult [BEq ε] [BEq α] : Except ε α → Except ε α → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false

private def limits : Limits := ⟨2048, 8, 1 <<< 26, 1 <<< 20, 1 <<< 16⟩

private def constant (index : Nat) : Constant := {
  sharing := #[], refs := #[], univs := #[.zero, .succ .zero]
  info := .defn {
    kind := .defn, safety := .safe, lvls := index.toUInt64, typ := .sort 1, value := .sort 0 }
}

private def raw (bytes : ByteArray) : Address × ByteArray :=
  (Address.admissionHash bytes, bytes)

private def records (count : Nat) : Array (Address × ByteArray) :=
  (Array.range count).map fun i => raw (serConstant (constant i))

private def environment (records : Array (Address × ByteArray)) : Env :=
  { consts := records.foldl (fun out (a, bytes) => out.insert a
      { buf := bytes, len := bytes.size }) {} }

/-- Keep the original literal implementation: the production entry has a
compiler simplification, so comparing two calls to that entry is insufficient. -/
private def serialStore (limits : Limits) (env : Env) : Except String RecordStore := do
  let records := (env.consts.toArray.map fun (a, c) => (a, c.rawBytes)).qsort
    fun x y => x.1.cmpBytes y.1 == .lt
  let blobs := (env.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList
  (preflight limits records.toList blobs).mapError Ix.RoleBinding.byteError
  (uniqueKeys records.toList blobs).mapError Ix.RoleBinding.byteError
  (authenticate Address.admissionHash records.toList blobs).mapError Ix.RoleBinding.byteError
  let decoded ← (decodeRecords limits records.toList).mapError Ix.RoleBinding.byteError
  return decoded.foldl (fun out (a, c) => out.insert a c) {}

private def storeBytes (result : Except String RecordStore) : Except String (Array (Address × ByteArray)) :=
  result.map fun store => (store.toArray.map fun (a, c) => (a, serConstant c)).qsort
    fun x y => x.1.cmpBytes y.1 == .lt

private def storeParity (label : String) (limits : Limits) (env : Env) : Except String Unit := do
  let expected := storeBytes (serialStore limits env)
  need s!"{label}: explicit parallel store preserves the serial result"
    (sameResult (storeBytes (Ix.RoleBinding.recordStoreParallel limits env)) expected)
  need s!"{label}: production store preserves the serial result"
    (sameResult (storeBytes (Ix.RoleBinding.recordStore limits env)) expected)

private def storeError (label : String) (limits : Limits) (env : Env) (error : ByteError) :
    Except String Unit := do
  storeParity label limits env
  need s!"{label}: exact refusal"
    (sameResult (storeBytes (Ix.RoleBinding.recordStore limits env))
      (.error (Ix.RoleBinding.byteError error)))

private def decodingChecks (largeCount : Nat) : Except String Unit := do
  for count in [0, 1, 17, largeCount] do
    let input := records count
    let expected := (Array.range count).map fun i =>
      (Address.admissionHash (serConstant (constant i)), constant i)
    for tasks in [0, 1, 2, 8, 256, 1024] do
      let actual := Ix.RoleBinding.RecordDecoding.parallel tasks limits input.toList
      need s!"{count} records / {tasks} tasks: complete input order and values"
        (sameResult actual (.ok expected.toList))
      need s!"{count} records / {tasks} tasks: serial parity"
        (sameResult actual (decodeRecords limits input.toList))
  let input := records largeCount
  let malformed := raw (ByteArray.mk #[255])
  let noncanonical := raw ((serConstant (constant 900)).push 0)
  -- With 769 records and 256 tasks the chunk size is four. The earlier
  -- failure may end one chunk while the other starts the next.
  for (first, second) in [(0, 4), (3, 4), (4, 255), (255, 256), (767, 768)] do
    for (early, later) in [(malformed, noncanonical), (noncanonical, malformed)] do
      let altered := (input.set! first early).set! second later
      let .error reason := Ixon.Canonical.deConstant limits.maxRecordBytes
        limits.maxRecordUnivNodes early.2 | throw "fixture unexpectedly decodes"
      let expected := Except.error (ByteError.decode first early.1 reason)
      for tasks in [1, 8, 256, 1024] do
        let actual := Ix.RoleBinding.RecordDecoding.parallel tasks limits altered.toList
        need s!"failures at {first}/{second}, {tasks} tasks: earliest complete error"
          (sameResult actual expected && sameResult actual (decodeRecords limits altered.toList))
  let manyUniverses := { constant 900 with univs := Array.replicate 64 .zero }
  let oversized := raw (ByteArray.mk (Array.replicate 65 0))
  for (tight, excessive) in [
      ({ limits with maxRecordBytes := 64 }, oversized),
      ({ limits with maxRecordUnivNodes := 8 }, raw (serConstant manyUniverses))] do
    need "ordinary records fit the tighter per-record bound" (decodeRecords tight input.toList).isOk
    let .error reason := Ixon.Canonical.deConstant tight.maxRecordBytes
      tight.maxRecordUnivNodes excessive.2 | throw "oversized fixture unexpectedly decodes"
    for first in [3, 4, 768] do
      let altered := input.set! first excessive
      let expected := Except.error (ByteError.decode first excessive.1 reason)
      let actual := Ix.RoleBinding.RecordDecoding.parallel 256 tight altered.toList
      need "per-record bounds preserve the exact late refusal across chunks"
        (sameResult actual expected && sameResult actual (decodeRecords tight altered.toList))

private def storeChecks (count : Nat) : Except String Unit := do
  let input := records count
  let env := environment input.reverse
  storeParity "large canonical store" limits env
  let .ok store := Ix.RoleBinding.recordStore limits env | throw "canonical store refused"
  need "all distinct records survive parallel store construction" (store.size == count)
  for i in [0, 3, 4, 255, 256, 768] do
    let record := constant i
    need "stored values match their original address"
      (store[Address.admissionHash (serConstant record)]? == some record)

  let malformed := raw (ByteArray.mk #[255])
  let noncanonical := raw ((serConstant (constant 900)).push 0)
  for orphan in [malformed, noncanonical] do
    let altered := environment (input.push orphan)
    need "orphan controls have no named roots" altered.named.isEmpty
    storeParity "authenticated orphan" limits altered
    need "an authenticated malformed or noncanonical orphan refuses the checked store"
      (!(Ix.RoleBinding.checkedStore limits altered).isOk)
    let both := environment ((input.push malformed).push noncanonical)
    storeParity "multiple authenticated orphan failures" limits both
    need "multiple authenticated orphans still refuse" (!(Ix.RoleBinding.recordStore limits both).isOk)

  let bad : Env := environment #[malformed]
  let wrong := Address.admissionHash (ByteArray.mk #[1, 2, 3])
  need "mismatch fixture has distinct addresses" (wrong != malformed.1)
  let unauthenticated := environment #[(wrong, malformed.2)]
  let badBlob := { bad with blobs := ({} : Std.HashMap Address ByteArray).insert wrong malformed.2 }
  storeError "record count precedes authentication and decoding"
    { limits with maxRecords := 0 } unauthenticated (.limit .records)
  storeError "blob count precedes decoding"
    { limits with maxBlobs := 0 } badBlob (.limit .blobs)
  storeError "payload total precedes authentication and decoding"
    { limits with maxTotalBytes := 0 } unauthenticated (.limit .totalBytes)
  storeError "record authentication precedes decoding" limits unauthenticated
    (.mismatch .records 0 wrong)
  storeError "blob authentication precedes record decoding" limits badBlob
    (.mismatch .blobs 0 wrong)
  let bothBad := { unauthenticated with blobs := badBlob.blobs }
  storeError "record authentication precedes blob authentication" limits bothBad
    (.mismatch .records 0 wrong)
  let .error reason := Ixon.Canonical.deConstant limits.maxRecordBytes
    limits.maxRecordUnivNodes malformed.2 | throw "malformed fixture unexpectedly decodes"
  storeError "decode error retains its address and position" limits bad
    (.decode 0 malformed.1 reason)
  let cachedRecord : LazyConstant :=
    { buf := malformed.2, len := malformed.2.size, cache := some (constant 0) }
  let cached := { bad with consts := bad.consts.insert malformed.1 cachedRecord }
  storeError "a valid materialized cache cannot rescue malformed bytes" limits cached
    (.decode 0 malformed.1 reason)

private def unit (label : String) (check : Unit → Except String Unit) : LSpec.TestSeq :=
  .individualIO label none (do
    let result ← IO.lazyPure fun _ => check ()
    return match result with
      | .ok _ => (true, 0, 0, none)
      | .error message => (false, 0, 0, some message)) .done

public def suite : List LSpec.TestSeq := [
  unit "canonical decoding: values, boundaries and exact first refusals" (fun _ => decodingChecks 769),
  unit "record store: phase precedence, exact errors and authenticated orphans" (fun _ => storeChecks 769)
]

end Tests.Ix.RecordDecoding
