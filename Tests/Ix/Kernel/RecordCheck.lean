import LSpec
import Ix.KernelCheck.Run
import Ix.KernelCheck.Meta
import Ix.RoleBinding.Generate
import Tests.Ix.Kernel.ReaderRoundtrip

/-! The normal record API returns verdicts, not mode-erasure agreement.
Small real checker inputs exercise rollback, first-error precedence, prefix
visibility, read-state commits and blocking. Compiled fixture records also
run through both real readers and one/several logical workers. -/

namespace Tests.Ix.Kernel.RecordCheck

open LSpec _root_.Ix.Kernel _root_.Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep

private def addr (n : Nat) : Address := Address.blake3 s!"record-check-{n}".toUTF8
private def cv (key : Nat → Key md) (n : Nat) : ConstantVal md :=
  ⟨key n, [], .sort (.succ .zero)⟩
private def good (key : Nat → Key md) (n : Nat) : Declaration md :=
  .defnDecl (cv key n) (.sort .zero) .opaque
private def bad (key : Nat → Key md) (n : Nat) : Declaration md :=
  .defnDecl (cv key n) (.sort (.succ .zero)) .opaque
private def use (key : Nat → Key md) (n srcN : Nat) : Declaration md :=
  .defnDecl (cv key n) (.const (key srcN) []) .opaque

private def fixture (key : Nat → Key md) : LoopSource Nat md :=
  let idx a := (List.range 25).find? fun n => addr n == a
  { view := fun a => (idx a).map fun n =>
      { kind := "fixture", recs := if n == 10 then #[addr 11] else #[],
        deps := fun _ => match n with
          | 2 => #[addr 1] | 9 => #[addr 8] | 18 => #[addr 17] | 22 => #[addr 21] | _ => #[] }
    read := fun st a => do
      let some n := idx a | throw (.malformed "missing fixture")
      if n == 6 then throw (.declined "fixture read decline")
      if n == 7 then throw (.malformed "fixture read rejection")
      if n == 11 then throw (.malformed "consumed recursor was read")
      if n == 16 && st != 13 then throw (.malformed s!"reading state {st}, expected 13")
      if n >= 17 && n != 18 then throw (.declined "tier disabled")
      return { decls := match n with
        | 1 => #[good key 1, bad key 2]
        | 3 => #[good key 0]
        | 4 => #[use key 4 0]
        | 5 => #[.axiomDecl (cv key 5)]
        | 12 => #[good key 12, bad key 13, good key 0]
        | 13 => #[use key 30 12]
        | 14 => #[use key 14 15]
        | 16 => #[]
        | 18 => #[use key 18 17]
        | _ => #[good key n] }
    commit := fun st _ _ => st + 1
    init := pure 0
    tier := some fun _ a => (idx a).bind fun n => match n with
      | 17 => some (.ok (.defs .part [(cv key 17, .sort .zero)]))
      | 19 => some (.ok (.unsafeOpaque (cv key 19) (.const (key 17) [])))
      | 20 => some (.ok (.defs .unsaf [(cv key 20, .const (key 17) [])]))
      | 21 => some (.ok (.defs .unsaf [(cv key 21, .sort (.succ .zero))]))
      | 22 => some (.ok (.unsafeAxiom (cv key 22)))
      | 23 => some (.ok (.unsafeAxiom { cv key 23 with type := .const (key 2) [] }))
      | 24 => some (.ok (.unsafeAxiom { cv key 24 with type := .const (key 1) [] }))
      | _ => none }

private def rowKey (r : Row) := (r.address, r.names, r.kind, r.outcome, r.reason)
private def reasonAt (rows : Array Row) (n : Nat) : String :=
  (rows[n]?).map (·.reason) |>.getD "missing row"
private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def outcomes (key : Nat → Key md) : IO Nat := do
  let src := fixture key
  let names a := #[toString a]
  let skip := ({} : Std.HashSet String).insert (toString (addr 8))
  let addresses := (Array.range 17).map addr
  let expected := #["accept", "reject", "blocked", "reject", "accept", "decline", "decline",
    "reject", "decline", "blocked", "accept", "accept", "reject", "accept", "reject", "accept", "accept"]
  let baseline ← runRecords src [] names addresses { skip }
  ensure (baseline.execution == .serial) "serial execution not reported"
  ensure (baseline.rows.map (·.address) == addresses) "record/recursor emission order changed"
  ensure (baseline.rows.map (·.outcome) == expected) s!"wrong logical outcomes: {baseline.rows.map (·.outcome)}"
  ensure ((reasonAt baseline.rows 1).startsWith "type mismatch in" &&
    (reasonAt baseline.rows 3).startsWith "duplicate declaration" &&
    (reasonAt baseline.rows 12).startsWith "type mismatch in") "first-error precedence changed"
  ensure ((reasonAt baseline.rows 6) == "reader: fixture read decline" &&
    (reasonAt baseline.rows 7) == "reader: fixture read rejection") "read error classification changed"
  ensure (baseline.failed[addr 2]? == some (addr 1) && baseline.failed[addr 9]? == some (addr 8))
    "blocked roots were not propagated"
  for n in [1, 3] do
    let pooled ← runRecords src [] names addresses { workers := some n, skip }
    ensure (pooled.execution == .pool n && pooled.execution.workers == n) "pool execution not reported"
    ensure (pooled.rows.map rowKey == baseline.rows.map rowKey) s!"pool {n}: verdict/order mismatch"
    ensure (pooled.counts == baseline.counts && pooled.reasons == baseline.reasons &&
      pooled.failed == baseline.failed) s!"pool {n}: aggregate maps mismatch"
  let tierAddresses := (Array.range 25).map addr
  let tiered ← runRecords src [] names tierAddresses { tier := true, skip }
  ensure (tiered.execution == .serialTier none) "tier execution not reported"
  let tierRows := tiered.rows.filter fun r => (Array.range 8).any fun i => r.address == addr (17 + i)
  let tierOrder := #[18, 17, 19, 20, 21, 22, 23, 24]
  ensure (tierRows.map (·.address) == tierOrder.map addr) "tier staging/fence order changed"
  ensure (tierRows.map (·.outcome) == #["decline", "typed", "decline", "typed", "decline", "blocked", "decline", "typed"])
    s!"wrong tier outcomes: {tierRows.map (·.outcome)}"
  ensure ((reasonAt tierRows 0).startsWith "fence: names the tier record" &&
    (reasonAt tierRows 1) == "partial" && (reasonAt tierRows 3) == "unsafe") "tier/fence reasons changed"
  ensure (tiered.failed[addr 22]? == some (addr 21)) "tier blocker root changed"
  for n in [1, 3] do
    let requested ← runRecords src [] names tierAddresses { workers := some n, tier := true, skip }
    ensure (requested.execution == .serialTier (some n) && requested.execution.workers == 1)
      "tier request silently claimed parallel execution"
    ensure (requested.rows.map rowKey == tiered.rows.map rowKey) "tier fallback changed outcomes"
  -- Inspect the real final logical state: prior good declarations survive a
  -- later failure; failed declarations and typed-only constants do not leak in.
  let state ← checkLoopWith src.view src.read src.commit (← src.init) (Checker.stepRecord []) {}
    names tierAddresses skip (fun _ => pure ()) (tier := src.tierHook)
  for n in [0, 1, 12, 15, 30] do ensure ((state.checker.fe.find? (key n)).isSome) s!"lost good prefix {n}"
  for n in [2, 13, 14, 17, 19, 20, 21, 24] do
    ensure ((state.checker.fe.find? (key n)).isNone) s!"failed/tier declaration leaked: {n}"
  let mut refusedZero := false
  try
    let _ ← runRecords src [] names addresses { workers := some 0 }
  catch e => refusedZero := e.toString == "record check: the pool needs a worker"
  ensure refusedZero "zero workers did not give the precise configuration error"
  -- `kernel-check-ixe`'s hand-rolled row line is `Row.json`'s compressed
  -- rendering, byte for byte (key order, escapes, numbers)
  let escaped : Row := ⟨addr 0, #["a\"b", "c\\d\ne", "é\u0001"], "kind\t", "decline",
    "reason: \"x\"\r\n", 12, 3⟩
  for row in (baseline.rows ++ tiered.rows).push escaped do
    ensure (row.jsonLine == row.json.compress) s!"Row.jsonLine is not Row.json: {row.jsonLine}"
  return baseline.rows.size + tiered.rows.size

private def compiled : IO Nat := do
  let (_, inp) ← Tests.Ix.Kernel.ReaderRoundtrip.input
  let table ← IO.ofExcept defaultTable
  let preA : Prelude .anon ← IO.ofExcept (preludeFor table)
  let preM : Prelude .meta ← IO.ofExcept (preludeFor table)
  let hints := Hints.ofStore inp.store inp.ixon.anonHints
  let s := setup inp.store (inp.ixon.blobs[·]?) table preA hints.lookup
  let wanted := Tests.Ix.Kernel.ReaderRoundtrip.defs "twice"
  let some named := inp.ixon.named[Ix.Name.fromLeanName wanted]?
    | throw (IO.userError "missing compiled target")
  let some targetRecord := s.store[named.addr]? | throw (IO.userError "missing target record")
  let target := owner named.addr targetRecord
  let addresses := closure s.store s.extra ((preA.records.map (·.1)).push target)
  let names := ((reportNames inp.ixon s.store).getD · #[])
  let (cxM, evM) := Benchmarks.Kernel.CheckIxeMeta.metaContext s (inp.ixon.blobs[·]?) table preM hints.lookup
  let display := Benchmarks.Kernel.CheckIxeMeta.displayTable inp.ixon cxM
  let nameCx : Ix.KernelDisplay.NameCx := ⟨inp.ixon.names, Ix.KernelDisplay.metaTable inp.ixon cxM⟩
  let srcM : LoopSource (State .meta) .meta :=
    { view := s.view, init := pure {}, commit := fun st _ rd => st.commit rd,
      read := fun st a => do
        let some source := s.store[a]? | throw (.malformed "record is missing")
        let rd ← readRecord cxM st a source
        return (Ix.KernelDisplay.nameRead nameCx (Benchmarks.Kernel.CheckIxeMeta.withDisplay display rd)).1 }
  let anonReport ← runRecords s.source s.evidence names addresses
  let metaReport ← runRecords srcM evM names addresses
  ensure ((anonReport.rows.find? (·.address == target)).map (·.outcome) == some "accept")
    "compiled target was not actually accepted"
  ensure ((metaReport.rows.find? (·.address == target)).map (·.outcome) == some "accept")
    "compiled meta target was not actually accepted"
  ensure (metaReport.rows.map rowKey == anonReport.rows.map rowKey) "compiled anon/meta verdicts differ"
  for n in [1, 3] do
    let a ← runRecords s.source s.evidence names addresses { workers := some n }
    let m ← runRecords srcM evM names addresses { workers := some n }
    ensure (a.rows.map rowKey == anonReport.rows.map rowKey && m.rows.map rowKey == metaReport.rows.map rowKey)
      s!"compiled pool {n}: actual verdict mismatch"
  return addresses.size

private def check : IO Nat := do
  let a ← outcomes (md := .anon) (fun n => .id (addr n))
  let m ← outcomes (md := .meta) (fun n => .id (addr n))
  let c ← compiled
  IO.println s!"record checks: {a} anon + {m} meta fixture outcomes, {c} compiled records; serial/1/3 workers"
  return a + m + c

/-! ## The host loader's record-store refusals

`Ix.RoleBinding.recordStore` (and `checkedStore`, which role generation and
emission reuse) authenticates and decodes every record of an artifact, named
or not. Its parallel form is proved equal to the serial one
(`recordStore_eq_parallel`, `RecordDecoding.parallel_eq`); no theorem says
what it refuses. These cases pin it: an authenticated record that does not
decode, or decodes only non-canonically (a trailing byte), refuses the whole
store even when no name reaches it (an orphan), with the exact error of the
first such record in address order; a record over a per-record bound is
refused the same way; the batch limits come before authentication, and
authentication before decoding; and a materialized cache beside the bytes
cannot rescue them. -/

namespace StoreRefusals

open _root_.Ix.Kernel.Admission (Limits ByteError)

private def need (label : String) (ok : Bool) : Except String Unit :=
  if ok then .ok () else .error label

private def storeLimits : Limits :=
  { maxRecords := 2048, maxBlobs := 8, maxTotalBytes := 1 <<< 26,
    maxRecordBytes := 1 <<< 20, maxRecordUnivNodes := 1 <<< 16 }

private def fixtureConstant (index : Nat) : Ixon.Constant := {
  sharing := #[], refs := #[], univs := #[.zero, .succ .zero]
  info := .defn {
    kind := .defn, safety := .safe, lvls := index.toUInt64, typ := .sort 1, value := .sort 0 } }

private def rawRecord (bytes : ByteArray) : Address × ByteArray :=
  (Address.admissionHash bytes, bytes)

private def canonicalRecords (count : Nat) : Array (Address × ByteArray) :=
  (Array.range count).map fun i => rawRecord (Ixon.serConstant (fixtureConstant i))

/-- An environment of these records and no names: every record is an orphan. -/
private def orphanEnv (records : Array (Address × ByteArray)) : Ixon.Env :=
  { consts := records.foldl (fun out (a, bytes) => out.insert a
      { buf := bytes, len := bytes.size }) {} }

/-- `recordStore` and `checkedStore` both refuse `env` with exactly `e`, as
`byteError` renders it. -/
private def refuses (label : String) (limits : Limits) (env : Ixon.Env) (e : ByteError) :
    Except String Unit := do
  let expected := _root_.Ix.RoleBinding.byteError e
  match _root_.Ix.RoleBinding.recordStore limits env with
  | .ok _ => throw s!"{label}: the store was built; expected the refusal {expected}"
  | .error actual =>
    need s!"{label}: refused with {actual}; expected {expected}" (actual == expected)
  match _root_.Ix.RoleBinding.checkedStore limits env with
  | .ok _ => throw s!"{label}: checkedStore built the store"
  | .error actual => need s!"{label}: checkedStore refused with {actual}" (actual == expected)

/-- The decoder's message for `bytes` under `limits`; an error if they decode. -/
private def decodeReason (limits : Limits) (bytes : ByteArray) : Except String String :=
  match Ixon.Canonical.deConstant limits.maxRecordBytes limits.maxRecordUnivNodes bytes with
  | .ok _ => .error "a refusal fixture unexpectedly decodes"
  | .error reason => .ok reason

/-- The position of `address` in the store's address order. -/
private def addressPosition (env : Ixon.Env) (address : Address) : Nat :=
  let sorted := (env.consts.toArray.map (·.1)).qsort fun x y => x.cmpBytes y == .lt
  (sorted.findIdx? (· == address)).getD sorted.size

/-- The refusals, over `count` canonical records; the number of cases. -/
def checks (count : Nat) : Except String Nat := do
  let input := canonicalRecords count
  let canonical := orphanEnv input
  let .ok store := _root_.Ix.RoleBinding.recordStore storeLimits canonical
    | throw "the canonical store is refused"
  need "every canonical record is in the store" (store.size == count)
  let malformed := rawRecord (ByteArray.mk #[255])
  let noncanonical := rawRecord ((Ixon.serConstant (fixtureConstant (count + 1))).push 0)
  let mut cases := 0
  -- an authenticated orphan that does not decode, or decodes only with a trailing byte
  for (label, orphan) in [("malformed", malformed), ("noncanonical", noncanonical)] do
    let env := orphanEnv (input.push orphan)
    need "orphan controls have no named roots" env.named.isEmpty
    refuses s!"an authenticated {label} orphan" storeLimits env
      (.decode (addressPosition env orphan.1) orphan.1 (← decodeReason storeLimits orphan.2))
    cases := cases + 1
  -- both: the first in address order is the one reported
  let both := orphanEnv ((input.push malformed).push noncanonical)
  let first := if malformed.1.cmpBytes noncanonical.1 == .lt then malformed else noncanonical
  refuses "two authenticated orphans: the first in address order" storeLimits both
    (.decode (addressPosition both first.1) first.1 (← decodeReason storeLimits first.2))
  -- a record over a per-record bound
  let oversized := rawRecord (ByteArray.mk (Array.replicate 65 0))
  let manyUniverses :=
    rawRecord (Ixon.serConstant { fixtureConstant (count + 2) with univs := Array.replicate 64 .zero })
  for (label, tight, excessive, limit) in [
      ("bytes", { storeLimits with maxRecordBytes := 64 }, oversized, ByteError.limit .recordBytes),
      ("universe nodes", { storeLimits with maxRecordUnivNodes := 8 }, manyUniverses,
        ByteError.limit .recordUnivNodes)] do
    need s!"the canonical records fit the tighter {label} bound"
      (_root_.Ix.RoleBinding.recordStore tight canonical).isOk
    let env := orphanEnv (input.push excessive)
    -- declined by the limit (`ByteError.asLimit`), not rejected as malformed
    refuses s!"an orphan over the per-record {label} bound" tight env limit
    cases := cases + 1
  -- phase precedence: the batch limits, then authentication (records, then blobs), then decoding
  let bad := orphanEnv #[malformed]
  let wrong := Address.admissionHash (ByteArray.mk #[1, 2, 3])
  need "the mismatch fixture has distinct addresses" (wrong != malformed.1)
  let unauthenticated := orphanEnv #[(wrong, malformed.2)]
  let badBlob := { bad with blobs := ({} : Std.HashMap Address ByteArray).insert wrong malformed.2 }
  refuses "the record count precedes authentication and decoding"
    { storeLimits with maxRecords := 0 } unauthenticated (.limit .records)
  refuses "the blob count precedes decoding" { storeLimits with maxBlobs := 0 } badBlob (.limit .blobs)
  refuses "the payload total precedes authentication and decoding"
    { storeLimits with maxTotalBytes := 0 } unauthenticated (.limit .totalBytes)
  refuses "record authentication precedes decoding" storeLimits unauthenticated
    (.mismatch .records 0 wrong)
  refuses "blob authentication precedes record decoding" storeLimits badBlob (.mismatch .blobs 0 wrong)
  refuses "record authentication precedes blob authentication" storeLimits
    { unauthenticated with blobs := badBlob.blobs } (.mismatch .records 0 wrong)
  -- a materialized cache beside malformed bytes is not read
  let reason ← decodeReason storeLimits malformed.2
  refuses "a decode error keeps its address and position" storeLimits bad (.decode 0 malformed.1 reason)
  let cachedRecord : Ixon.LazyConstant :=
    { buf := malformed.2, len := malformed.2.size, cache := some (fixtureConstant 0) }
  refuses "a valid materialized cache cannot rescue malformed bytes" storeLimits
    { bad with consts := bad.consts.insert malformed.1 cachedRecord } (.decode 0 malformed.1 reason)
  return cases + 9

/-- `pure x`, opaque to the compiler, so that `checks` of it is not a closed term
evaluated when the module initializes. -/
@[noinline] def atRunTime (α : Type) (x : α) : IO α := pure x

end StoreRefusals

def suite : List TestSeq := [
  .individualIO "actual anon/meta outcomes, rollback, tiers and worker replay" none (do
    let n ← check
    return (true, n, 0, none)) .done,
  -- 769 records: at 256 tasks the parallel decoder's chunks are four records long
  .individualIO "record store: orphan, noncanonical and oversized records, phase precedence, cache"
    none (do
      return match StoreRefusals.checks (← StoreRefusals.atRunTime Nat 769) with
        | .ok n => (true, n, 0, none)
        | .error message => (false, 0, 0, some message)) .done]

end Tests.Ix.Kernel.RecordCheck
