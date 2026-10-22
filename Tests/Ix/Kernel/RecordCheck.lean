import LSpec
import Ix.KernelCheck.Run
import Ix.KernelCheck.Meta
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

def suite : List TestSeq := [
  .individualIO "actual anon/meta outcomes, rollback, tiers and worker replay" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Kernel.RecordCheck
