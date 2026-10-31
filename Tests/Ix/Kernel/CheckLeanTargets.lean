import LSpec
import Ix.Cli.CheckLeanTargets
import Ix.KernelCheck.Run
import Tests.Ix.Kernel.ReaderRoundtrip

namespace Tests.Ix.Kernel.CheckLeanTargets

open LSpec _root_.Ix.Kernel _root_.Ix.Kernel.Reader
open Benchmarks.Kernel.CheckIxeStep
open _root_.Ix.Cli.CheckLeanTargets

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def errText : Error → String
  | .selector m => m | .input n e => s!"{n}: {e}" | .coverage n m => s!"{n}: {m}"
private def get (r : Except Error α) : IO α := IO.ofExcept (r.mapError errText)
private def selectorError (r : Except Error α) : Bool :=
  match r with | .error (.selector _) => true | _ => false
private def coverageError (r : Except Error α) : Bool :=
  match r with | .error (.coverage _ _) => true | _ => false

/-- Every tier observation is from the same cached declaration handed to the
loop; every logical observation is the loop's actual onRead callback. -/
private def runPlan (s : Setup) (cx : Ctx md) (ev : Evidences md)
    (erase : Key md → Key .anon) (plan : Plan) : IO (RunReport × Produced) := do
  let mut tiers : Std.HashMap Address (Except ReadError (Tier.TierDecl md)) := {}
  let mut produced : Produced := {}
  for a in plan.addresses do
    if let some c := s.store[a]? then
      if let some d := readTierAt cx a c then
        tiers := tiers.insert a d
        if let .ok d := d then produced := noteTier erase produced a d
  let src : LoopSource (State md) md := {
    view := s.view, init := pure {}, commit := fun st _ rd => st.commit rd,
    read := fun st a => match s.store[a]? with
      | some c => readRecord cx st a c
      | none => .error (.malformed "record is missing"),
    tier := some fun _ a => tiers[a]? }
  let seen ← IO.mkRef produced
  let report ← runRecords src ev (fun _ => #[]) plan.addresses { tier := true }
    (onRead := fun a r _ => if let .ok rd := r then seen.modify (noteRead erase · a rd) else pure ())
  return (report, ← seen.get)

private def check : IO Nat := do
  let (_, inp) ← Tests.Ix.Kernel.ReaderRoundtrip.input
  let table ← IO.ofExcept defaultTable
  let pre : Prelude .anon ← IO.ofExcept (preludeFor table)
  let preM : Prelude .meta ← IO.ofExcept (preludeFor table)
  let hints := Hints.ofStore inp.store inp.ixon.anonHints
  let s := setup inp.store (inp.ixon.blobs[·]?) table pre hints.lookup
  let initial := pre.records.map fun (a, c) => owner a c
  let names := inp.ixon.named.toArray.map fun (n, v) => (toString n, v.addr)
  let inventory := namedCandidates inp.store names
  let label (n : String) := toString (Tests.Ix.Kernel.ReaderRoundtrip.defs n)
  let labels := #["Color", "Color.red", "Color.rec", "Point.x", "twice", "spin._unsafe_rec", "unsafeId"].map label
  let plan ← get (select s initial inventory (.only labels))
  ensure (plan.targets.map (·.label) == labels && plan.requested == labels.size) "named coverage changed"
  let some recTarget := plan.targets.find? (·.label == label "Color.rec") | throw (IO.userError "recursor absent")
  ensure (recTarget.producer != recTarget.reference.block) "fixture did not exercise a borrowed recursor row"
  ensure (plan.addresses.size > plan.producers.size) "supporting closure was omitted"
  let (a, ak) ← runPlan s s.cx s.evidence id plan
  let (cxM, evM) := Benchmarks.Kernel.CheckIxeMeta.metaContext s (inp.ixon.blobs[·]?) table preM hints.lookup
  let (m, mk) ← runPlan s cxM evM (fun k => Key.map (md := .meta) (md' := .anon) id k) plan
  ensure (coverageError (results { plan with targets := #[] } a.rows ak)) "empty plan gave vacuous coverage"
  let expected := #["accept", "accept", "accept", "accept", "accept", "typed", "typed"]
  for (report, keys) in [(a, ak), (m, mk)] do
    let out ← get (results plan report.rows keys)
    ensure (out.map (·.target.label) == labels && out.map (·.outcome) == expected)
      s!"wrong actual selected outcomes: {out.map (·.outcome)}"
    ensure (coverageError (results plan report.rows {})) "accepted owner hid missing emitted keys"
    ensure (coverageError (results plan (report.rows.filter (·.address != recTarget.producer)) keys))
      "missing producer row accepted"
    let some row := report.rows.find? (·.address == recTarget.producer) | throw (IO.userError "no recursor producer row")
    ensure (coverageError (results plan (report.rows.push row) keys)) "duplicate producer row accepted"
  -- More than three aliases remain individually covered; a producer cap
  -- retains all selected aliases while preserving its complete dependencies.
  let some twice := plan.targets.find? (·.label == label "twice") | throw (IO.userError "twice absent")
  let some color := plan.targets.find? (·.label == label "Color") | throw (IO.userError "Color absent")
  let aliases := (Array.range 5).map fun i => (s!"alias{i}", twice.address)
  let aliased := namedCandidates inp.store (aliases.push (label "Color", color.address))
  let cap ← get (select s initial aliased (.only (aliases.map (·.1) |>.push (label "Color"))) (some 1))
  ensure (cap.targets.size == 5 && cap.producers.size == 1 && cap.omitted == #[label "Color"] && cap.requested == 6)
    "alias cap used record counts or truncated selected aliases"
  ensure (initial.all cap.addresses.contains && cap.addresses.contains twice.producer) "cap cut prelude/dependencies"
  let (ar, keys) ← runPlan s s.cx s.evidence id cap
  ensure ((← get (results cap ar.rows keys)).all (·.outcome == "accept")) "an alias did not receive acceptance"
  let blocked := ar.rows.map fun r => if r.address == twice.producer then
    { r with outcome := "blocked", reason := "fixture root" } else r
  let rejected := ar.rows.map fun r => if r.address == twice.producer then
    { r with outcome := "reject", reason := "fixture rejection" } else r
  for (rows, outcome, reason) in [(blocked, "blocked", "fixture root"), (rejected, "reject", "fixture rejection")] do
    let out ← get (results cap rows {})
    ensure (out.size == 5 && out.all (fun r => r.outcome == outcome && r.reason == reason)) "failure fan-out changed"
  for request in [.only #[], .only #["missing"], .only #["#bad"]] do
    ensure (selectorError (select s initial inventory request)) "empty/unmatched selector accepted"
  ensure (selectorError (select s initial #[] .all) && selectorError (select s initial inventory .all (some 0)))
    "empty inventory or zero cap accepted"
  let ambiguous := namedCandidates inp.store #[("x.«0»", twice.address), ("x.0", twice.address)]
  ensure (selectorError (select s initial ambiguous (.only #["«x».0"]))) "ambiguous normalization picked a name"
  ensure ((← get (select s initial ambiguous (.only #["x.«0»"]))).targets.size == 1) "exact spelling lost precedence"
  let missing := namedCandidates {} #[("missing payload", twice.address)]
  match select s initial missing .all with
  | .error (.input _ (.malformed "selected record is missing")) => pure ()
  | _ => throw (IO.userError "missing selected payload was not concrete")
  -- Validate malformed projections independently of their accepted owner.
  let bad : Ixon.Constant := { info := .cPrj ⟨0, 999, recTarget.producer⟩, sharing := #[], refs := #[], univs := #[] }
  let badAddr := Address.blake3 (Ixon.serConstant bad)
  let badStore := inp.store.insert badAddr bad
  let badSetup := setup badStore (inp.ixon.blobs[·]?) table pre hints.lookup
  match select badSetup initial (namedCandidates badStore #[("bad constructor", badAddr)]) .all with
  | .error (.input _ (.malformed _)) => pure ()
  | _ => throw (IO.userError "malformed projection inherited owner acceptance")
  -- Omitted constructor projection: inventory derives the exact key, but
  -- does not repair the reader store or turn its missing-record reject into accept.
  let some ctor := plan.targets.find? (·.label == label "Color.red") | throw (IO.userError "constructor absent")
  let stripped := inp.store.erase ctor.address
  let strippedSetup := setup stripped (inp.ixon.blobs[·]?) table pre hints.lookup
  let anonInventory ← get (anonymousCandidates stripped)
  let anonPlan ← get (select strippedSetup initial anonInventory (.only #[toString ctor.address]))
  let (anonReport, anonKeys) ← runPlan strippedSetup strippedSetup.cx strippedSetup.evidence id anonPlan
  let resolved ← get (results anonPlan anonReport.rows anonKeys)
  ensure (anonPlan.targets.size == 1 && anonPlan.targets.all (fun t => t.key == ctor.key && t.address == ctor.address))
    "derived subject changed the selected key"
  ensure (resolved.size == 1 && resolved.all (fun r => r.outcome == "reject" &&
    r.reason == s!"reader: reference {ctor.address} is missing or has invalid ownership"))
    "inventory derivation hid the unchanged reader's missing-record rejection"
  ensure (anonPlan.targets.map (·.fileLabel) == #[toString ctor.address] &&
    _root_.Ix.Cli.ConstsFile.parseLines ((toString ctor.address) ++ "\n# reason\n") == #[toString ctor.address])
    "anonymous fail-out label is swallowed as a comment"
  ensure ((← get (select strippedSetup initial anonInventory (.only #[s!"#{ctor.address}"]))).targets.size == 1)
    "direct #hex selector stopped resolving"
  let conflict ← get (anonymousCandidates (inp.store.insert ctor.address bad))
  match select s initial conflict (.only #[toString ctor.address]) with
  | .error (.input _ (.malformed "derived projection conflicts with the record at its address")) => pure ()
  | _ => throw (IO.userError "derived projection conflict was hidden")
  let blockConflict : Ixon.Constant := { info := .muts #[], sharing := #[], refs := #[], univs := #[] }
  let conflicts ← get (anonymousCandidates (inp.store.insert ctor.address blockConflict))
  let conflicts := conflicts.filter (·.address == ctor.address)
  match select s initial conflicts .all with
  | .error (.input _ (.malformed "derived projection conflicts with the record at its address")) => pure ()
  | _ => throw (IO.userError "container filtering hid a projection conflict")
  -- Replacement, rather than accumulation, prevents an earlier observation
  -- from hiding that the actual latest reading emits no selected key.
  let replaced := noteRead id keys twice.producer ({} : Read .anon)
  ensure (coverageError (results cap ar.rows replaced)) "stale observed keys survived replacement"
  IO.println s!"selected coverage: {labels.size} named at both modes; 5 aliases; caps, recursors, omitted projections and failures"
  return labels.size * 2 + 5

def suite : List TestSeq := [
  .individualIO "selected labels require their actual producer and emitted key" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Kernel.CheckLeanTargets
