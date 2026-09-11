import Compilatrix.Tools.CallReuseCheck

/-! Independent byte accounting over complete source-driven heap/frame
snapshots. This module imports no evaluator, compiler, or space model. -/

namespace Compilatrix.Tools.SpaceCheck

open Lean System Check

private def number (value : Json) (key : String) : IO Nat := do nat (← field value key)

private def word (value : Nat) : IO Unit :=
  need (value < 18446744073709551616) "space Word overflow"

private def valueFits (value : Json) : IO Unit := do
  if value == toJson "erased" then return
  if let .ok location := value.getObjVal? "loc" then word (← number location "l")
  else
    let literal ← field (← field value "lit") "l"
    word (← number (← field literal "nat") "n")

private def nodeFits (box : Json) : IO Unit := do
  word (← number box "rc")
  need (["shared", "unique"].contains (← strField box "world")) "unknown heap ownership"
  let node ← field box "node"
  let fields ← if let .ok ctor := node.getObjVal? "ctorN" then do
      let identity ← field ctor "cid"
      need (isHex 64 (← strField identity "block")) "invalid constructor identity"
      word (← number identity "indIdx")
      word (← number identity "cidx")
      arrField ctor "fields"
    else do
      let pap ← field node "papN"
      need (isHex 64 (← strField pap "f")) "invalid PAP identity"
      word (← number pap "arity")
      arrField pap "args"
  need (fields.size ≤ 2) "space payload exceeds fixed cell"
  for value in fields do valueFits value

private def frame (definitions : List Json) (value : Json) : IO (Nat × List Nat) := do
  need (definitions.contains (← field value "definition")) "space frame refers to unknown code"
  word (← number value "block")
  word (← number value "pc")
  let values ← arrField value "values"
  let credits ← arrField value "credits"
  for value in values do valueFits value
  let mut reservations := []
  for credit in credits do
    if credit == Json.null then continue
    need (isHex 64 (← strField credit "layout")) "invalid credit layout identity"
    let presence ← field credit "presence"
    if presence == toJson "absent" then continue
    let location ← number (← field presence "present") "reservation"
    word location
    reservations := reservations ++ [location]
  need ((← field value "reservations") == toJson reservations) "frame reservation list disagrees with credits"
  let bytes := 64 + 16 * values.size + 48 * credits.size
  need ((← number value "bytes") == bytes) "space frame bytes disagree"
  return (bytes, reservations)

private def within (demand capacity : Json) : IO Bool := do
  return (← number demand "heap") ≤ (← number capacity "heap") &&
    (← number demand "control") ≤ (← number capacity "control")

private def inspectState (definitions : List Json) (state original : Json) : IO (Nat × Nat) := do
  let store ← field state "store"
  let heap ← field store "heap"
  let nodes ← arrField heap "nodes"
  let live := nodes.countP (· != Json.null)
  let frees ← number heap "frees"
  for node in nodes do if node != Json.null then nodeFits node
  for key in ["allocs", "frees", "reuses", "rcops"] do word (← number heap key)
  for key in ["resetAttempts", "hotResets", "coldResets", "reusedPayloadUnits", "peakLiveNodes"] do
    word (← number store key)
  let active ← field state "active"
  let (activeBytes, activeReservations) ← if active == Json.null then do
      valueFits (← field state "returned")
      pure (16, [])
    else frame definitions active
  let mut control := activeBytes
  let mut owners := [activeReservations]
  let saved ← arrField state "saved"
  need (active != Json.null || saved.isEmpty) "halted state retains callers"
  for continuation in saved do
    let (bytes, locations) ← frame definitions (← field continuation "frame")
    let arguments ← arrField continuation "arguments"
    let kind ← strField continuation "kind"
    need (["resume", "applyMore"].contains kind && (kind != "resume" || arguments.isEmpty))
      "invalid saved continuation"
    for value in arguments do valueFits value
    let cost := 16 + bytes + 16 * arguments.size
    need ((← number continuation "bytes") == cost) "saved continuation bytes disagree"
    control := control + cost
    owners := owners ++ [locations]
  let reservations := owners.flatten
  need (reservations.eraseDups.length == reservations.length) "space duplicates reservation ownership"
  for location in reservations do
    need (location < nodes.size && nodes[location]! == Json.null) "space reservation aliases a live or absent slot"
  need ((← field state "reservations") == toJson reservations) "space reservation inventory disagreement"
  need ((← field original "owners") == toJson owners) "space caller owners differ from original execution"
  need ((← number state "slots") == nodes.size && (← number heap "allocs") == nodes.size)
    "space committed slot history disagrees with fresh allocations"
  need ((← number state "live") == live && live + reservations.length + frees == nodes.size)
    "space live/reserved/freed partition disagreement"
  need (live ≤ (← number store "peakLiveNodes")) "space live nodes exceed peak"
  for (key, expected) in [("live_bytes", 112 * live), ("reserved_bytes", 112 * reservations.length),
      ("occupied_bytes", 112 * (live + reservations.length)), ("retained_free_bytes", 112 * frees)] do
    need ((← number state key) == expected) s!"space {key} disagreement"
  let committed := 96 + 112 * nodes.size
  word committed
  word control
  let demand ← field state "demand"
  need ((← number demand "heap") == committed) "space committed bytes disagreement"
  need ((← number demand "control") == control) "space control bytes disagreement"
  let counters ← field original "counters"
  for key in ["allocs", "frees", "reuses", "rcops"] do
    need ((← field heap key) == (← field counters key)) "space heap counters differ from original execution"
  for key in ["resetAttempts", "hotResets", "coldResets", "reusedPayloadUnits", "peakLiveNodes"] do
    need ((← field store key) == (← field counters key)) "space counters differ from original execution"
  return (committed, control)

private def inspectFailure (prefixes : Array Json) (failure : Json) (start : Nat := 0) : IO Unit := do
  let step ← number failure "step"
  need (start + step < prefixes.size) "capacity failure lies outside execution"
  let capacity ← field failure "capacity"
  for index in [start:start + step] do
    need (← within (← field prefixes[index]! "demand") capacity) "capacity failure skipped an earlier disallowed state"
  let needed ← field prefixes[start + step]! "demand"
  need ((← field failure "needed") == needed) "capacity failure demand disagrees with its state"
  need (!(← within needed capacity)) "capacity failure did not exhaust storage"

private def constructor (nodes : Array Json) (value : Json) : IO (Json × Array Json) := do
  let location ← number (← field value "loc") "l"
  need (location < nodes.size && nodes[location]! != Json.null) "space result refers to a dead or absent node"
  let ctor ← field (← field nodes[location]! "node") "ctorN"
  return (← field ctor "cid", ← arrField ctor "fields")

private def listResult (nodes : Array Json) (nilId consId : Json) : Nat → Json → IO (List Nat)
  | 0, _ => throw (IO.userError "space result is cyclic or exceeds its heap")
  | fuel + 1, value => do
      let (identity, fields) ← constructor nodes value
      if identity == nilId then
        need fields.isEmpty "space result nil has fields"
        return []
      need (identity == consId && fields.size == 2) "space result is not the source list type"
      let head ← number (← field (← field (← field fields[0]! "lit") "l") "nat") "n"
      return head :: (← listResult nodes nilId consId fuel fields[1]!)

private def inspectResult (row artifact result : Json) : IO Unit := do
  let nodes ← arrField (← field (← field result "store") "heap") "nodes"
  let constructors ← arrField (← field artifact "sidecars") "constructors"
  need (constructors.size ≥ 2) "space source has no list constructor identities"
  let nilId ← field constructors[0]! "identity"
  let consId ← field constructors[1]! "identity"
  let input ← (← arrField row "input").toList.mapM nat
  let replacement ← number row "replacement"
  let value ← field result "value"
  if ← checked ((← field row "aliased").getBool?) then
    let (identity, fields) ← constructor nodes value
    need (constructors.size == 3 && identity == (← field constructors[2]! "identity") && fields.size == 2)
      "space result is not the source pair type"
    need ((← listResult nodes nilId consId (nodes.size + 1) fields[0]!) == input.map (fun _ => replacement) &&
      (← listResult nodes nilId consId (nodes.size + 1) fields[1]!) == input.drop (← number row "unique_prefix"))
      "finite result disagrees with source map and retained alias"
  else
    need ((← listResult nodes nilId consId (nodes.size + 1) value) == input.map (fun _ => replacement))
      "finite result disagrees with source map"

def inspectSnapshot (row snapshot : Json) : IO Unit := do
  need ((← strField snapshot "format") == "compilatrix/source-space-case/1") "unknown source space format"
  need ((← strField snapshot "policy") == "ixir2-fixed-slot-space/1") "unknown space policy"
  need ((← field snapshot "layout") == Json.mkObj [("fields", toJson (2 : Nat))]) "unknown space layout"
  need ((← field snapshot "summary") == row) "space report/snapshot disagreement"
  let artifact ← field snapshot "source_artifact"
  let sourceRow ← field artifact "summary"
  CallReuseCheck.inspectSnapshot sourceRow artifact
  for key in ["name", "source_root", "input", "replacement", "aliased", "unique_prefix", "prefixes"] do
    need ((← field row key) == (← field sourceRow key)) s!"space source {key} disagreement"
  let selected ← field (← field artifact "ixir2_diagnostic") "selected"
  let mut definitions := [← field selected "main"]
  for entry in ← arrField selected "declarations" do
    let pair ← array entry
    need (pair.size == 2) "invalid selected declaration"
    definitions := definitions ++ [← field (← field pair[1]! "fn") "definition"]
  let prefixes ← arrField snapshot "prefixes"
  let original ← arrField artifact "prefixes"
  need (!prefixes.isEmpty && prefixes.size == original.size && prefixes.size == (← number row "prefixes"))
    "space prefix inventory disagreement"
  let mut maximumHeap := 0
  let mut maximumControl := 0
  let mut previousSlots := 0
  for index in [:prefixes.size] do
    let state := prefixes[index]!
    need ((← number state "step") == index) "space prefix sequence has a gap"
    let (heap, control) ← inspectState definitions state original[index]!
    let slots ← number state "slots"
    need (previousSlots ≤ slots && slots ≤ previousSlots + 1) "space backing slots shrank or skipped allocation"
    previousSlots := slots
    maximumHeap := max maximumHeap heap
    maximumControl := max maximumControl control
  let demand ← field row "demand"
  need ((← number demand "heap") == maximumHeap && (← number demand "control") == maximumControl)
    "space maximum demand disagreement"
  let result ← field snapshot "result"
  let last := prefixes.back!
  need ((← field result "store") == (← field last "store") &&
    (← field result "value") == (← field last "returned") &&
    (← field result "heap_remaining") == (← field last "heap_remaining") &&
    (← number result "control_remaining") + prefixes.size - 1 == (← number snapshot "fuel"))
    "space terminal result differs from prefix execution"
  let physical ← field (← field artifact "observations") "selected_physical"
  need ((← field result "store") == (← field physical "store")) "finite heap differs from source physical execution"
  for key in ["control_remaining", "heap_remaining"] do
    need ((← field result key) == (← field physical key)) "finite fuel differs from source physical execution"
  inspectResult row artifact result
  need ((← number row "fresh_slots") == previousSlots && maximumHeap == 96 + 112 * previousSlots &&
    (← field row "peak_live_nodes") == (← field (← field result "store") "peakLiveNodes")) "space terminal size disagreement"
  let reclaimed ← field snapshot "reclaimed"
  need (reclaimed == (← field physical "reclaimed")) "space reclamation differs from source execution"
  let releasedHeap ← field reclaimed "heap"
  need ((← arrField releasedHeap "nodes").size == previousSlots &&
    (← arrField releasedHeap "nodes").all (· == Json.null) &&
    (← number releasedHeap "frees") == previousSlots) "space reclamation lost backing slots or leaked ownership"
  need ((← number snapshot "reclaimed_committed_bytes") == maximumHeap) "space release incorrectly returned backing capacity"
  let failures ← field snapshot "failures"
  for (key, heap, control) in [("heap_short", maximumHeap - 1, maximumControl),
      ("control_short", maximumHeap, maximumControl - 1),
      ("no_descriptor", 95, maximumControl), ("no_control", maximumHeap, 0)] do
    let failure ← field failures key
    let capacity ← field failure "capacity"
    need ((← number capacity "heap") == heap && (← number capacity "control") == control) "capacity boundary budget disagreement"
    inspectFailure prefixes failure
  let witness ← field snapshot "reserved_allocation"
  need ((witness != Json.null) == (← checked ((← field row "reserved_allocation").getBool?)))
    "reservation witness/report disagreement"
  if witness != Json.null then
    let before ← number witness "before_step"
    let after ← number witness "after_step"
    need (after == before + 1 && after < prefixes.size) "invalid callee allocation witness"
    let left := prefixes[before]!
    let right := prefixes[after]!
    need ((← number right "slots") == (← number left "slots") + 1 &&
      (← field right "reservations") == (← field left "reservations")) "callee did not allocate while preserving reservations"
    let saved ← arrField left "saved"
    let locations := ((← saved.mapM (fun c => do arrField (← field c "frame") "reservations")).toList.map Array.toList).flatten
    need (!locations.isEmpty && (← field witness "saved_reservations") == toJson locations)
      "callee witness has no suspended reservation"
    let failed ← field witness "failure"
    need ((← number failed "step") == 1) "callee did not fail on its allocating step"
    inspectFailure prefixes failed before
    let available ← number (← field failed "capacity") "heap"
    need ((← number (← field right "demand") "heap") - (← number right "reserved_bytes") ≤ available)
      "omitting reserved bytes would not hide the witnessed exhaustion"

def inspectArena (report : Json) : IO Unit := do
  let rows ← arrField report "native_arena"
  need (rows.size == 65) "native byte-capacity matrix is incomplete"
  for index in [:rows.size] do
    let row := rows[index]!
    need ((← number row "length") == index && (← number row "required_bytes") == 80 + 32 * (index + 2) &&
      (← number row "short_cells") == index + 1 && (← number row "exact_cells") == index + 2)
      "native byte-capacity arithmetic disagreement"

def regressions (row snapshot report : Json) : IO Unit := do
  let rejects := CallReuseCheck.rejects
  let replace := CallReuseCheck.replaceAt
  let states ← arrField snapshot "prefixes"
  let witness ← field snapshot "reserved_allocation"
  let before ← number witness "before_step"
  let after ← number witness "after_step"
  for (key, message) in [("live_bytes", "space live_bytes"), ("reserved_bytes", "space reserved_bytes"),
      ("occupied_bytes", "space occupied_bytes")] do
    let state ← replace states[after]! [key] (toJson (1 : Nat))
    let changed ← replace snapshot ["prefixes"] (Json.arr (states.set! after state))
    rejects key message (inspectSnapshot row changed)
  let some freed := states.findIdx? (fun state =>
      ((state.getObjVal? "retained_free_bytes").bind Json.getNat?).toOption.any (· > 0))
    | throw (IO.userError "no retained freed-slot regression state")
  let state := states[freed]!
  let omitted := (← number (← field state "demand") "heap") - (← number state "retained_free_bytes")
  let changedState ← replace state ["demand", "heap"] (toJson omitted)
  let changed ← replace snapshot ["prefixes"] (Json.arr (states.set! freed changedState))
  rejects "freed backing capacity" "space committed bytes" (inspectSnapshot row changed)
  let changedState ← replace states[before]! ["active", "bytes"] (toJson (64 : Nat))
  let changed ← replace snapshot ["prefixes"] (Json.arr (states.set! before changedState))
  rejects "active values" "space frame bytes" (inspectSnapshot row changed)
  let changedState ← replace states[before]! ["saved"] (Json.arr #[])
  let changed ← replace snapshot ["prefixes"] (Json.arr (states.set! before changedState))
  rejects "missing saved caller" "space reservation inventory" (inspectSnapshot row changed)
  let some consumed := states.findIdx? (fun state =>
    (((state.getObjVal? "active").bind (·.getObjVal? "credits")).bind Json.getArr?).toOption.any
      (fun credits => !credits.isEmpty && credits.any (· == Json.null)))
    | throw (IO.userError "no consumed-credit storage regression state")
  let active ← field states[consumed]! "active"
  let forgotten := 64 + 16 * (← arrField active "values").size
  let changedState ← replace states[consumed]! ["active", "bytes"] (toJson forgotten)
  let changed ← replace snapshot ["prefixes"] (Json.arr (states.set! consumed changedState))
  rejects "consumed credit entries" "space frame bytes" (inspectSnapshot row changed)
  let changed ← replace snapshot ["failures", "heap_short", "step"] (toJson (states.size - 1))
  rejects "late capacity failure" "skipped an earlier disallowed state" (inspectSnapshot row changed)
  let changed ← replace snapshot ["failures", "control_short", "needed", "control"] (toJson (0 : Nat))
  rejects "false control demand" "capacity failure demand" (inspectSnapshot row changed)
  let changed ← replace snapshot ["reclaimed_committed_bytes"] (toJson (96 : Nat))
  rejects "reclaimed backing capacity" "release incorrectly returned backing capacity" (inspectSnapshot row changed)
  let changed ← replace snapshot ["policy"] (toJson "peak-live/0")
  rejects "wrong storage policy" "unknown space policy" (inspectSnapshot row changed)
  let invalidValue := Json.mkObj [("loc", Json.mkObj [("l", toJson (999999 : Nat))])]
  let last ← replace states.back! ["returned"] invalidValue
  let changed ← replace snapshot ["prefixes"] (Json.arr (states.set! (states.size - 1) last))
  let changed ← replace changed ["result", "value"] invalidValue
  rejects "invalid returned location" "space result refers to a dead or absent node" (inspectSnapshot row changed)
  let rows ← arrField report "native_arena"
  let changedRow ← replace rows[0]! ["required_bytes"] (toJson (64 : Nat))
  let changed ← replace report ["native_arena"] (Json.arr (rows.set! 0 changedRow))
  rejects "omitted native descriptor" "native byte-capacity arithmetic" (inspectArena changed)

end Compilatrix.Tools.SpaceCheck
