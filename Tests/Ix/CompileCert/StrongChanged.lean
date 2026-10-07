import Ix.CompileCert.StrongCertifier

/-! S over the changed constants of W+ (M5): `compile-certify --strong` on the `ChangedDefs`
fixture (compiled under Pass 3 by the `changed` mode into `changed.ixe`), run in-process
(`Certifier.runW`, then `Strong.runStrong`), read back from the files it writes.

S decides only constants W certifies by the `direct`/`raw` routes. Checks:

1. the fixture has constants W certifies by a W+ route (a theorem or equation row, a type
   row, a changed block), and each is S-unsupported with the class `Strong.wPlusClass`;
2. every W-certified constant that is S-blocked is blocked by one of them, with that class
   named; there is at least one;
3. every other W-certified (direct or raw) constant is S-certified, there is at least one, and
   nothing is S-rejected.

Negative, beside the valid run above (its neighbour): the same W state with every W+ constant's
route forged to `direct`. The forged labels put those constants into cones, whose own W
associations (`checkIndexed`) and admissions decide them: none becomes S-certified, and the cones
that reach them are refused. So S's verdict goes through the cones' checks, not through the route
label. A fixture result, not a library claim. -/

namespace Tests.Ix.CompileCert.StrongChanged

open _root_.Ix.CompileCert.Certifier _root_.Ix.CompileCert.Strong

def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"strong changed check failed: {label}")
  IO.println s!"PASS: {label}"

/-- The rows of a TSV file without its header, split at tabs. -/
def rowsOf (path : System.FilePath) : IO (Array (Array String)) := do
  let text ← IO.FS.readFile path
  let lines := (text.splitOn "\n").filter (· ≠ "")
  return (lines.drop 1).toArray.map fun l => (l.splitOn "\t").toArray

def cell (row : Array String) (i : Nat) : String := row.getD i ""

/-- name ↦ (S verdict, cause) from `<prefix>.strong.tsv`. -/
def sVerdicts (pre : String) : IO (Std.HashMap String (String × String)) := do
  let rows ← rowsOf s!"{pre}.strong.tsv"
  return rows.foldl (fun m r => m.insert (cell r 0) (cell r 2, cell r 3)) {}

def checks (ixe dir : String) : IO Unit := do
  let base : Config :=
    { lean := .modules #[`Tests.Ix.CompileCert.ChangedDefs], ixe, out := s!"{dir}/strong-changed",
      strong := true, workers := 4, strongTasks := 4 }
  let (_, some w) ← runW base | throw (IO.userError "W produced no state")
  let _ ← runStrong base w
  -- W's verdicts and routes (the cause column of a certified constant is its route)
  let wRows ← rowsOf s!"{base.out}.tsv"
  let certified := wRows.filter (cell · 2 == "certified")
  -- a certified constant with no route recorded is decided by S (as `runStrong` does)
  let inS (route : String) : Bool := route == "" || sRoute route
  let wPlus := (certified.filter (fun r => !inS (cell r 3))).map (cell · 0)
  let direct := (certified.filter (fun r => inS (cell r 3))).map (cell · 0)
  let isWPlus : Std.HashSet String := wPlus.foldl (·.insert ·) {}
  let s ← sVerdicts base.out
  let verdict (n : String) : String × String := s.getD n ("none", "")
  -- 1. the W+ constants
  require s!"the fixture has {wPlus.size} constants certified by a W+ route" (wPlus.size > 0)
  require s!"each of the {wPlus.size} is S-unsupported: {wPlusClass}"
    (wPlus.all fun n => verdict n == ("S-unsupported", wPlusClass))
  -- 2. the W-certified constants S-blocked: by a W+ constant, with the class named
  let blocked := direct.filter fun n => (verdict n).1 == "S-blocked"
  let blockedByWPlus := blocked.filter fun n =>
    let cause := (verdict n).2
    match cause.splitOn s!": {wPlusClass}" with
    | [dep, ""] => isWPlus.contains dep
    | _ => false
  require s!"{blocked.size} W-certified constants S-blocked, each by a W+ constant with the class named"
    (blocked.size > 0 && blockedByWPlus.size == blocked.size)
  -- 3. everything else S-certified; nothing S-rejected
  let sCertified := direct.filter fun n => (verdict n).1 == "S-certified"
  require s!"the other {direct.size - blocked.size} W-certified constants (direct or raw) are S-certified \
    ({sCertified.size})" (sCertified.size > 0 && sCertified.size + blocked.size == direct.size)
  let rejected := s.toList.filter fun (_, v) => v.1 == "S-rejected"
  require "nothing is S-rejected" rejected.isEmpty
  -- negative, beside the valid run above: every W+ constant's route forged to `direct`, so none
  -- is kept out of S by its label and every cone that reaches one runs; the cones' own W
  -- associations (and admissions) refuse them, and no W+ constant becomes S-certified
  let forgedRoutes := w.names.foldl (fun m n =>
    if isWPlus.contains (toString n) then m.insert n "direct" else m) w.routes
  let forgedCfg := { base with out := s!"{dir}/strong-changed-forged" }
  let _ ← runStrong forgedCfg { w with routes := forgedRoutes }
  let s' ← sVerdicts forgedCfg.out
  let forgedCertified := wPlus.filter fun n => (s'.getD n ("none", "")).1 == "S-certified"
  let refusedCones := s'.toList.filter fun (_, (word, cause)) => word == "S-rejected" &&
    ((cause.splitOn "cone W association refused").length > 1 || (cause.splitOn "cone admission refused").length > 1)
  require s!"forged: all {wPlus.size} W+ routes given as direct: none of them S-certified \
    ({forgedCertified.size}); {refusedCones.length} cones that reach them refused by their own W association \
    or admission; their honest neighbour: S-unsupported, {wPlusClass}"
    (forgedCertified.isEmpty && refusedCones.length > 0 &&
      wPlus.all fun n => verdict n == ("S-unsupported", wPlusClass))
  IO.println s!"strong changed: {wPlus.size} W+ constants S-unsupported ({wPlusClass}), \
    {blocked.size} users S-blocked by them, {sCertified.size} S-certified, 0 S-rejected; \
    with every W+ route forged to direct none of them S-certified ({refusedCones.length} cones refused), \
    beside the honest run"

/-- The W+ pre-screen may leave tasks running past its report (as `compile-certify` does, the
process exits at once after its report). -/
def run (ixe dir : String) : IO Unit := do
  try
    checks ixe dir
    (← IO.getStdout).flush
    IO.Process.exit 0
  catch e =>
    IO.eprintln s!"{e}"
    (← IO.getStdout).flush
    IO.Process.exit 1

end Tests.Ix.CompileCert.StrongChanged
