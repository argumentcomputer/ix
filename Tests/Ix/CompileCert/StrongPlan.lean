import Ix.CompileCert.StrongCertifier

/-! The S cover's plan (`compile-certify --strong-plan`, `Strong.runStrong`): the cones the
cover would run, in its order, with its batches and budget, none of them run and each counted as
accepted. Read from the outputs `lake run check-cert` writes for the fixture (`BlockDefs` over
the `compiled` artifact): `certify-strong` (the cover, every cone run) and `certify-strong-plan`
(the plan of the same cover). Checks:

1. the plan wrote no S verdict (no `.strong.tsv`, `.strong.cones.tsv`, `.strong.classes.tsv`,
   `.strong.json`, `.strong.live.tsv` under its prefix);
2. every cone of the cover was accepted, and the plan's cones are exactly the cover's cones (root,
   roots, members);
3. the constants the plan puts in a cone are exactly the cover's S-Certified constants, and its
   running total ends at their number.

Negative controls, each beside its valid neighbour (the untampered plan, accepted by the same
comparison): a plan with one cone's member count changed, a plan with one cone dropped, a plan
whose names omit one constant; and the verdict check on the cover's own prefix (which has
verdicts) refuses, beside the plan's prefix. This is a test of the plan against the cover on one
fixture, not a claim about any library.

Units of the cover's batching, each beside its neighbour: `batchGroup` puts an auxiliary
declaration (`f._simp_1`, `f.eq_1`, `f._proof_1._simp_2`) in `f`'s namespace, and a declaration
whose last component is not auxiliary (`f.baz`, `f.equiv_1`) in its own. -/

namespace Tests.Ix.CompileCert.StrongPlan

def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"strong plan check failed: {label}")
  IO.println s!"PASS: {label}"

/-- The rows of a TSV file without its header, split at tabs. -/
def rowsOf (path : System.FilePath) : IO (Array (Array String)) := do
  let text ← IO.FS.readFile path
  let lines := (text.splitOn "\n").filter (· ≠ "")
  return (lines.drop 1).toArray.map fun l => (l.splitOn "\t").toArray

def cell (row : Array String) (i : Nat) : String := row.getD i ""

/-- `(root, roots, members)` of a cone row, sorted (the cones file is sorted by root, the plan is
in the cover's order). -/
def coneKeys (rows : Array (Array String)) (root roots members : Nat) : Array String :=
  (rows.map fun r => s!"{cell r root}|{cell r roots}|{cell r members}").qsort (· < ·)

/-- No S verdict file under a prefix. -/
def noVerdicts (pre : String) : IO Bool := do
  let mut clean := true
  for suffix in [".strong.tsv", ".strong.cones.tsv", ".strong.classes.tsv", ".strong.json",
      ".strong.live.tsv"] do
    if ← System.FilePath.pathExists (pre ++ suffix) then clean := false
  return clean

/-- The plan agrees with the cover: the same cones, and the same constants in a cone. -/
def agrees (cover plan : Array (Array String)) (certified planned : Array String) : Bool :=
  coneKeys cover 0 1 2 == coneKeys plan 1 2 3 &&
    certified.qsort (· < ·) == planned.qsort (· < ·)

/-- The batching units (pure): `batchGroup`. Returns the number of checks. -/
def units : IO Nat := do
  let group := _root_.Ix.CompileCert.Strong.batchGroup
  let checks : List (String × Bool) := [
    ("batchGroup: f._simp_1 is grouped in f's namespace",
      group `Std.DTreeMap.Internal.Impl.mem_alter_self._simp_1 == `Std.DTreeMap.Internal.Impl),
    ("batchGroup: f.eq_1 and f._proof_1._simp_2 are grouped in f's namespace",
      group `Foo.bar.eq_1 == `Foo && group `Foo.bar._proof_1._simp_2 == `Foo),
    ("batchGroup (neighbour): f itself is in its namespace", group `Foo.bar == `Foo),
    ("batchGroup (not auxiliary): f.baz and f.equiv_1 are in f's own namespace",
      group `Foo.bar.baz == `Foo.bar && group `Foo.bar.equiv_1 == `Foo.bar)]
  for (label, ok) in checks do require label ok
  return checks.length

def run (dir : String) : IO Unit := do
  let nUnits ← units
  let coverPre := s!"{dir}/certify-strong"
  let planPre := s!"{dir}/certify-strong-plan"
  -- 1. the plan wrote no verdict; the cover's prefix has verdicts (the check's negative)
  require "the plan wrote no S verdict" (← noVerdicts planPre)
  require "the verdict check refuses the cover's own prefix (it has verdicts)" (!(← noVerdicts coverPre))
  -- 2. the cones
  let cover ← rowsOf s!"{coverPre}.strong.cones.tsv"
  let plan ← rowsOf s!"{planPre}.strong.plan.tsv"
  require s!"every cone of the cover was accepted ({cover.size} cones)"
    (cover.size > 0 && cover.all (cell · 12 == "certified"))
  let verdicts ← rowsOf s!"{coverPre}.strong.tsv"
  let certified := (verdicts.filter (cell · 2 == "S-certified")).map (cell · 0)
  let names ← rowsOf s!"{planPre}.strong.plan.names.tsv"
  let planned := (names.filter (cell · 1 != "-")).map (cell · 0)
  require s!"the plan's {plan.size} cones are the cover's {cover.size} cones (root, roots, members), \
    and its {planned.size} constants in a cone are the cover's {certified.size} S-certified"
    (agrees cover plan certified planned)
  let total := (plan.back?.map (cell · 5)).getD ""
  require s!"the plan's running total ({total}) is the number of S-certified constants"
    (total == toString certified.size)
  -- negatives, beside the untampered plan (accepted just above)
  let some first := plan[0]? | throw (IO.userError "empty plan")
  let bumped := plan.set! 0 (first.set! 3 (toString ((cell first 3).toNat?.getD 0 + 1)))
  require "refused: a plan with one cone's member count changed" (!agrees cover bumped certified planned)
  require "refused: a plan with one cone dropped" (!agrees cover plan.pop certified planned)
  require "refused: a plan whose names omit one constant" (!agrees cover plan certified planned.pop)
  IO.println s!"strong plan: {plan.size} planned cones = the cover's {cover.size} accepted cones; \
    {planned.size} constants in a cone = {certified.size} S-certified; no verdict written; \
    4 refusals beside the valid plan; {nUnits} batching units"

end Tests.Ix.CompileCert.StrongPlan
