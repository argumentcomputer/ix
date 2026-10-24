/-
  pass3-plan-cache: Pass 3's clique tables, the plan table
  (`CompileEnv.p3CliquePlans`, `Ix.Compile.Pass.Clique.cliquePlanFor`) and the
  rows table (`CompileEnv.p3CliqueRows`, `Ix.Compile.Pass.cliqueRows`), are
  memos that change nothing but time (CQ5.2 (b); ported from the donor's
  `Tests/Ix/Compile/PlanCache.lean`).

  Over the twins closure (every family, the clique families and the clique
  ownership sources included, with the rows' prerequisites: `familyClosure`):

  1. the reference: the pure-Lean pipeline at 32 workers, without the check;
  2. the check mode (`DriverOptions.checkPlans`, `IX_PASS3_CHECK_PLANS=1` in
     the CLI) at 1, 4 and 32 workers: every plan and row set a table supplies
     is recomputed and compared; each run must succeed, write the reference's
     bytes and fail exactly the reference's blocks with the same messages;
  3. coverage, asserted: the reference's plan table holds a transported plan,
     and its rows table that plan's rows;
  4. negative controls with their valid neighbours, on the reference's final
     state:
     - the table's own plan of a transported clique passes the check (a table
       hit, `cliquePlanFor`); the table with that entry replaced by a
       `notEncoded` outcome, and by the plan under another permutation, fails
       it with `planCheckPrefix`; without the check the replaced entry is
       returned as is (the check, not the lookup, is what detects it);
     - the table's own rows pass the check (`cliqueRows`); the rows table with
       that entry emptied fails it with `planCheckPrefix`; without the check
       the emission takes the emptied entry (fewer constants).

  Not here: the Rust compiler's check mode (`IX_PASS3_CHECK_PLANS=1`, read by
  `compile_env`), which the compiler gate runs on Init+Std; and the donor's
  view and image-expansion table checks (those tables have no check mode in
  this compiler).

  Run with: `lake test -- --ignored pass3-plan-cache`.
-/
import Tests.Ix.Compile.Twins

open Lean

namespace Tests.Ix.Compile.PlanCache

open Ix.Compile.Pass.Clique (CliqueOutcome planCheckPrefix cliquePlanFor)

def say (s : String) : IO Unit := do
  IO.println s!"[plan-cache] {s}"
  (← IO.getStdout).flush

/-- A compile's block failures, by name. -/
def failuresOf (cenv : Ix.CompileM.CompileEnv) : List (String × String) :=
  ((cenv.ungrounded.toList.map fun (n, e) => (n.pretty, e)).toArray.qsort
    (fun a b => a.1 < b.1)).toList

def checkFailed (msg : String) : Bool := (msg.splitOn planCheckPrefix).length > 1

def run : IO UInt32 := do
  let env ← Tests.Ix.Compile.Twins.fixturesEnv
  let (_, closure) := Tests.Ix.Compile.Twins.familyClosure env Tests.Ix.Compile.Twins.allFamilies
  say s!"{closure.length} constants (the twins closure)"
  let mut problems : Array String := #[]
  -- 1. the reference
  let ref ← match ← Ix.CompileM.compileLeanConsts closure (numWorkers := 32) with
    | .ok o => pure o
    | .error e => say s!"FAIL the reference compile: {e}"; return 1
  let refFails := failuresOf ref.cenv
  say s!"reference: {ref.bytes.size} B, {refFails.length} block failures"
  -- 2. the check mode
  for w in [1, 4, 32] do
    match ← Ix.CompileM.compileLeanConsts closure (numWorkers := w) (opts := { checkPlans := true }) with
    | .error e => problems := problems.push s!"the check run at {w} workers fails: {e}"
    | .ok o =>
      if o.bytes != ref.bytes then problems := problems.push s!"the check run at {w} workers: other bytes"
      if failuresOf o.cenv != refFails then
        problems := problems.push s!"the check run at {w} workers: other block failures"
      say s!"check run at {w} workers: {o.bytes.size} B, {o.cenv.p3CliquePlans.size} plans and \
        {o.cenv.p3CliqueRows.size} row sets, each taken from a table recomputed"
  -- 3. coverage
  let cenv := ref.cenv
  let transported := (cenv.p3CliquePlans.toArray.qsort fun a b => a.1.pretty < b.1.pretty).filterMap
    fun (k, o) => match o with
      | .transported p => some (k, p)
      | _ => none
  say s!"plan table: {cenv.p3CliquePlans.size} plans ({transported.size} transported); rows table: \
    {cenv.p3CliqueRows.size} row sets"
  let some (key, plan) := transported[0]? | say "FAIL coverage: no transported plan"; return 1
  unless cenv.p3CliqueRows.contains key do
    problems := problems.push s!"coverage: no row set for {key.pretty}"
  let some (cl, carried) := cenv.p3Cliques.get? key | say s!"FAIL {key.pretty} is not in the clique table"; return 1
  -- 4. the plan table's check
  let h : Ix.Compile.Pass.Clique.HookEnv := { Ix.Compile.Pass.cliqueHookEnv cenv with checkPlans := true }
  match cliquePlanFor h cl carried with
  | .ok (o, hit, _) =>
    unless hit && o.same (.transported plan) do
      problems := problems.push s!"the table's own plan of {key.pretty} is not returned as a table hit"
  | .error e => problems := problems.push s!"the table's own plan of {key.pretty} fails the check: {e}"
  let planted : List (String × CliqueOutcome) :=
    [("a notEncoded outcome", .notEncoded "planted"),
     ("the plan under another permutation", .transported { plan with sigma := plan.sigma.reverse })]
  for (what, o') in planted do
    let hp := { h with plans := h.plans.insert key o' }
    match cliquePlanFor hp cl carried with
    | .error e =>
      unless checkFailed e do problems := problems.push s!"{what}: the check's error lacks its prefix: {e}"
    | .ok _ => problems := problems.push s!"{what} in the plan table passes the check"
    match cliquePlanFor { hp with checkPlans := false } cl carried with
    | .ok (o, true, _) =>
      unless o.same o' do problems := problems.push s!"{what}: without the check the table's entry is not returned"
    | _ => problems := problems.push s!"{what}: without the check the lookup is not a table hit"
  say s!"plan table: the table's own plan passes the check, {planted.length} replaced entries fail it"
  -- 4. the rows table's check
  let mut full := 0
  match Ix.Compile.Pass.cliqueRows { cenv with p3CheckPlans := true } with
  | .ok st => full := st.auxNamed.size
  | .error e => problems := problems.push s!"the table's own rows fail the check: {e}"
  let emptied := { cenv with p3CliqueRows := cenv.p3CliqueRows.insert key (#[], #[]) }
  match Ix.Compile.Pass.cliqueRows { emptied with p3CheckPlans := true } with
  | .error e =>
    unless checkFailed e do problems := problems.push s!"an emptied row set: the check's error lacks its prefix: {e}"
  | .ok _ => problems := problems.push "an emptied row set passes the check"
  match Ix.Compile.Pass.cliqueRows { emptied with p3CheckPlans := false } with
  | .ok st =>
    unless st.auxNamed.size < full do
      problems := problems.push "without the check the emission does not take the emptied row set"
  | .error e => problems := problems.push s!"without the check an emptied row set fails: {e}"
  say s!"rows table: the table's own rows pass the check ({full} constants), an emptied entry fails it"
  for p in problems do say s!"FAIL {p}"
  say s!"{problems.size} problem(s)"
  return if problems.isEmpty then 0 else 1

end Tests.Ix.Compile.PlanCache
