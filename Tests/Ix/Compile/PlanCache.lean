/-
  pass3-plan-cache: the clique plan table of the Pass 3 clique hook
  (`CompileEnv.p3CliquePlans`, `Ix.Compile.Pass.cliquePlanFor`; design
  document §5.4) is a memo that changes nothing but time.

  Over the twins closure (every family, the clique ownership families
  included) and the aux fixture corpus (`validateAuxClosure`:
  `Tests.Ix.Compile.Mutual`'s `TypeBrecOnEqDef*` cliques with their carried
  equation lemmas, and the rest), with the switch on:

  1. the reference: the sequential driver without the check;
  2. the check mode (`checkPlans`, `IX_PASS3_CHECK_PLANS=1` in the CLI):
     the sequential driver and the wave driver at 1, 4 and 32 workers, every
     plan the table supplies recomputed and compared (`CliqueOutcome.same`);
     each run must succeed, write the reference's bytes and fail exactly the
     reference's blocks with the same messages;
  3. coverage, asserted: the table holds a transported plan and the
     sequential check run took a plan from the table (so recomputed one);
  4. a negative control with its valid neighbour: on the final compile
     state, the table's own plan of a transported clique passes the check;
     the same table with that entry replaced (by a `notEncoded` outcome, and
     by the plan with another permutation) fails it with
     `planCheckPrefix`; without the check the replaced entry is returned
     as is (the check, not the lookup, is what detects it).

  Run with: `lake test -- --ignored pass3-plan-cache`.
-/
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.ValidateAux
import Tests.Ix.Compile.Pass3
open Lean

namespace Tests.Ix.Compile.PlanCache

def say (s : String) : IO Unit := do
  IO.println s!"[plan-cache] {s} (t={(← IO.monoMsNow) / 1000}s)"
  (← IO.getStdout).flush

def failuresOf (cenv : Ix.CompileM.CompileEnv) : List (String × String) :=
  (cenv.ungrounded.toList.map fun (n, e) => (n.pretty, e)).toArray.qsort (fun a b => a.1 < b.1) |>.toList

def run : IO UInt32 := do
  let env ← get_env!
  let families := Tests.Ix.Compile.Twins.allFamilies ++ Tests.Ix.Compile.Twins.ownershipFamilies
  let (_, twins) := Tests.Ix.Compile.Twins.familyClosure env families
  let fixtures := validateAuxClosure env
  let names : Std.HashSet Name := twins.foldl (init := {}) fun s (n, _) => s.insert n
  let closure := twins ++ fixtures.filter (!names.contains ·.1)
  say s!"{closure.length} constants (twins {twins.length}, fixture corpus {fixtures.length})"
  let phases ← Ix.CompileM.rsCompilePhasesOf closure
  let mut nameByHash : Std.HashMap Address Ix.Name := {}
  for (ln, _) in closure do
    let (ixn, _) := StateT.run (Ix.CanonM.canonName ln) {}
    nameByHash := nameByHash.insert ixn.getHash ixn
  let mut problems : Array String := #[]
  -- 1. the reference
  let (refBytes, refFails) ← match Ix.CompileM.compileEnvAux phases.rawEnv phases.condensed
      (nameByHash := nameByHash) (pass3 := true) with
    | .error e => throw (IO.userError s!"[plan-cache] reference compile: {e}")
    | .ok (ixon, _, cenv) => pure (← IO.ofExcept (Ixon.serEnv ixon), failuresOf cenv)
  say s!"reference (sequential, no check): {refBytes.size} B, {refFails.length} block failures"
  -- 2. the check mode, every driver
  let mut seqState : Option Ix.CompileM.CompileEnv := none
  let check (label : String) (r : Except String (Ixon.Env × Nat × Ix.CompileM.CompileEnv)) :
      IO (Option Ix.CompileM.CompileEnv × Array String) := do
    match r with
    | .error e => return (none, #[s!"{label}: the compile failed: {e}"])
    | .ok (ixon, _, cenv) =>
      let bytes ← IO.ofExcept (Ixon.serEnv ixon)
      let transported := cenv.p3CliquePlans.fold (init := 0) fun n _ o =>
        match o with | .transported _ => n + 1 | _ => n
      say s!"{label} (check on): {bytes.size} B, {cenv.ungrounded.size} block failures, \
        {cenv.p3CliquePlans.size} plans in the table ({transported} transported), \
        {cenv.p3PlanReuses} taken from the table and recomputed equal"
      let mut ps := #[]
      unless cenv.p3CheckPlans do ps := ps.push s!"{label}: the check was not on"
      unless bytes == refBytes do ps := ps.push s!"{label}: bytes differ from the reference \
        ({Address.blake3 bytes} vs {Address.blake3 refBytes})"
      unless failuresOf cenv == refFails do ps := ps.push s!"{label}: block failures differ from the reference"
      return (some cenv, ps)
  let (s, ps) ← check "sequential" (Ix.CompileM.compileEnvAux phases.rawEnv phases.condensed
    (nameByHash := nameByHash) (pass3 := true) (checkPlans := true))
  seqState := s
  problems := problems ++ ps
  for k in [1, 4, 32] do
    let (_, ps) ← check s!"wave --jobs {k}" (← Ix.CompileM.compileEnvParallelAux phases.rawEnv
      phases.condensed (numWorkers := k) (nameByHash := nameByHash) (pass3? := some true)
      (checkPlans? := some true))
    problems := problems ++ ps
  -- 3. coverage
  let some cenv := seqState | do
      say s!"FAIL: {problems.size} problem(s)"
      for p in problems do say s!"  {p}"
      return 1
  let transported := (cenv.p3CliquePlans.toArray.filterMap fun (k, o) => match o with
    | .transported p => some (k, p) | _ => none).qsort fun a b => a.1.pretty < b.1.pretty
  if transported.isEmpty then problems := problems.push "coverage: no transported plan in the table"
  if cenv.p3PlanReuses == 0 then
    problems := problems.push "coverage: the sequential check run took no plan from the table (checked nothing)"
  -- 4. the negative control and its neighbour
  if let some (key, plan) := transported[0]? then
    let carried := ((cenv.p3Cliques.get? key).map (·.2)).getD #[]
    let on := { cenv with p3CheckPlans := true }
    match Ix.Compile.Pass.cliquePlanFor on plan.all carried with
    | .ok (o, true) =>
      if o.same (.transported plan) then say s!"neighbour: the table's plan of {key.pretty} passes the check"
      else problems := problems.push "neighbour: the lookup returned another plan"
    | .ok (_, false) => problems := problems.push "neighbour: the plan was not taken from the table"
    | .error e => problems := problems.push s!"neighbour: the table's own plan fails the check: {e}"
    let corrupt : List (String × Ix.Compile.Pass.CliqueOutcome) :=
      [("notEncoded", .notEncoded "replaced for the negative control"),
       ("another permutation", .transported { plan with sigma := plan.sigma.reverse })]
    for (what, bad) in corrupt do
      let table := cenv.p3CliquePlans.insert key bad
      match Ix.Compile.Pass.cliquePlanFor { on with p3CliquePlans := table } plan.all carried with
      | .error e =>
        if (e.splitOn Ix.Compile.Pass.planCheckPrefix).length > 1 then
          say s!"negative ({what}): rejected: {e.take 160}"
        else problems := problems.push s!"negative ({what}): failed without the check's prefix: {e}"
      | .ok _ => problems := problems.push s!"negative ({what}): a replaced entry passed the check"
      match Ix.Compile.Pass.cliquePlanFor { cenv with p3CheckPlans := false, p3CliquePlans := table }
          plan.all carried with
      | .ok (o, true) =>
        unless o.same bad do problems := problems.push s!"negative ({what}): without the check, not the table's entry"
      | _ => problems := problems.push s!"negative ({what}): without the check, the lookup did not use the table"
  if problems.isEmpty then
    say "PASS"
    return 0
  say s!"FAIL: {problems.size} problem(s)"
  for p in problems do say s!"  {p}"
  return 1

end Tests.Ix.Compile.PlanCache
