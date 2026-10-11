/-
  compile-caller-independence: a block compiles the same whether or not
  anything depends on it (M1-f; design document §6.3, the block rule and
  "How it is checked": caller independence).

  Fixture `Tests/Ix/Compile/Fixtures/CallerIndependence.lean`. For each
  case, the block's logical unit `U` (`Lean.unitMembers`: the block, its
  eager auxiliaries and the on-demand ones that exist) and two inputs:

  - **with dependents**: the selected closure of the block and of its
    dependents (constants that reference the block and are not auxiliaries
    of its unit);
  - **without**: the selected closure of the block alone, with the
    unrelated constants of the fixture (`CallerInd.Unrelated`) in place of
    the dependents.

  Both are compiled by the Lean pipeline (Pass 3, the only mode since M6R
  slice 6; until then also with the legacy surgery, `IX_PASS3=off`), and
  every name of `U`, and every `_ix` name the compiler stores for a member
  of `U`, must have the same `Named` entry (address and metadata) in both
  outputs, with the same records (the clique table entry, the
  non-canonical set entry). The cases:

  1. **inductive block with an on-demand auxiliary** (`T`, with `T.a.hinj`
     realised by the dependent `useHinj`): identical with and without the
     dependents. A third input drops the on-demand auxiliary: per §6.3 the
     unit may then compile differently (the expectation is stated, not
     assumed: differences are allowed inside `U` and counted, and every
     constant outside `U` must be identical);
  2. **definition clique with an external unfolding caller** (`WP` and
     `WQ`: one well-founded clique in both member orders, so one of them
     is changed under the switch; `*.caller` mentions a member and Lean's
     encoding `all₀._mutual`; `*.useEqns` realises the equation lemmas,
     which are part of the unit). Expectation by decision 5: identical
     bytes for the clique whether or not the caller is present, and the
     caller, which unfolds the encoding, is refused by name with the switch
     on (`cliqueCallers`; reported, never fatal); any other refusal is
     fatal. `expectedFailures` lists the cases the current line fails (a
     stale entry fails the suite); it is empty since M1-a;
  3. **split member with O11a** (`SA`/`SB`; `SA._sizeOf_1` goes through
     `SB._sizeOf_inst` with the switch on, checked): identical with and
     without the dependents (`SA.depth`, `sizeA`).

  Run with: `lake test -- --ignored compile-caller-independence`.
-/
import Ix.EnvScope
import Ix.CompileM
import Ix.CompileDriver
import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.O11aDecline

open Lean

namespace Tests.Ix.Compile.CallerIndependence

abbrev IxName := _root_.Ix.Name
abbrev Out := Ix.CompileM.LeanPipelineOut

def say (s : String) : IO Unit := do
  IO.println s!"[caller-independence] {s}"
  (← IO.getStdout).flush

def fixture : String := "Tests/Ix/Compile/Fixtures/CallerIndependence.lean"

def ixN (n : Name) : IxName := Tests.Ix.Compile.Pass3.ixN n

/-- Cases the current line is expected to fail, `(case, switch on?, cause)`.
Exact in both directions: a listed case that passes fails the suite. -/
def expectedFailures : List (String × Bool × String) := [
  -- Empty since the clique hook decides a clique's form from its own unit
  -- (M1-a: `scheduleCliques` no longer reads callers or demotes). Before that,
  -- measured on the pre-M1-a line (2026-10-06), `WP` and `WQ` failed with the
  -- switch on: with `CallerInd.WP.caller` present the changed clique compiled in
  -- Lean's form and 14 of the unit's 16 names differed; `WQ` agreed in bytes but
  -- the clique table carried the caller's name as the demotion reason. A caller
  -- that unfolds the encoding is now refused by name (`cliqueCallers`) and never
  -- changes the clique.
  ]

/-- The Lean name before an `_ix` component, when `n` has one. -/
def ixOwner? (n : Name) : Option Name :=
  let comps := n.components
  match comps.findIdx? (· == `_ix) with
  | some i => some (comps.take i |>.foldl (init := .anonymous) fun p c => match c with
      | .str _ s => p.str s
      | .num _ k => p.num k
      | .anonymous => p)
  | none => none

/-- The names compared for a unit: the members of `U` in either output, and
every `_ix` name stored for a member of `U`. -/
def comparedNames (U : Std.HashSet Name) (a b : Out) : Array IxName := Id.run do
  let mut out : Array IxName := #[]
  let mut seen : Std.HashSet IxName := {}
  for o in [a, b] do
    for (n, _) in o.env.named do
      let ln := Tests.Ix.Compile.Pass3.toLeanName n
      let keep := U.contains ln || (ixOwner? ln).any U.contains
      if keep && !seen.contains n then
        seen := seen.insert n
        out := out.push n
  return out

/-- Differences of the unit between two outputs: names whose `Named` entry
differs or is missing on one side, and records that differ. -/
def unitDiffs (U : Std.HashSet Name) (a b : Out) : Array String := Id.run do
  let mut out : Array String := #[]
  for n in comparedNames U a b do
    match a.env.named[n]?, b.env.named[n]? with
    | some x, some y =>
      if x.addr != y.addr then out := out.push s!"{n.pretty}: {x.addr} / {y.addr}"
      else if x != y then out := out.push s!"{n.pretty}: metadata differs"
    | some _, none => out := out.push s!"{n.pretty}: only with dependents"
    | none, some _ => out := out.push s!"{n.pretty}: only without dependents"
    | none, none => pure ()
  for ln in U do
    let n := ixN ln
    let ca := a.cenv.p3Cliques.get? n
    let cb := b.cenv.p3Cliques.get? n
    if ca != cb then
      -- the record is (the clique in Lean's order, the carried lemmas); since
      -- M1-a there is no demotion reason to show
      let fmt := fun (ms : Array _) (ls : Array _) => s!"{ms.size} members, {ls.size} carried lemmas"
      out := out.push s!"{ln}: clique record {ca.map fun (ms, ls) => fmt ms ls} / \
        {cb.map fun (ms, ls) => fmt ms ls}"
    if a.cenv.p3NonCanonical.get? n != b.cenv.p3NonCanonical.get? n then
      out := out.push s!"{ln}: non-canonical record {a.cenv.p3NonCanonical.get? n} / \
        {b.cenv.p3NonCanonical.get? n}"
  return out

/-- The clique hook's named error for a caller that unfolds a transported clique's
encoding (`Ix.Compile.Pass.cliqueCallers`). -/
def callerRefusal : String := "caller refused (block rule, callers adapt)"

/-- Compile `cs`. Any refusal is fatal, except the named refusal of a declared
`caller` (decision 5: the caller adapts, the clique never changes for it); such a
refusal is reported, and the unit is still compared. -/
def compile (env : Environment) (label : String) (cs : List (Name × ConstantInfo)) (mode : Bool)
    (callers : List Name := []) : IO Out := do
  let unit : Tests.Ix.Compile.Pass3.CUnit := { name := label, env, seeds := #[], closure := cs }
  let out ← Tests.Ix.Compile.Pass3.compileUnit unit
  for (n, why) in out.cenv.ungrounded.toList do
    if callers.any (fun c => ixN c == n) && (why.splitOn callerRefusal).length > 1 then
      say s!"  {label} mode={mode}: {n.pretty} refused by name (decision 5): {why.take 160}"
    else
      throw (IO.userError s!"{label} mode={mode}: refusal {n.pretty}: {why.take 200}")
  return out

/-- `xs ∪ ys` by name, in `xs`'s order then `ys`'s. -/
def union (xs ys : List (Name × ConstantInfo)) : List (Name × ConstantInfo) :=
  let s : Std.HashSet Name := xs.foldl (fun s (n, _) => s.insert n) {}
  xs ++ ys.filter (!s.contains ·.1)

def run : IO UInt32 := do
  let env ← getFileEnv fixture
  let idx := Lean.unitIndex env.constants
  let sel := fun (roots : List Name) => Ix.EnvScope.collectSelectedDeps env roots
  let unitOf := fun (n : Name) => Lean.unitMembers env.constants idx n
  let U' := fun (n : Name) => (unitOf n).foldl (fun (s : Std.HashSet Name) m => s.insert m) {}
  let unrelated := sel [`CallerInd.Unrelated.flip_flip]
  let mut errors : Array String := #[]
  -- (case, block root, dependents)
  let cases : List (String × Name × List Name) := [
    ("T", `CallerInd.T, [`CallerInd.useHinj, `CallerInd.T.depth, `CallerInd.T.depth_b]),
    ("WP", `CallerInd.WP.wa, [`CallerInd.WP.caller, `CallerInd.WP.useEqns]),
    ("WQ", `CallerInd.WQ.wb, [`CallerInd.WQ.caller, `CallerInd.WQ.useEqns]),
    ("SA", `CallerInd.SA._sizeOf_1, [`CallerInd.SA.depth, `CallerInd.sizeA])]
  let mut failed : Array (String × Bool) := #[]
  for (case, root, deps) in cases do
    let U := U' root
    let without := union (sel [root]) unrelated
    let withDeps := sel (root :: deps)
    -- the inputs are what the case says
    for d in deps do
      if U.contains d then errors := errors.push s!"{case}: dependent {d} is in the unit"
      if without.any (·.1 == d) then errors := errors.push s!"{case}: dependent {d} in the input without dependents"
      unless withDeps.any (·.1 == d) do errors := errors.push s!"{case}: dependent {d} missing"
    for u in U do
      unless without.any (·.1 == u) do errors := errors.push s!"{case}: {u} of the unit is not carried"
    say s!"{case}: unit of {root}: {U.size} constants; inputs {withDeps.length} with dependents, \
      {without.length} without"
    -- the declared external callers that unfold the clique's encoding: with the switch
    -- on they may be refused by name (and are reported either way); nothing else may be
    let callers := if case == "WP" || case == "WQ" then deps.filter (·.toString.endsWith ".caller") else []
    -- Pass 3 only (until M6R slice 6 also the legacy surgery, `mode=false`)
    for mode in [true] do
      let a ← compile env s!"{case}-with" withDeps mode (callers := if mode then callers else [])
      let b ← compile env s!"{case}-without" without mode
      if mode then
        for c in callers do
          let refused := a.cenv.ungrounded.contains (ixN c)
          say s!"  {case} mode={mode}: caller {c} {if refused then "refused by name" else "compiled"}"
      let ds := unitDiffs U a b
      let n := (comparedNames U a b).size
      say s!"{case} mode={mode}: {n} names of the unit compared: {ds.size} differ"
      for d in ds.toList.take 8 do say s!"  {case} mode={mode}: {d}"
      if !ds.isEmpty then failed := failed.push (case, mode)
      -- case-specific checks
      if case == "SA" && mode then
        for (o, lbl) in [(a, "with"), (b, "without")] do
          let r ← IO.ofExcept (Tests.Ix.Compile.O11aDecline.references o.env root
            `CallerInd.SB._sizeOf_inst)
          unless r do errors := errors.push s!"SA {lbl}: O11a did not fire on {root}"
      if case == "WP" || case == "WQ" then
        let row := fun (o : Out) => match o.cenv.p3Cliques.get? (ixN root) with
          | some (ms, ls) => s!"transported ({ms.size} members, {ls.size} carried lemmas)"
          | none => "-"
        say s!"  {case} mode={mode}: clique table with dependents: {row a}; without: {row b}"
      if case == "T" then
        -- the on-demand auxiliary dropped: differences confined to the unit
        let hinj := `CallerInd.T.a.hinj
        unless U.contains hinj do errors := errors.push s!"T: {hinj} is not in the unit"
        let noAux := union (Tests.Ix.Compile.O11aDecline.dropWithDependents (sel [root]) [hinj]) unrelated
        if noAux.any (·.1 == hinj) then errors := errors.push s!"T: {hinj} still present"
        let c ← compile env "T-noaux" noAux mode
        let mut inside := 0
        let mut outside := 0
        for (nm, x) in c.env.named do
          let some y := b.env.named[nm]? | continue
          let ln := Tests.Ix.Compile.Pass3.toLeanName nm
          if x != y then
            if U.contains ln || (ixOwner? ln).any U.contains then inside := inside + 1
            else
              outside := outside + 1
              errors := errors.push s!"T mode={mode}: without {hinj}, {ln} outside the unit differs"
        say s!"  T mode={mode}: without the on-demand {hinj}: {inside} names of the unit differ \
          (allowed, §6.3), {outside} outside (must be 0)"
  -- the expected failures, exact in both directions
  for (case, mode) in failed do
    unless expectedFailures.any (fun (c, m, _) => c == case && m == mode) do
      errors := errors.push s!"{case} mode={mode}: the unit differs with and without dependents"
  for (case, mode, cause) in expectedFailures do
    if failed.contains (case, mode) then say s!"expected failure {case} mode={mode}: {cause}"
    else errors := errors.push s!"stale expected failure {case} mode={mode} ({cause})"
  for e in errors do say s!"FAIL {e}"
  say s!"{if errors.isEmpty then "PASS" else s!"FAIL ({errors.size})"}: {cases.length} cases (Pass 3), \
    {expectedFailures.length} expected failure(s)"
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.CallerIndependence
