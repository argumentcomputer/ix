/-
  clique-ownership-units: the clique-ownership cases compiled by the compiler
  (CQ5.2 (b)), ported from the donor's `Tests/Ix/Compile/CliqueOwnership.lean`
  sections that need the pipeline ("Left for the wiring step" in
  `Tests.Ix.Compile.Clique.Ownership`, whose library checks stay there).

  **Compile units.** Every well-founded case (`WF*`, without an alteration),
  as a unit: its members and their closure (`Harness.closureOf`) with the
  rows' prerequisites (`Twins.rowPrereqNames`: a well-founded clique is
  transported only when they are in the input, decision (ii)), compiled by
  the Lean pipeline:
  * the members' equation lemmas are not in the unit, so no carried lemma's
    statement check can be what stops a wrong transport (FIX-pfwf O4);
  * the plan is the compiler's: the plan table's entry for the clique
    (`CompileEnv.p3CliquePlans`, over compiled addresses). When it
    transports, every member it replaces is evaluated one fixpoint unfolding
    deep against Lean's (`evalMember`), the planned constants go through
    Lean's kernel, and the certified checker and the Rust kernel check the
    compiled members, the reserved `_ix` constants (canonical constants,
    rows, `_ix.src` copies) and the neighbours;
  * **callers** (the block rule, "callers adapt", `Clique.cliqueCallers`):
    WF8's `caller` (it references a member and one of Lean's encoding
    constants) is refused by name when the clique is transported, and
    compiles when it is not; its `neighbour` (a member only) always
    compiles; the clique compiles to the same addresses with and without
    them. Both ways must be exercised (WF8's two orders: one transported,
    one kept);
  * **the Rust leg**: the same input through the Rust compiler
    (`ClosureHarness.rustClosure`): the same refused names, the same `Named`
    entries for the members and every reserved name, and the two kernels on
    the Rust file's names.

  **Carried-lemma units.** Each `Lem` clique (structural) with its members'
  `eq_def`s realised (`unfold_used`, and `equations_used` where present), as
  a unit seeded by the members and those constants:
  * the clique table carries every member's `eq_def` (`scheduleCliques`);
  * the plan: under decision (ii) a structural clique keeps Lean's form, so
    the canonical order is `unchanged` and every other order is
    `baseline SHAPE` with the reason "no row recipe for a structural
    clique". The donor expected the non-canonical orders transported (five
    transported, one unchanged); the library-level plan with the lemmas
    transported stays checked by `clique-ownership` (`runLemmaPlan`), and so
    does the donor's control `lemmaControl` there in spirit: with nothing
    transported in the compile there is no transported lemma to reject;
  * no block fails; the kernels check every compiled name of the case's
    namespace (`unfold_used` and the carried lemmas included), and the Rust
    leg compares the members, the carried lemmas and `unfold_used`.

  Run with: `lake test -- --ignored clique-ownership-units` (after
  `lake build ix`).
-/
import Tests.Ix.Compile.Clique.Ownership
import Tests.Ix.Compile.Harness.Kernels

open Lean Meta

namespace Tests.Ix.Compile.Clique.OwnershipUnits

open Tests.Ix.Compile.Clique.Common
open Tests.Ix.Compile.Clique.Ownership (Case Outcome srcNs lemNs checkedNs auxOf evalMember invPermM
  coreCtx cases)
open Tests.Ix.Compile.Clique.Transport (eqnCliques checkDecls)
open Tests.Ix.Compile.Harness (CUnit closureOf compileUnit kernelFailures)
open _root_.Ix.Compile.Pass.Clique (Encoding CliqueOutcome)

/-- The plan the compile made for the clique of `m`: the clique table's
members and carried lemmas, and the plan table's entry under the clique's
first member. -/
def planOf (cenv : _root_.Ix.CompileM.CompileEnv) (m : Name) :
    Except String (Array IxName × Array IxName × CliqueOutcome) := do
  let some (all, carried) := cenv.p3Cliques.get? (ixName m) | throw "not in the clique table"
  let some key := all[0]? | throw "an empty clique"
  let some o := cenv.p3CliquePlans.get? key | throw s!"no plan for {key.pretty} in the plan table"
  return (all, carried, o)

/-- The outcome's line for the log. -/
def outcomeLine : CliqueOutcome → String
  | .transported p => s!"transported (sigma {p.sigma}, aliases (O17) {p.aliases.size})"
  | .unchanged _ src => s!"unchanged (order by {src.describe})"
  | .baseline _ cause why => s!"baseline {cause.tag}: {why}"
  | .notEncoded why => s!"not encoded: {why}"

/-- The Rust leg of a unit: the same closure through the Rust compiler. The
refused names must be Lean's, every name of `keys` must have the same `Named`
entry in both outputs, and the two kernels must accept the Rust file's
`names`. The failures and a summary. -/
def rustLeg (u : CUnit) (on : _root_.Ix.CompileM.LeanPipelineOut) (keys : Array IxName)
    (names : Array String) : IO (Array String × String) := do
  let dir ← IO.FS.createTempDir
  try
    let (bytes, status) ← Tests.Ix.Compile.ClosureHarness.rustClosure u.env u.closure (dir / "rust.ixe")
    let rust ← IO.ofExcept (Ixon.rsDeEnv bytes)
    let mut failures : Array String := #[]
    let leanFailed := (on.cenv.ungrounded.toArray.map (·.1.pretty)).qsort (· < ·)
    let rustFailed := (status.ungrounded.map (·.1)).qsort (· < ·)
    unless leanFailed == rustFailed do
      failures := failures.push s!"{u.name}: Rust failures {rustFailed} differ from Lean's {leanFailed}"
    let mut same := 0
    for n in keys do
      match on.env.named.get? n, rust.named.get? n with
      | some a, some b =>
        if a == b then same := same + 1
        else failures := failures.push s!"{u.name}: Rust's {n.pretty} differs from Lean's"
      | some _, none => failures := failures.push s!"{u.name}: Rust has no {n.pretty}"
      | none, some _ => failures := failures.push s!"{u.name}: only Rust has {n.pretty}"
      | none, none => pure ()
    if same == 0 then failures := failures.push s!"{u.name}: the Rust leg compared nothing"
    let kf ← if names.isEmpty then pure #[] else kernelFailures dir bytes names
    for (leg, n, m) in kf do
      failures := failures.push s!"{u.name}: Rust-compiled {n} rejected by {leg}: {m.take 200}"
    return (failures, s!"rust: {same}/{keys.size} entries identical to Lean's, failures \
      {rustFailed.size}, {kf.size} kernel failure(s) on {names.size} names")
  finally IO.FS.removeDirAll dir

/-- The kernels on the Lean compile's `names`. -/
def leanKernels (on : _root_.Ix.CompileM.LeanPipelineOut) (names : Array String) :
    IO (Array (String × String × String)) := do
  if names.isEmpty then return #[]
  let dir ← IO.FS.createTempDir
  try kernelFailures dir on.bytes names
  finally IO.FS.removeDirAll dir

/-- The reserved names of an output (canonical constants, rows, copies). -/
def reservedNames (on : _root_.Ix.CompileM.LeanPipelineOut) : Array IxName :=
  (on.env.named.toArray.filterMap fun (n, _) =>
    if _root_.Ix.Compile.Pass.hasReserved n then some n else none).qsort (·.pretty < ·.pretty)

/-! ## Compile units -/

/-- Compile `c`'s clique as a unit (its members, plus `callers` and
`neighbours` relative to the fixture namespace) and check it. -/
def runUnitCase (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name))
    (c : Case) (callers neighbours : Array Name := #[]) : IO Outcome := do
  let ns := srcNs ++ c.name.toName
  let some (enc, ms) := eqn.get? (ns ++ `first) |
    return { name := c.name, outcome := "MISSING", failures := #[s!"{c.name}: no clique recorded for first"] }
  let extra := (callers ++ neighbours).map (ns ++ ·)
  let prereqs := Tests.Ix.Compile.Twins.rowPrereqNames env
  let mkUnit (seeds : Array Name) : CUnit :=
    { name := s!"clique-ownership-{c.name}", env, seeds, closure := closureOf env (seeds.toList ++ prereqs) }
  let u := mkUnit (ms ++ extra)
  let mut failures : Array String := #[]
  -- the unit carries no equation lemma of a member
  let eqLemmas := u.closure.filterMap fun (n, _) =>
    if ms.contains n.getPrefix && (match n with | .str _ s => s.startsWith "eq_" | _ => false) then some n else none
  unless eqLemmas.isEmpty do failures := failures.push s!"{c.name}: the unit carries equation lemmas {eqLemmas}"
  let on ← compileUnit u
  let reserved := reservedNames on
  -- the Rust leg: the members, the reserved names, the neighbours
  let compiledNames := ms.map (·.toString) ++ reserved.map (·.pretty) ++ neighbours.map (fun k => (ns ++ k).toString)
  let (rustFailures, rustSummary) ← rustLeg u on (ms.map ixName ++ reserved) compiledNames
  failures := failures ++ rustFailures
  let (all, carried, outcome) ← match planOf on.cenv ms[0]! with
    | .ok r => pure r
    | .error e => return { name := c.name, outcome := e, failures := failures.push s!"{c.name}: {e}" }
  unless carried.isEmpty do failures := failures.push s!"{c.name}: carried lemmas {carried.map (·.pretty)} in a unit without them"
  unless all.size == ms.size && ms.all (all.contains <| ixName ·) do
    failures := failures.push s!"{c.name}: the clique table has {all.map (·.pretty)}, the fixture {ms}"
  let refused := on.cenv.ungrounded.toList.filter fun (_, e) =>
    (e.splitOn _root_.Ix.Compile.Pass.Clique.callerRefusalPrefix).length > 1
  let refusedNames : Array Name := refused.toArray.map (toLeanName ·.1)
  let isTransported := match outcome with | .transported _ => true | _ => false
  -- callers and neighbours
  for k in callers do
    let n := ns ++ k
    if isTransported then
      match refused.find? (toLeanName ·.1 == n) with
      | none => failures := failures.push s!"{c.name}: caller {k} of a transported clique was not refused"
      | some (_, e) =>
        unless (e.splitOn n.toString).length > 1 && (e.splitOn ms[0]!.toString).length > 1 do
          failures := failures.push s!"{c.name}: the refusal of {k} does not name the caller and the clique: {e}"
    else if on.cenv.ungrounded.contains (ixName n) then
      failures := failures.push s!"{c.name}: caller {k} of a clique in Lean's form failed: {on.cenv.ungrounded.get? (ixName n)}"
  for k in neighbours do
    if on.cenv.ungrounded.contains (ixName (ns ++ k)) then
      failures := failures.push s!"{c.name}: neighbour {k} failed: {on.cenv.ungrounded.get? (ixName (ns ++ k))}"
  for (n, e) in on.cenv.ungrounded.toList do
    unless refusedNames.contains (toLeanName n) do
      failures := failures.push s!"{c.name}: unexpected block failure {n.pretty}: {e.take 300}"
  -- the clique does not depend on its callers
  if !extra.isEmpty then
    let alone ← compileUnit (mkUnit ms)
    for m in ms do
      let a := (on.env.named.get? (ixName m)).map (·.addr)
      let b := (alone.env.named.get? (ixName m)).map (·.addr)
      unless a.isSome && a == b do
        failures := failures.push s!"{c.name}: {m} compiles to {a} with its callers and {b} without"
  -- the kernels on the Lean compile
  let kf ← leanKernels on compiledNames
  for (leg, n, m) in kf do failures := failures.push s!"{c.name}: compiled {n} rejected by {leg}: {m.take 200}"
  let rows := reserved.filter fun n => n.pretty.endsWith "._ix.row"
  let tag := s!"unit: {outcomeLine outcome}; {refused.length} caller(s) refused; {reserved.size} reserved \
    names ({rows.size} rows); kernels {kf.size} failure(s) on {compiledNames.size} names; {rustSummary}"
  let refusalLines := refused.toArray.map fun (n, e) => s!"refused {n.pretty}: {e}"
  match outcome with
  | .transported plan =>
    let isFixpoint := enc != .structural
    let srcComps (π : Array Nat) : MetaM (Array Expr) := do
      let inv ← invPermM π
      (List.range ms.size).toArray.mapM fun p => do
        let m := ms[inv[p]!]!
        let rel := m.replacePrefix ns .anonymous
        let some (_, o) := c.oracles.find? (·.1 == rel) | throwError "no oracle for {rel}"
        pure (mkConst o)
    let decls := plan.members.toArray.map (·.2) ++ plan.canon.map (·.1)
    let body : MetaM Outcome := do
      let mut failures := failures
      let scratch := checkedNs ++ (c.name ++ "Unit").toName
      let ks ← checkDecls scratch ns decls
      for (n, m?) in ks do
        if let some m := m? then failures := failures.push s!"{c.name}: Lean's kernel rejects the planned {n}: {m.take 300}"
      let outNames : NameSet := decls.foldl (fun s d => s.insert (toLeanName d.name)) {}
      let rn (n : Name) : Name := if outNames.contains n then scratch ++ n.replacePrefix ns .anonymous else n
      let tgtNames : NameSet := outNames.foldl (fun s n => s.insert (rn n)) {}
      let srcNames : NameSet := (ms ++ auxOf env enc ms).foldl (·.insert ·) {}
      let mut values := #[]
      for p in c.probes do
        let m := ns ++ p.member
        let v ← evalMember srcNames m p.args
          (← if isFixpoint then some <$> srcComps (_root_.Ix.Compile.Pass.Clique.idPerm ms.size) else pure none)
        let w ← if outNames.contains m then
            evalMember tgtNames (rn m) p.args (← if isFixpoint then some <$> srcComps plan.sigma else pure none)
          else pure v
        let same ← isDefEq v w
        values := values.push s!"{p.member} {p.args.map toString}: Lean {← ppExpr v}, compiled {← ppExpr w}{if same then "" else "  <-- DIFFERENT"}"
        if p.checkExpected then
          unless ← isDefEq v p.expected do failures := failures.push s!"{c.name}: Lean's {p.member} is not {← ppExpr p.expected}"
        unless same do
          failures := failures.push s!"{c.name}: WRONG MEANING (compile unit): {p.member} {p.args.map toString} is {← ppExpr v} in Lean, {← ppExpr w} compiled"
      return { name := c.name, outcome := tag,
               kernel := s!"{ks.size - (ks.filter (·.2.isSome)).size}/{ks.size} planned (Lean)",
               values := refusalLines ++ values, failures }
    let (r, _) ← (body.run' {} : CoreM Outcome).toIO coreCtx { env }
    return r
  | .notEncoded why => return { name := c.name, outcome := tag, values := refusalLines,
                                failures := failures.push s!"{c.name}: not encoded: {why}" }
  | _ => return { name := c.name, outcome := tag, values := refusalLines, failures }

/-! ## Carried-lemma units -/

/-- The carried-lemma cliques: the namespace under `Lem` and a member. -/
def lemmaCases : Array (String × Name) :=
  #[("SC1", `od), ("SC0", `od), ("MA", `sa), ("MB", `sa), ("MC", `f), ("MD", `f)]

/-- Compile one carried-lemma unit and check it (see the module docstring).
The outcome line starts with the plan's kind: `unchanged`, or `kept` (a
non-canonical order kept in Lean's form for want of a row recipe). -/
def runLemmaUnit (env : Environment) (eqn : Std.HashMap Name (Encoding × Array Name))
    (nm : String) (member : Name) : IO Outcome := do
  let ns := lemNs ++ nm.toName
  let some (enc, ms) := eqn.get? (ns ++ member) |
    return { name := nm, outcome := "MISSING", failures := #[s!"{nm}: no clique recorded for {member}"] }
  let mut failures : Array String := #[]
  unless enc == .structural do failures := failures.push s!"{nm}: not a structural clique"
  let used := ns ++ `unfold_used
  let derived := if env.contains (ns ++ `equations_used) then #[ns ++ `equations_used] else #[]
  let seeds := ms.push used ++ derived
  let u : CUnit := { name := s!"clique-lemmas-{nm}", env, seeds, closure := closureOf env seeds.toList }
  let on ← compileUnit u
  for (n, e) in on.cenv.ungrounded.toList do
    failures := failures.push s!"{nm}: block failure {n.pretty}: {e.take 300}"
  let (_, carried, outcome) ← match planOf on.cenv ms[0]! with
    | .ok r => pure r
    | .error e => return { name := nm, outcome := e, failures := failures.push s!"{nm}: {e}" }
  -- the carried lemmas: every member's `eq_def`
  let expectCarried := (ms.map fun m => ixName (m ++ `eq_def)).qsort (·.pretty < ·.pretty)
  unless carried.map (·.pretty) == expectCarried.map (·.pretty) do
    failures := failures.push s!"{nm}: carried {carried.map (·.pretty)}, expected {expectCarried.map (·.pretty)}"
  -- the plan: Lean's form, canonical or kept (decision (ii))
  let kind := match outcome with
    | .unchanged _ _ => "unchanged"
    | .baseline _ .shape why =>
      if (why.splitOn "no row recipe for a structural clique").length > 1 then "kept" else "other"
    | _ => "other"
  if kind == "other" then
    failures := failures.push s!"{nm}: plan {outcomeLine outcome}, expected unchanged or kept for want of a row recipe"
  -- the kernels on every compiled name of the case
  let names := on.env.named.toArray.filterMap fun (n, _) =>
    if ns.isPrefixOf (toLeanName n) then some n.pretty else none
  let kf ← leanKernels on names
  for (leg, n, m) in kf do failures := failures.push s!"{nm}: compiled {n} rejected by {leg}: {m.take 200}"
  unless names.contains (ixName used).pretty && carried.all (fun l => names.contains l.pretty) &&
      derived.all (fun n => names.contains (ixName n).pretty) do
    failures := failures.push s!"{nm}: the kernels did not check unfold_used and every carried lemma"
  -- the Rust leg: members, carried lemmas, `unfold_used`
  let keys := ms.map ixName ++ carried ++ #[ixName used] ++ derived.map ixName
  let (rustFailures, rustSummary) ← rustLeg u on keys #[]
  failures := failures ++ rustFailures
  return { name := nm, outcome := s!"{kind}: {outcomeLine outcome}; carried {carried.size}; {rustSummary}",
           kernel := s!"{names.size} compiled names, {kf.size} kernel failure(s)", failures }

/-! ## The suite -/

def say (s : String) : IO Unit := do
  IO.println s!"[clique-ownership-units] {s}"
  (← IO.getStdout).flush

def runOn (env : Environment) : IO UInt32 := do
  let eqn := eqnCliques env
  let mut failures : Array String := #[]
  -- the compile units: every well-founded case, and the callers of WF8
  let mut units := 0
  let mut transported := 0
  let mut refusals := 0
  let mut compiledCallers := 0
  let mut seen : Std.HashSet String := {}
  for c in cases do
    unless c.name.startsWith "WF" && c.alter.isNone && !seen.contains c.name do continue
    seen := seen.insert c.name
    let (callers, neighbours) := if c.name.startsWith "WF8" then (#[`caller], #[`neighbour]) else (#[], #[])
    let o ← try runUnitCase env eqn c callers neighbours
      catch e => pure { name := c.name, outcome := "ERROR", failures := #[s!"{c.name} (unit): {e}"] }
    units := units + 1
    if (o.outcome.splitOn "unit: transported").length > 1 then transported := transported + 1
    say s!"{c.name} (compile unit): {o.outcome}, kernel {o.kernel}"
    for v in o.values do say s!"  {v}"
    for f in o.failures do say s!"  FAIL {f}"
    if !callers.isEmpty && o.failures.isEmpty then
      if (o.outcome.splitOn "; 1 caller(s) refused").length > 1 then refusals := refusals + 1
      else compiledCallers := compiledCallers + 1
    failures := failures ++ o.failures
  unless refusals ≥ 1 && compiledCallers ≥ 1 do
    failures := failures.push s!"callers: {refusals} refused and {compiledCallers} compiled; the block rule \
      needs a transported and a kept WF8 order"
  if transported == 0 then failures := failures.push "coverage: no compile unit transported its clique"
  say s!"compile units: {units}, {transported} transported; WF8 callers refused {refusals}, compiled {compiledCallers}"
  -- the carried-lemma units
  let mut kinds : Array (String × String) := #[]
  for (nm, member) in lemmaCases do
    let o ← try runLemmaUnit env eqn nm member
      catch e => pure { name := nm, outcome := "ERROR", failures := #[s!"{nm} (carried lemmas): {e}"] }
    say s!"{nm} (carried lemmas): {o.outcome}, kernel {o.kernel}"
    for f in o.failures do say s!"  FAIL {f}"
    kinds := kinds.push (nm, (o.outcome.splitOn ":")[0]!)
    failures := failures ++ o.failures
  -- `SC0` and `SC1` are one clique in two orders: one is canonical
  let kindOf (nm : String) : String := ((kinds.find? (·.1 == nm)).map (·.2)).getD ""
  unless [kindOf "SC0", kindOf "SC1"].contains "unchanged" && [kindOf "SC0", kindOf "SC1"].contains "kept" do
    failures := failures.push s!"carried lemmas: SC0 and SC1 (one clique, two orders) do not split into one \
      unchanged and one kept: {kindOf "SC0"}, {kindOf "SC1"}"
  say s!"carried-lemma units: {lemmaCases.size}: {kinds.toList}"
  for f in failures do say s!"FAIL {f}"
  say s!"{failures.size} failure(s)"
  return if failures.isEmpty then 0 else 1

def run : IO UInt32 := do runOn (← fixturesEnv)

end Tests.Ix.Compile.Clique.OwnershipUnits
