/-
  pass3-cliques: changed definition cliques under the switch
  (`IX_PASS3=images`; `Ix.Compile.Pass.Cliques`, design document §5).

  One compile unit, the closure of every clique twin family
  (`Tests/Ix/Compile/Twins/Cliques.lean`), compiled by the Lean pipeline with
  the switch off and on:

  1. **plans**: every clique of the fixtures, as the compiler planned it
     (`Ix.Compile.Pass.planClique` against the switch-on compile state):
     encoding, Lean's order, `σ`, the source of the order, the outcome
     (transported, unchanged, baseline with its cause, not encoded) and the
     transport's causes;
  2. **identity**: with the switch on, every name whose address moved is in
     the cone of a transported clique (its members and everything that
     references them, transitively), and every new name is reserved (`_ix`);
  3. **decompile**: the switch-on output decompiles to the source constants
     (the members through their `_ix.inline` records);
  4. **kernels**: `ix check-rs`, `ix check-lean` (meta mode) and the
     certified checker on every fixture constant and every `_ix` constant of
     the switch-on output (the value pins `rfl` over clique members among
     them);
  5. **twins under the switch**: for every presentation pair, every Lean name
     and every `_ix` name compiles to the reference's address, except the
     entries of the switch-on non-canonical set
     (`Tests.Ix.Compile.NonCanonical.nonCanonicalOn`), which is exact in both
     directions.

  Run with: `lake test -- --ignored pass3-cliques` (after `lake build ix
  kernel-check-ixe`). `PASS3_CLIQUES_ONLY=<substring>` restricts the
  families (the exactness check then covers only those); `PASS3_KEEP=<dir>`
  keeps the outputs; `IX_TWINS_DUMP=<dir>` dumps the differing Lean terms.
-/
import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.NonCanonical

open Lean
open Tests.Ix.Compile.NonCanonical
open Tests.Ix.Compile.Twins (Family Pres mapInto comparePair DiffRec Compiled)

namespace Tests.Ix.Compile.Pass3Cliques

abbrev IxName := _root_.Ix.Name

def toLeanName : IxName → Name := Tests.Ix.Compile.Pass3.toLeanName

/-! ## Plans -/

structure PlanRow where
  /-- the clique, Lean's order -/
  all : Array IxName
  outcome : String
  transported : Bool
  causes : Array String := #[]

/-- Every clique of the seeds, planned as the compiler planned it. -/
def plans (on : Ix.CompileM.LeanPipelineOut) (seeds : Array Name) : Array PlanRow := Id.run do
  let cenv := on.cenv
  let const? := cenv.env.get?
  let mut seen : Std.HashSet IxName := {}
  let mut out : Array PlanRow := #[]
  for s in seeds do
    let n := _root_.Ix.Name.fromLeanName s
    if seen.contains n then continue
    let some ci := const? n | continue
    let all := Ix.Compile.Pass.allOf ci
    if all.size < 2 || (Ix.Compile.Pass.cliqueDecl? ci).isNone then continue
    for a in all do seen := seen.insert a
    let row : PlanRow := match cenv.p3Cliques.get? n with
      | none => { all, outcome := "not in the clique table (no encoding marker, or members in one block)", transported := false }
      | some (_, _, demoted) =>
      if !demoted.isEmpty then { all, outcome := s!"DEMOTED: {demoted}", transported := false } else
      let carried := (cenv.p3Cliques.get? n).map (·.2.1) |>.getD #[]
      match Ix.Compile.Pass.planClique const? (Ix.Compile.Pass.cliqueAddr cenv) all carried with
      | .notEncoded why => { all, outcome := s!"not encoded ({why})", transported := false }
      | .unchanged enc src =>
        { all, outcome := s!"unchanged ({enc.tag}; order by {src.tag})", transported := false }
      | .baseline enc c why => { all, outcome := s!"baseline {c} ({enc.tag}): {why}", transported := false }
      | .transported p =>
        { all, outcome := s!"TRANSPORTED (carried {carried.map (·.pretty)}) {p.record}", transported := true
          causes := p.causes.map fun (c, k, why) => s!"{c.pretty} {k.tag}: {why}" }
    out := out.push row
  return out

/-! ## Identity: cones of the transported cliques -/

def cone (u : Tests.Ix.Compile.Pass3.CUnit) (members : Array Name) : Std.HashSet Name := Id.run do
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ci) in u.closure do
    for r in ci.getUsedConstantsAsSet do
      rev := rev.insert r ((rev.getD r #[]).push n)
  let mut out : Std.HashSet Name := {}
  let mut todo := members
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if out.contains n then continue
    out := out.insert n
    for d in rev.getD n #[] do
      if !out.contains d then todo := todo.push d
  return out

def identity (u : Tests.Ix.Compile.Pass3.CUnit) (off on : Ix.CompileM.LeanPipelineOut)
    (members : Array Name) : Array String × String := Id.run do
  -- the cones of the transported cliques and of the changed blocks (Pass 3
  -- rewrites those too, `pass3`)
  let c := cone u members
  let cb := Tests.Ix.Compile.Pass3.cone u (on.cenv.p3Blocks.toArray.map (·.2))
  let mut problems := #[]
  let mut equal := 0
  let mut moved := 0
  let mut newReserved := 0
  for (n, nd) in off.env.named do
    if Tests.Ix.Compile.Pass3.isSyntheticMuts n then continue
    match on.env.named.get? n with
    | none => problems := problems.push s!"{n.pretty} missing with the switch on"
    | some nd' =>
      if nd'.addr == nd.addr then equal := equal + 1
      else if c.contains (toLeanName n) || cb.contains (toLeanName n) then moved := moved + 1
      else problems := problems.push s!"{n.pretty} moved outside the transported cliques' cones"
  for (n, _) in on.env.named do
    if Tests.Ix.Compile.Pass3.isSyntheticMuts n || off.env.named.contains n then continue
    if Ix.Compile.Pass.hasReserved n then newReserved := newReserved + 1
    else problems := problems.push s!"{n.pretty} is new with the switch on and not reserved"
  return (problems, s!"equal names {equal}, moved in cones {moved}, new reserved {newReserved}")

/-! ## Twins under the switch -/

/-- The `_ix` names of presentation `p` in the switch-on output, relative to
the reference's namespace by the name map. -/
def ixNames (on : Ix.CompileM.LeanPipelineOut) (a p : Pres) : Array (Name × Name) :=
  on.env.named.toArray.filterMap fun (n, _) =>
    let ln := toLeanName n
    if Ix.Compile.Pass.hasReserved n && p.ns.isPrefixOf ln then some (ln, mapInto a p ln) else none

/-- The differences between the `_ix` constants of `a` and `b` (a one-sided
`_ix` name is a difference too). -/
def compareIx (on : Ix.CompileM.LeanPipelineOut) (a b : Pres) : Array DiffRec := Id.run do
  let addr (n : Name) : Option String :=
    (on.env.getAddr? (_root_.Ix.Name.fromLeanName n)).map toString
  let as := ixNames on a a
  let bs := ixNames on a b
  let rel (n : Name) : Name := n.replacePrefix a.ns .anonymous
  let mut out := #[]
  for (nb, t) in bs do
    match as.find? (·.1 == t) with
    | some (na, _) =>
      if addr na != addr nb then
        out := out.push { constant := rel na, cls := "ROOT[ix]", addrA := (addr na).getD "-",
                          addrB := (addr nb).getD "-", firstDiff := "" }
    | none =>
      out := out.push { constant := rel t, cls := "ONLY-B", addrA := "-",
                        addrB := (addr nb).getD "-", firstDiff := "" }
  for (na, _) in as do
    unless bs.any (·.2 == na) do
      out := out.push { constant := rel na, cls := "ONLY-A", addrA := (addr na).getD "-",
                        addrB := "-", firstDiff := "" }
  return out

def entrySyntax (f : Family) (a b : Pres) (d : DiffRec) : String :=
  let s := Tests.Ix.Compile.Twins.lastStr d.constant
  let isIx := (d.constant.toString.splitOn "._ix").length > 1
  let isEq := s == "eq_def" || s == "eq_unfold" || s.startsWith "eq_"
  let parent := Tests.Ix.Compile.Twins.lastStr d.constant.getPrefix
  let (cause, role) :=
    if d.cls == "INHERITED" then (".inherited", "user constant")
    else if isIx then (".pendingTransport /- REVIEW -/", "canonical constant")
    else if isEq && (parent == "_mutual" || parent == "mutual") then (".orderStmt", "encoding equation")
    else if isEq then (".lazy", "equation lemma")
    else if s.startsWith "_proof_" || s == "_mutual" || s == "mutual" || s == "_f"
        || s.startsWith "match_" then
      (".orderStmt", "Lean's encoding constant (faithful; canonical form under `_ix`)")
    else (".pendingTransport /- REVIEW -/", "clique member")
  let note := match d.cls with
    | "INHERITED" => s!"via {d.via}" | c => c
  s!"  e `{f.fixture} \"{a.id}\" \"{b.id}\" `{d.constant} \"{role}\" {cause}\n" ++
  s!"    \"{d.addrA}\" \"{d.addrB}\" \"{d.firstDiff}\" \"{note}\","

/-! ## The suite -/

def run (env : Environment) : IO UInt32 := do
  let only := ← IO.getEnv "PASS3_CLIQUES_ONLY"
  let keep? := (← IO.getEnv "PASS3_KEEP").map System.FilePath.mk
  let dumpDir := (← IO.getEnv "IX_TWINS_DUMP").map System.FilePath.mk
  if let some d := dumpDir then IO.FS.createDirAll d
  let families := Tests.Ix.Compile.Twins.cliqueFamilies.filter fun f =>
    match only with
    | some s => (f.fixture.toString.splitOn s).length > 1
    | none => true
  let (seeds, _) := Tests.Ix.Compile.Twins.familyClosure env families
  -- the composition fallback of `partial_fixpoint` needs `monotone_compose`
  -- (a library compile has it; a closure has it only when asked)
  let extra := [``Lean.Order.monotone_compose].filter env.contains
  let closure := Tests.Ix.Compile.Pass3.closureOf env (seeds.toList ++ extra)
  let u : Tests.Ix.Compile.Pass3.CUnit := { name := "cliques", env, seeds, closure }
  IO.println s!"[pass3-cliques] {families.length} families, {seeds.size} fixture constants, \
    {u.closure.length} in the closure"
  let t0 ← IO.monoMsNow
  let off ← Tests.Ix.Compile.Pass3.compileUnit u false
  let on ← Tests.Ix.Compile.Pass3.compileUnit u true
  IO.println s!"[pass3-cliques] compiles: off {off.bytes.size} B ({off.cenv.ungrounded.size} failures), \
    on {on.bytes.size} B ({on.cenv.ungrounded.size} failures), {(← IO.monoMsNow) - t0} ms"
  let mut problems : Array String := #[]
  for (n, e) in on.cenv.ungrounded do
    if !off.cenv.ungrounded.contains n then
      problems := problems.push s!"{n.pretty} fails only with the switch on: {e.take 300}"
  -- 1. plans
  let rows := plans on seeds
  let mut members : Array Name := #[]
  let mut nT := 0
  for r in rows do
    IO.println s!"[pass3-cliques] clique {r.all.map (·.pretty)}: {r.outcome}"
    if r.transported then
      nT := nT + 1
      members := members ++ r.all.map toLeanName
  IO.println s!"[pass3-cliques] {rows.size} cliques, {nT} transported"
  -- 2. identity
  let (iprob, isum) := identity u off on members
  IO.println s!"[pass3-cliques] identity: {isum}, {iprob.size} problem(s)"
  problems := problems ++ iprob
  -- 3. decompile
  if on.cenv.ungrounded.isEmpty then
    let (dprob, dsum) ← Tests.Ix.Compile.Pass3.decompileCheck u on
    IO.println s!"[pass3-cliques] decompile: {dsum}, {dprob.size} problem(s)"
    problems := problems ++ dprob
  else
    IO.println s!"[pass3-cliques] decompile: skipped ({on.cenv.ungrounded.size} block failures)"
  -- 4. kernels
  let dir ← match keep? with
    | some d => do IO.FS.createDirAll d; pure d
    | none => IO.FS.createTempDir
  try
    let path := dir / "on.ixe"
    IO.FS.writeBinFile path on.bytes
    let seedSet : Std.HashSet String := seeds.foldl (fun s n => s.insert (_root_.Ix.Name.fromLeanName n).pretty) {}
    let names := on.env.named.toArray.filterMap fun (n, _) =>
      let s := n.pretty
      if seedSet.contains s || Ix.Compile.Pass.hasReserved n then some s else none
    let nIx := (names.filter fun s => (s.splitOn "._ix").length > 1).size
    let failed ← Tests.Ix.Compile.Pass3.kernelFailures dir path names
    IO.println s!"[pass3-cliques] kernels: {names.size} names ({nIx} `_ix`), {failed.size} failure(s)"
    for (leg, n, m) in failed do
      problems := problems.push s!"kernel {leg}: {n}: {m.take 240}"
  finally
    if keep?.isNone then IO.FS.removeDirAll dir
  -- 5. twins under the switch
  let lean : Compiled := { addr := fun n => (on.env.getAddr? (_root_.Ix.Name.fromLeanName n)).map toString }
  let mut total := 0
  let mut unexpected : Array String := #[]
  let mut stale : Array String := #[]
  for f in families do
    let some a := f.pres.head? | continue
    for b in f.pres.tail do
      let ds ← comparePair env lean f a b dumpDir
      -- the canonical constants are stored only where a member or a carried
      -- lemma reaches them, by address: equal Lean names imply equal canonical
      -- constants; the `_ix` names both sides carry are compared for the log
      for d in (compareIx on a b).filter (·.cls == "ROOT[ix]") do
        IO.println s!"[pass3-cliques]   canonical constant differs: {d.constant} {d.addrA} {d.addrB}"
      let ds := ds.foldl (init := #[]) fun acc d =>
        if acc.any (·.constant == d.constant) then acc else acc.push d
      total := total + ds.size
      let es := nonCanonicalOn.filter fun e => e.fixture == f.fixture && e.presA == a.id && e.presB == b.id
      for d in ds do
        unless es.any (·.constant == d.constant) do unexpected := unexpected.push (entrySyntax f a b d)
      for e in es do
        unless ds.any (·.constant == e.constant) do
          stale := stale.push s!"{f.fixture} {a.id}/{b.id} {e.constant} ({e.cause.tag})"
      IO.println s!"[pass3-cliques] twins {f.fixture.getString!} {a.id}/{b.id}: {ds.size} differ, {es.length} recorded"
      for d in ds do
        if d.cls != "INHERITED" then IO.println s!"[pass3-cliques]   {d.cls} {d.constant} {d.firstDiff}"
  IO.println s!"[pass3-cliques] twins: {total} differences; {unexpected.size} unrecorded, {stale.size} stale entries"
  for s in unexpected do IO.println s
  for s in stale do IO.println s!"[pass3-cliques] STALE {s}"
  problems := problems ++ unexpected.map (fun _ => "unrecorded twin difference") ++
    stale.map (s!"stale entry: " ++ ·)
  for p in problems do IO.println s!"[pass3-cliques] FAIL {p}"
  IO.println s!"[pass3-cliques] {problems.size} problem(s)"
  return if problems.isEmpty then 0 else 1

end Tests.Ix.Compile.Pass3Cliques
