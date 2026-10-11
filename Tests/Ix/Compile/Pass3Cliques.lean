/-
  pass3-cliques: changed definition cliques under Pass 3 (the only mode since
  M6R slice 6; `Ix.Compile.Pass.Cliques`, design document §5).

  One compile unit, the closure of every clique twin family
  (`Tests/Ix/Compile/Twins/Cliques.lean`), compiled by the Lean pipeline:

  1. **plans**: every clique of the fixtures, as the compiler planned it
     (`Ix.Compile.Pass.planClique` against the compile state):
     encoding, Lean's order, `σ`, the source of the order, the outcome
     (transported, unchanged, baseline with its cause, not encoded) and the
     transport's causes;
  2. **names**: every named entry of the output is an input constant, a
     reserved `_ix` name or a synthetic `Muts` name (`Pass3.namesCheck`), and
     no block fails (until M6R slice 6 this step compared the output with the
     legacy surgery's, `IX_PASS3=off`: every moved name in a transported
     clique's cone; that mode is deleted);
  3. **decompile**: the output decompiles to the source constants
     (the members through their `_ix.inline` records);
  4. **kernels**: `ix check-rs`, `ix check-lean` (meta mode) and the
     certified checker on every fixture constant and every `_ix` constant of
     the output (the value pins `rfl` over clique members among
     them);
  5. **twins**: for every presentation pair, every Lean name
     compiles to the reference's address, except the entries of the switch-on
     non-canonical set (`Tests.Ix.Compile.NonCanonical.nonCanonicalOn`), which
     is exact in both directions. The canonical `_ix` constants are stored
     only where a member or a carried lemma reaches them, by address, so equal
     members imply equal canonical constants; an `_ix` name both sides carry
     with different addresses is logged (`canonical constant differs`).

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

/-- The cliques among Lean constants (M.1: `all` with two or more members, of a
safe definition or a theorem), each once, as Lean names. -/
def leanCliques (cs : List (Name × ConstantInfo)) : Array (Array Name) := Id.run do
  let mut out := #[]
  for (n, ci) in cs do
    let (all, ok) := match ci with
      | .defnInfo v => (v.all, v.safety == Lean.DefinitionSafety.safe)
      | .thmInfo v => (v.all, true)
      | _ => ([], false)
    if ok && all.length ≥ 2 && all.head? == some n then out := out.push all.toArray
  return out

/-- Every clique, planned as the compiler planned it. -/
def plans (on : Ix.CompileM.LeanPipelineOut) (cliques : Array (Array Name)) : Array PlanRow := Id.run do
  let cenv := on.cenv
  let const? := cenv.env.get?
  let mut out : Array PlanRow := #[]
  for cl in cliques do
    let all := cl.map _root_.Ix.Name.fromLeanName
    let some n := all[0]? | continue
    let row : PlanRow := match cenv.p3Cliques.get? n with
      | none => { all, outcome := "not in the clique table (no encoding marker, or members in one block)", transported := false }
      | some (_, carried) =>
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

/-! ## A library (`PASS3_CLIQUES_FILE=<file.lean>`) -/

/-- Compile a file's environment as `ix compile-lean` does, and list every clique of it as the compiler planned it; optionally write
the output (`PASS3_CLIQUES_OUT`) and check the transported and canonical
constants with the three kernels (`PASS3_CLIQUES_KERNELS=1`). -/
def runFile (path : String) : IO UInt32 := do
  let fe ← getFileEnvCore path
  let constList ← Ix.EnvScope.defaultConstList fe path
  IO.println s!"[pass3-cliques-file] {path}: {constList.length} constants"
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv fe.env constList).mapError toString)
  let t0 ← IO.monoMsNow
  let on ← match ← Ix.CompileM.compileLeanInput input (numWorkers := 32) with
    | .ok o => pure o
    | .error e => throw (IO.userError s!"compile failed: {e}")
  IO.println s!"[pass3-cliques-file] compiled: {on.bytes.size} B, {on.cenv.ungrounded.size} block failures, \
    {(← IO.monoMsNow) - t0} ms"
  -- every caller refused by the block rule (`Ix.Compile.Pass.cliqueCallers`),
  -- then the first other failures
  let (refused, other) := on.cenv.ungrounded.toList.partition fun (_, e) =>
    (e.splitOn "caller refused").length > 1
  IO.println s!"[pass3-cliques-file] callers refused (block rule): {refused.length}"
  for (n, e) in refused.toArray.qsort (fun a b => a.1.pretty < b.1.pretty) do
    IO.println s!"[pass3-cliques-file]   refused: {n.pretty}: {e}"
  for (n, e) in other.take 20 do
    IO.println s!"[pass3-cliques-file]   failed: {n.pretty}: {e.take 300}"
  if let some out := ← IO.getEnv "PASS3_CLIQUES_OUT" then
    IO.FS.writeBinFile out on.bytes
  -- the cliques
  let rows := plans on (leanCliques constList)
  let mut tally : Std.HashMap String Nat := {}
  let mut members : Array String := #[]
  for r in rows do
    IO.println s!"[pass3-cliques-file] clique {r.all.map (·.pretty)}: {r.outcome}"
    let key := (r.outcome.splitOn " ").headD "?"
    tally := tally.insert key (tally.getD key 0 + 1)
    if r.transported then members := members ++ r.all.map (·.pretty)
  IO.println s!"[pass3-cliques-file] {rows.size} cliques of two or more members: {tally.toList}"
  let table := on.cenv.p3Cliques.toList.filter fun (n, (all, _)) => all[0]? == some n
  IO.println s!"[pass3-cliques-file] clique table: {table.length} cliques, \
    {(table.foldl (fun acc (_, (_, c)) => acc + c.size) 0)} carried lemmas"
  if (← IO.getEnv "PASS3_CLIQUES_KERNELS") == some "1" then
    let dir ← IO.FS.createTempDir
    try
      let p := dir / "on.ixe"
      IO.FS.writeBinFile p on.bytes
      let carried := table.foldl (fun acc (_, (_, c)) => acc ++ c.map (·.pretty)) #[]
      let names := (on.env.named.toArray.filterMap fun (n, _) =>
        if Ix.Compile.Pass.hasReserved n then some n.pretty else none) ++ members ++ carried
      let failed ← Tests.Ix.Compile.Pass3.kernelFailures dir p names
      IO.println s!"[pass3-cliques-file] kernels: {names.size} names, {failed.size} failure(s)"
      for (leg, n, m) in failed.toList.take 40 do
        IO.println s!"[pass3-cliques-file]   {leg}: {n}: {m.take 240}"
      return if failed.isEmpty then 0 else 1
    finally IO.FS.removeDirAll dir
  return 0

/-! ## The suite -/

def run (env : Environment) : IO UInt32 := do
  if let some p := ← IO.getEnv "PASS3_CLIQUES_FILE" then return ← runFile p
  let only := ← IO.getEnv "PASS3_CLIQUES_ONLY"
  let keep? := (← IO.getEnv "PASS3_KEEP").map System.FilePath.mk
  let dumpDir := (← IO.getEnv "IX_TWINS_DUMP").map System.FilePath.mk
  if let some d := dumpDir then IO.FS.createDirAll d
  let families := (Tests.Ix.Compile.Twins.cliqueFamilies ++ Tests.Ix.Compile.Twins.ownershipFamilies).filter fun f =>
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
  let on ← Tests.Ix.Compile.Pass3.compileUnit u
  IO.println s!"[pass3-cliques] compile: {on.bytes.size} B ({on.cenv.ungrounded.size} failures), \
    {(← IO.monoMsNow) - t0} ms"
  let mut problems : Array String := #[]
  for (n, e) in on.cenv.ungrounded do
    problems := problems.push s!"{n.pretty} fails: {e.take 300}"
  -- 1. plans
  let rows := plans on (leanCliques (seeds.toList.filterMap fun n => (env.find? n).map (n, ·)))
  let mut nT := 0
  for r in rows do
    IO.println s!"[pass3-cliques] clique {r.all.map (·.pretty)}: {r.outcome}"
    if r.transported then
      nT := nT + 1
  IO.println s!"[pass3-cliques] {rows.size} cliques, {nT} transported"
  -- 2. names
  let nr := Tests.Ix.Compile.Pass3.namesCheck u on
  IO.println s!"[pass3-cliques] names: {nr.inputNames} input constants, {nr.reserved} reserved, \
    {nr.problems.size} problem(s)"
  problems := problems ++ nr.problems
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
    let r ← Tests.Ix.Compile.Pass3.kernelRun dir path names
    let names := r.targets
    let nIx := (names.filter fun s => (s.splitOn "._ix").length > 1).size
    -- no failure is recorded (the empty record), and every leg checks every name
    let (kprob, ksum) := Tests.Ix.Compile.Pass3Kernels.check [] "cliques" "on" r.failed r.checked
      names.size
    IO.println s!"[pass3-cliques] kernels: {names.size} names ({nIx} `_ix`), {ksum}"
    problems := problems ++ kprob.map (s!"kernel " ++ ·)
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
