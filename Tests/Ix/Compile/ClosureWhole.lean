import Ix.Meta
import Ix.EnvScope
import Ix.CompileCertified
import Tests.Ix.Compile.ClosureHarness

/-!
  compile-closure-whole: a closure compile agrees with the whole compile,
  and a closure carries whole logical units. The harness compares each
  selected closure's compiled names and metadata with the whole artifact.

  The whole environment is Init+Std: the environment of
  `Benchmarks/Compile/CompileInitStd.lean` (`import Init`, `import Std` and
  a few definitions), elaborated at run time. It must not be the test
  environment restricted to Init+Std modules. Any later module can realise
  an on-demand auxiliary of an Init block under a private name of its own
  (the test environment has dozens of
  `_private.<M>.0.PSigma.casesOn._arg_pusher`). These belong to the logical
  unit, so a closure drawn from the larger environment carries them.

  The whole compile is read from `CLOSURE_WHOLE_IXE=<ixe>` when it is set.
  That must be a whole-environment compile of that file by this tree, for
  example `ix compile Benchmarks/Compile/CompileInitStd.lean --out <ixe>`.
  The test compares its stored Named entries with the closure outputs.
  Otherwise the whole environment is compiled once by the streamed Lean
  pipeline through `ClosureHarness.compileClosure`.

  Roots: a fixed list over the kinds that read their own unit, plus the
  first mutual inductive blocks, size functions of mutual blocks,
  definition cliques and definitions with an on-demand `eq_def` of
  Init+Std. `CLOSURE_ROOTS=a,b,…` replaces the list. A root's closure is
  the selected closure (`Ix.EnvScope.collectSelectedDeps`). Per root:

  1. the closure stays inside the whole environment;
  2. **whole units**: for every constant of the closure, every existing
     member of its declaration's logical unit (`Ix.EnvScope.unitMembers`:
     the block, its eager auxiliaries and its on-demand ones) is in the
     closure;
  3. the closure compiles with no refusal;
  4. **closure against whole**: every name of the closure's output is in
     the whole output with the same `Named` entry: the address (hence the
     constant's bytes) and the metadata. Each difference is classified:
     absent, address, or the metadata fields that differ (`constMeta`,
     `original`, `hints`). The classes are counted. Every difference
     fails the run: classify, never waive. Both sides are compared as read
     back from their bytes (`Ixon.rsDeEnv`), so the stored-file and
     in-process modes compare one representation;
  5. every constant of the closure is in the closure's output;
  6. **carried support**: every closure carries the library support every
     selected closure carries (`Ix.EnvScope.introducedSupport`), and,
     derived from the output, every constant the closure's output references
     that the closure without that support does not account for is carried
     (the set observed is printed);
  7. **local scope** of a mutual-inductive fixture
     (`Tests/Ix/Compile/Fixtures/LocalCollapse.lean`): its selected closure
     (the `--local` scope) compiles with no refusal, the certified compile is
     byte-identical, it decompiles to the source, its output introduces no
     reference, and `ix validate-lean --ns LocalCollapse` passes all
     five phases, including source/reader fidelity; the same closure with
     recursors only (without that support) also compiles with no refusal;
  8. **the certified compiler**: the certified compile of every closure
     is the streamed Lean compile's artifact, byte for
     byte.

  Run with: `lake test -- --ignored compile-closure-whole`.
-/

open Lean
open Tests.Ix.Compile.ClosureHarness

namespace Tests.Ix.Compile.ClosureWhole

def say (s : String) : IO Unit := do
  IO.println s!"[closure-whole] {s}"
  (← IO.getStdout).flush

/-- Roots over the kinds that read their own unit or a sibling's: structural
and well-founded recursion with equation lemmas, a nested inductive, a
structure, theorems, a `Std` container operation. -/
def fixedRoots : List Name :=
  [``Nat.add, ``Nat.gcd, ``List.map, ``List.foldl, ``Array.foldlM, ``Lean.Syntax,
   ``String.splitOn, ``Std.HashMap.insert, ``Nat.lt_irrefl, ``List.length_append,
   ``Prod.mk.injEq, ``Option.map]

/-- Discovered roots: the first `k` (by name) mutual inductive blocks, size
functions of mutual blocks, definition cliques, and definitions with an
on-demand `eq_def`. -/
def discoveredRoots (whole : List (Name × ConstantInfo)) (k : Nat) : List Name := Id.run do
  let names := nameSet whole
  let sorted := (whole.toArray.qsort fun a b => a.1.toString < b.1.toString)
  let mut ind : Array Name := #[]
  let mut size : Array Name := #[]
  let mut clq : Array Name := #[]
  let mut eqd : Array Name := #[]
  for (n, ci) in sorted do
    match ci with
    | .inductInfo v =>
      if v.all.length ≥ 2 && v.all.head? == some n then
        if ind.size < k then ind := ind.push n
        if size.size < k && names.contains (n.str "_sizeOf_1") then size := size.push (n.str "_sizeOf_1")
    | .defnInfo v =>
      if v.all.length ≥ 2 && v.all.head? == some n && clq.size < k then clq := clq.push n
      if eqd.size < k && names.contains (n.str "eq_def") && v.all.length == 1 then eqd := eqd.push n
    | .thmInfo v =>
      if v.all.length ≥ 2 && v.all.head? == some n && clq.size < k then clq := clq.push n
    | _ => pure ()
  return (ind ++ size ++ clq ++ eqd).toList

/-- The whole compile: `CLOSURE_WHOLE_IXE` when set, otherwise the certified
parallel ready-queue compile (`binderData := false`, matching `compileClosure`
bit-for-bit without redundant wave barriers or `serEnv`/`rsDeEnv`). -/
def loadOrCompile (env : Environment) (whole : List (Name × ConstantInfo)) : IO Ixon.Env := do
  if let some path ← IO.getEnv "CLOSURE_WHOLE_IXE" then
    say s!"whole: reading {path}"
    return ← readIxe path
  say s!"whole: compiling {whole.length} Init+Std constants (certified parallel pipeline, binderData := false)"
  let out ← IO.ofExcept (← Ix.CompileM.compileCertified env whole 32 (binderData := false))
  unless out.failures.isEmpty do
    throw (IO.userError s!"whole: {out.failures.toMap.size} refusals")
  return out.env

/-- The references of the constant at `addr` (a projection's are its block's). -/
def constRefs (env : Ixon.Env) (addr : Address) : Array Address :=
  let blockRefs := fun (b : Address) => ((env.getConst? b).map (·.refs)).getD #[]
  match env.getConst? addr with
  | none => #[]
  | some c => match c.info with
    | .dPrj p => blockRefs p.block
    | .rPrj p => blockRefs p.block
    | .iPrj p => blockRefs p.block
    | .cPrj p => blockRefs p.block
    | _ => c.refs

/-- 6. The references the closure's output makes that no constant of the
closure *without* the carried library support (`base`) accounts
for: derived from the output, not from a list. Every such reference must be
carried by the producer's closure (`full`). `_ix` names (the compiler's own
canonical constants) are not references into the input. -/
def introducedRefs (out : Ixon.Env) (base full : Std.HashSet Name) :
    Std.HashSet Name × Array String := Id.run do
  let names : Std.HashMap Address (Array Name) := out.named.fold (init := {}) fun m n nd =>
    m.insert nd.addr ((m.getD nd.addr #[]).push (toLeanName n))
  let isIx (n : Name) : Bool := n.components.contains `_ix
  let mut seen : Std.HashSet Address := {}
  let mut intro : Std.HashSet Name := {}
  let mut bad : Array String := #[]
  for (n0, nd) in out.named do
    -- only the references of constants the closure has without the introduced
    -- references (and of the compiler's own `_ix` constants): what a pass put there
    let ln0 := toLeanName n0
    unless base.contains ln0 || isIx ln0 do continue
    if seen.contains nd.addr then continue
    seen := seen.insert nd.addr
    for x in constRefs out nd.addr do
      let ns := names.getD x #[]
      if ns.isEmpty || ns.any base.contains || ns.any isIx then continue
      for n in ns do intro := intro.insert n
      unless ns.any full.contains do bad := bad.push s!"{ns} is referenced but not carried"
  return (intro, bad)

/-- A name set, sorted, for printing. -/
def sortedNames (s : Std.HashSet Name) : Array String :=
  s.toList.map toString |>.toArray.qsort (· < ·)

/-- The actual LocalCollapse report gate: all five phases, with explicit
nonzero source coverage for the source/reader comparison. -/
def localPhaseProblems (exitCode : UInt32) (phases : Array (String × String × String)) :
    Array String := Id.run do
  let mut errors := #[]
  if exitCode != 0 then errors := errors.push s!"local collapse: validate-lean exit {exitCode}"
  if phases.size != 5 then errors := errors.push s!"local collapse: expected 5 phase rows, got {phases.size}"
  for key in ["1.", "2.", "3.", "4.", "5."] do
    let rows := phases.filter (·.1.startsWith key)
    let [(name, result, detail)] := rows.toList
      | errors := errors.push s!"local collapse: expected one phase {key} row, got {rows.size}"
        continue
    unless result == "pass" do
      errors := errors.push s!"local collapse: validate-lean {name}: {result}: {detail}"
    if key == "4." then
      unless name == "4. Source/reader fidelity" do
        errors := errors.push s!"local collapse: wrong phase-4 scope: {name}"
      let coverage : Option (Nat × Nat) := do
        let [line] := (detail.splitOn "\n").filter (·.startsWith "source coverage:") | none
        let ["source", "coverage:", counts, "named", "constants"] := line.splitOn " " | none
        let [checked, expected] := counts.splitOn "/" | none
        return (← checked.toNat?, ← expected.toNat?)
      unless coverage.any (fun (checked, expected) => checked > 0 && checked == expected) do
        errors := errors.push "local collapse: phase 4 lacks complete nonzero source coverage"
  return errors

private structure RootCheckResult where
  root : Name
  closureLen : Nat
  namedSize : Nat
  compared : Nat
  addrDiffs : Nat
  metaDiffs : Nat
  missing : Nat
  classes : Std.HashMap String Nat
  introduced : Std.HashSet Name
  errors : Array String

private def checkRootClosure (env : Environment) (ref : Ixon.Env)
    (r : Name) (c : List (Name × ConstantInfo)) (base : Std.HashSet Name) :
    IO RootCheckResult := do
  let out ← compileClosure env c (workers := 4) (serialize := false)
  let mut errors : Array String := #[]
  -- 3. no refusal
  unless out.cenv.ungrounded.isEmpty do
    errors := errors.push s!"{r}: {out.cenv.ungrounded.size} refusals, first \
      {out.cenv.ungrounded.toList.head?.map (·.1.pretty)}"
  let outEnv := out.env
  -- 5. every closure constant is in the output
  let mut missing := 0
  for (n, _) in c do
    unless outEnv.named.contains (ixN n) do
      missing := missing + 1
      errors := errors.push s!"{r}: {n} is not in the closure's output"
  -- 4. closure against whole, classified
  let mut compared := 0
  let mut a := 0
  let mut m := 0
  let mut classes : Std.HashMap String Nat := {}
  for (name, named) in outEnv.named do
    compared := compared + 1
    let cls? := match ref.named[name]? with
      | none => some "absent from the whole output"
      | some w => namedDiff named w
    let some cls := cls? | continue
    classes := classes.insert cls (classes.getD cls 0 + 1)
    if cls.startsWith "metadata" then
      m := m + 1
      if m ≤ 5 then errors := errors.push s!"{r}: {name.pretty}: {cls} differs from the whole compile"
    else
      a := a + 1
      if a ≤ 5 then
        let w := (ref.named[name]?).map (toString ·.addr) |>.getD "none"
        errors := errors.push s!"{r}: {name.pretty}: {cls}: {named.addr} in the closure, \
          {w} in the whole compile"
  if a > 5 then errors := errors.push s!"{r}: … {a - 5} more address differences"
  if m > 5 then errors := errors.push s!"{r}: … {m - 5} more metadata differences"
  -- 6. the references the output introduces are carried
  let (intro, bad) := introducedRefs outEnv base (nameSet c)
  errors := errors ++ bad.map (s!"{r}: {·}")
  return {
    root := r, closureLen := c.length, namedSize := outEnv.named.size
    compared, addrDiffs := a, metaDiffs := m, missing, classes, introduced := intro, errors }

def run : IO UInt32 := do
  let env ← getFileEnv "Benchmarks/Compile/CompileInitStd.lean"
  let whole := env.constants.toList
  let wholeNames := nameSet whole
  let requested ← match ← IO.getEnv "CLOSURE_ROOTS" with
    | some s => pure ((s.splitOn ",").filter (!·.isEmpty) |>.map String.toName)
    | none => pure (fixedRoots ++ discoveredRoots whole 3)
  let mut errors : Array String := #[]
  for r in requested do
    unless wholeNames.contains r do errors := errors.push s!"root {r} is not in the whole environment"
  let roots := requested.filter wholeNames.contains
  say s!"Init+Std: {whole.length} constants; {roots.length} roots: {roots}"
  -- 1, 2: the closures and their units (one unit index for every check)
  let units := Ix.EnvScope.unitIndex env.constants
  let mut closures : Array (Name × List (Name × ConstantInfo) × Std.HashSet Name) := #[]
  let mut unitChecks := 0
  -- 6: the carried library support
  let support := Ix.EnvScope.introducedSupport env
  for r in roots do
    let c := Ix.EnvScope.collectSelectedDepsWith env units [r]
    let cn := nameSet c
    for (n, _) in c do
      unless wholeNames.contains n do
        errors := errors.push s!"{r}: the closure leaves the whole environment at {n}"
      for u in Ix.EnvScope.unitMembers env.constants units n do
        unitChecks := unitChecks + 1
        unless cn.contains u do errors := errors.push s!"{r}: {n} is carried without {u} of its unit"
    for s in support do
      unless cn.contains s do errors := errors.push s!"{r}: the introduced reference {s} is not carried"
    -- the closure without the introduced references, for the derived check
    let base := nameSet (Ix.EnvScope.collectDepsWith env units [r] .selected)
    closures := closures.push (r, c, base)
  say s!"introduced references carried by every closure: {support}"
  say s!"closures: {closures.foldl (· + ·.2.1.length) 0} constants over {roots.length} roots; \
    {unitChecks} unit memberships checked"
  -- 3, 4, 5: each closure compiled in parallel batches, against the whole compile
  let ref ← loadOrCompile env whole
  let mut compared := 0
  let mut addrDiffs := 0
  let mut metaDiffs := 0
  let mut classes : Std.HashMap String Nat := {}
  let mut missing := 0
  let mut introduced : Std.HashSet Name := {}
  let maxConc := 8
  for start in [0:closures.size:maxConc] do
    let stop := min (start + maxConc) closures.size
    let mut tasks : Array (Task (Except IO.Error RootCheckResult)) :=
      Array.emptyWithCapacity (stop - start)
    for (r, c, base) in closures.extract start stop do
      tasks := tasks.push (← IO.asTask (prio := .dedicated) (checkRootClosure env ref r c base))
    for task in tasks do
      let res ← match ← IO.wait task with
        | .ok res => pure res
        | .error e => throw e
      compared := compared + res.compared
      addrDiffs := addrDiffs + res.addrDiffs
      metaDiffs := metaDiffs + res.metaDiffs
      missing := missing + res.missing
      for (cls, count) in res.classes do
        classes := classes.insert cls (classes.getD cls 0 + count)
      introduced := res.introduced.fold (·.insert ·) introduced
      errors := errors ++ res.errors
      say s!"{res.root}: closure {res.closureLen}, output {res.namedSize} names; {res.addrDiffs} address, \
        {res.metaDiffs} metadata differences"
  let classLine := classes.toList.map (fun (k, v) => s!"{k} {v}") |>.toArray.qsort (· < ·)
  say s!"{roots.length} roots, {compared} carried names compared with the whole compile: \
    {addrDiffs} address differences, {metaDiffs} metadata differences (classes: {classLine}), \
    {missing} closure constants missing from the output"
  say s!"references introduced by the outputs (derived): {sortedNames introduced}"
  for e in errors do say s!"FAIL {e}"
  say s!"{if errors.isEmpty then "PASS" else s!"FAIL ({errors.size})"}"
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.ClosureWhole
