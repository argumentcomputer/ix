/-
  compile-closure-whole: a closure compile agrees with the whole compile, and
  a closure carries whole logical units (M1-d; design document §6.2, the
  closure-against-whole theorem, and §6.3, "How it is checked").

  The whole environment is Init+Std: the environment of
  `Benchmarks/Compile/CompileInitStd.lean` (`import Init`, `import Std`, and
  one definition `id'`), elaborated at run time. It must be that environment
  and not the test environment restricted to Init+Std modules: an on-demand
  auxiliary of an Init block can be realised by any later module, under a
  private name of that module (the test environment has dozens of
  `_private.<M>.0.PSigma.casesOn._arg_pusher`, realised by Lean, Ix,
  Batteries and test modules), and by §6.3 those belong to the unit, so a
  closure drawn from the larger environment carries them. The whole
  environment is compiled once by the Lean pipeline (`compileLeanInput`), or
  read from a stored compile of the same file: `CLOSURE_WHOLE_ON=<ixe>` (the
  reference `initstd-a3.ixe`, the output of
  `ix compile-lean Benchmarks/Compile/CompileInitStd.lean`). Pass 3 only since
  M6R slice 6 (until then also the legacy surgery, `CLOSURE_WHOLE_OFF`
  = `initstd-a2.ixe`).

  For every root (a fixed list over the kinds that read their own unit,
  plus mutual inductive blocks, definition cliques and definitions with
  on-demand equation lemmas discovered in Init+Std; `CLOSURE_ROOTS=a,b,…`
  replaces the list), the closure is what `ix compile --consts` hands the
  compiler (`Ix.EnvScope.collectSelectedDeps`). Per root:

  1. the closure stays inside the whole environment;
  2. **whole units**: for every constant of the closure, every member of its
     declaration's logical unit that exists (`Lean.unitMembers`: the block,
     its eager auxiliaries and its on-demand ones) is in the closure;
  3. the closure compiles with no refusal;
  4. **closure against whole**: every name of the closure's output is in the
     whole output with the same `Named` entry (address, hence the
     constant's bytes, and metadata); address differences and
     metadata-only differences are counted separately;
  5. every constant of the closure is in the closure's output.
  6. **introduced references**: every closure carries the compiler's
     introduced references (`Ix.EnvScope.introducedSupport`, read from the
     compiler's own declarations: the Pass 3 images' packing and rule
     constants and the clique transport's prerequisites), and, derived from
     the output, every constant the closure's output references that the
     closure without them does not account for is carried (the set observed
     is printed);
  7. **local scope** of a collapse fixture
     (`Tests/Ix/Compile/Fixtures/LocalCollapse.lean`): it compiles with no
     refusal, decompiles to the source and passes `ix validate-lean --local`;
     the same closure without the introduced references is refused naming
     one of them (negative control).
  8. **the Rust compiler** (M6R slice 5): every closure of 3-5 and 7 compiled
     by the Rust compiler (`rsCompileEnvBytesFFI`, Pass 3, its only mode)
     gives the Lean compile's artifact byte for byte, so the Rust output of a
     closure carries the same units, `_ix` canonical constants and introduced
     references, and agrees with the whole compile (Rust's whole Init+Std
     compile is Lean's, the byte gates).

  Run with: `lake test -- --ignored compile-closure-whole`.
-/
import Ix.EnvScope
import Ix.CompileM
import Ix.CompileDriver
import Tests.Ix.Compile.Pass3

open Lean

namespace Tests.Ix.Compile.ClosureWhole

abbrev IxName := _root_.Ix.Name

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
  let names : Std.HashSet Name := whole.foldl (fun s (n, _) => s.insert n) {}
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

/-- The Rust compiler on the same closure (`rsCompileEnvBytesFFI`): its artifact must be the Lean compile's, byte for byte. Returns the
problem, if any. -/
def rustLeg (label : String) (env : Environment) (closure : List (Name × ConstantInfo))
    (mode : Bool) (lean : Ix.CompileM.LeanPipelineOut) : IO (Option String) := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closure).mapError toString)
  let constants ← IO.ofExcept input.prepare
  let dir ← IO.FS.createTempDir
  let path := dir / "rust.ixe"
  let status ← Ix.CompileM.rsCompileEnvBytesFFI constants path.toString true
  let bytes ← IO.FS.readBinFile path
  IO.FS.removeDirAll dir
  if bytes == lean.bytes && status.ungrounded.isEmpty then return none
  let rust ← IO.ofExcept (Ixon.deEnv bytes)
  let mut differ := 0
  let mut leanOnly := 0
  for (n, a) in lean.env.named do
    match rust.named.get? n with
    | some b => if a != b then differ := differ + 1
    | none => leanOnly := leanOnly + 1
  let rustOnly := (rust.named.toList.filter fun (n, _) => !lean.env.named.contains n).length
  return some s!"{label} mode={mode}: the Rust compile differs: Rust {bytes.size} B, Lean \
    {lean.bytes.size} B; Named entries different {differ}, Lean-only {leanOnly}, Rust-only \
    {rustOnly}; Rust failures {status.ungrounded.size}"

def loadOrCompile (env : Environment) (whole : List (Name × ConstantInfo)) (mode : Bool) :
    IO Ixon.Env := do
  let var := "CLOSURE_WHOLE_ON"
  if let some path ← IO.getEnv var then
    say s!"whole mode={mode}: reading {path}"
    return ← IO.ofExcept (Ixon.rsDeEnv (← IO.FS.readBinFile path))
  say s!"whole mode={mode}: compiling {whole.length} Init+Std constants"
  let unit : Tests.Ix.Compile.Pass3.CUnit :=
    { name := s!"initstd-whole-{mode}", env, seeds := #[], closure := whole }
  let out ← Tests.Ix.Compile.Pass3.compileUnit unit
  unless out.cenv.ungrounded.isEmpty do
    throw (IO.userError s!"whole mode={mode}: {out.cenv.ungrounded.size} refusals")
  return out.env

/-- The references the closure's output makes that no constant of the
closure *without* the compiler's introduced references (`base`) accounts
for: derived from the output, not from a list. Every such reference must be
carried by the producer's closure (`full`). `_ix` names (the compiler's own
canonical constants) are not references into the input. -/
def introducedRefs (out : Ix.CompileM.LeanPipelineOut) (base full : Std.HashSet Name) :
    Std.HashSet Name × Array String := Id.run do
  let names : Std.HashMap Address (Array IxName) := out.env.named.fold (init := {}) fun m n nd =>
    m.insert nd.addr ((m.getD nd.addr #[]).push n)
  let mut seen : Std.HashSet Address := {}
  let mut intro : Std.HashSet Name := {}
  let mut bad : Array String := #[]
  for (n0, nd) in out.env.named do
    -- only the references of constants the closure has without the introduced
    -- references (and of the compiler's own `_ix` constants): what a pass put there
    let ln0 := Tests.Ix.Compile.Pass3.toLeanName n0
    unless base.contains ln0 || ln0.components.contains `_ix do continue
    if seen.contains nd.addr then continue
    seen := seen.insert nd.addr
    let some (k, _) := Tests.Ix.Compile.Pass3.ixonBody out.env nd.addr | continue
    for x in k.refs do
      let ns := (names.getD x #[]).map Tests.Ix.Compile.Pass3.toLeanName
      if ns.isEmpty then continue
      if ns.any base.contains || ns.any (fun n => n.components.contains `_ix) then continue
      for n in ns do intro := intro.insert n
      unless ns.any full.contains do bad := bad.push s!"{ns} is referenced but not carried"
  return (intro, bad)

/-- The local scope of a collapse fixture (the corpus
sweep's `compile-lean --local` defect): the selected closure of the file's
own constants compiles with no refusal and decompiles to the source, and
`ix validate-lean --local` passes. Negative control:
the same closure without the compiler's introduced references is refused,
naming one of them. -/
def localCollapse : IO (Array String) := do
  let file := "Tests/Ix/Compile/Fixtures/LocalCollapse.lean"
  let env ← getFileEnv file
  let own := env.constants.toList.filterMap fun (n, _) =>
    if (env.getModuleIdxFor? n).isNone then some n else none
  let full := Ix.EnvScope.collectSelectedDeps env own
  -- the scope as `--local` had it before M1-d (recursors only: no units, no
  -- introduced references), which the corpus sweep found refused
  let noSupport := Ix.EnvScope.collectDeps env own (withRecursors := true)
  let mut errors : Array String := #[]
  let u : Tests.Ix.Compile.Pass3.CUnit := { name := "local-collapse", env, seeds := own.toArray, closure := full }
  let out ← Tests.Ix.Compile.Pass3.compileUnit u
  unless out.cenv.ungrounded.isEmpty do
    errors := errors.push s!"local collapse: {out.cenv.ungrounded.size} refusals, first \
      {out.cenv.ungrounded.toList.head?}"
  match ← rustLeg "local collapse" env full true out with
  | none => say "local collapse: the Rust compile is byte-identical with the Lean compile"
  | some e => errors := errors.push e
  let (de, summary) ← Tests.Ix.Compile.Pass3.decompileCheck u out
  errors := errors ++ de.map (s!"local collapse: {·}")
  let baseNames : Std.HashSet Name := (Ix.EnvScope.collectDeps env own (withRecursors := true)
    (withCompilerSupport := true) (withCheckerSupport := true) (withUnits := true)).foldl (fun s (n, _) => s.insert n) {}
  let fullNames : Std.HashSet Name := full.foldl (fun s (n, _) => s.insert n) {}
  let (intro, bad) := introducedRefs out baseNames fullNames
  errors := errors ++ bad.map (s!"local collapse: {·}")
  say s!"local collapse: references introduced by the output (derived): {intro.toList.map toString |>.toArray.qsort (· < ·)}"
  say s!"local collapse: closure {full.length} (the pre-M1-d scope \
    {noSupport.length}); {out.cenv.ungrounded.size} refusals; {summary}"
  let neg : List (String × String) ← try
      let o ← Tests.Ix.Compile.Pass3.compileUnit { u with closure := noSupport }
      pure (o.cenv.ungrounded.toList.map fun (n, m) => (n.pretty, m))
    catch e => pure [("compile", toString e)]
  let support := ["True", "And", "PProd", "PUnit", "Eq"]
  if neg.isEmpty then
    errors := errors.push "local collapse: the negative control compiled (the fixture does not exercise the scope defect)"
  else unless neg.any (fun (_, m) => support.any fun s => (m.splitOn s!"missingConstant: {s}").length > 1) do
    errors := errors.push s!"local collapse: the negative control fails for another reason: {neg.head?}"
  say s!"local collapse negative control (the pre-M1-d scope: recursors only): {neg.length} refusal(s), first {neg.head?}"
  let exe ← IO.FS.realPath (".lake" / "build" / "bin" / "ix")
  let args : Array String := #["validate-lean", "--local", "--workers", "8", file]
  let r ← IO.Process.output { cmd := exe.toString, args := args, env := #[("IX_PASS3", none)] }
  let verdict := (r.stdout.splitOn "\n").filter (fun l => (l.splitOn "VERDICTS").length > 1)
  say s!"local collapse: ix validate-lean --local: exit {r.exitCode}; {verdict}"
  if r.exitCode != 0 then errors := errors.push s!"local collapse: validate-lean --local exit {r.exitCode}"
  return errors

def run : IO UInt32 := do
  let env ← getFileEnv "Benchmarks/Compile/CompileInitStd.lean"
  let whole := env.constants.toList
  let wholeNames : Std.HashSet Name := whole.foldl (fun s (n, _) => s.insert n) {}
  let roots ← match ← IO.getEnv "CLOSURE_ROOTS" with
    | some s => pure ((s.splitOn ",").filter (!·.isEmpty) |>.map String.toName)
    | none => pure (fixedRoots ++ discoveredRoots whole 3)
  let mut errors : Array String := #[]
  for r in roots do
    unless wholeNames.contains r do errors := errors.push s!"root {r} is not in the whole environment"
  say s!"Init+Std: {whole.length} constants; {roots.length} roots: {roots}"
  let units := Lean.unitIndex env.constants
  -- the closures and their units
  let mut closures : Array (Name × List (Name × ConstantInfo) × Std.HashSet Name) := #[]
  let support := Ix.EnvScope.introducedSupport env
  let mut unitChecks := 0
  for r in roots do
    let c := Ix.EnvScope.collectSelectedDeps env [r]
    let cn : Std.HashSet Name := c.foldl (fun s (n, _) => s.insert n) {}
    for (n, _) in c do
      unless wholeNames.contains n do errors := errors.push s!"{r}: closure leaves the whole environment at {n}"
      for u in Lean.unitMembers env.constants units n do
        unitChecks := unitChecks + 1
        unless cn.contains u do errors := errors.push s!"{r}: {n} is carried without {u} of its unit"
    for s in support do
      unless cn.contains s do errors := errors.push s!"{r}: the introduced reference {s} is not carried"
    let base := (Ix.EnvScope.collectDeps env [r] (withRecursors := true) (withCompilerSupport := true)
      (withCheckerSupport := true) (withUnits := true)).foldl (fun (s : Std.HashSet Name) (n, _) => s.insert n) {}
    closures := closures.push (r, c, base)
  say s!"introduced references carried by every closure: {support}"
  say s!"closures: {closures.map (·.2.1.length) |>.foldl (· + ·) 0} constants over {roots.length} \
    roots; {unitChecks} unit memberships checked"
  -- Pass 3 only (until M6R slice 6 also the legacy surgery, `mode=false`)
  for mode in [true] do
    let ref ← loadOrCompile env whole mode
    let mut compared := 0
    let mut addrDiffs := 0
    let mut metaDiffs := 0
    let mut missing := 0
    let mut introduced : Std.HashSet Name := {}
    let mut rustSame := 0
    for (r, c, base) in closures do
      let unit : Tests.Ix.Compile.Pass3.CUnit :=
        { name := s!"closure-{r}", env, seeds := #[r], closure := c }
      let out ← Tests.Ix.Compile.Pass3.compileUnit unit
      unless out.cenv.ungrounded.isEmpty do
        errors := errors.push s!"{r} mode={mode}: {out.cenv.ungrounded.size} refusals, first \
          {(out.cenv.ungrounded.toList.head?.map (·.1.pretty))}"
      -- 8. the Rust compiler on the same closure
      match ← rustLeg s!"{r}" env c mode out with
      | none => rustSame := rustSame + 1
      | some e => errors := errors.push e
      for (n, _) in c do
        unless out.env.named.contains (Tests.Ix.Compile.Pass3.ixN n) do
          missing := missing + 1
          errors := errors.push s!"{r} mode={mode}: {n} is not in the closure's output"
      let mut a := 0
      let mut m := 0
      for (name, named) in out.env.named do
        compared := compared + 1
        match ref.named[name]? with
        | none =>
          a := a + 1
          errors := errors.push s!"{r} mode={mode}: {name.pretty} is not in the whole output"
        | some w =>
          if named.addr != w.addr then
            a := a + 1
            if a ≤ 5 then
              errors := errors.push s!"{r} mode={mode}: {name.pretty}: {named.addr} in the closure, \
                {w.addr} in the whole compile"
          else if named != w then
            m := m + 1
            if m ≤ 5 then errors := errors.push s!"{r} mode={mode}: {name.pretty}: metadata differs"
      if a > 5 then errors := errors.push s!"{r} mode={mode}: … {a - 5} more address differences"
      if m > 5 then errors := errors.push s!"{r} mode={mode}: … {m - 5} more metadata differences"
      let cn : Std.HashSet Name := c.foldl (fun s (n, _) => s.insert n) {}
      let (intro, bad) := introducedRefs out base cn
      introduced := intro.fold (·.insert ·) introduced
      errors := errors ++ bad.map (s!"{r} mode={mode}: {·}")
      addrDiffs := addrDiffs + a
      metaDiffs := metaDiffs + m
      say s!"mode={mode} {r}: closure {c.length}, output {out.env.named.size} names; {a} address, \
        {m} metadata differences"
    say s!"mode={mode}: {roots.length} roots, {compared} carried names compared with the whole \
      compile: {addrDiffs} address differences, {metaDiffs} metadata differences, {missing} \
      closure constants missing from the output; references introduced by the output (derived): \
      {introduced.toList.map toString |>.toArray.qsort (· < ·)}"
    say s!"mode={mode}: Rust compiler on the same closures: {rustSame}/{closures.size} \
      byte-identical with the Lean compile"
  errors := errors ++ (← localCollapse)
  for e in errors do say s!"FAIL {e}"
  say s!"{if errors.isEmpty then "PASS" else s!"FAIL ({errors.size})"}"
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.ClosureWhole
