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
  environment is compiled once per switch state by the Lean pipeline
  (`compileLeanInput`), or read from a stored compile of the same file:
  `CLOSURE_WHOLE_OFF=<ixe>` / `CLOSURE_WHOLE_ON=<ixe>` (the reference
  `initstd-a2.ixe` and the switch-on output of
  `ix compile-lean Benchmarks/Compile/CompileInitStd.lean`).

  For every root (a fixed list over the kinds that read their own unit,
  plus mutual inductive blocks, definition cliques and definitions with
  on-demand equation lemmas discovered in Init+Std; `CLOSURE_ROOTS=a,b,…`
  replaces the list), the closure is what `ix compile --consts` hands the
  compiler (`Ix.EnvScope.collectSelectedDeps`). Per root and switch state:

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

def loadOrCompile (env : Environment) (whole : List (Name × ConstantInfo)) (mode : Bool) :
    IO Ixon.Env := do
  let var := if mode then "CLOSURE_WHOLE_ON" else "CLOSURE_WHOLE_OFF"
  if let some path ← IO.getEnv var then
    say s!"whole mode={mode}: reading {path}"
    return ← IO.ofExcept (Ixon.rsDeEnv (← IO.FS.readBinFile path))
  say s!"whole mode={mode}: compiling {whole.length} Init+Std constants"
  let unit : Tests.Ix.Compile.Pass3.CUnit :=
    { name := s!"initstd-whole-{mode}", env, seeds := #[], closure := whole }
  let out ← Tests.Ix.Compile.Pass3.compileUnit unit mode
  unless out.cenv.ungrounded.isEmpty do
    throw (IO.userError s!"whole mode={mode}: {out.cenv.ungrounded.size} refusals")
  return out.env

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
  -- the closures and their units (independent of the switch)
  let mut closures : Array (Name × List (Name × ConstantInfo)) := #[]
  let mut unitChecks := 0
  for r in roots do
    let c := Ix.EnvScope.collectSelectedDeps env [r]
    let cn : Std.HashSet Name := c.foldl (fun s (n, _) => s.insert n) {}
    for (n, _) in c do
      unless wholeNames.contains n do errors := errors.push s!"{r}: closure leaves the whole environment at {n}"
      for u in Lean.unitMembers env.constants units n do
        unitChecks := unitChecks + 1
        unless cn.contains u do errors := errors.push s!"{r}: {n} is carried without {u} of its unit"
    closures := closures.push (r, c)
  say s!"closures: {closures.map (·.2.length) |>.foldl (· + ·) 0} constants over {roots.length} \
    roots; {unitChecks} unit memberships checked"
  for mode in [false, true] do
    let ref ← loadOrCompile env whole mode
    let mut compared := 0
    let mut addrDiffs := 0
    let mut metaDiffs := 0
    let mut missing := 0
    for (r, c) in closures do
      let unit : Tests.Ix.Compile.Pass3.CUnit :=
        { name := s!"closure-{r}", env, seeds := #[r], closure := c }
      let out ← Tests.Ix.Compile.Pass3.compileUnit unit mode
      unless out.cenv.ungrounded.isEmpty do
        errors := errors.push s!"{r} mode={mode}: {out.cenv.ungrounded.size} refusals, first \
          {(out.cenv.ungrounded.toList.head?.map (·.1.pretty))}"
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
      addrDiffs := addrDiffs + a
      metaDiffs := metaDiffs + m
      say s!"mode={mode} {r}: closure {c.length}, output {out.env.named.size} names; {a} address, \
        {m} metadata differences"
    say s!"mode={mode}: {roots.length} roots, {compared} carried names compared with the whole \
      compile: {addrDiffs} address differences, {metaDiffs} metadata differences, {missing} \
      closure constants missing from the output"
  for e in errors do say s!"FAIL {e}"
  say s!"{if errors.isEmpty then "PASS" else s!"FAIL ({errors.size})"}"
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.ClosureWhole
