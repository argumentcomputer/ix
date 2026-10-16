/-
  compile-closure-whole: a closure compile agrees with the whole compile,
  and a closure carries whole logical units. This is the design document's
  §6.2 (the closure-against-whole theorem, "a block's output is a function
  of its closure") and §6.3 ("How it is checked").

  The whole environment is Init+Std: the environment of
  `Benchmarks/Compile/CompileInitStd.lean` (`import Init`, `import Std` and
  a few definitions), elaborated at run time. It must not be the test
  environment restricted to Init+Std modules. Any later module can realise
  an on-demand auxiliary of an Init block under a private name of its own
  (the test environment has dozens of
  `_private.<M>.0.PSigma.casesOn._arg_pusher`). By §6.3 those belong to the
  unit, so a closure drawn from the larger environment carries them.

  The whole compile is read from `CLOSURE_WHOLE_IXE=<ixe>` when it is set.
  That must be a whole-environment compile of that file by this tree, for
  example the Rust compile
  `ix compile Benchmarks/Compile/CompileInitStd.lean --out <ixe>`
  (ALIGNED with `ix compile-lean`, so the same Named entries).
  Otherwise the whole environment is compiled once by the Lean pipeline.

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
  8. **the Rust compiler**: the Rust compile of every closure
     (`rsCompileEnvBytesFFI`) is the Lean compile's artifact, byte for
     byte.

  Ported from 940e4fe6 and a9cf3607 `Tests/Ix/Compile/ClosureWhole.lean`:
  - The donor's numbering is kept.
  - Checks 6 and 7 are dropped: the introduced references
    (`introducedSupport`) and the local scope of the `LocalCollapse`
    fixture with `ix validate-lean --local` are LC-15b (CQ4.3).
  - The `mode` loop is gone, and `CLOSURE_WHOLE_ON` is renamed to
    `CLOSURE_WHOLE_IXE` (R11-16).
  - Pass 3 is replaced by the closure harness.
  - Metadata differences are now classified by field.

  Run with: `lake test -- --ignored compile-closure-whole`.
-/
import Ix.Meta
import Ix.EnvScope
import Tests.Ix.Compile.ClosureHarness

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

/-- The whole compile, as read back from its bytes: `CLOSURE_WHOLE_IXE`, or
the Lean pipeline on `whole`. -/
def loadOrCompile (env : Environment) (whole : List (Name × ConstantInfo)) : IO Ixon.Env := do
  if let some path ← IO.getEnv "CLOSURE_WHOLE_IXE" then
    say s!"whole: reading {path}"
    return ← readIxe path
  say s!"whole: compiling {whole.length} Init+Std constants (Lean pipeline)"
  let out ← compileClosure env whole
  unless out.cenv.ungrounded.isEmpty do
    throw (IO.userError s!"whole: {out.cenv.ungrounded.size} refusals")
  IO.ofExcept (Ixon.rsDeEnv out.bytes)

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
  let mut closures : Array (Name × List (Name × ConstantInfo)) := #[]
  let mut unitChecks := 0
  for r in roots do
    let c := Ix.EnvScope.collectSelectedDeps env [r]
    let cn := nameSet c
    for (n, _) in c do
      unless wholeNames.contains n do
        errors := errors.push s!"{r}: the closure leaves the whole environment at {n}"
      for u in Ix.EnvScope.unitMembers env.constants units n do
        unitChecks := unitChecks + 1
        unless cn.contains u do errors := errors.push s!"{r}: {n} is carried without {u} of its unit"
    closures := closures.push (r, c)
  say s!"closures: {closures.foldl (· + ·.2.length) 0} constants over {roots.length} roots; \
    {unitChecks} unit memberships checked"
  -- 3, 4, 5, 8: each closure compiled, against the whole compile
  let ref ← loadOrCompile env whole
  let dir ← IO.FS.createTempDir
  let mut compared := 0
  let mut addrDiffs := 0
  let mut metaDiffs := 0
  let mut classes : Std.HashMap String Nat := {}
  let mut missing := 0
  let mut rustSame := 0
  for (r, c) in closures do
    let out ← compileClosure env c
    -- 3. no refusal
    unless out.cenv.ungrounded.isEmpty do
      errors := errors.push s!"{r}: {out.cenv.ungrounded.size} refusals, first \
        {out.cenv.ungrounded.toList.head?.map (·.1.pretty)}"
    -- 8. the Rust compiler on the same closure
    match ← rustCheck s!"{r}" env c out (dir / "rust.ixe") with
    | none => rustSame := rustSame + 1
    | some e => errors := errors.push e
    let outEnv ← IO.ofExcept (Ixon.rsDeEnv out.bytes)
    -- 5. every closure constant is in the output
    for (n, _) in c do
      unless outEnv.named.contains (ixN n) do
        missing := missing + 1
        errors := errors.push s!"{r}: {n} is not in the closure's output"
    -- 4. closure against whole, classified
    let mut a := 0
    let mut m := 0
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
    addrDiffs := addrDiffs + a
    metaDiffs := metaDiffs + m
    say s!"{r}: closure {c.length}, output {outEnv.named.size} names; {a} address, \
      {m} metadata differences"
  let classLine := classes.toList.map (fun (k, v) => s!"{k} {v}") |>.toArray.qsort (· < ·)
  say s!"{roots.length} roots, {compared} carried names compared with the whole compile: \
    {addrDiffs} address differences, {metaDiffs} metadata differences (classes: {classLine}), \
    {missing} closure constants missing from the output"
  say s!"Rust compiler on the same closures: {rustSame}/{closures.size} byte-identical with the \
    Lean compile"
  for e in errors do say s!"FAIL {e}"
  say s!"{if errors.isEmpty then "PASS" else s!"FAIL ({errors.size})"}"
  IO.FS.removeDirAll dir
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.ClosureWhole
