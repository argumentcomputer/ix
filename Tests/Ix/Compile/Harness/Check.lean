/-
  The compiler suites' unit harness (R11-08), checks of one compiled unit
  against its source and a suite's records:

  - `namesCheck`: every input constant is emitted or has a block failure;
    every named entry is an input constant, a reserved `_ix` name (D14) or a
    block's synthetic `Muts` entry; the changed blocks (`CompileEnv.p3Blocks`);
  - `displayProblems`: every changed block has an `_ix` display name;
  - `failureProblems`: every block failure is a recorded root, a consequence
    of one (its message names a root or an earlier consequence), or a
    recorded refusal of Pass 3's images; the records checked both ways;
  - `decompileProblems`: decompile fidelity (`ClosureHarness.decompileCheck`)
    but for recorded roundtrip defects, checked both ways.

  The record types are here; a suite's records are its data
  (`Tests.Ix.Compile.Pass3Kernels`).
-/
import Ix.Compile.Pass
import Tests.Ix.Compile.Harness.Units

open Lean

namespace Tests.Ix.Compile.Harness

/-! ## 1. Changed blocks and names -/

/-- What `namesCheck` reports. -/
structure NamesReport where
  /-- The Lean `all` of each changed block (`p3Blocks`), by first member. -/
  changedBlocks : Array (Array _root_.Ix.Name) := #[]
  inputNames : Nat := 0
  reserved : Nat := 0
  problems : Array String := #[]

/-- The changed blocks of the output and its named entries: every input
constant is emitted or has a block failure (a partial output skips the
whole-environment decompile and kernel requests come from emitted names, so
a missing name must not disappear from both without a failure), and every
named entry is an input constant (`inputHas`: the kernel view counts, for a
raw `addDecl`'s nested auxiliary recursors), a reserved `_ix` name or a
block's `Muts` entry, so Pass 3 invents no other name. -/
def namesCheck (u : CUnit) (out : _root_.Ix.CompileM.LeanPipelineOut) : NamesReport := Id.run do
  let blocks := (out.cenv.p3Blocks.toArray.map (·.2)).qsort fun a b =>
    ((a[0]?).map (·.pretty)).getD "" < ((b[0]?).map (·.pretty)).getD ""
  let mut r : NamesReport := { changedBlocks := blocks }
  for (n, _) in u.closure do
    let name := ixN n
    unless out.env.named.contains name || out.cenv.ungrounded.contains name do
      let msg := s!"{name.pretty} is neither emitted nor recorded as a block failure"
      r := { r with problems := r.problems.push msg }
  for (n, nd) in out.env.named do
    if isMutsEntry nd then continue
    if _root_.Ix.Compile.Pass.hasReserved n then r := { r with reserved := r.reserved + 1 }
    else if inputHas u.env (toLeanName n) then r := { r with inputNames := r.inputNames + 1 }
    else
      let msg := s!"{n.pretty} is neither an input constant nor a reserved name"
      r := { r with problems := r.problems.push msg }
  return r

/-! ## 5. Display names -/

/-- Every changed block has an `_ix` display name under one of its members
(the side-car edit moved its Ix auxiliaries). -/
def displayProblems (u : CUnit) (out : _root_.Ix.CompileM.LeanPipelineOut)
    (changedBlocks : Array (Array _root_.Ix.Name)) : Array String := Id.run do
  let mut problems : Array String := #[]
  for all in changedBlocks do
    let some x := all[0]? | continue
    let hasIx := out.env.named.toList.any fun (n, _) =>
      _root_.Ix.Compile.Pass.hasReserved n && all.any fun m => (toLeanName m).isPrefixOf (toLeanName n)
    unless hasIx do
      problems := problems.push s!"{u.name}: no `_ix` name for the block of {x.pretty}"
  return problems

/-! ## Block failures -/

/-- Recorded root block failures of a unit, by exact name, with their cause
and a substring of their message (a refusal of Pass 2, a compile totality
defect). -/
structure CompileFailure where
  unit : String
  cause : String
  msg : String
  names : List String

/-- Recorded refusals of Pass 3's own images, by unit and exact name. -/
structure ImageRefusal where
  unit : String
  cause : String
  msg : String
  names : List String

/-- Recorded source-recovery (decompile) defects, by unit and constant. -/
structure DecompileKnown where
  unit : String
  cause : String
  names : List String

/-- The failures that follow from recorded root failures (`roots`): a failure
whose message names (a member of) a root or an earlier consequence, to a
fixed point. Under Pass 3 a Lean auxiliary of a changed block is its image,
whose type mentions every member of the Lean block, the refused component
included (REFUSED-SIBLING). -/
def refusalClosure (roots : Std.HashSet _root_.Ix.Name) (out : _root_.Ix.CompileM.LeanPipelineOut) :
    Std.HashSet _root_.Ix.Name := Id.run do
  let mut bad : Std.HashSet String := roots.fold (fun s n => s.insert n.pretty) {}
  let mut found : Std.HashSet _root_.Ix.Name := {}
  let mut changed := true
  while changed do
    changed := false
    for (n, e) in out.cenv.ungrounded do
      if found.contains n || roots.contains n then continue
      let msg := leanOf e
      if bad.toList.any fun b => hasSub msg b then
        found := found.insert n
        bad := bad.insert n.pretty
        changed := true
  return found

/-- Every block failure of the unit is a recorded root (`recorded`), a
consequence of one (`refusalClosure`) or a recorded image refusal
(`refusals`); every recorded name fails with its message. Returns the
problems and the report lines (with `emit`, a candidate record row per
unrecorded failure). -/
def failureProblems (u : CUnit) (out : _root_.Ix.CompileM.LeanPipelineOut)
    (recorded : List CompileFailure) (refusals : List ImageRefusal) (emit : Bool) :
    Array String × Array String := Id.run do
  let recorded := recorded.filter (·.unit == u.name)
  let refusals := refusals.filter (·.unit == u.name)
  let mut problems : Array String := #[]
  let mut lines : Array String := #[]
  let roots : Std.HashSet _root_.Ix.Name := out.cenv.ungrounded.fold (init := {}) fun s n e =>
    if recorded.any (fun r => r.names.contains n.pretty && hasSub e r.msg) then s.insert n else s
  let consequence := refusalClosure roots out
  let mut nConsequences := 0
  let mut nRefusals := 0
  for (n, e) in out.cenv.ungrounded do
    if roots.contains n then continue
    if consequence.contains n then nConsequences := nConsequences + 1
    else if refusals.any (fun r => r.names.contains n.pretty && hasSub e r.msg) then
      nRefusals := nRefusals + 1
    else
      problems := problems.push s!"{u.name}: {n.pretty} fails, not recorded: {e.take 240}"
      if emit then
        lines := lines.push s!"  emit: \{ unit := {u.name.quote}, cause := \"?\", \
msg := {((e.take 60).toString).quote}, names := [{n.pretty.quote}] },"
  lines := lines.push s!"  block failures: {roots.size} recorded root(s) \
[{", ".intercalate (recorded.map (·.cause))}], {nConsequences} consequence(s) (REFUSED-SIBLING), \
{nRefusals} recorded image refusal(s)"
  let fails (nm msg : String) : Bool :=
    out.cenv.ungrounded.toList.any fun (n, e) => n.pretty == nm && hasSub e msg
  for r in recorded do
    for nm in r.names do
      unless fails nm r.msg do
        problems := problems.push
          s!"{u.name}: {nm} is recorded as failing ({r.cause}: {r.msg}) but does not (stale)"
  for r in refusals do
    for nm in r.names do
      unless fails nm r.msg do
        problems := problems.push
          s!"{u.name}: {nm} is recorded as an image refusal ({r.msg}) but does not fail (stale)"
  return (problems, lines)

/-! ## 2. Decompile -/

/-- The constant a decompile problem names. -/
def decompileSubject (p : String) : String :=
  if p.startsWith "decompile mismatch: " then (p.drop 20).toString
  else if p.startsWith "not decompiled: " then (p.drop 16).toString
  else if p.startsWith "decompile error " then (((p.drop 16).toString.splitOn ": ").headD "")
  else p

/-- Decompile fidelity of a complete output (`ClosureHarness.decompileCheck`):
every problem not recorded in `known` (by the constant it names) is a
problem, and so is a recorded constant with no problem. A partial output
(a block failed) is not decompilable as a whole and is skipped. Returns the
problems and the report lines. -/
def decompileProblems (u : CUnit) (out : _root_.Ix.CompileM.LeanPipelineOut)
    (known : List DecompileKnown) : IO (Array String × Array String) := do
  unless out.cenv.ungrounded.isEmpty do
    return (#[], #[s!"  decompile: skipped, {out.cenv.ungrounded.size} block failure(s)"])
  let (dprob, dsum) ← Tests.Ix.Compile.ClosureHarness.decompileCheck u.env u.closure out
  let known : Std.HashSet String := (known.filter (·.unit == u.name)).foldl
    (fun s k => k.names.foldl (·.insert ·) s) {}
  let recorded := dprob.filter fun p => known.contains (decompileSubject p)
  let mut lines := #[s!"  decompile: {dsum}, {dprob.size} problem(s) ({recorded.size} recorded \
as documented roundtrip defects)"]
  for p in dprob.toList.take 8 do lines := lines.push s!"    {p}"
  let mut problems := (dprob.filter fun p => !known.contains (decompileSubject p)).map
    (s!"{u.name}: " ++ ·)
  for k in known do
    unless dprob.any (decompileSubject · == k) do
      problems := problems.push s!"{u.name}: {k} is recorded as a decompile problem but has none (stale)"
  return (problems, lines)

end Tests.Ix.Compile.Harness
