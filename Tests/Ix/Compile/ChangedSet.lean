/-
  changed-set: the changed-set record of a Pass 3 compile
  (`Ix.Compile.ChangedSet`; design document, the output contract, §11.5).

  Units: every `pass3` fixture file (the aux-cert reproducers, the prototype's
  cases, the definitional and proof-justified pass fixtures), the closure of
  the twin families, the closure of the clique families, and Init+Std (the
  environment of `Benchmarks/Compile/CompileInitStd.lean`). Each unit is
  compiled by the Lean pipeline (`compileLeanInput`, Pass 3) twice, with 1
  and with 32 workers. Per unit:

  1. **determinism**: the two records render to the same bytes (and the two
     `.ixe` are the same bytes);
  2. **addresses**: every entry with an address names a constant of the
     artifact, and the artifact's `Named` entry of the name has that address;
  3. **coverage, from the compile** (the record's sources must all reach it):
     every image-kind head (`p3Heads`) has an `image` entry; every member of
     every clique the compiler's `planClique` transports, recomputed from the
     final state, has a `transported` entry;
  4. **coverage, from the artifact** (independent of the tables): every name
     whose metadata carries an `_ix.inline` decompile record has an entry
     whose claim is `differs`; every reserved (`_ix`) name of the artifact has
     a `canonical` entry; and conversely every `rewritten` entry carries an
     `_ix.inline` record;
  5. Init+Std only: the twelve constants W rejects on `initstd-a3` ("value
     differs", `plans/review2/M4-d-strong-model.md` §6) are each claimed
     (`transported` or `carried`), and with `CHANGED_SET_INITSTD=<file>` the
     record `ix compile-lean` wrote equals this compile's byte for byte.

  Run with: `lake test -- --ignored changed-set`. `CHANGED_SET_ONLY` restricts
  the units (comma-separated stems, `twins`, `cliques`, `initstd`).
-/
import Ix.Meta
import Ix.EnvScope
import Ix.CompileM
import Ix.CompileDriver
import Ix.Compile.ChangedSet
import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.Pass3Cliques
import Tests.Ix.Compile.Twins

open Lean

namespace Tests.Ix.Compile.ChangedSet

abbrev IxName := _root_.Ix.Name
open _root_.Ix.Compile.ChangedSet (Record Change)

def say (s : String) : IO Unit := IO.println s!"[changed-set] {s}"

def compileWith (name : String) (env : Environment) (closure : List (Name × ConstantInfo))
    (workers : Nat) : IO Ix.CompileM.LeanPipelineOut := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closure).mapError toString)
  match ← Ix.CompileM.compileLeanInput input (numWorkers := workers) (pass3? := some true) with
  | .ok o => pure o
  | .error e => throw (IO.userError s!"{name}: Lean compile (workers {workers}) failed: {e}")

/-- The checks of one compile's record (2–4); problems, and a summary. -/
def checks (unit : String) (cliques : Array (Array Name)) (out : Ix.CompileM.LeanPipelineOut)
    (r : Record) : Array String × String := Id.run do
  let cenv := out.cenv
  let mut ps : Array String := #[]
  let mut withAddr := 0
  -- 2. addresses
  for e in r.entries do
    let some a := e.addr | continue
    withAddr := withAddr + 1
    unless out.env.consts.contains a do
      ps := ps.push s!"{unit}: {e.name.pretty} ({e.change.tag}): address {a} is not a constant of the artifact"
    match out.env.named.get? e.name with
    | some n => if n.addr != a then
        ps := ps.push s!"{unit}: {e.name.pretty} ({e.change.tag}): the artifact names {n.addr}, the record {a}"
    | none => ps := ps.push s!"{unit}: {e.name.pretty} ({e.change.tag}): not a name of the artifact"
  let claims : Std.HashMap IxName (Array Change) := r.entries.foldl (init := {}) fun m e =>
    m.insert e.name ((m.getD e.name #[]).push e.change)
  let has (n : IxName) (c : Change) : Bool := ((claims.getD n #[]).contains c)
  -- 3. coverage from the compile
  let mut heads := 0
  for (h, _) in cenv.p3Heads do
    if cenv.ungrounded.contains h then continue
    heads := heads + 1
    unless has h .image do ps := ps.push s!"{unit}: image head {h.pretty} has no `image` entry"
  let mut transported := 0
  for cl in cliques do
    let all := cl.map _root_.Ix.Name.fromLeanName
    let some k := all[0]? | continue
    let some (_, carried) := cenv.p3Cliques.get? k | continue
    match Ix.Compile.Pass.planClique cenv.env.get? (Ix.Compile.Pass.cliqueAddr cenv) all carried with
    | .transported _ =>
      for m in all do
        if cenv.ungrounded.contains m then continue
        transported := transported + 1
        unless has m .transported do ps := ps.push s!"{unit}: transported member {m.pretty} has no `transported` entry"
    | _ => pure ()
  -- 4. coverage from the artifact
  let differs (n : IxName) : Bool := (claims.getD n #[]).any (·.differs)
  let mut inline := 0
  let mut reserved := 0
  for (n, named) in out.env.named do
    if Tests.Ix.Compile.Pass3.hasRecord named.constMeta then
      inline := inline + 1
      unless differs n do ps := ps.push s!"{unit}: {n.pretty} carries an `_ix.inline` record but no `differs` claim"
    if Ix.Compile.Pass.hasReserved n then
      reserved := reserved + 1
      unless has n .canonical do ps := ps.push s!"{unit}: reserved name {n.pretty} has no `canonical` entry"
  for e in r.entries do
    if e.change == .rewritten then
      let ok := match out.env.named.get? e.name with
        | some n => Tests.Ix.Compile.Pass3.hasRecord n.constMeta
        | none => false
      unless ok do ps := ps.push s!"{unit}: rewritten {e.name.pretty} carries no `_ix.inline` record"
  let counts := ", ".intercalate (r.counts.toList.filterMap fun (t, k) => if k == 0 then none else some s!"{t} {k}")
  return (ps, s!"{unit}: {r.entries.size} entries ({counts}); {withAddr} addresses checked; \
    {heads} image heads, {transported} transported members, {inline} `_ix.inline` carriers, \
    {reserved} reserved names covered")

/-- 1 and the rest, for one unit. -/
def runUnit (unit : String) (env : Environment) (closure : List (Name × ConstantInfo))
    (cliques : Array (Array Name)) : IO (Array String × Option (Ix.CompileM.LeanPipelineOut × String)) := do
  let a ← compileWith unit env closure 1
  let ra := (_root_.Ix.Compile.ChangedSet.ofCompile a.cenv).render
  let aBytes := a.bytes
  let b ← compileWith unit env closure 32
  let rb := _root_.Ix.Compile.ChangedSet.ofCompile b.cenv
  let rbs := rb.render
  let mut ps : Array String := #[]
  if ra != rbs then ps := ps.push s!"{unit}: the records of 1 and 32 workers differ"
  if aBytes != b.bytes then ps := ps.push s!"{unit}: the artifacts of 1 and 32 workers differ"
  let (cs, line) := checks unit cliques b rb
  say s!"{line}; record {rbs.utf8ByteSize} B, 1 and 32 workers {if ra == rbs then "identical" else "DIFFER"}"
  return (ps ++ cs, some (b, rbs))

/-- The twelve Init+Std constants W rejects on `initstd-a3` (M4-d §6), as
name fragments (several are private): each must be claimed by a
`transported` or `carried` entry. -/
def initStdRejected : List String :=
  ["findLeadingSpacesSize.consumeSpaces", "findLeadingSpacesSize.findNextLine",
   "removeNumLeadingSpaces.consumeSpaces", "removeNumLeadingSpaces.saveLine",
   "findLeadingSpacesSize.consumeSpaces.eq_def", "findLeadingSpacesSize.findNextLine.eq_def",
   "removeNumLeadingSpaces.consumeSpaces.eq_def", "removeNumLeadingSpaces.saveLine.eq_def",
   "mergeSortTR₂_run_eq_mergeSort", "mergeSortTR₂_run'_eq_mergeSort", "bitblast.go_decl_eq",
   "bitblast.goCache_decl_eq"]

def endsWithFragment (n : String) (frag : String) : Bool :=
  n == frag || n.endsWith ("." ++ frag)

def run (env : Environment) : IO UInt32 := do
  let only := ((← IO.getEnv "CHANGED_SET_ONLY").map (·.splitOn ",")).getD []
  let want := fun (s : String) => only.isEmpty || only.contains s
  let mut problems : Array String := #[]
  let mut units := 0
  let files := Tests.Ix.Compile.Pass3.auxCertFiles ++ Tests.Ix.Compile.Pass3.protoFiles ++
    Tests.Ix.Compile.Pass3.passFiles ++ Tests.Ix.Compile.Pass3.pjPassFiles
  for p in files do
    let stem := (System.FilePath.mk p).fileStem.getD p
    if !want stem || Tests.Ix.Compile.Pass3.leanRejects.contains stem then continue
    let u ← Tests.Ix.Compile.Pass3.unitOfFile p
    units := units + 1
    try
      let (ps, _) ← runUnit stem u.env u.closure (Tests.Ix.Compile.Pass3Cliques.leanCliques u.closure)
      problems := problems ++ ps
    catch e =>
      -- a fixture the compile refuses as a whole (an expected refusal of the
      -- pass3 record) has no record to check; any other error is a problem
      problems := problems.push s!"{stem}: {e}"
  if want "twins" then
    let (seeds, _) := Tests.Ix.Compile.Twins.familyClosure env Tests.Ix.Compile.Twins.allFamilies
    let closure := Tests.Ix.Compile.Pass3.closureOf env seeds.toList
    units := units + 1
    let (ps, _) ← runUnit "twins" env closure (Tests.Ix.Compile.Pass3Cliques.leanCliques closure)
    problems := problems ++ ps
  if want "cliques" then
    let families := Tests.Ix.Compile.Twins.cliqueFamilies ++ Tests.Ix.Compile.Twins.ownershipFamilies
    let (seeds, _) := Tests.Ix.Compile.Twins.familyClosure env families
    let extra := [``Lean.Order.monotone_compose].filter env.contains
    let closure := Tests.Ix.Compile.Pass3.closureOf env (seeds.toList ++ extra)
    units := units + 1
    let (ps, _) ← runUnit "cliques" env closure (Tests.Ix.Compile.Pass3Cliques.leanCliques closure)
    problems := problems ++ ps
  if want "initstd" then
    let ienv ← getFileEnv "Benchmarks/Compile/CompileInitStd.lean"
    let whole := ienv.constants.toList
    say s!"Init+Std: {whole.length} constants"
    units := units + 1
    let (ps, res) ← runUnit "initstd" ienv whole (Tests.Ix.Compile.Pass3Cliques.leanCliques whole)
    problems := problems ++ ps
    if let some (out, rendered) := res then
      unless out.cenv.ungrounded.isEmpty do
        problems := problems.push s!"initstd: {out.cenv.ungrounded.size} block failures"
      let r := _root_.Ix.Compile.ChangedSet.ofCompile out.cenv
      for frag in initStdRejected do
        let hit := r.entries.any fun e =>
          (e.change == .transported || e.change == .carried) && endsWithFragment e.name.pretty frag
        unless hit do problems := problems.push s!"initstd: W's rejected constant …{frag} is not claimed"
      say s!"initstd: the {initStdRejected.length} constants W rejects on initstd-a3 checked against the record"
      if let some p := ← IO.getEnv "CHANGED_SET_INITSTD" then
        let file ← IO.FS.readFile p
        if file == rendered then say s!"initstd: {p} (ix compile-lean) is byte-identical with this compile's record"
        else problems := problems.push s!"initstd: {p} differs from this compile's record"
  for p in problems do say s!"FAIL {p}"
  say s!"{if problems.isEmpty then "PASS" else "FAIL"}: {units} units, {problems.size} problem(s)"
  return if problems.isEmpty then 0 else 1

end Tests.Ix.Compile.ChangedSet
