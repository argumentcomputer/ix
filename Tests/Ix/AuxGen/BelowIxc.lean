import LSpec
import Ix.Meta
import Ix.CompileDriver
import Tests.Ix.AuxGen.FlatBlockSource

/-! # `.below` and `.brecOn` from IxC Source mode (AuxGen M2a, M2b, M3)

`lake exe IxTests --ignored auxgen-below-ixc` (the fixtures) and
`--ignored auxgen-below-initstd` (Init+Std, a measurement). The plans are
`auxgen-m2.md` and `auxgen-m3.md`.

AuxGen's `.below` asks its kernel the sort levels it emits into every
Type-level `.below` value; `.brecOn` asks levels too, and its `.eq`'s unit-like
test asks `inferType?`, `whnf?` and `isDefEq?`. Since AuxGen M2b (`.below`)
and M3 (`.brecOn`, after the generated `.below` is admitted to IxC,
`AuxOracle.admitBelow`) the compile driver answers them in IxC Source mode
(`fallback`, safe blocks), over the Source service run ahead of the waves
(`Ix.AuxGen.Source.RunAhead`, one snapshot per level of the schedule), with
each block's own canonical flat block installed when its layout is not
Lean's (`AuxKernel.withFlatBlock`).

1. **Shadow agreement.** Each block that holds an inductive has its aux
   patches generated as the driver's tail generates them, with the IxC arm in
   `shadow` mode over its level's snapshot: every IxC answer is compared with
   `Ix.Tc`'s, spelling included (`Ix.Compile.ExactKey.levelEq`), each `isDefEq?`
   decision exactly. Asserted: no answer or decision differs (the stop rule
   of `auxgen-m2.md` §3: a spelling change would move Lean's output without
   a Rust mirror). The counts are printed: queries, fast-path hits on each
   side, answered, refused, flat blocks, decisions, expression questions,
   the generated `.below` admitted.
2. **The fold's bytes in each mode.** `compileEnvFoldWithSource` under each
   measurement setting (`AuxIxcOptions`), against production's
   (`compileEnvFold`: `fallback`, the recursors on IxC, the recursors' asks
   since AuxGen M4b), by their serialized
   environments. All asserted equal: `shadow` (`Ix.Tc`'s answers: production
   gives the bytes `Ix.Tc` gives), `failClosed` (IxC alone: no refusal on
   these corpora), both again with every inductive block asked, and
   `fallbackEager` (M2b's production, both kernels asked; production's
   `fallback` is lazy since M3).
3. **Init+Std only, timed**: the production fold and the measurement fold's
   compile phases, and the service's work alone
   (`Ix.AuxGen.Source.measure`: as it runs; lowering, then folding (lever
   P1); the `.below`-only asks (lever P2)).
4. **Terms out of IxC** (fixtures, AuxGen M3): the decision-grade egress
   round-trips, and IxC's `infer`, `whnf` and `isDefEq` agree with the
   declarations (`egressFixtures`).
5. **Recursors on IxC** (AuxGen M4a, measurement modes): the shadow also
   runs the recursor generator's `whnf`s (named: the input when unreduced,
   the named replay when reduced) and the elimination decision on IxC, and
   checks the canonical block (flat install, or Lean-layout recursors equal
   to Lean's). A field that names no member of the block skips
   `findRecTarget`'s Phase 2; `Ix.Tc` still decides it in the shadow. Asserted:
   no difference from `Ix.Tc` (`auxgen-m4.md` §3's stop rule; a skipped field
   `Ix.Tc` finds recursive counts), no refusal, the replay exercised on the
   fixtures; every measurement fold (recursors on IxC) has production's
   bytes, and a fold that does not says where it differs (`foldDiff`).

Asserted besides: no IxC refusal on these corpora (`failClosed` would fail a
block on one; production falls back to `Ix.Tc`). -/

namespace Tests.Ix.AuxGen.BelowIxc

open LSpec
open Tests.Ix.AuxGen.FlatBlockSource (fixtureModules inductiveBlocks)

/-- Two tails' counts together. -/
def addStats (a b : Ix.AuxGen.IxcStats) : Ix.AuxGen.IxcStats :=
  { queries := a.queries + b.queries, tcFast := a.tcFast + b.tcFast
    ixcFast := a.ixcFast + b.ixcFast, answered := a.answered + b.answered
    equal := a.equal + b.equal, differ := a.differ + b.differ
    refused := a.refused + b.refused, scopesRefused := a.scopesRefused + b.scopesRefused
    flatInstalled := a.flatInstalled + b.flatInstalled
    flatRefused := a.flatRefused + b.flatRefused
    decisions := a.decisions + b.decisions, decisionsEqual := a.decisionsEqual + b.decisionsEqual
    decisionsDiffer := a.decisionsDiffer + b.decisionsDiffer
    exprQueries := a.exprQueries + b.exprQueries, exprAnswered := a.exprAnswered + b.exprAnswered
    belowAdmitted := a.belowAdmitted + b.belowAdmitted, belowRefused := a.belowRefused + b.belowRefused
    recWhnf := a.recWhnf + b.recWhnf, recStuck := a.recStuck + b.recStuck
    recSame := a.recSame + b.recSame, recReplayed := a.recReplayed + b.recReplayed
    recBeta := a.recBeta + b.recBeta
    recRefused := a.recRefused + b.recRefused, recEqual := a.recEqual + b.recEqual
    recDiffer := a.recDiffer + b.recDiffer, recDiffName := a.recDiffName + b.recDiffName
    recDiffInfo := a.recDiffInfo + b.recDiffInfo, recDiffLevel := a.recDiffLevel + b.recDiffLevel
    recDiffOther := a.recDiffOther + b.recDiffOther
    recDecisionDiffer := a.recDecisionDiffer + b.recDecisionDiffer
    recSkipped := a.recSkipped + b.recSkipped, recSkipDiffer := a.recSkipDiffer + b.recSkipDiffer
    recForced := a.recForced + b.recForced, elim := a.elim + b.elim
    elimEqual := a.elimEqual + b.elimEqual, elimDiffer := a.elimDiffer + b.elimDiffer
    elimRefused := a.elimRefused + b.elimRefused, leanRecSame := a.leanRecSame + b.leanRecSame
    leanRecDiffer := a.leanRecDiffer + b.leanRecDiffer, asked := a.asked + b.asked
    samples := (a.samples ++ b.samples).extract 0 24 }

def statsLine (st : Ix.AuxGen.IxcStats) : String :=
  s!"queries {st.queries} (fast path: Ix.Tc {st.tcFast}, IxC {st.ixcFast}); \
    IxC answered {st.answered}: equal {st.equal}, differ {st.differ}; refused {st.refused}, \
    scopes refused {st.scopesRefused}; flat blocks installed {st.flatInstalled}, \
    refused {st.flatRefused}; isDefEq decisions {st.decisions}: equal {st.decisionsEqual}, \
    differ {st.decisionsDiffer}; inferType/whnf {st.exprQueries}, IxC answered \
    {st.exprAnswered}; generated .below admitted {st.belowAdmitted}, refused {st.belowRefused}; \
    recursor whnf {st.recWhnf} (stuck {st.recStuck}, stuck after β {st.recBeta}, unreduced \
    {st.recSame}, replayed \
    {st.recReplayed}, refused {st.recRefused}): equal {st.recEqual}, differ {st.recDiffer} \
    (binder name {st.recDiffName}, info {st.recDiffInfo}, level {st.recDiffLevel}, other \
    {st.recDiffOther}, at decision sites {st.recDecisionDiffer}); fields skipped {st.recSkipped} \
    (decided recursive by Ix.Tc {st.recSkipDiffer}); elimination {st.elim}: equal \
    {st.elimEqual}, differ {st.elimDiffer}, refused {st.elimRefused}; questions needing the \
    service {st.recForced}; Lean-layout recursors equal to Lean's {st.leanRecSame}, not \
    {st.leanRecDiffer}"

/-- **One block's aux tail with the IxC arm**, as the driver's tail generates
the patches (`sortConsts`, the classes restricted to Lean's `all`,
`generateAuxPatches`), over `oracle`: the tail's counts and its canonical-block
verdict (AuxGen M4c); `none` for a block with no inductive class. -/
def tailStats (cenv : Ix.CompileM.CompileEnv) (lo : Ix.Name) (all : Array Ix.Name)
    (oracle : Ix.AuxGen.AuxOracle) :
    Except String (Option (Ix.AuxGen.IxcStats × Option Ix.AuxGen.CanonicalVerdict)) :=
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := {}, current := lo, mutCtx := default, univCtx := [] }
  let act : Ix.CompileM.CompileM
      (Option (Ix.AuxGen.IxcStats × Option Ix.AuxGen.CanonicalVerdict)) := do
    let mut cs : Array Ix.MutConst := #[]
    for n in all do
      match (← Ix.AuxGen.lookupConst? n) with
      | some (.inductInfo val) => cs := cs.push (← Ix.CompileM.MutConst.mkIndc val)
      | some (.defnInfo val) => cs := cs.push (Ix.MutConst.fromDefinitionVal val)
      | some (.opaqueInfo val) => cs := cs.push (Ix.MutConst.fromOpaqueVal val)
      | some (.thmInfo val) => cs := cs.push (Ix.MutConst.fromTheoremVal val)
      | some (.recInfo val) => cs := cs.push (.recr val)
      | _ => pure ()
    let sorted ← Ix.CompileM.sortConsts cs.toList
    let classNames : Array (Array Ix.Name) := (sorted.map fun c => (c.map (·.name)).toArray).toArray
    let originalAll : Array Ix.Name := Id.run do
      for c in cs do
        if let .indc ind := c then return ind.all
      return #[]
    if originalAll.isEmpty then return none
    -- an unsafe block's tail keeps `Ix.Tc`, as in the driver (`compileBlockWithAux`)
    let unsafeBlock := cs.any fun
      | .indc ind => ind.isUnsafe
      | .recr rv => rv.isUnsafe
      | .defn d => d.safety == .unsaf
    if unsafeBlock then return none
    let inAll (n : Ix.Name) := originalAll.any (Ix.Compile.ExactKey.nameEq · n)
    let classes := (classNames.map (·.filter inAll)).filter (!·.isEmpty)
    if classes.isEmpty then return none
    let maps := Ix.AuxGen.AddrMaps.ofCompileEnv (← Ix.CompileM.getCompileEnv)
    let (_, ctx) ← (Ix.AuxGen.generateAuxPatches classes originalAll maps (.ixc maps oracle)).run
      Ix.AuxGen.AuxKernelCtx.new
    return some (ctx.ixcStats, ctx.canonical)
  match Ix.CompileM.CompileM.run cenv blockEnv {} act with
  | .ok (r, _) => .ok r
  | .error e => .error (toString e)

/-- **Shadow agreement** over every block that holds an inductive, each over
its level's snapshot of a run-ahead over the input with production's asks: the
counts summed, each block's canonical-block verdict by its canonical key (as
the fold keys it), and the blocks whose tail failed. The harness runs a tail
for every such block, including the ones production promotes without running
their own tail (a family a parent's tail compiled). -/
def shadow (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (cenv : Ix.CompileM.CompileEnv) :
    IO (Ix.AuxGen.IxcStats × Array (Ix.Name × Ix.AuxGen.CanonicalVerdict) × Array String) := do
  let levels := Ix.CompileM.scheduleLevels blocks (Ix.CompileM.FoldSchedule.of blocks)
  let ra := Ix.AuxGen.Source.RunAhead.start env.get? blocks levels ({} : Ix.CompileM.AuxIxcOptions).asks
  let mut total : Ix.AuxGen.IxcStats := {}
  let mut verdicts : Array (Ix.Name × Ix.AuxGen.CanonicalVerdict) := #[]
  let mut errors : Array String := #[]
  for (lo, members) in inductiveBlocks env blocks do
    let key := Ix.CompileM.blockKey lo ((blocks.blocks.get? lo).getD {})
    let some t := ra.runFor key
      | do errors := errors.push s!"{lo.pretty}: in no level of the schedule"; continue
    let oracle := Ix.AuxGen.Ixc.oracleOfRun .shadow false (fun _ => t.get) (ra.membersFor key)
      { recursors := true, lookup := env.get? }
    match ← IO.lazyPure fun _ => tailStats cenv lo members oracle with
    | .error e => errors := errors.push s!"{lo.pretty}: aux generation: {e.take 200}"
    | .ok none => pure ()
    | .ok (some (st, v?)) =>
      total := addStats total st
      if let some v := v? then verdicts := verdicts.push (key, v)
  return (total, verdicts, errors)

/-- A fold's serialized environment. -/
def serialized (r : Except String (Ixon.Env × Nat × Ix.CompileM.CompileEnv)) : Except String ByteArray := do
  let (ixe, _, _) ← r
  Ixon.serEnv ixe

/-- Where two folds' environments differ: the names whose address differs
(at most five shown), and the block failures. -/
def foldDiff (prod out : Ixon.Env × Nat × Ix.CompileM.CompileEnv) : String := Id.run do
  let (pe, _, _) := prod
  let (oe, _, oc) := out
  let mut addr : Array String := #[]
  for (n, a) in pe.named do
    match oe.named.get? n with
    | some b =>
      if a.addr != b.addr then addr := addr.push n.pretty
    | none => addr := addr.push s!"{n.pretty} (missing)"
  let msgs := oc.ungrounded.fold (init := ({} : Std.HashMap String Nat)) fun m _ e =>
    m.insert (e.take 400).toString ((m.getD (e.take 400).toString 0) + 1)
  s!"{addr.size} names with another address ({", ".intercalate (addr.extract 0 5).toList}), \
    {oc.ungrounded.size} block failures, by message: \
    {" / ".intercalate (msgs.toList.map fun (e, k) => s!"{k}x {e}")}"

/-- The measurement fold in `opts`, against the production fold's bytes
`expected`: whether they are equal, the run-ahead's report line, the time. -/
def foldIxc (opts : Ix.CompileM.AuxIxcOptions) (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (expected : ByteArray) (width : Nat) (prod : Ixon.Env × Nat × Ix.CompileM.CompileEnv) :
    IO (Bool × String × Nat) := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure fun _ =>
    Ix.CompileM.compileEnvFoldWithSource env blocks (width := width) (aux := opts)
  let t1 ← IO.monoMsNow
  match r with
  | .error e => return (false, s!"failed: {e.take 300}", t1 - t0)
  | .ok (out, report) =>
    match serialized (.ok out) with
    | .error e => return (false, s!"serialization failed: {e}", t1 - t0)
    | .ok bytes =>
      let same := bytes == expected
      return (same, if same then report.summary else s!"{report.summary}; {foldDiff prod out}",
        t1 - t0)

/-- The modes the folds are compared in, with whether equality is asserted. -/
def foldModes : Array (String × Ix.CompileM.AuxIxcOptions × Bool) :=
  #[("shadow", { mode := .shadow, recursors := true }, true),
    -- M4b–M5b's production (IxC first, `Ix.Tc` behind a refusal); production
    -- is `failClosed` since AuxGen M5c
    ("fallback", { mode := .fallback, recursors := true }, true),
    ("shadow, every inductive block asked",
      { mode := .shadow, asks := .inductive, recursors := true }, true),
    ("failClosed, every inductive block asked",
      { mode := .failClosed, asks := .inductive, recursors := true }, true),
    -- M2b's production (both kernels asked); production is lazy since AuxGen M3
    ("fallbackEager", { mode := .fallbackEager, recursors := true }, true),
    -- M3's production: the recursors on Ix.Tc, the `.below` asks (production
    -- puts the recursors on IxC since AuxGen M4b)
    ("M3's production (recursors on Ix.Tc, the .below asks)",
      { mode := .fallback, recursors := false, asks := .below }, true),
    ("failClosed, recursors on Ix.Tc", { mode := .failClosed, recursors := false }, true)]

/-- AuxGen M5: the acceptance table's lines (its counts, by kind and verdict,
and the first refusals). -/
def acceptanceLines (t : Ix.AuxGen.AuxTable) : Array String := Id.run do
  let mut lines := #[s!"production's acceptance table: {t.rows.size} rows: \
    {t.counts.line}"]
  for l in t.byKind do lines := lines.push s!"  {l}"
  for l in t.refusals 8 do lines := lines.push s!"  refused: {l.take 300}"
  return lines

/-- AuxGen M5: what production's acceptance table satisfies against its
artifact `ixe`:
* it is not empty, and no regenerated auxiliary is refused by Source mode
  (the stop rule), nor left unchecked as late unless `allowLate`;
* every published name with an original form has a row (the classifier's
  domain), except Pass 3's images (`isImage`: a changed block's image-kind
  heads, published by Pass 3's image blocks, not by an aux tail's promotion),
  which are counted apart;
* each row is `identical` exactly when its original form's address is its
  published address (today's address rule; identity is decided on bytes).
The errors, and information lines. -/
def acceptanceErrors (ixe : Ixon.Env) (t : Ix.AuxGen.AuxTable) (isImage : Ix.Name → Bool)
    (allowLate : Bool) : Array String × Array String := Id.run do
  let mut errors : Array String := #[]
  let c := t.counts
  if t.rows.isEmpty then errors := errors.push "the acceptance table is empty"
  if c.refused - c.late != 0 then
    errors := errors.push s!"{c.refused - c.late} regenerated auxiliaries refused by Source mode \
      (stop rule): {", ".intercalate (t.refusals 4).toList}"
  if !allowLate && c.late != 0 then
    errors := errors.push s!"{c.late} regenerated auxiliaries not checked at generation (late)"
  let mut missing : Array String := #[]
  let mut images := 0
  let mut imagesSameAddr := 0
  let mut imagesWithRow := 0
  for (n, named) in ixe.named do
    if named.original.isSome then
      if isImage n then
        images := images + 1
        if named.original.any (·.1 == named.addr) then imagesSameAddr := imagesSameAddr + 1
        if (t.verdict? n).isSome then imagesWithRow := imagesWithRow + 1
      else if (t.verdict? n).isNone then missing := missing.push n.pretty
  if !missing.isEmpty then
    errors := errors.push s!"{missing.size} published names with an original form, not Pass 3 \
      images, have no row: {", ".intercalate (missing.extract 0 4).toList}"
  let info := #[s!"Pass 3 images with an original form: {images} ({imagesSameAddr} at their \
    original's address, {imagesWithRow} with a row)"]
  let mut disagree : Array String := #[]
  for r in t.rows do
    match ixe.named.get? r.name with
    | some named =>
      let sameAddr := named.original.any (·.1 == named.addr)
      if sameAddr != (r.verdict == .identical) then disagree := disagree.push r.name.pretty
    | none => disagree := disagree.push s!"{r.name.pretty} (not published)"
  if !disagree.isEmpty then
    errors := errors.push s!"{disagree.size} rows whose identity disagrees with the addresses: \
      {", ".intercalate (disagree.extract 0 4).toList}"
  return (errors, info)

/-- AuxGen M5: every tail verdict reaches a row of the table: the generated
name's own (promoted: the verdict, unless its bytes are identical), or each
display name it was published at (the verdict itself). -/
def admissionRowErrors (r : Ix.AuxGen.CompileReport) (t : Ix.AuxGen.AuxTable) :
    Array String := Id.run do
  let mut unreached : Array String := #[]
  let mut wrong : Array String := #[]
  for (n, v) in r.admitted do
    let displays := r.display.filter fun (g, _) => Ix.Compile.ExactKey.nameEq g n
    match t.verdict? n with
    | some w =>
      if w != .identical && w != v then wrong := wrong.push s!"{n.pretty} (row {repr w})"
    | none =>
      if displays.isEmpty then unreached := unreached.push n.pretty
    for (_, d) in displays do
      match t.verdict? d with
      | some w => if w != v then wrong := wrong.push s!"{d.pretty} (row {repr w})"
      | none => unreached := unreached.push s!"{n.pretty} as {d.pretty}"
  let mut errors : Array String := #[]
  if !unreached.isEmpty then
    errors := errors.push s!"{unreached.size} tail verdicts reach no row: \
      {", ".intercalate (unreached.extract 0 4).toList}"
  if !wrong.isEmpty then
    errors := errors.push s!"{wrong.size} rows do not carry their tail verdict: \
      {", ".intercalate (wrong.extract 0 4).toList}"
  return errors

/-- AuxGen M5: the table's rule on constructed facts (`AuxTable.ofFacts`). A
refusal is a refused row on both routes (promoted, and under a display name);
identical bytes win over the tail's verdict; a promoted name the tail did not
check is refused as late; a name without a row is not identical. -/
def tableRuleErrors : Array String := Id.run do
  let nm (s : String) : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon s
  let t := Ix.AuxGen.AuxTable.ofFacts
    (identity := #[(nm "p", false), (nm "q", true), (nm "late", false)])
    (generated := #[(nm "p", .casesOnDef), (nm "g", .brecOnDef)])
    (admitted := #[(nm "p", .refused "no"), (nm "q", .refused "no"), (nm "g", .refused "bad")])
    (exempt := #[])
    (display := #[(nm "g", nm "g_ix")])
  let mut errors : Array String := #[]
  unless t.verdict? (nm "p") == some (.refused "no") do
    errors := errors.push "the table: a promoted refusal is not a refused row"
  unless t.verdict? (nm "g_ix") == some (.refused "bad") do
    errors := errors.push "the table: a displayed refusal is not a refused row"
  unless t.identical (nm "q") do
    errors := errors.push "the table: identical bytes are not identical"
  unless t.verdict? (nm "late") == some (.refused Ix.AuxGen.AuxTable.lateReason) do
    errors := errors.push "the table: an unchecked promoted name is not late"
  if t.identical (nm "g") || (t.verdict? (nm "g")).isSome then
    errors := errors.push "the table: a moved generated name has a row of its own"
  unless t.counts.refused == 3 && t.counts.late == 1 && t.counts.identical == 1 do
    errors := errors.push s!"the table's counts: {repr t.counts}"
  -- AuxGen M5b: a block's Source status (`AuxTable.withBlockStatus`). On a block
  -- Source accepts, a refusal stays a refusal (the stop rule applies there); on
  -- one it does not accept, every generated name is exempt with the status
  let refusedOnAccepted := Ix.AuxGen.AuxTable.withBlockStatus none #[nm "p"]
    #[(nm "p", .refused "no")]
  unless refusedOnAccepted == #[(nm "p", .refused "no")] do
    errors := errors.push "the block-status rule: an accepted block's refusal is not kept"
  let why := "blocked behind BEq (ingress: declined: inductive block without a recursor)"
  let onNotAccepted := Ix.AuxGen.AuxTable.withBlockStatus (some why) #[nm "p", nm "q"]
    #[(nm "p", .refused "no")]
  let reason := s!"{Ix.AuxGen.AuxTable.notAcceptedPrefix}{why}"
  unless onNotAccepted == #[(nm "p", .exempt reason), (nm "q", .exempt reason)] do
    errors := errors.push "the block-status rule: a non-accepted block's names are not exempt"
  let t2 := Ix.AuxGen.AuxTable.ofFacts (identity := #[(nm "p", false), (nm "q", false)])
    (generated := #[]) (admitted := onNotAccepted) (exempt := #[])
  unless t2.counts.notAccepted == 2 && t2.counts.refused == 0 do
    errors := errors.push s!"the block-status counts: {repr t2.counts}"
  return errors

/-- Everything but the timing of the service alone, on one input. -/
def evaluate (label : String) (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (width : Nat) :
    IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let t0 ← IO.monoMsNow
  let prod ← IO.lazyPure fun _ => Ix.CompileM.compileEnvFold env blocks (width := width)
  let t1 ← IO.monoMsNow
  let (_, _, cenv) ← IO.ofExcept prod
  let expected ← IO.ofExcept (serialized prod)
  lines := lines.push s!"{label}: {env.consts.size} constants, {blocks.blocks.size} blocks; \
    production fold {t1 - t0} ms, {expected.size} bytes"
  for (name, opts, asserted) in foldModes do
    let (same, report, ms) ← foldIxc opts env blocks expected width (← IO.ofExcept prod)
    lines := lines.push s!"fold, {name}: {ms} ms; \
      {if same then "bytes equal to production" else "bytes DIFFER from production"}; \
      run-ahead: {report}"
    if asserted && !same then errors := errors.push s!"{name}: the fold's bytes differ from production"
  let t2 ← IO.monoMsNow
  let (st, shadowVerdicts, tailErrors) ← shadow env blocks cenv
  let t3 ← IO.monoMsNow
  lines := lines.push s!"shadow, per block ({t3 - t2} ms): {statsLine st}"
  for s in st.samples do lines := lines.push s!"  {s.take 300}"
  for e in tailErrors do errors := errors.push e
  if st.differ != 0 then
    errors := errors.push s!"{st.differ} IxC answers spelled differently from Ix.Tc's (stop rule)"
  if st.queries == 0 then errors := errors.push "no level question was asked"
  if st.decisionsDiffer != 0 then
    errors := errors.push s!"{st.decisionsDiffer} isDefEq decisions differ from Ix.Tc's"
  -- AuxGen M4a's stop rule (auxgen-m4.md §3)
  if st.recDiffer != 0 then
    errors := errors.push s!"{st.recDiffer} recursor whnf answers differ from Ix.Tc's (stop rule)"
  if st.recSkipDiffer != 0 then
    errors := errors.push s!"{st.recSkipDiffer} skipped fields Ix.Tc decided recursive (stop rule)"
  if st.elimDiffer != 0 then
    errors := errors.push s!"{st.elimDiffer} elimination decisions differ from Ix.Tc's (stop rule)"
  if st.leanRecDiffer != 0 then
    errors := errors.push s!"{st.leanRecDiffer} Lean-layout canonical recursors differ from Lean's"
  -- AuxGen M4c: production records each block's canonical-block verdict
  -- (`CompileEnv.auxReport`). Every recorded verdict is the shadow harness's
  -- for the same block, none is a refusal or a difference, and production
  -- records a verdict for exactly the harness's blocks it did not promote: a
  -- block whose key a parent's aux tail compiled (`CompileEnv.auxGenExtraNames`)
  -- is promoted without its own tail, so it has no verdict of its own; every
  -- other block has one. No block drops out silently.
  let canonical := cenv.auxReport.canonicalSummary
  lines := lines.push s!"production's canonical verdicts: {canonical.line}"
  for (k, why) in canonical.findings.extract 0 4 do
    lines := lines.push s!"  {k.pretty}: {why.take 300}"
  if canonical.refused + canonical.leanDiffer != 0 then
    errors := errors.push s!"production recorded {canonical.refused} refused canonical flat blocks \
      and {canonical.leanDiffer} Lean-layout blocks whose recursors differ from Lean's"
  if canonical.installed + canonical.leanSame == 0 then
    errors := errors.push "production recorded no canonical verdict"
  let sameKey (a b : Ix.Name) : Bool := Ix.Compile.ExactKey.nameEq a b
  let mut disagree : Array String := #[]
  for (key, v) in cenv.auxReport.canonical do
    match shadowVerdicts.find? (sameKey ·.1 key) with
    | some (_, w) =>
      if v != w then disagree := disagree.push s!"{key.pretty} ({repr v} vs {repr w})"
    | none => disagree := disagree.push s!"{key.pretty} (not checked by the harness)"
  if !disagree.isEmpty then
    errors := errors.push s!"{disagree.size} production canonical verdicts are not the shadow \
      harness's: {", ".intercalate (disagree.extract 0 4).toList}"
  let recordedKey (k : Ix.Name) : Bool := cenv.auxReport.canonical.any (sameKey ·.1 k)
  let promoted (k : Ix.Name) : Bool := cenv.auxGenExtraNames.contains k
  let unrecorded := shadowVerdicts.filter fun (k, _) => !recordedKey k
  let promotedRecorded := shadowVerdicts.filter fun (k, _) => recordedKey k && promoted k
  let dropped := shadowVerdicts.filter fun (k, _) => !recordedKey k && !promoted k
  lines := lines.push s!"canonical verdicts: production records {cenv.auxReport.canonical.size}, \
    the harness has {shadowVerdicts.size}; {unrecorded.size} harness-only, all promoted without \
    their own tail: {", ".intercalate ((unrecorded.extract 0 8).map (·.1.pretty)).toList}"
  if !promotedRecorded.isEmpty then
    errors := errors.push s!"{promotedRecorded.size} promoted blocks have a verdict of their own: \
      {", ".intercalate ((promotedRecorded.extract 0 4).map (·.1.pretty)).toList}"
  if !dropped.isEmpty then
    errors := errors.push s!"{dropped.size} blocks production compiled with their own tail have no \
      recorded verdict: {", ".intercalate ((dropped.extract 0 4).map (·.1.pretty)).toList}"
  -- AuxGen M5: production's acceptance table (`CompileEnv.auxReport.table`)
  let (pe, _, _) ← IO.ofExcept prod
  let table := cenv.auxReport.table
  for l in acceptanceLines table do lines := lines.push l
  let (accErrors, accInfo) :=
    acceptanceErrors pe table (cenv.p3Heads.contains ·) (allowLate := true)
  for l in accInfo do lines := lines.push l
  for e in accErrors do errors := errors.push e
  -- the tails' Source verdicts themselves (a changed block's regenerated
  -- auxiliaries are published under display names, so not every verdict is a
  -- row): none refused (the stop rule)
  let adm := cenv.auxReport.admitted
  let admRefused := adm.filter fun (_, v) => match v with | .refused _ => true | _ => false
  let admExempt := adm.filter fun (_, v) => match v with | .exempt _ => true | _ => false
  lines := lines.push s!"tail admissions: {adm.size}: \
    {adm.size - admRefused.size - admExempt.size} accepted, {admExempt.size} exempt, \
    {admRefused.size} refused"
  if !admRefused.isEmpty then
    errors := errors.push s!"{admRefused.size} generated auxiliaries refused by Source mode in \
      their tails (stop rule): {", ".intercalate ((admRefused.extract 0 4).map fun (n, v) =>
        s!"{n.pretty}: {(repr v).pretty.take 200}").toList}"
  if label == "fixtures" && adm.isEmpty then
    errors := errors.push "no generated auxiliary was admitted in a tail"
  -- every tail verdict reaches a row: its own (promoted) or its display
  -- name's, with that verdict unless the bytes are identical
  for e in admissionRowErrors cenv.auxReport table do errors := errors.push e
  -- AuxGen M5b: this corpus is closed over recursors, so Source accepts every
  -- block and no row is exempt for its block's Source status
  lines := lines.push s!"rows exempt for their block's Source status: {table.counts.notAccepted}"
  if table.counts.notAccepted != 0 then
    errors := errors.push s!"{table.counts.notAccepted} rows exempt for their block's Source \
      status on a corpus Source accepts whole"
  lines := lines.push s!"displayed auxiliaries (rows under `_ix` names): \
    {cenv.auxReport.display.size}"
  if label == "fixtures" && cenv.auxReport.display.isEmpty then
    errors := errors.push "no changed block's auxiliary was displayed"
  -- the table's rule on constructed facts: a refusal is a refused row on both routes
  for e in tableRuleErrors do errors := errors.push e
  if st.recWhnf == 0 || st.elim == 0 then
    errors := errors.push "no recursor question was asked"
  if label == "fixtures" && st.recReplayed == 0 then
    errors := errors.push "the named replay was never exercised (the alias fixtures)"
  if st.recRefused + st.elimRefused != 0 then
    errors := errors.push s!"IxC refused {st.recRefused} recursor whnfs, {st.elimRefused} \
      elimination decisions"
  if st.refused + st.scopesRefused + st.flatRefused + st.belowRefused != 0 then
    errors := errors.push s!"IxC refused {st.refused} queries, {st.scopesRefused} scopes, \
      {st.flatRefused} flat blocks, {st.belowRefused} generated .below (failClosed fails a \
      block on one)"
  return (errors, lines)

def report (errors lines : Array String) : IO (Bool × Nat × Nat × Option String) := do
  for l in lines do IO.println l
  for e in errors do IO.println s!"  error: {e}"
  let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
  return (errors.isEmpty, 1, 0, msg)

/-! ## The fixtures -/

def fixtureInput : IO (Ix.Environment × Ix.CondensedBlocks) := do
  let leanEnv ← getCompileEnv (fixtureModules ++ #[`IxC.Kernel.PinGen.Certs])
  let idxs := fixtureModules.filterMap leanEnv.getModuleIdx?
  let seeds := leanEnv.constants.toList.toArray.filterMap fun (n, _) =>
    if (leanEnv.getModuleIdxFor? n).any idxs.contains then some n else none
  let certs := (Ix.RoleEvidence.certTheorems.flatMap (·.2)).toArray
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv
    (seeds ++ certs ++ Tests.Ix.Kernel.SourceIngress.preludeNames))
  let env := Tests.Ix.Kernel.SourceIngressStep.canon closed.toArray (workers := 4)
  return (env, Ix.Cert.blocksOf env)

def fixtures : TestSeq :=
  .individualIO "AuxGen M2a: .below's levels from IxC agree with Ix.Tc's; the measurement fold's bytes"
    none (do
      let (env, blocks) ← fixtureInput
      let (errors, lines) ← evaluate "fixtures" env blocks 16
      report errors lines) .done

/-! ## failClosed's retry, its named failure, the deferred `Ix.Tc` bookkeeping (AuxGen M5c)

Production runs a safe block's tail under `failClosed` (`Ix.CompileM.runAuxTail`).
Over the fixtures' safe inductive blocks, through the driver's own tail:
1. **A refusal on an accepted block fails it, named.** An oracle whose every
   question IxC refuses (planted), on a block Source mode accepts: the tail fails,
   and the failure names the block, the scope, the question and IxC's reason.
2. **A block Source mode does not accept re-runs on `fallback`, rolled back
   exactly.** The same planted oracle, with a status saying the block is not
   accepted: the tail succeeds by its retry, the report records it, every
   generated auxiliary is exempt with the status, and the block state after it is
   the state a `fallback` tail leaves from the same start (so the failed
   attempt's writes are all rolled back).
3. **The deferred bookkeeping is the eager one.** For each block with a
   Prop-level `.below` family, the `Ix.Tc` kenv its recursor generation finds
   under `failClosed` (the bookkeeping logged, then replayed) equals the kenv of
   the same tail with the bookkeeping run eagerly (`AuxKernelCtx.deferTc`). -/

/-- A block's aux-tail arguments as `compileBlockWithAux` makes them (its
prologue, in the same block state): the members, their classes, the block's
address, the address maps; `none` for a block with no tail. -/
def tailArgs (lo : Ix.Name) (members : Array Ix.Name) : Ix.CompileM.CompileM
    (Option (Array Ix.MutConst × List (List Ix.MutConst) × Address × Ix.AuxGen.AddrMaps)) := do
  let const ← Ix.CompileM.findConst lo
  unless members.size != 1 || const matches .inductInfo _ do return none
  let mut cs : Array Ix.MutConst := #[]
  for n in members do
    match ← Ix.CompileM.findConst n with
    | .inductInfo val => cs := cs.push (← Ix.CompileM.MutConst.mkIndc val)
    | .defnInfo val => cs := cs.push (Ix.MutConst.fromDefinitionVal val)
    | .opaqueInfo val => cs := cs.push (Ix.MutConst.fromOpaqueVal val)
    | .thmInfo val => cs := cs.push (Ix.MutConst.fromTheoremVal val)
    | .recInfo val => cs := cs.push (.recr val)
    | _ => continue
  let sortedClasses := Ix.CompileM.orderRecursorFamily (← Ix.CompileM.sortConsts cs.toList)
  let blockResult ← Ix.CompileM.compileMutualBlock sortedClasses
  unless blockResult.block.info matches .muts _ do return none
  for (name, proj, _) in blockResult.projections do
    let projAddr := Address.admissionHash (Ixon.ser proj)
    Ix.CompileM.modifyBlockState fun st =>
      { st with blockNameToAddr := st.blockNameToAddr.insert name projAddr }
  let bstate ← Ix.CompileM.getBlockState
  let maps := Ix.AuxGen.AddrMaps.ofCompileEnv (← Ix.CompileM.getCompileEnv)
    (aux := bstate.auxNameToAddr) (primary := bstate.blockNameToAddr)
  return some (cs, sortedClasses, blockResult.blockAddr, maps)

/-- `o` with every question refused (planted) and `status` as its block status,
in `failClosed`; its installs, its retry and its `withFamily` are `o`'s. -/
def planted (o : Ix.AuxGen.AuxOracle) (status : Option String) : Ix.AuxGen.AuxOracle :=
  let bad {α} : Except String α := .error "planted refusal (AuxGen M5c test)"
  let scope : Ix.AuxGen.OracleScope :=
    .mk (fun _ => bad) (fun _ => bad) (fun _ => bad) (fun _ => bad) (fun _ => bad)
      (fun _ _ => bad) (fun _ => bad)
  match o with
  | .mk _ trace _ withFlat admitBelow recursors asked _ admit _ retry withFamily =>
    .mk .failClosed trace (fun _ _ => bad) withFlat admitBelow recursors asked
      (fun _ _ _ => scope) admit (fun _ => status) retry withFamily

/-- A block state as the tests compare it: the aux constants, named entries and
name addresses, the block's own registrations, and the sizes of its tables. -/
def stateKey (st : Ix.CompileM.BlockState) : String :=
  let consts := st.auxConsts.map fun (a, _) => toString a
  let named := st.auxNamed.map fun (n, nd) => s!"{n.pretty}@{nd.addr}"
  let aux := (st.auxNameToAddr.toArray.map fun (_, a) => toString a).qsort (· < ·)
  let primary := (st.blockNameToAddr.toArray.map fun (_, a) => toString a).qsort (· < ·)
  let refs := st.refs.map toString
  s!"{consts} {named} {aux} {primary} {refs} {st.univs.size} {st.metaUnivs.size} \
    {st.blockBlobs.size} {st.auxGenExtraNames.size} {st.exprCache.size}"

/-- Two kenv constants alike: the constructor, the type, the level count, and
the value, constructors or inductive they carry. -/
def kconstKey : Ix.AuxGen.MKConst → String
  | .defn _ _ _ _ _ l t v _ b => s!"defn {l} {t.addr} {v.addr} {b.addr}"
  | .recr _ _ k u l p i m n b j t rs _ =>
    s!"recr {k} {u} {l} {p} {i} {m} {n} {b.addr} {j} {t.addr} {rs.size}"
  | .axio _ _ u l t => s!"axio {u} {l} {t.addr}"
  | .quot _ _ _ l t => s!"quot {l} {t.addr}"
  | .indc _ _ l p i u b j t cs _ =>
    s!"indc {l} {p} {i} {u} {b.addr} {j} {t.addr} {cs.map (·.addr)}"
  | .ctor _ _ u l ind c p f t => s!"ctor {u} {l} {ind.addr} {c} {p} {f} {t.addr}"

/-- Where two kenvs differ (at most three entries), or `none`. -/
def kenvDiff (a b : Std.HashMap Ix.AuxGen.MKId Ix.AuxGen.MKConst) : Option String := Id.run do
  if a.size != b.size then return some s!"{a.size} entries against {b.size}"
  let mut out : Array String := #[]
  for (k, v) in a do
    match b.get? k with
    | some w => if kconstKey v != kconstKey w then out := out.push s!"{k.addr} differs"
    | none => out := out.push s!"{k.addr} missing"
  return if out.isEmpty then none else some (", ".intercalate (out.extract 0 3).toList)

/-- `act` in a fresh block state of block `lo` over `cenv`. -/
def runIn (cenv : Ix.CompileM.CompileEnv) (lo : Ix.Name) (act : Ix.CompileM.CompileM α) :
    Except String (α × Ix.CompileM.BlockState) :=
  let blockEnv : Ix.CompileM.BlockEnv := { all := {}, current := lo, mutCtx := default, univCtx := [] }
  (Ix.CompileM.CompileM.run cenv blockEnv {} act).mapError toString

def m5cEvaluate (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let prod ← IO.lazyPure fun _ => Ix.CompileM.compileEnvFold env blocks (width := 16)
  let (_, _, cenv) ← IO.ofExcept prod
  let levels := Ix.CompileM.scheduleLevels blocks (Ix.CompileM.FoldSchedule.of blocks)
  let opts : Ix.CompileM.AuxIxcOptions := {}
  let ra := Ix.AuxGen.Source.RunAhead.start env.get? blocks levels opts.asks
  let mut named := 0
  let mut retried := 0
  let mut families := 0
  let mut notStandalone := 0
  for (lo, members) in inductiveBlocks env blocks do
    let key := Ix.CompileM.blockKey lo ((blocks.blocks.get? lo).getD {})
    let some real := opts.oracleFor ra env.get? key | continue
    let some fb := real.retry | do errors := errors.push s!"{lo.pretty}: no retry oracle"; continue
    -- 3. the replayed kenv against the eager one, at the family's generation
    let famKenv (defer : Bool) :
        Ix.CompileM.CompileM (Option (Std.HashMap Ix.AuxGen.MKId Ix.AuxGen.MKConst)) := do
      let some (cs, sorted, addr, maps) ← tailArgs lo members | return none
      let (_, kctx) ← (Ix.AuxGen.compileMutualAuxTail cs sorted addr maps (.ixc maps real)).run
        { Ix.AuxGen.AuxKernelCtx.new with deferTc := defer, captureFamilyKenv := true }
      return kctx.familyKenv
    match ← IO.lazyPure fun _ => runIn cenv lo (famKenv true) with
    | .error e =>
      -- a block this harness cannot re-run on its own over the production fold's
      -- environment (a family another block's tail compiled: its claims are
      -- taken) fails before the family's generation in both runs, alike
      match ← IO.lazyPure fun _ => runIn cenv lo (famKenv false) with
      | .error e' =>
        if e == e' then notStandalone := notStandalone + 1
        else errors := errors.push s!"{lo.pretty}: the tails fail differently: {e.take 160} / \
          {e'.take 160}"
      | .ok _ => errors := errors.push s!"{lo.pretty}: only the deferred tail fails: {e.take 200}"
    | .ok (none, _) => pure ()
    | .ok (some deferred, _) =>
      match ← IO.lazyPure fun _ => runIn cenv lo (famKenv false) with
      | .ok (some eager, _) =>
        families := families + 1
        if let some d := kenvDiff deferred eager then
          errors := errors.push s!"{lo.pretty}: the replayed kenv is not the eager one: {d}"
      | .ok (none, _) => errors := errors.push s!"{lo.pretty}: the eager tail reached no family"
      | .error e => errors := errors.push s!"{lo.pretty}: eager tail: {e.take 200}"
    -- 1 and 2 on the first blocks Source mode accepts
    if real.blockStatus () != none || named ≥ 8 then continue
    let tail (k : Ix.AuxGen.AddrMaps → Ix.AuxGen.AuxKernel) (viaDriver : Bool) :
        Ix.CompileM.CompileM (Option Ix.AuxGen.AuxKernelCtx) := do
      let some (cs, sorted, addr, maps) ← tailArgs lo members | return none
      if viaDriver then
        return some (← Ix.CompileM.runAuxTail lo cs sorted addr maps (k maps)).2
      return some (← (Ix.AuxGen.compileMutualAuxTail cs sorted addr maps (k maps)).run
        Ix.AuxGen.AuxKernelCtx.new).2
    match ← IO.lazyPure fun _ => runIn cenv lo (tail (.ixc · (planted real none)) true) with
    | .ok (none, _) => continue
    | .ok (some _, _) => errors := errors.push s!"{lo.pretty}: a planted refusal did not fail the block"
    | .error e =>
      named := named + 1
      for part in [lo.pretty, "accepted by Source mode", "IxC refused", " in ",
          "planted refusal (AuxGen M5c test)"] do
        unless (e.splitOn part).length > 1 do
          errors := errors.push s!"{lo.pretty}: the failure does not name {part}: {e.take 300}"
    let why := "planted: not accepted (AuxGen M5c test)"
    match ← IO.lazyPure fun _ => runIn cenv lo (tail (.ixc · (planted real (some why))) true),
        ← IO.lazyPure fun _ => runIn cenv lo (tail (.ixc · fb) false) with
    | .ok (some kctx, st), .ok (some _, st') =>
      retried := retried + 1
      if st.auxReport.retried != some why then
        errors := errors.push s!"{lo.pretty}: the retry is not recorded"
      if stateKey { st with auxReport := {} } != stateKey { st' with auxReport := {} } then
        errors := errors.push s!"{lo.pretty}: the retried block state is not the fallback tail's"
      let exempt := kctx.admitted.filter fun (_, v) => v matches .exempt _
      unless exempt.size == kctx.generated.size && kctx.admitted.size == kctx.generated.size do
        errors := errors.push s!"{lo.pretty}: {exempt.size} of {kctx.generated.size} generated \
          auxiliaries exempt after the retry"
    | .error e, _ => errors := errors.push s!"{lo.pretty}: the retry failed: {e.take 200}"
    | _, .error e => errors := errors.push s!"{lo.pretty}: the fallback tail failed: {e.take 200}"
    | _, _ => errors := errors.push s!"{lo.pretty}: a tail ran on one side only"
  lines := lines.push s!"M5c: named failures {named}, retries {retried}, Prop families with \
    the replayed kenv compared {families} (blocks this harness cannot re-run alone, failing \
    alike both ways: {notStandalone})"
  if named == 0 then errors := errors.push "no planted refusal failed a block"
  if retried == 0 then errors := errors.push "no planted retry ran"
  if families == 0 then errors := errors.push "no Prop-level .below family was compared"
  return (errors, lines)

def m5c : TestSeq :=
  .individualIO "AuxGen M5c: failClosed's named failure, its exact retry, the replayed kenv"
    none (do
      let (env, blocks) ← fixtureInput
      let (errors, lines) ← m5cEvaluate env blocks
      report errors lines) .done

/-! ## Terms out of IxC (AuxGen M3)

`.brecOn.eq`'s unit-like test reads IxC's `inferType?` and `whnf?` answers
(decision-grade egress, `Ix.AuxGen.Ixc.Scope.egress`). Per inductive of the
fixtures' safe blocks, over its parameters as locals (free variables
included): the egress round-trips (an annotated IxC term, out and back in,
is the same term); the type IxC infers for the applied inductive and for
each applied constructor is definitionally equal to the declared one; the
weak head normal form of the applied inductive is equal to it; and the
applied inductive is not a sort (a negative). -/

/-- Instantiate the leading `n` binders of `ty` with `args`. -/
def instantiateParams (ty : Ix.Expr) (args : Array Ix.Expr) : Ix.Expr := Id.run do
  let mut cur := ty
  for a in args do
    match cur with
    | .forallE _ _ body _ _ => cur := Ix.AuxGen.instantiate1 body a
    | _ => pure ()
  return cur

/-- One inductive's checks over a scope of the service: how many, and the
failures. -/
def egressChecks (svc : Ix.AuxGen.Source.Service) (env : Ix.Environment) (iv : Ix.InductiveVal) :
    Except String (Nat × Array String) := do
  let lps := iv.cnst.levelParams
  let lvls := lps.map Ix.Level.mkParam
  let (fvars, decls, body) := Ix.AuxGen.forallTelescope iv.cnst.type iv.numParams "egress" 0
  let s ← Ix.AuxGen.Ixc.Scope.new svc.env lps
  let s ← s.push (decls.map fun d => (d.fvarName, d.domain))
  let mut checks := 0
  let mut bad : Array String := #[]
  let what := iv.cnst.name.pretty
  -- the round trip
  let k ← s.term body
  let (k1, s) ← s.run fun r => r.annotate s.depth k
  let e ← s.egress k1
  let k' ← s.term e
  let (k2, s) ← s.run fun r => r.annotate s.depth k'
  checks := checks + 1
  if !(k1 == k2) then bad := bad.push s!"{what}: the egress does not round-trip"
  -- infer, whnf and a negative on the applied inductive
  let app := Ix.AuxGen.mkAppN (Ix.Expr.mkConst iv.cnst.name lvls) fvars
  let (ty, s) ← s.inferExpr app
  let (q, s) ← s.defEq ty body
  checks := checks + 1
  if !q then bad := bad.push s!"{what}: the inferred type is not the declared one"
  let (w, s) ← s.whnfExpr app
  let (q, s) ← s.defEq w app
  checks := checks + 1
  if !q then bad := bad.push s!"{what}: the weak head normal form is not equal to the term"
  let (q, s) ← s.defEq app (Ix.Expr.mkSort Ix.Level.mkZero)
  checks := checks + 1
  if q then bad := bad.push s!"{what}: equal to Prop"
  -- each constructor's inferred type
  let mut s := s
  for c in iv.ctors do
    let some (.ctorInfo cv) := env.consts.get? c | do
      bad := bad.push s!"{c.pretty}: not a constructor of the environment"; continue
    let (ty, s') ← s.inferExpr (Ix.AuxGen.mkAppN (Ix.Expr.mkConst c lvls) fvars)
    let (q, s') ← s'.defEq ty (instantiateParams cv.cnst.type fvars)
    s := s'
    checks := checks + 1
    if !q then bad := bad.push s!"{c.pretty}: the inferred type is not the declared one"
  return (checks, bad)

def egressFixtures : TestSeq :=
  .individualIO "AuxGen M3: IxC's terms out (decision-grade egress, infer, whnf, isDefEq)"
    none (do
      let (env, blocks) ← fixtureInput
      let levels := Ix.CompileM.scheduleLevels blocks (Ix.CompileM.FoldSchedule.of blocks)
      let ra := Ix.AuxGen.Source.RunAhead.start env.get? blocks levels .inductive
      let mut checks := 0
      let mut inductives := 0
      let mut errors : Array String := #[]
      for (lo, members) in inductiveBlocks env blocks do
        let key := Ix.CompileM.blockKey lo ((blocks.blocks.get? lo).getD {})
        let some t := ra.runFor key
          | do errors := errors.push s!"{lo.pretty}: in no level of the schedule"; continue
        let svc ← match t.get.service with
          | .ok svc => pure (svc.ensureNames members)
          | .error e => do errors := errors.push s!"{lo.pretty}: service: {e}"; continue
        for n in members do
          let some (.inductInfo iv) := env.consts.get? n | continue
          if iv.isUnsafe then continue
          inductives := inductives + 1
          match egressChecks svc env iv with
          | .error e => errors := errors.push s!"{n.pretty}: refused: {e.take 300}"
          | .ok (c, bad) =>
            checks := checks + c
            errors := errors ++ bad
      if checks == 0 then errors := errors.push "nothing was checked"
      report errors #[s!"egress: {inductives} inductives, {checks} checks, {errors.size} failures"]) .done

def suite : List TestSeq := [fixtures, egressFixtures, m5c]

/-! ## Init+Std, timed -/

def workers : Nat := 32

def initStd : TestSeq :=
  .individualIO "AuxGen M2a on Init+Std: shadow agreement, the measurement fold, the service timed"
    none (do
      let t0 ← IO.monoMsNow
      let leanEnv ← getCompileEnv #[`Init, `Std]
      let consts := leanEnv.constants.toList.toArray
      let env ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon consts workers
      let blocks ← IO.lazyPure fun _ =>
        Tests.Ix.Kernel.SourceIngressStep.condense env (parallel := true)
      let t1 ← IO.monoMsNow
      IO.println s!"Init+Std: load, canon and condense {t1 - t0} ms"
      let (errors, lines) ← evaluate "Init+Std" env blocks (4 * workers)
      let levels := Ix.CompileM.scheduleLevels blocks (Ix.CompileM.FoldSchedule.of blocks)
      let measured ← Ix.AuxGen.Source.measure env.get? blocks levels
      report errors (lines.push s!"schedule levels: {levels.size}" ++ measured)) .done

def initStdSuite : List TestSeq := [initStd]

end Tests.Ix.AuxGen.BelowIxc
