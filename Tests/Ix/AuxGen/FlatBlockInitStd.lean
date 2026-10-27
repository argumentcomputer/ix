import Tests.Ix.AuxGen.FlatBlockSource
import Tests.Ix.AuxGen.BelowIxc

/-! # The drivers' Source service on Init+Std (`lake exe IxTests --ignored auxgen-flat-initstd`)

AuxGen on IxC, M1, on the compiler's own input: Init+Std, without the
certificate module, canonicalized and condensed as `kernel-source-ingress`
does it, compiled by the wave fold with its Source service
(`Ix.CompileM.compileEnvFoldWithSource`, the IO pipeline's `4 * workers`
tasks per wave). The fold runs the service ahead of the waves and asks it for
every block with a Type-level `.below` (AuxGen M2b's asks, lever P2) and, since
M4b, every block the recursor generator can ask past the fast paths
(`Asks.recursors`), whose aux tail asks IxC, at the committed bundle's evidence
(`Ix.RoleEvidence.bundleEvidence`). Then:
1. **the service alone**: a service of its own asked for every block that
   holds an inductive in dependency order (`Run.start`, `Run.ask`), timed,
   and for the drivers' asks (`Run.askWhere`, production's asks); and those
   asks again over a lookup view
   like the IO pipeline's, whose theorem and opaque bodies are canonicalized
   on demand (the share of canonicalization in the service's time);
2. **the flat blocks**: each inductive block's canonical classes and
   recursors as the aux tail generates them (`generateAuxPatches`); where the
   layout is not Lean's (`Flat.needed`), its flat block is built, installed
   in a service of its own and σ checked against `Key.map` (as in
   `auxgen-flat-source`).

Printed: each phase's time, the drivers' report, the refusals. Asserted: the
service started; every block production's asks select is asked for and
accepted, and no group is refused or blocked; the service alone agrees, over
both views; every flat block is accepted and σ fits `Key.map` on it. -/

namespace Tests.Ix.AuxGen.FlatBlockInitStd

open LSpec
open Ix.AuxGen.Source (Service Status Run)
open Tests.Ix.AuxGen.FlatBlockSource
open Tests.Ix.Kernel.SourceIngressStep (canon condense)

def workers : Nat := 32

def evaluate : IO (Array String × Array String) := do
  let t0 ← IO.monoMsNow
  let leanEnv ← getCompileEnv #[`Init, `Std]
  let consts := leanEnv.constants.toList.toArray
  let env ← IO.lazyPure fun _ => canon consts workers
  let blocks ← IO.lazyPure fun _ => condense env (parallel := true)
  let t1 ← IO.monoMsNow
  let ((ixe, _, cenv), report) ← match ← IO.lazyPure fun _ =>
      Ix.CompileM.compileEnvFoldWithSource env blocks (width := 4 * workers) with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"compile: {e}")
  let t2 ← IO.monoMsNow
  -- 1. the service alone, asked for the same blocks in dependency order
  let ind := inductiveBlocks env blocks
  let asks := ind.map fun (lo, ms) => (lo, lo, ms.foldl (·.insert ·) ({} : Ix.Set Ix.Name))
  let input : Ix.AuxGen.Source.Input := { get? := env.get?, blocks := blocks }
  let ran ← IO.lazyPure fun _ => (Run.start input).ask asks
  let alone := ran.report
  let t3 ← IO.monoMsNow
  -- 1'. the same, asked only for the blocks the drivers ask for (production's
  -- asks: the Type-level `.below` blocks since AuxGen M2b, lever P2, and the
  -- recursors' since M4b)
  let prodAsks := ({} : Ix.CompileM.AuxIxcOptions).asks
  let belowRan ← IO.lazyPure fun _ => (Run.start input).askWhere prodAsks asks
  let aloneBelow := belowRan.report
  let t3e ← IO.monoMsNow
  -- 1a. the share of the conversions: every group it met, placed and
  -- converted again, one thread
  let met : Array Ix.Name := match ran.service with
    | .ok svc => svc.entries.filterMap (·.names[0]?)
    | .error _ => #[]
  let t3c ← IO.monoMsNow
  let converted ← IO.lazyPure fun _ => met.foldl (init := 0) fun k n =>
    match env.consts.get? n with
    | some ci => if (Ix.LeanIngress.convert (input.groupFor n ci)).toBool then k + 1 else k
    | none => k
  let t3d ← IO.monoMsNow
  -- 1b. the same over a view like the IO pipeline's: theorem and opaque
  -- bodies canonicalized again on demand (`compileDecoratedConsts`' fallback)
  let leanByIx ← IO.lazyPure fun _ => consts.foldl (init := ({} : Std.HashMap Ix.Name _))
    fun m (ln, lci) => m.insert ((Ix.CanonM.canonName ln).run' {}) (ln, lci)
  let viewGet (n : Ix.Name) : Option Ix.ConstantInfo := match env.consts.get? n with
    | some (.thmInfo _) | some (.opaqueInfo _) =>
      (leanByIx.get? n).bind fun c => ((Ix.CanonM.canonChunk #[c])[0]?).map (·.2)
    | other => other
  let t3a ← IO.monoMsNow
  let viewed ← IO.lazyPure fun _ =>
    ((Run.start { get? := viewGet, blocks := blocks }).askWhere prodAsks asks).report
  let t3b ← IO.monoMsNow
  -- 2. the flat blocks
  let lookup := cenv.env.consts.get?
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let mut flatSvc : Option Service := none
  let mut needed := 0
  let mut accepted := 0
  let mut auxNs := 0
  for (lo, members) in ind do
    let s0 ← IO.monoNanosNow
    match ← IO.lazyPure fun _ => blockAux cenv lo members with
    | .error e =>
      auxNs := auxNs + ((← IO.monoNanosNow) - s0)
      errors := errors.push s!"{lo.pretty}: aux generation: {e.take 200}"
    | .ok none => auxNs := auxNs + ((← IO.monoNanosNow) - s0)
    | .ok (some b) =>
      auxNs := auxNs + ((← IO.monoNanosNow) - s0)
      let nClasses := b.classes.size
      let auxNames := (b.out.canonicalRecs.extract nClasses b.out.canonicalRecs.size).map (·.1)
      let leanNested := match b.originalAll[0]?.bind lookup with
        | some (.inductInfo v) => v.numNested
        | _ => 0
      unless Ix.AuxGen.Flat.needed b.classes b.originalAll auxNames leanNested do continue
      needed := needed + 1
      let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
      let svc := flatSvc.getD (Service.start pre input (Ix.RoleEvidence.bundleEvidence ()))
      match Ix.AuxGen.Flat.build lookup b.classes b.out.canonicalRecs svc.sigma with
      | .error e => errors := errors.push s!"{lo.pretty}: build: {e}"
      | .ok fb =>
        let svc ← IO.lazyPure fun _ => svc.installFlat fb
        flatSvc := some svc
        match svc.flatStatus? (fb.firstName.getD default) with
        | some .accepted =>
          accepted := accepted + 1
          unless fits svc.sigma (sourceTerms lookup b) do
            errors := errors.push s!"{lo.pretty}: σ does not fit Key.map"
        | some (.refused why) =>
          errors := errors.push s!"{lo.pretty}: flat block refused: {why.take 200}"
        | _ => errors := errors.push s!"{lo.pretty}: flat block not recorded"
  let t4 ← IO.monoMsNow
  lines := lines.push s!"Init+Std: {env.consts.size} constants, {blocks.blocks.size} blocks, \
    {ind.size} holding an inductive; load, canon and condense {t1 - t0} ms"
  lines := lines.push s!"compile with the drivers' service (fold, {4 * workers} tasks per wave): \
    {t2 - t1} ms"
  lines := lines.push s!"drivers' service: {report.summary}"
  lines := lines.push s!"the service alone, every inductive block (dependency order, one thread): \
    {t3 - t2} ms; {alone.summary}"
  lines := lines.push s!"the service alone, the blocks production asks for (one thread): \
    {t3e - t3} ms; {aloneBelow.summary}"
  lines := lines.push s!"its conversions alone: its {met.size} groups placed and converted \
    again (one thread): \
    {t3d - t3c} ms ({converted} converted)"
  lines := lines.push s!"the service alone over the IO pipeline's view (theorem and opaque bodies \
    canonicalized on demand), production's asks: {t3b - t3a} ms; {viewed.summary}"
  lines := lines.push s!"flat blocks: needed {needed}, accepted {accepted}; aux generation \
    {auxNs / 1000000} ms, flat blocks and checks {t4 - t3b} ms in all"
  for (k, why) in report.notAccepted do
    lines := lines.push s!"  block not accepted: {k.pretty}: {why.take 160}"
  for (g, why) in report.refused do
    lines := lines.push s!"  group refused: {g}: {why.take 160}"
  if let some e := report.error then errors := errors.push s!"no service: {e}"
  let nAsked := (ind.filter fun (_, ms) => prodAsks.selects env.get? ms).size
  unless report.blocks == nAsked do
    errors := errors.push s!"{report.blocks} blocks asked for, {nAsked} hold an inductive and \
      production's asks select them"
  unless alone.accepted == alone.blocks && alone.blocks == ind.size do
    errors := errors.push s!"the service over every inductive block: {alone.summary}"
  unless report.accepted == report.blocks do
    errors := errors.push s!"{report.blocks - report.accepted} inductive blocks not accepted"
  unless report.groupsRefused == 0 && report.groupsBlocked == 0 do
    errors := errors.push s!"groups refused {report.groupsRefused}, blocked {report.groupsBlocked}"
  unless aloneBelow.blocks == report.blocks && aloneBelow.accepted == report.accepted do
    errors := errors.push s!"the service alone disagrees: {aloneBelow.summary}"
  unless viewed == aloneBelow do
    errors := errors.push s!"the service over the IO pipeline's view disagrees: {viewed.summary}"
  -- AuxGen M4c: production's recorded canonical-block verdicts
  -- (`CompileEnv.auxReport`): every flat block this test needs is installed
  -- there too, and nothing is refused or differs
  let canonical := cenv.auxReport.canonicalSummary
  lines := lines.push s!"production's canonical verdicts: {canonical.line}"
  for (k, why) in canonical.findings.extract 0 4 do
    lines := lines.push s!"  {k.pretty}: {why.take 300}"
  unless canonical.refused == 0 && canonical.leanDiffer == 0 do
    errors := errors.push s!"production's canonical verdicts: {canonical.line}"
  unless canonical.installed == needed do
    errors := errors.push s!"production installed {canonical.installed} canonical flat blocks, \
      this test needs {needed}"
  if canonical.leanSame == 0 then
    errors := errors.push "production recorded no Lean-layout canonical verdict"
  -- AuxGen M5: production's acceptance table. Init+Std regenerates nothing
  -- (`auxgen-m5.md` §0), so no row is late, and the table agrees with the
  -- artifact's addresses
  let table := cenv.auxReport.table
  for l in Tests.Ix.AuxGen.BelowIxc.acceptanceLines table do lines := lines.push l
  let (accErrors, accInfo) := Tests.Ix.AuxGen.BelowIxc.acceptanceErrors ixe table
    (fun _ => false) (allowLate := false)
  for l in accInfo do lines := lines.push l
  for e in accErrors do errors := errors.push e
  return (errors, lines)

def run : IO UInt32 := do
  let (errors, lines) ← evaluate
  for l in lines do IO.println s!"[auxgen-flat-initstd] {l}"
  for e in errors.extract 0 40 do IO.println s!"[auxgen-flat-initstd] error: {e}"
  if errors.isEmpty then
    IO.println "[auxgen-flat-initstd] PASS"
    return 0
  IO.println s!"[auxgen-flat-initstd] FAIL: {errors.size} error(s)"
  return 1

end Tests.Ix.AuxGen.FlatBlockInitStd
