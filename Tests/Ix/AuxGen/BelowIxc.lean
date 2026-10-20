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
   (`compileEnvFold`: `fallback`, the `.below` asks), by their serialized
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
    samples := (a.samples ++ b.samples).extract 0 24 }

def statsLine (st : Ix.AuxGen.IxcStats) : String :=
  s!"queries {st.queries} (fast path: Ix.Tc {st.tcFast}, IxC {st.ixcFast}); \
    IxC answered {st.answered}: equal {st.equal}, differ {st.differ}; refused {st.refused}, \
    scopes refused {st.scopesRefused}; flat blocks installed {st.flatInstalled}, \
    refused {st.flatRefused}; isDefEq decisions {st.decisions}: equal {st.decisionsEqual}, \
    differ {st.decisionsDiffer}; inferType/whnf {st.exprQueries}, IxC answered \
    {st.exprAnswered}; generated .below admitted {st.belowAdmitted}, refused {st.belowRefused}"

/-- **One block's aux tail with the IxC arm**, as the driver's tail generates
the patches (`sortConsts`, the classes restricted to Lean's `all`,
`generateAuxPatches`), over `oracle`: the tail's counts; `none` for a block
with no inductive class. -/
def tailStats (cenv : Ix.CompileM.CompileEnv) (lo : Ix.Name) (all : Array Ix.Name)
    (oracle : Ix.AuxGen.AuxOracle) : Except String (Option Ix.AuxGen.IxcStats) :=
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := {}, current := lo, mutCtx := default, univCtx := [] }
  let act : Ix.CompileM.CompileM (Option Ix.AuxGen.IxcStats) := do
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
    return some ctx.ixcStats
  match Ix.CompileM.CompileM.run cenv blockEnv {} act with
  | .ok (r, _) => .ok r
  | .error e => .error (toString e)

/-- **Shadow agreement** over every block that holds an inductive, each over
its level's snapshot of a run-ahead over the input with production's asks: the counts summed, and
the blocks whose tail failed. -/
def shadow (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (cenv : Ix.CompileM.CompileEnv) :
    IO (Ix.AuxGen.IxcStats × Array String) := do
  let levels := Ix.CompileM.scheduleLevels blocks (Ix.CompileM.FoldSchedule.of blocks)
  let ra := Ix.AuxGen.Source.RunAhead.start env.get? blocks levels ({} : Ix.CompileM.AuxIxcOptions).asks
  let mut total : Ix.AuxGen.IxcStats := {}
  let mut errors : Array String := #[]
  for (lo, members) in inductiveBlocks env blocks do
    let key := Ix.CompileM.blockKey lo ((blocks.blocks.get? lo).getD {})
    let some t := ra.runFor key
      | do errors := errors.push s!"{lo.pretty}: in no level of the schedule"; continue
    let oracle := Ix.AuxGen.Ixc.oracleOfRun .shadow false (fun _ => t.get) (ra.membersFor key)
    match ← IO.lazyPure fun _ => tailStats cenv lo members oracle with
    | .error e => errors := errors.push s!"{lo.pretty}: aux generation: {e.take 200}"
    | .ok none => pure ()
    | .ok (some st) => total := addStats total st
  return (total, errors)

/-- A fold's serialized environment. -/
def serialized (r : Except String (Ixon.Env × Nat × Ix.CompileM.CompileEnv)) : Except String ByteArray := do
  let (ixe, _, _) ← r
  Ixon.serEnv ixe

/-- The measurement fold in `opts`, against the production fold's bytes
`expected`: whether they are equal, the run-ahead's report line, the time. -/
def foldIxc (opts : Ix.CompileM.AuxIxcOptions) (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (expected : ByteArray) (width : Nat) : IO (Bool × String × Nat) := do
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure fun _ =>
    Ix.CompileM.compileEnvFoldWithSource env blocks (width := width) (aux := opts)
  let t1 ← IO.monoMsNow
  match r with
  | .error e => return (false, s!"failed: {e.take 300}", t1 - t0)
  | .ok (out, report) =>
    match serialized (.ok out) with
    | .error e => return (false, s!"serialization failed: {e}", t1 - t0)
    | .ok bytes => return (bytes == expected, report.summary, t1 - t0)

/-- The modes the folds are compared in, with whether equality is asserted. -/
def foldModes : Array (String × Ix.CompileM.AuxIxcOptions × Bool) :=
  #[("shadow", { mode := .shadow }, true),
    ("failClosed", { mode := .failClosed }, true),
    ("shadow, every inductive block asked", { mode := .shadow, asks := .inductive }, true),
    ("failClosed, every inductive block asked", { mode := .failClosed, asks := .inductive }, true),
    -- M2b's production (both kernels asked); production is lazy since AuxGen M3
    ("fallbackEager", { mode := .fallbackEager }, true)]

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
    let (same, report, ms) ← foldIxc opts env blocks expected width
    lines := lines.push s!"fold, {name}: {ms} ms; \
      {if same then "bytes equal to production" else "bytes DIFFER from production"}; \
      run-ahead: {report}"
    if asserted && !same then errors := errors.push s!"{name}: the fold's bytes differ from production"
  let t2 ← IO.monoMsNow
  let (st, tailErrors) ← shadow env blocks cenv
  let t3 ← IO.monoMsNow
  lines := lines.push s!"shadow, per block ({t3 - t2} ms): {statsLine st}"
  for s in st.samples do lines := lines.push s!"  {s.take 300}"
  for e in tailErrors do errors := errors.push e
  if st.differ != 0 then
    errors := errors.push s!"{st.differ} IxC answers spelled differently from Ix.Tc's (stop rule)"
  if st.queries == 0 then errors := errors.push "no level question was asked"
  if st.decisionsDiffer != 0 then
    errors := errors.push s!"{st.decisionsDiffer} isDefEq decisions differ from Ix.Tc's"
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

def suite : List TestSeq := [fixtures, egressFixtures]

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
