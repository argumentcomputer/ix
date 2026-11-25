import IxCC.Anf.Convert
import IxCC.Anf.Shrink
import IxCC.Anf.Inline
import IxCC.Anf.Specialize
import IxCC.Anf.Prune
import IxCC.Anf.Defun
import IxCC.Anf.Pipeline.PostCert

/-! # The Phase 1 middle end

`Anf.Pipeline` (Phase 1): P1, then the steps of a
certificate. `produce` follows the Phase 1 schedule

  P1 → P2 → prune → (P3 → P2)* → P4 → P2 → (P3 → P2)* → prune

(the designed order `P1 → P2 → P3 → P2 → P4 → P2 → P3 → P2`, with each inlining invocation
iterated as rounds, each round followed by a shrink, until the default
oracle has nothing left to inline or the round budget is spent), making every
heuristic choice natively; the recheck (`run`) re-runs the proved passes on
those choices (D17: P1 has no certificate; P2 reads rounds per global and two
size bounds; P3 inline rounds; P4 its decisions). `run` never searches, so it
is the function `Recheck.run` evaluates in the kernel.

Pruning the globals unreachable from the roots (an addition to the designed order)
runs after the first shrink (erasure's unused helpers), inside every P3 and
P4 step (inlining and specialisation leave the originals behind: the step
drops them before the back end's work is measured, `checkReachable`, so a
round or a specialisation is taken or refused on what the roots reach, and
the steps after it neither walk nor count dead globals) and last (what the
shrink steps since have cut off). A program that still has an
`fn`, an `app` or a function-valued `glob` is not `FirstOrder`; the
Anf → Fir boundary declines it in
Phase 1 (`residual` reports what remains). -/

namespace IxCC.Anf.Pipeline

/-- One certified step. -/
inductive Step where
  | shrink (cert : Shrink.Cert)
  | inline (round : Inline.Round)
  | specialize (cert : Specialize.Cert)
  | prune
  deriving Inhabited

/-- The middle end's certificate (the oracle decisions the Phase 1 passes read,
plus optional post-P8 optimization decisions omitted for plain programs). -/
structure Cert where
  shrink : Shrink.Params := {}
  steps : List Step := []
  post : Option PostCert := none
  deriving Inhabited

/-- A step, then the size check (P2, P3 and P4 can grow the program; pruning
only removes globals). P3 and P4 leave behind the globals whose every use they
replaced, so their check is `checkReachable`: the step's result is what the
roots reach of the pass's output, and the back end's work is measured on that.
The ids a later step names are therefore those of the pruned program. -/
def Step.run (p : Shrink.Params) : Step → Program → Except String Program
  | .shrink c, P =>
    -- one round count per global id
    if c.length ≤ P.size then Shrink.run p c P >>= checkGlobalNodes
    else .error "shrink: the certificate lists more globals than the program has"
  | .inline r, P =>
    -- a round lists each caller once, so no more callers than the program has globals
    if r.length ≤ P.size then Inline.round P r >>= fun x => checkReachable x.1
    else .error "inline: a round lists more callers than the program has globals"
  | .specialize c, P => Specialize.run c P >>= checkReachable
  | .prune, P => pure (Prune.run P)

def Step.name : Step → String
  | .shrink _ => "P2"
  | .inline _ => "P3"
  | .specialize _ => "P4"
  | .prune => "prune"

/-- Refuse a Lam program holding a global over `maxLamNodes` or deeper than
`maxLamDepth` (both counted over worklists with an early exit), before ANF
conversion recurses over it. -/
def checkLamNodes (L : Lam.Program) : Except String Lam.Program :=
  if L.globalList.all fun (_, gl) => lamNodesUpTo maxLamNodes gl.body ≤ maxLamNodes then
    if L.globalList.all fun (_, gl) => lamDepthUpTo maxLamDepth maxLamNodes gl.body ≤ maxLamDepth then .ok L
    else .error "middle end: a Lam global exceeds the depth budget"
  else .error "middle end: a Lam global exceeds the node budget"

/-- The recheck: the Lam size check, P1 and the size check, then the
certificate's steps. -/
def run (cert : Cert) (L : Lam.Program) : Except String Program := do
  let P ← checkLamNodes L >>= convert >>= checkGlobalNodes
  cert.steps.foldlM (fun P s => s.run cert.shrink P) P

structure Budgets where
  shrink : Shrink.Budgets := {}
  inline : Inline.Budgets := {}
  spec : Specialize.Budgets := {}
  /-- Retry an inline round the re-run refuses, without the callers whose
  walk it refuses alone (`produce`). Producer only. -/
  retryInline : Bool := true
  deriving Inhabited

/-- What `produce` did: the certificate, the program after each step (for
the differential tests) and the shrink rule counts. -/
structure Trace where
  cert : Cert
  stages : List (String × Program)
  fires : Walk.Fires
  /-- When `firstOrder P = false`, the producer's post-P8 output matching
  `cert.post` (untrusted producer metadata; never recorded in `Cert`). -/
  postOut : Option Program := none

/-- The most steps a certificate may hold (the cap `Recheck.checkMidCert`
applies to every certificate's middle end). -/
def maxSteps : Nat := 64

/-- Count non-`tick` nodes of `todo`, stopping as soon as the count passes `cap`. -/
private def countNonTickUpTo (cap : Nat) : Nat → List Exp → Nat → Nat
  | 0, _, acc => acc
  | _, [], acc => acc
  | fuel + 1, e :: todo, acc =>
    if acc > cap then acc
    else
      match e with
      | .bind _ b body =>
        match b with
        | .fn _ fb => countNonTickUpTo cap fuel (fb :: body :: todo) (acc + 2)
        | .con _ as | .prim _ as | .call _ as | .app _ as =>
          countNonTickUpTo cap fuel (body :: todo) (acc + as.length + 2)
        | .atom _ | .glob _ | .proj .. => countNonTickUpTo cap fuel (body :: todo) (acc + 2)
      | .join _ _ b body => countNonTickUpTo cap fuel (b :: body :: todo) (acc + 1)
      | .jump _ as => countNonTickUpTo cap fuel todo (acc + as.length + 1)
      | .case _ alts d => countNonTickUpTo cap fuel (alts.map Alt.body ++ d.toList ++ todo) (acc + 1)
      | .ret _ | .trap => countNonTickUpTo cap fuel todo (acc + 1)
      | .tick body => countNonTickUpTo cap fuel (body :: todo) acc

private def nonTickNodesLe (e : Exp) (cap : Nat) : Bool :=
  countNonTickUpTo cap (maxGlobalNodes + 2) [e] 0 ≤ cap

/-- Total call-site count per global across `P`. -/
private def callSiteCounts (P : Program) : Src.NatMap Nat :=
  P.globalList.foldl (fun m (_, gd) =>
    gd.body.sites.foldl (fun m g => m.insert g (m.getD g 0 + 1)) m) .leaf

/-- Post-P5 inline oracle: inlines non-recursive, non-dispatcher callees that are
single-call-site helpers (≤ 512 nodes, zero code duplication) or small bodies
ignoring `tick` inflation (≤ 160 non-tick nodes). -/
private def producePostExtraRound (P : Program) (noInline : List Key.GKey) : Inline.Round :=
  let recs := Inline.directRecursive P
  let counts := callSiteCounts P
  let inl : Src.NatMap Bool :=
    Src.NatMap.ofList (P.globalList.map fun (g, gd) =>
      let ok :=
        !Inline.isNoInlineKey noInline gd.key &&
        !Walk.isDispatchKey gd.key &&
        !recs.contains g &&
        (gd.ps.isEmpty ||
          nonTickNodesLe gd.body 160 ||
          (counts.getD g 0 == 1 && gd.body.nodesLe 512 && !P.roots.contains g) ||
          (match gd.key with
           | .byName .. | .wrapper .. => true
           | _ => false))
      (g, ok))
  P.globalList.filterMap fun (f, gd) =>
    if Walk.isDispatchKey gd.key then none
    else
      let sites : Src.NatSet := gd.body.sites.foldl (fun s g => s.insert g) .leaf
      let refs := (gd.body.refs.foldl (init := ((.leaf : Src.NatSet), ([] : List GlobalId)))
        fun (seen, acc) g => if seen.contains g then (seen, acc) else (Src.NatSet.insert seen g, g :: acc)).2.reverse
      let cs := refs.filter fun g =>
        g != f && (match P.global? g with
          | some gd' => inl.getD g false && (gd'.ps.isEmpty || sites.contains g)
          | none => false)
      if cs.isEmpty then none else some (f, cs.take Inline.maxCertCallees)

private def refinePostExtraLoop (B : Budgets) :
    Nat → Program → List PostStep → Program × List PostStep
  | 0, P, revSteps => (P, revSteps)
  | rem + 1, P, revSteps =>
    if revSteps.length + 3 > maxPostSteps then (P, revSteps)
    else
      let r := producePostExtraRound P B.inline.noInline
      if r.isEmpty || !Inline.checkCert r then (P, revSteps)
      else
        let res :=
          match PostStep.run B.shrink.params (.inline r) P with
          | .ok P3 => some (r, P3)
          | .error _ =>
            let r' := r.filter fun e => (PostStep.run B.shrink.params (.inline [e]) P).isOk
            if r'.isEmpty then none
            else (PostStep.run B.shrink.params (.inline r') P).toOption.map (r', ·)
        match res with
        | none => (P, revSteps)
        | some (r', P3) =>
          let steps1 := PostStep.inline r' :: revSteps
          let (P2, steps2) :=
            match Shrink.produce B.shrink P3 with
            | .ok (c, P2', _) =>
              if c.any (· > 0) && c.length ≤ P3.size && Shrink.checkCert c then
                match checkGlobalNodes P2' with
                | .ok P2'' => (P2'', PostStep.shrink c :: steps1)
                | .error _ => (P3, steps1)
              else (P3, steps1)
            | .error _ => (P3, steps1)
          let (P4, steps3) :=
            if steps2.length + 1 ≤ maxPostSteps then
              let Pp := Prune.run P2
              if Pp.size < P2.size then (Pp, PostStep.prune :: steps2) else (P2, steps2)
            else (P2, steps2)
          refinePostExtraLoop B rem P4 steps3

/-- Follow `producePostBy` with up to 4 rounds of post-P5 single-use / tick-free
inlining + shrink + prune, keeping the original `(pc, Qout)` if any budget check fails. -/
private def refinePostExtra (B : Budgets) (pc : PostCert) (Qout : Program) : PostCert × Program :=
  let (Q', revSteps) := refinePostExtraLoop B 4 Qout pc.steps.reverse
  let pc' : PostCert := { pc with steps := revSteps.reverse }
  if checkPostCert pc' && firstOrder Q' then
    match checkGlobalNodes Q' with
    | .ok Q'' => (pc', Q'')
    | .error _ => (pc, Qout)
  else (pc, Qout)

/-- The Phase 1 schedule with the default oracles, within what the re-run
accepts: P1 and every shrink step are followed by the re-run's size, depth
and back-end work check (`checkGlobalNodes`), and a program that fails it is
refused here, with the re-run's message, before the back end runs; an inline
round or a specialisation is taken through the re-run's own step
(`Step.run`: the pass, then `checkReachable`, which measures the back end's
work on the globals the roots still reach and keeps only those), and one it
refuses (a walk, step or program past its budgets)
is not taken: a refused round is retried once without the callers whose walk
the re-run refuses alone (`Budgets.retryInline`), and ends that invocation's
rounds if it is still refused or no caller is left; a refused
specialisation ends the schedule's phases, as one that adds no global does;
and a round or specialisation is only begun while the certificate has room
for its two steps and the final prune (`maxSteps`). Where the re-run would
accept every step anyway, none of these checks changes a choice. -/
def produceOnce (B : Budgets := {}) (L : Lam.Program) : Except String Trace := do
  let p1 ← checkLamNodes L >>= convert >>= checkGlobalNodes
  let mut P := p1
  let mut steps : Array Step := #[]
  let mut stages : Array (String × Program) := #[("P1", p1)]
  let mut fires : Walk.Fires := {}
  -- P2, then drop what the roots never reach (erasure's wrappers and helpers)
  let (c, P2, f) ← Shrink.produce B.shrink P
  P ← checkGlobalNodes P2; fires := fires.add f
  steps := steps.push (.shrink c); stages := stages.push ("P2", P)
  P := Prune.run P
  steps := steps.push .prune; stages := stages.push ("prune", P)
  for phase in [0:4] do
    if phase > 0 then
      -- P4, then P2
      if steps.size + 3 > maxSteps then break
      let sc := Specialize.produce B.spec (phase - 1) P
      -- the re-run's step (`Step.run`) in its two halves: the pass, whose
      -- output still holds the originals, so that its size says whether it
      -- added a global; then the step's check, which keeps what the roots reach
      let .ok S := Specialize.run sc P | break
      if phase > 1 && S.size == P.size then break
      let .ok P4 := checkReachable S | break
      P := P4
      steps := steps.push (.specialize sc); stages := stages.push ("P4", P)
      let (c, P2, f) ← Shrink.produce B.shrink P
      P ← checkGlobalNodes P2; fires := fires.add f
      steps := steps.push (.shrink c); stages := stages.push ("P2", P)
    -- (P3, P2) rounds
    for _ in [0:B.inline.rounds] do
      if steps.size + 3 > maxSteps then break
      let r := Inline.produce B.inline P
      if r.isEmpty then break
      -- a round the re-run refuses is retried once without the callers whose
      -- walk the re-run refuses alone (each caller's walk is independent of
      -- the others'): at most one re-run per caller and one of the rest
      let some (r, P3) := (match Step.run B.shrink.params (.inline r) P with
          | .ok P3 => some (r, P3)
          | .error _ =>
            if !B.retryInline then none else
            let r := r.filter fun e => (Step.run B.shrink.params (.inline [e]) P).isOk
            if r.isEmpty then none
            else (Step.run B.shrink.params (.inline r) P).toOption.map (r, ·)) | break
      steps := steps.push (.inline r); stages := stages.push ("P3", P3)
      let (c, P2, f) ← Shrink.produce B.shrink P3
      P ← checkGlobalNodes P2; fires := fires.add f
      steps := steps.push (.shrink c); stages := stages.push ("P2", P)
  P := Prune.run P
  steps := steps.push .prune; stages := stages.push ("prune", P)
  let (post, postOut) : Option PostCert × Option Program :=
    if firstOrder P then (none, none)
    else match defun P with
      | .ok Q8 =>
        let (pc0, Qout0) := producePostBy B.shrink.params
          (fun Q => match Shrink.produce B.shrink Q with
            | .ok (c, Q', _) => .ok (c, Q')
            | .error e => .error e)
          P.size Q8 B.inline.noInline
        let (pc, Qout) := refinePostExtra B pc0 Qout0
        (some pc, some Qout)
      | .error _ => (none, none)
  return { cert := { shrink := B.shrink.params, steps := steps.toList, post }
           stages := stages.toList, fires, postOut }

/-- Run `attempt` with the inline-round retry if `retry`, and without it when
that fails: a retried round's larger program may fail a budget checked later
(the whole program's nodes or back-end work after the next shrink step, or a
later stage), where the run without the retry would not. -/
def withRetryFallback {ε α : Type} (retry : Bool) (attempt : Bool → Except ε α) : Except ε α :=
  match attempt retry with
  | .ok a => .ok a
  | .error e => if retry then attempt false else .error e

/-- `produceOnce`, falling back to the run without the inline-round retry
when the run with it fails (`withRetryFallback`). On higher-order closures
(`post.isSome`), retries once with `smallJoin := Shrink.maxCertSmallJoin` (64)
so defunctionalized join-of-closure dispatchers simplify cleanly without
affecting first-order Phase 1 certificates. -/
def produce (B : Budgets := {}) (L : Lam.Program) : Except String Trace := do
  let tr ← withRetryFallback B.retryInline fun retry => produceOnce { B with retryInline := retry } L
  if tr.cert.post.isSome && B.shrink.params.smallJoin < Shrink.maxCertSmallJoin then
    let B' : Budgets :=
      { B with shrink := { B.shrink with params := { B.shrink.params with smallJoin := Shrink.maxCertSmallJoin } } }
    match withRetryFallback B'.retryInline fun retry => produceOnce { B' with retryInline := retry } L with
    | .ok tr' => return tr'
    | .error _ => return tr
  else
    return tr

/-! ## What the Anf → Fir boundary will decline -/

/-- Residual higher-order forms of a program (P8's input in Phase 2): local
closures, unknown calls and function-valued `glob`s, with the global they
occur in. -/
structure Residual where
  fns : List GlobalId := []
  apps : List GlobalId := []
  globs : List GlobalId := []
  deriving Inhabited

mutual

def countFn : Exp → Nat × Nat × List GlobalId
  | .bind _ b e =>
    let (a, c, gs) := countFnBind b
    let (a', c', gs') := countFn e
    (a + a', c + c', gs ++ gs')
  | .join _ _ b e =>
    let (a, c, gs) := countFn b
    let (a', c', gs') := countFn e
    (a + a', c + c', gs ++ gs')
  | .case _ alts d =>
    let (a, c, gs) := countFnAlts alts
    let (a', c', gs') := match d with
      | some e => countFn e
      | none => (0, 0, [])
    (a + a', c + c', gs ++ gs')
  | .tick e => countFn e
  | .jump .. | .ret _ | .trap => (0, 0, [])

def countFnBind : Bind → Nat × Nat × List GlobalId
  | .fn _ b => let (a, c, gs) := countFn b; (a + 1, c, gs)
  | .app .. => (0, 1, [])
  | .glob g => (0, 0, [g])
  | _ => (0, 0, [])

def countFnAlts : List Alt → Nat × Nat × List GlobalId
  | [] => (0, 0, [])
  | .mk _ _ b :: as =>
    let (a, c, gs) := countFn b
    let (a', c', gs') := countFnAlts as
    (a + a', c + c', gs ++ gs')

end

/-- The residual higher-order forms. -/
def residual (P : Program) : Residual :=
  P.globalList.foldl (fun r (g, gd) =>
    let (fns, apps, globs) := countFn gd.body
    let fnGlobs := globs.filter fun h => (P.arity? h).any (· > 0)
    { fns := if fns > 0 then r.fns ++ [g] else r.fns
      apps := if apps > 0 then r.apps ++ [g] else r.apps
      globs := if fnGlobs.isEmpty then r.globs else r.globs ++ [g] }) {}

end IxCC.Anf.Pipeline
