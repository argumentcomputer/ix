import IxCC.Anf.Convert
import IxCC.Anf.Shrink
import IxCC.Anf.Inline
import IxCC.Anf.Specialize
import IxCC.Anf.Prune

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
runs after the first shrink (erasure's unused helpers) and last (inlining
and specialisation leave the originals behind). A program that still has an
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

/-- The middle end's certificate (the oracle decisions the Phase 1 passes read). -/
structure Cert where
  shrink : Shrink.Params := {}
  steps : List Step := []
  deriving Inhabited

/-- The nodes of `P`'s globals, counting each up to what is left of
`maxProgramNodes` and stopping once the total passes it. -/
def programNodesUpTo : List (GlobalId × GDef) → Nat → Nat
  | [], used => used
  | (_, gd) :: rest, used =>
    let used := used + gd.body.nodesUpTo (maxProgramNodes - used)
    if used > maxProgramNodes then used else programNodesUpTo rest used

/-- Refuse a program holding a global over `maxGlobalNodes` or deeper than
`maxDepth`, more than `maxProgramNodes` nodes in all, or more back-end work
than `maxBackWork`. The counts stop early and walk explicit worklists
(`Exp.nodesUpTo`, `Exp.depthUpTo`), so the check is cheap and shallow whatever
the program's size and depth. Inlining a callee doubles a mutually recursive
pair each round with one firing, so the walk's budgets alone do not bound
certificate rounds. -/
def checkGlobalNodes (P : Program) : Except String Program :=
  if !(P.globalList.all (fun (_, gd) => gd.body.nodesLe maxGlobalNodes) &&
      programNodesUpTo P.globalList 0 ≤ maxProgramNodes) then
    .error "middle end: a global or the program exceeds the node budget"
  else if !(P.globalList.all fun (_, gd) => gd.body.depthUpTo maxDepth maxGlobalNodes ≤ maxDepth) then
    .error "middle end: a global exceeds the depth budget"
  else if backWork P > maxBackWork then
    .error "middle end: the program exceeds the back end's work budget"
  else .ok P

/-- A step, then the size check (P2, P3 and P4 can grow the program; pruning
only removes globals). -/
def Step.run (p : Shrink.Params) : Step → Program → Except String Program
  | .shrink c, P =>
    -- one round count per global id
    if c.length ≤ P.size then Shrink.run p c P >>= checkGlobalNodes
    else .error "shrink: the certificate lists more globals than the program has"
  | .inline r, P =>
    -- a round lists each caller once, so no more callers than the program has globals
    if r.length ≤ P.size then Inline.round P r >>= fun x => checkGlobalNodes x.1
    else .error "inline: a round lists more callers than the program has globals"
  | .specialize c, P => Specialize.run c P >>= checkGlobalNodes
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
  deriving Inhabited

/-- What `produce` did: the certificate, the program after each step (for
the differential tests) and the shrink rule counts. -/
structure Trace where
  cert : Cert
  stages : List (String × Program)
  fires : Walk.Fires

/-- The most steps a certificate may hold (the cap `Recheck.checkMidCert`
applies to every certificate's middle end). -/
def maxSteps : Nat := 64

/-- The Phase 1 schedule with the default oracles, within what the re-run
accepts: P1 and every shrink step are followed by the re-run's size, depth
and back-end work check (`checkGlobalNodes`), and a program that fails it is
refused here, with the re-run's message, before the back end runs; an inline
round or a specialisation is taken through the re-run's own step
(`Step.run`), and one it refuses (a walk, step or program past its budgets)
is not taken: a refused round ends that invocation's rounds, and a refused
specialisation ends the schedule's phases, as one that adds no global does;
and a round or specialisation is only begun while the certificate has room
for its two steps and the final prune (`maxSteps`). Where the re-run would
accept every step anyway, none of these checks changes a choice. -/
def produce (B : Budgets := {}) (L : Lam.Program) : Except String Trace := do
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
      let .ok P4 := Step.run B.shrink.params (.specialize sc) P | break
      if phase > 1 && P4.size == P.size then break
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
      let .ok P3 := Step.run B.shrink.params (.inline r) P | break
      steps := steps.push (.inline r); stages := stages.push ("P3", P3)
      let (c, P2, f) ← Shrink.produce B.shrink P3
      P ← checkGlobalNodes P2; fires := fires.add f
      steps := steps.push (.shrink c); stages := stages.push ("P2", P)
  P := Prune.run P
  steps := steps.push .prune; stages := stages.push ("prune", P)
  return { cert := { shrink := B.shrink.params, steps := steps.toList }
           stages := stages.toList, fires }

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
