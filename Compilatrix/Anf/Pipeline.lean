import Compilatrix.Anf.Convert
import Compilatrix.Anf.Shrink
import Compilatrix.Anf.Inline
import Compilatrix.Anf.Specialize
import Compilatrix.Anf.Prune

/-! # The Phase 1 middle end

`Anf.Pipeline` (design note 02 §8, Phase 1): P1, then the steps of a
certificate. `produce` follows the Phase 1 schedule

  P1 → P2 → (P3 → P2)* → P4 → P2 → (P3 → P2)* → prune

(02's `P1 → P2 → P3 → P2 → P4 → P2 → P3 → P2`, with each inlining invocation
iterated as rounds, each round followed by a shrink, until the default
oracle has nothing left to inline or the round budget is spent), making every
heuristic choice natively; the recheck (`run`) re-runs the proved passes on
those choices (D17: P1 has no certificate; P2 reads rounds per global and two
size bounds; P3 inline rounds; P4 its decisions). `run` never searches, so it
is the function `Recheck.run` evaluates in the kernel.

The pipeline ends by pruning the globals unreachable from the roots (an
addition to 02's list: inlining and specialisation leave the originals
behind). A program that still has an `fn`, an `app` or a function-valued
`glob` is not `FirstOrder`; the Anf → Fir boundary (M1.F5) declines it in
Phase 1 (`residual` reports what remains). -/

namespace Compilatrix.Anf.Pipeline

/-- One certified step. -/
inductive Step where
  | shrink (cert : Shrink.Cert)
  | inline (round : Inline.Round)
  | specialize (cert : Specialize.Cert)
  | prune
  deriving Inhabited

/-- The middle end's certificate (the Phase 1 part of 02 §7.4's
`Anf.Oracle`). -/
structure Cert where
  shrink : Shrink.Params := {}
  steps : List Step := []
  deriving Inhabited

def Step.run (p : Shrink.Params) : Step → Program → Except String Program
  | .shrink c, P => Shrink.run p c P
  | .inline r, P => (Inline.round P r).map (·.1)
  | .specialize c, P => Specialize.run c P
  | .prune, P => pure (Prune.run P)

def Step.name : Step → String
  | .shrink _ => "P2"
  | .inline _ => "P3"
  | .specialize _ => "P4"
  | .prune => "prune"

/-- The recheck: P1, then the certificate's steps. -/
def run (cert : Cert) (L : Lam.Program) : Except String Program := do
  let P ← convert L
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

/-- The Phase 1 schedule with the default oracles. -/
def produce (B : Budgets := {}) (L : Lam.Program) : Except String Trace := do
  let p1 ← convert L
  let mut P := p1
  let mut steps : Array Step := #[]
  let mut stages : Array (String × Program) := #[("P1", p1)]
  let mut fires : Walk.Fires := {}
  let shrink := fun (P : Program) => Shrink.produce B.shrink P
  -- P2
  let (c, P2, f) ← shrink P
  P := P2; steps := steps.push (.shrink c); stages := stages.push ("P2", P); fires := fires.add f
  for phase in [0:2] do
    if phase == 1 then
      -- P4, then P2
      let sc := Specialize.produce B.spec 0 P
      P ← Specialize.run sc P
      steps := steps.push (.specialize sc); stages := stages.push ("P4", P)
      let (c, P2, f) ← shrink P
      P := P2; steps := steps.push (.shrink c); stages := stages.push ("P2", P); fires := fires.add f
    -- (P3, P2) rounds
    for _ in [0:B.inline.rounds] do
      let r := Inline.produce B.inline P
      if r.isEmpty then break
      let (P3, _) ← Inline.round P r
      steps := steps.push (.inline r); stages := stages.push ("P3", P3)
      let (c, P2, f) ← shrink P3
      P := P2; steps := steps.push (.shrink c); stages := stages.push ("P2", P); fires := fires.add f
  P := Prune.run P
  steps := steps.push .prune; stages := stages.push ("prune", P)
  return { cert := { shrink := B.shrink.params, steps := steps.toList }, stages := stages.toList, fires }

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

end Compilatrix.Anf.Pipeline
