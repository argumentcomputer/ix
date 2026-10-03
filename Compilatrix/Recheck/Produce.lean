import Compilatrix.Recheck.Run
import Compilatrix.Ixon.V3.Env
import Compilatrix.Ixon.V3.Tc.Driver
import Compilatrix.Src.Ingress
import Compilatrix.Src.Pinned
import Compilatrix.Src.Hints
import Compilatrix.Src.Table.Build
import Compilatrix.Src.Relevance.Annotate
import Compilatrix.Src.Admit
import Compilatrix.Xv.Alloc.Driver
import Compilatrix.Xv.Stacking.Run
import Compilatrix.X86.Layout.Tunnel

/-! # Ingress, `produce` and `compile`

The untrusted half of the compiler (design note 00 "Produce and recheck",
D17) and the whole compiler:

* `ingress` (01 §1.2; not on the recheck path): strict v3 decoding, the
  `compilatrix/k1-equations/1` sidecar (the roots chosen by name, and the
  table proposals), erased typing, ingress into a `Src.Program` and the
  pinned identities;
* `produce cfg input`: every search and oracle, natively and unconstrained
  (arrays, hash maps): `Table.build` on the sidecar's proposals, the
  relevance annotator, `Admit` (a producer gate: a program outside the
  admitted fragment is declined here), the middle end's default oracles
  (`Anf.Pipeline.produce`), linear scan with its validated all-slots
  fallback (`Alloc.run`), and the frame-layout and block-order oracles; the
  result is the certificate;
* `compile = ingress; produce; Recheck.run`: the object is `run`'s, never
  `produce`'s. -/

namespace Compilatrix.Recheck

open Compilatrix.Ixon
open Compilatrix.Src (CId)

/-- Ingress's output: the program `run` starts from, and what `produce`
also reads (the decoded environment for the annotator; the sidecar for the
table proposals and the roots' names). -/
structure Input where
  env : V3.Env
  hints : Src.Hints
  program : Src.Program
  /-- The roots' names, by root position (the sidecar's; `root<i>` where
  it has none). -/
  names : List String

/-- The sidecar roots named `names`, in that order (every root when `names`
is empty); an unknown or repeated name is an error. -/
def selectRoots (roots : Array (Ixon.Address × Option String)) (names : List String) :
    Except Err (Array (Ixon.Address × Option String)) := do
  if names.isEmpty then return roots
  let mut out := #[]
  for n in names do
    if out.any (·.2 == some n) then
      throw { stage := .cli, code := "cli.root", message := s!"root {n} is named twice" }
    match roots.find? (·.2 == some n) with
    | some r => out := out.push r
    | none =>
      let known := roots.toList.filterMap (·.2)
      throw { stage := .cli, code := "cli.root", message := s!"no root named {n} in the sidecar (it names {known})" }
  return out

/-- Ingress: decode, choose the roots, erased typing (unless `typecheck` is
off), `Src` ingress and the pinned identities. -/
def ingress (bytes : ByteArray) (equations : Lean.Json) (roots : List String := [])
    (typecheck : Bool := true) : Except Err Input := do
  let env ← (V3.decodeAnonymousEnv bytes).mapError fun m => { stage := .ingress, code := "decode", message := m }
  let hints ← (Src.Hints.ofK1Json equations).mapError fun m => { stage := .ingress, code := "hints", message := m }
  let chosen ← selectRoots hints.roots roots
  if chosen.isEmpty then
    throw { stage := .ingress, code := "roots", message := "the sidecar names no root" }
  let hints := { hints with roots := chosen }
  if typecheck then
    (V3.Tc.checkEnv env).mapError fun m => { stage := .ingress, code := "typing", message := m }
  let p ← (Src.Ingress.ofEnv env (chosen.map (·.1))).mapError fun m =>
    { stage := .ingress, code := "ingress", message := m }
  let p := { p with known := Src.Pinned.known p }
  let names := chosen.toList.zipIdx.map fun ((_, n), i) => n.getD s!"root{i}"
  pure { env, hints, program := p, names }

/-- What `produce` found beside the certificate, for reports. -/
structure Produced where
  cert : Cert
  tableDiags : Array Src.Diag
  tableStats : Src.Table.Stats
  fires : Anf.Walk.Fires
  /-- Anf's stages as the producer computed them. -/
  stages : List (String × Anf.Program)
  alloc : List Xv.Alloc.Outcome

/-- Untrusted names from the sidecar, for diagnostics. -/
def sidecarName (h : Src.Hints) (a : Ixon.Address) : Option String :=
  match h.roots.find? (·.1 == a) with
  | some (_, n) => n
  | none => (h.proposals.find? (·.subject == a)).bind (·.name?)

/-- The producer: every oracle, run natively (see the module note). -/
def produceWith (cfg : Config) (inp : Input) : Except Err Produced := do
  let P := inp.program
  let (table, tableDiags, tableStats) := Src.Table.build cfg.table P inp.hints.proposals
  let p0 := { P with table }
  let ann ← (Src.Relevance.annotate inp.env p0).mapError fun m =>
    { stage := .relevance, code := "relevance-oracle", message := m }
  let (src, checked) ← match Src.Recheck.annotation p0 ann with
    | .ok r => pure r
    | .error (.install m) => throw { stage := .relevance, code := "relevance-S1", message := m }
    | .error (.relevance errs) =>
      throw { stage := .relevance, code := s!"relevance-{(errs[0]?.map (·.rule)).getD "S1"}"
              message := "; ".intercalate (errs.toList.take 8 |>.map (·.render p0)) }
    | .error (.table m) => throw { stage := .table, code := "table.entry", message := m }
  match Src.admit src (sidecarName inp.hints) cfg.admit with
  | .ok _ => pure ()
  | .error diags =>
    let d := diags[0]?.getD (Src.Diag.of "admit" "rejected")
    throw { Err.ofDiag .admit d with message := "; ".intercalate (diags.toList.map fun d => (splitCode d.render).2) }
  let (lam, _) ← (Lam.erase src checked).mapError Err.ofErase
  let trace ← (Anf.Pipeline.produce cfg.budgets lam).mapError fun m =>
    { stage := .anf, code := "anf.produce", message := m }
  let anf := ((trace.stages.getLast?).map (·.2)).getD default
  let fir ← (Fir.lower anf).mapError Err.ofFir
  let C := Cfg.lower (Own.immortal fir)
  checkParams cfg C (C.exports.zipIdx.map fun (f, i) => (i, f))
  let lowered ← (Rt.lower { names := cfg.names } C).mapError Err.ofRt
  let (xv, _) ← (Xv.Select.run lowered.program).mapError Err.ofSelect
  let r ← (Xv.Alloc.run cfg.env xv).mapError fun m => { stage := .alloc, code := "alloc.fallback", message := m }
  let layouts := Xv.Stacking.produce r.program
  let stacked ← (Xv.Stacking.run r.program layouts lowered.reps cfg.env).mapError (Err.ofBackend ∘ .stacking)
  let order := X86.Layout.Order.produce (X86.Layout.tunnel stacked.program) stacked.shape
  pure { cert := { table := Src.Table.TableCert.ofTable table, relevance := ann, mid := trace.cert
                   alloc := r.outs, frames := layouts, order }
         tableDiags, tableStats, fires := trace.fires, stages := trace.stages, alloc := r.outcomes }

/-- `produce` (D17): the certificate. -/
def produce (cfg : Config) (inp : Input) : Except Err Cert :=
  (·.cert) <$> produceWith cfg inp

/-- The configuration for an input: its root names unless the configuration
gives some. -/
def Config.forInput (cfg : Config) (inp : Input) : Config :=
  if cfg.names.isEmpty then { cfg with names := inp.names } else cfg

/-- The compiler on an ingested program: `produce`, then `run` on its
certificate. -/
def compileInput (cfg : Config) (inp : Input) : Except Err (Cert × Artifact) := do
  let cfg := cfg.forInput inp
  let c ← produce cfg inp
  let a ← run cfg inp.program c
  pure (c, a)

/-- The compiler: ingress, `produce`, `run`. -/
def compile (cfg : Config) (bytes : ByteArray) (equations : Lean.Json) (roots : List String := [])
    (typecheck : Bool := true) : Except Err (Cert × Artifact) := do
  compileInput cfg (← ingress bytes equations roots typecheck)

end Compilatrix.Recheck
