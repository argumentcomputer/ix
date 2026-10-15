import Ix.CanonM
import Ix.GraphM
import Ix.CondenseM
import Ix.LeanIngress
import Benchmarks.Kernel.CheckIxeStep

/-! # The Source-mode check one group at a time (untrusted harness)

`Ix.LeanIngress.checkSource` is all or nothing: the first group the ingress
refuses, or the first declaration the fold refuses, ends it. This driver
gives every declaration group of an environment its own verdict, as the
environment check does for Ixon records (`Benchmarks.Kernel.CheckIxeStep`):

* the groups (`groupsOf`) are converted (`convert`, on a pool of workers when
  asked), ordered (`graphOf`, `scheduleOf`) and lowered from the prelude's
  reader state (`lower`, `State.commit`), exactly as `leanIngress` does, except
  that a refused group does not end the run;
* the lowered declarations are prepared by `Frontend.preparePrelude` as the
  check prepares them, and checked one declaration at a time with
  `Checker.step` (phase A of the fold, then phase B on what it left pending),
  continuing past failures;
* a group that references a refused or blocked group is blocked and not
  checked; a group is accepted when every one of its declarations is.

None of this is a certified verdict; `checkSource` is. -/

namespace Tests.Ix.Kernel.SourceIngressStep

open Ix.LeanIngress
open Ix.Kernel.Reader (ReadError State Read CDecl CName Prelude)
open Benchmarks.Kernel.CheckIxeStep (Checker)

/-- An environment of Lean constants, canonicalized on `workers` workers. -/
def canon (consts : Array (Lean.Name × Lean.ConstantInfo)) (workers : Nat := 1) : Ix.Environment :=
  let size := (consts.size + workers - 1) / max workers 1
  let chunks := Ix.CanonM.chunks consts (max size 1)
  let tasks := chunks.map fun chunk => Task.spawn fun _ => Ix.CanonM.canonChunk chunk
  { consts := tasks.foldl (init := {}) fun m t => t.get.foldl (fun m (n, c) => m.insert n c) m }

/-- The condensation of an environment's reference graph, as the compiler's
driver computes it (`Ix.GraphM`, `Ix.CondenseM`). -/
def condense (env : Ix.Environment) (parallel : Bool := false) : Ix.CondensedBlocks :=
  Ix.CondenseM.run (if parallel then Ix.GraphM.envParallel env else Ix.GraphM.env env)

/-- `groups.map convert` on `workers` workers. -/
def convertAll (groups : Array Group) (workers : Nat) : Array (Except ReadError Converted) :=
  if workers ≤ 1 then groups.map convert else
  let size := (groups.size + workers - 1) / workers
  let tasks := (Ix.CanonM.chunks groups (max size 1)).map fun chunk =>
    Task.spawn fun _ => chunk.map convert
  tasks.flatMap Task.get

def kindOf : Group → String
  | .inductive .. => "inductive"
  | .definitions ms => match ms with
    | #[.defnInfo _] => "definition"
    | #[.thmInfo _] => "theorem"
    | #[.opaqueInfo _] => "opaque"
    | _ => s!"block({ms.size})"
  | .axiom _ => "axiom"
  | .quot _ => "quotient"
  | .invalid .. => "unplaced"

/-- One group's verdict. -/
structure Row where
  group : Nat
  names : Array CName
  kind : String
  /-- `accept`, `decline`, `reject` or `blocked` -/
  outcome : String
  reason : String
  micros : Nat := 0

def readOutcome : ReadError → String × String
  | .malformed m => ("reject", s!"ingress: {m}")
  | .declined m => ("decline", s!"ingress: {m}")

/-- What a run produced: the graph, the order (group indices), the rows by
group, the prepared declarations, and the times of its phases (ms). -/
structure Run where
  graph : Graph
  order : Array Nat
  rows : Array Row
  decls : Nat
  generated : Nat
  projRewrites : Nat
  times : Array (String × Nat)
  /-- Source mode's evidence (`Ix.LeanIngress.sourceEvidence`), and why each
  well-founded operation without evidence has none -/
  evidence : Ix.Kernel.Evidences := []
  evidenceErrors : List String := []

/-- **The run.** The evidence is Source mode's, from the prepared declarations
(`Ix.LeanIngress.sourceEvidenceReport`): the environment's certificate theorems,
closed, unless `evidence` is given. -/
def run (pre : Prelude) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) (workers : Nat := 1) (progress : Bool := false)
    (evidence : Option Ix.Kernel.Evidences := none) : IO Run := do
  let t0 ← IO.monoMsNow
  let groups ← IO.lazyPure fun _ => groupsOf env blocks
  let t1 ← IO.monoMsNow
  let converted ← IO.lazyPure fun _ => convertAll groups workers
  let t2 ← IO.monoMsNow
  let g ← IO.lazyPure fun _ => graphOf blocks groups converted
  let sched ← IO.lazyPure fun _ => scheduleOf g
  let t3 ← IO.monoMsNow
  let names : Array (Array CName) := groups.map (·.names.map ingressKey)
  let mut rows : Array (Option Row) := Array.replicate groups.size none
  -- lowering, in order, from the prelude's state
  let mut st : State := pre.state
  let mut lowered : Array CDecl := #[]
  let mut owner : Std.HashMap CName Nat := {}
  let mut generated := 0
  let mut rewrites := 0
  for (gi, c) in sched do
    let r := c >>= fun c => lower st c
    match r with
    | .error e =>
      let (o, why) := readOutcome e
      rows := rows.set! gi (some ⟨gi, names[gi]!, kindOf groups[gi]!, o, why, 0⟩)
    | .ok r =>
      st := st.commit r
      generated := generated + r.generated
      rewrites := rewrites + r.projRewrites
      for d in r.decls do
        for n in d.names do owner := owner.insert n gi
      lowered := lowered ++ r.decls
  let t4 ← IO.monoMsNow
  let prepared := Ix.Kernel.Frontend.preparePrelude pre.ix lowered
  let (ev, evErrors) ← match evidence with
    | some ev => pure (ev, [])
    | none => IO.lazyPure fun _ => Ix.LeanIngress.sourceEvidenceReport prepared
  let t4e ← IO.monoMsNow
  -- the step check
  let mut checker : Checker := {}
  let mut failed : Std.HashMap Nat Nat := {}
  for i in [0:groups.size] do
    if rows[i]!.isSome then failed := failed.insert i i
  let mut started : Std.HashSet Nat := {}
  let mut micros : Array Nat := Array.replicate groups.size 0
  let mut count := 0
  for d in prepared do
    count := count + 1
    if progress && count % 5000 == 0 then
      IO.eprintln s!"source-ingress: checked {count}/{prepared.size} declarations"
    let gi? := d.names.head?.bind (owner[·]?)
    if let some gi := gi? then
      if failed.contains gi then continue
      unless started.contains gi do
        started := started.insert gi
        if let some blocker := g.hard[gi]!.find? failed.contains then
          let root := failed.getD blocker blocker
          failed := failed.insert gi root
          rows := rows.set! gi (some ⟨gi, names[gi]!, kindOf groups[gi]!, "blocked",
            s!"{(names[root]!)[0]?.getD (.id .anonymous)}", 0⟩)
          continue
    let s0 ← IO.monoNanosNow
    let (c', err) ← IO.lazyPure fun _ => checker.step ev d
    let us := ((← IO.monoNanosNow) - s0) / 1000
    checker := c'
    match gi? with
    | some gi =>
      micros := micros.set! gi (micros[gi]! + us)
      if let some e := err then
        let (o, why) := Benchmarks.Kernel.CheckIxeStep.checkOutcome e
        failed := failed.insert gi gi
        rows := rows.set! gi (some ⟨gi, names[gi]!, kindOf groups[gi]!, o, why, micros[gi]!⟩)
    | none =>
      if let some e := err then
        IO.eprintln s!"source-ingress: prelude declaration {d.names.head?.getD (.id .anonymous)} failed: {e}"
  let t5 ← IO.monoMsNow
  let rows' := rows.zipIdx.map fun (r, gi) => r.getD
    ⟨gi, names[gi]!, kindOf groups[gi]!, "accept", "", micros[gi]!⟩
  return { graph := g, order := sched.map (·.1), rows := rows', decls := prepared.size, generated,
           projRewrites := rewrites,
           times := #[("group", t1 - t0), ("convert", t2 - t1), ("order", t3 - t2),
             ("lower", t4 - t3), ("evidence", t4e - t4), ("check", t5 - t4e)],
           evidence := ev, evidenceErrors := evErrors }

/-- Counts by outcome (constants and groups) and by outcome and reason
(constants). -/
structure Counts where
  constants : Std.HashMap String Nat := {}
  groups : Std.HashMap String Nat := {}
  reasons : Std.HashMap (String × String) Nat := {}

def Run.counts (r : Run) : Counts := Id.run do
  let mut c : Counts := {}
  for row in r.rows do
    let k := row.names.size
    c := { c with
      constants := c.constants.insert row.outcome (c.constants.getD row.outcome 0 + k)
      groups := c.groups.insert row.outcome (c.groups.getD row.outcome 0 + 1) }
    unless row.outcome == "accept" || row.outcome == "blocked" do
      let key := (row.outcome, row.reason)
      c := { c with reasons := c.reasons.insert key (c.reasons.getD key 0 + k) }
  return c

/-- The row of the group that declares `n`. -/
def Run.rowOf (r : Run) (n : CName) : Option Row :=
  r.rows.find? (·.names.contains n)

end Tests.Ix.Kernel.SourceIngressStep
