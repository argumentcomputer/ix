import IxCC.Anf.Walk

/-! # P2: shrink

`Anf.Shrink` (P2): the walk's rewrite rules (`Walk`,
`Cfg.shrink`), iterated per global. A **round** is one walk over a global's
body; a round in which no rule fires returns its input unchanged, so the
fixpoint is idempotent.

**Certificate** (D17): the number of rounds per global, in id order, and the
two size bounds the rules read (`Params`). `produce` iterates each global to
its fixpoint within the round budget and records the rounds it took; the
re-run (`run`) performs exactly those rounds, so no fixpoint test runs in the
kernel. Every round is correct on its own, so every certificate gives a
correct program (fewer rounds, less shrinking). The per-round rule counts
(`Walk.Fires`) are the rewrite trace's census: reported, not needed by the
re-run. -/

namespace IxCC.Anf.Shrink

/-- Rounds per global, in id order (missing entries mean none). -/
abbrev Cert := List Nat

/-- Maximum shrink rounds per global allowed in a certificate. -/
def maxCertRounds : Nat := 64

/-- Maximum globals listed in a shrink certificate. -/
def maxCertGlobals : Nat := 100000

/-- Maximum case-of-case threshold allowed in certificate parameters. -/
def maxCertCaseOfCase : Nat := 512

/-- Maximum small-join threshold allowed in certificate parameters. -/
def maxCertSmallJoin : Nat := 64

/-- The bounds the rules read (certificate data). -/
structure Params where
  /-- The largest alternative case-of-case copies. -/
  caseOfCase : Nat := 512
  /-- Join points of at most this many nodes are inlined at every jump. -/
  smallJoin : Nat := 24
  deriving Repr, Inhabited

/-- Check that shrink parameters in an untrusted certificate are within bounds. -/
def Params.checkCert (p : Params) : Bool :=
  p.caseOfCase ≤ maxCertCaseOfCase && p.smallJoin ≤ maxCertSmallJoin

/-- Check that a shrink round-count certificate is within bounds. -/
def checkCert (cert : Cert) : Bool :=
  cert.length ≤ maxCertGlobals && cert.all (· ≤ maxCertRounds)

structure Budgets where
  /-- Rounds per global per invocation. -/
  rounds : Nat := 64
  params : Params := {}
  deriving Repr, Inhabited

def cfg (P : Program) (p : Params) : Walk.Cfg :=
  { prog := P, shrink := true, caseOfCaseBound := p.caseOfCase, smallJoin := p.smallJoin }

/-- One round on one global. -/
def round (P : Program) (p : Params) (gd : GDef) : Except String (GDef × Walk.Fires) :=
  (Walk.global (cfg P p) gd).run {}

/-- Exactly `n` rounds, starting with `work` already done by the step; the
global and the step's work after them. A round is refused if it leaves the
global over `maxGlobalNodes` or deeper than `maxDepth` (so every round's walk
starts within the budgets) or brings the step's work over `maxStepWork`. -/
def rounds (P : Program) (p : Params) (gd : GDef) (work : Nat) : Nat → Except String (GDef × Nat)
  | 0 => pure (gd, work)
  | n + 1 => do
    let (gd', f) ← round P p gd
    if gd'.body.nodesLe maxGlobalNodes && gd'.body.depthUpTo maxDepth maxGlobalNodes ≤ maxDepth &&
        work + f.work ≤ maxStepWork then
      rounds P p gd' (work + f.work) n
    else .error "shrink: a global or the step exceeds the node, depth or work budget"

/-- The certified rounds of each global in turn, threading the step's work
and the nodes made so far: refused as soon as either passes its budget. -/
def runGlobals (P : Program) (p : Params) (cert : Cert) :
    List (GlobalId × GDef) → Nat → Nat → Except String (List (GlobalId × GDef))
  | [], _, _ => .ok []
  | (g, gd) :: rest, nodes, work =>
    match rounds P p gd work (cert.getD g 0) with
    | .error e => .error s!"shrink global {g}: {e}"
    | .ok (gd', work') =>
      if nodes + gd'.body.nodesUpTo maxProgramNodes > maxProgramNodes then
        .error "shrink: the program exceeds the node budget"
      else
        match runGlobals P p cert rest (nodes + gd'.body.nodesUpTo maxProgramNodes) work' with
        | .error e => .error e
        | .ok gs => .ok ((g, gd') :: gs)

/-- P2 re-run on its certificate, within the node and work budgets. -/
def run (p : Params) (cert : Cert) (P : Program) : Except String Program := do
  let gs ← runGlobals P p cert P.globalList 0 0
  return { P with globals := Src.NatMap.ofList gs }

/-- Rounds until one fires no rule (not counted), within `budget`. -/
def fixpoint (P : Program) (p : Params) (gd : GDef) :
    Nat → Nat → Walk.Fires → Except String (GDef × Nat × Walk.Fires)
  | 0, n, acc => pure (gd, n, acc)
  | budget + 1, n, acc => do
    let (gd', f) ← round P p gd
    if f.total == 0 then pure (gd, n, acc)
    else fixpoint P p gd' budget (n + 1) (acc.add f)

/-- `produce`: each global to its fixpoint; the certificate, the program and
the rule counts. -/
def produce (B : Budgets) (P : Program) : Except String (Cert × Program × Walk.Fires) := do
  let rs ← P.globalList.mapM fun (g, gd) => do
    let (gd', n, f) ← (fixpoint P B.params gd B.rounds 0 {}).mapError (s!"shrink global {g}: " ++ ·)
    return (g, gd', n, f)
  let P' := { P with globals := Src.NatMap.ofList (rs.map fun (g, gd, _) => (g, gd)) }
  let cert := (List.range P.size).map fun g => ((rs.find? (·.1 == g)).map (·.2.2.1)).getD 0
  return (cert, P', rs.foldl (fun acc (_, _, _, f) => acc.add f) {})

end IxCC.Anf.Shrink
