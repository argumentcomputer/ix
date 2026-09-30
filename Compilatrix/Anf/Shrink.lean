import Compilatrix.Anf.Walk

/-! # P2: shrink

`Anf.Shrink` (design note 02 §8, P2): the walk's rewrite rules (`Walk`,
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

namespace Compilatrix.Anf.Shrink

/-- Rounds per global, in id order (missing entries mean none). -/
abbrev Cert := List Nat

/-- The bounds the rules read (certificate data). -/
structure Params where
  /-- The largest alternative case-of-case copies. -/
  caseOfCase : Nat := 64
  /-- Join points of at most this many nodes are inlined at every jump. -/
  smallJoin : Nat := 24
  deriving Repr, Inhabited

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

/-- Exactly `n` rounds. -/
def rounds (P : Program) (p : Params) (gd : GDef) : Nat → Except String GDef
  | 0 => pure gd
  | n + 1 => do
    let (gd', _) ← round P p gd
    rounds P p gd' n

/-- P2 re-run on its certificate. -/
def run (p : Params) (cert : Cert) (P : Program) : Except String Program := do
  let gs ← P.globalList.mapM fun (g, gd) => do
    let gd' ← (rounds P p gd (cert.getD g 0)).mapError (s!"shrink global {g}: " ++ ·)
    return (g, gd')
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

end Compilatrix.Anf.Shrink
