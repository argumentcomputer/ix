import IxCCTests.Corpus.Manifest
import IxCCTests.Src.Support
import IxCC.Recheck

/-! The middle end's budgets against every committed program.

The replay refuses a middle-end step that passes a node or work budget
(`IxCC.Anf.Budget`). The budgets must leave every committed fixture and corpus
program far inside them, so this survey replays each program's honest
certificate step by step and records, over all of them, the largest

* global and program, after P1 and after every step (`maxGlobalNodes`,
  `maxProgramNodes`);
* nodes one walk copies, in an inline step and in a shrink round
  (`Walk.maxCopy`), and rule firings in one walk (`Walk.maxFires`); and it
  checks the walk's step bound on every walk (`Fires.steps` at most the
  walked global's nodes plus `Fires.copied`, the bound `Walk.maxCopy` turns
  into a budget; see `Anf/Walk.lean`, "Budgets");
* work and nodes a specialisation step charges (`Specialize.maxWork`,
  `Specialize.maxNodes`).

It fails if any reaches its budget, and prints the maxima with the headroom
factor and the first program that reaches each; `docs/compiler-design.md`
("Middle-end budgets") records them.

It also checks the shrink walk's pending join entry (case-of-case as a move)
against the walk without it, on every shrink round the certificate counts and
the round after them (where the producer stopped): each is walked a second time
on the same input with the pending choice forced off (`Walk.Cfg.pendForce :=
some false`). No round may be refused with the choice the walk makes where the
walk without it succeeds and fires a rule, none may copy more with it, and no
jump to a pending join point may be left without a known constructor
(`Fires.pendInline`). This is how "never worse than the walk without the
pending entry" is held: checked on the committed programs, not proved. The
programs are every root of every registered corpus family (compiled with the
roots it is compiled together with, as `tests-corpus` does) and, with all
their sidecar roots, `k1.ixe`, `src-sortpoly`, `src-diag`, the ownership
fixtures and the RC real-source closure. -/

namespace IxCCTests.Corpus.Budget

open IxCC IxCC.Recheck IxCCTests.Src
open System

structure Stats where
  maxGlobal : Nat := 0
  maxProgram : Nat := 0
  maxCopyInline : Nat := 0
  maxCopyShrink : Nat := 0
  maxFires : Nat := 0
  maxSpecWork : Nat := 0
  maxSpecNodes : Nat := 0
  maxWalkWork : Nat := 0
  maxStepWork : Nat := 0
  maxLam : Nat := 0
  maxSrcDepth : Nat := 0
  maxSrcVisits : Nat := 0
  maxLamDepth : Nat := 0
  maxDepth : Nat := 0
  maxCopyDepth : Nat := 0
  /-- Walks whose steps passed their global's nodes plus their copies (must be
  none), and the walks checked. -/
  stepsOver : Nat := 0
  walks : Nat := 0
  /-- Shrink rounds walked twice on the same input, with the pending choice
  as the walk makes it and forced off; among them those refused with the
  choice where forced off the walk succeeds and fires a rule (`pendWorse`), those
  copying more with it (`pendMoreCopies`), both must be none, and those refused
  forced off and walked with the choice (`pendGains`); and the jumps to a
  pending join point no known constructor resolved (`pendInline`, must be none). -/
  pendRounds : Nat := 0
  pendWorse : Nat := 0
  pendMoreCopies : Nat := 0
  pendGains : Nat := 0
  pendInline : Nat := 0
  maxBackWork : Nat := 0
  maxEditsAt : Nat := 0
  maxEditPermille : Nat := 0
  maxFactPermille : Nat := 0
  maxSlotsOver : Nat := 0
  programs : Nat := 0
  declined : Nat := 0

def Stats.merge (s t : Stats) : Stats :=
  { maxGlobal := max s.maxGlobal t.maxGlobal, maxProgram := max s.maxProgram t.maxProgram
    maxCopyInline := max s.maxCopyInline t.maxCopyInline
    maxCopyShrink := max s.maxCopyShrink t.maxCopyShrink
    maxFires := max s.maxFires t.maxFires, maxSpecWork := max s.maxSpecWork t.maxSpecWork
    maxSpecNodes := max s.maxSpecNodes t.maxSpecNodes
    maxWalkWork := max s.maxWalkWork t.maxWalkWork, maxStepWork := max s.maxStepWork t.maxStepWork
    maxLam := max s.maxLam t.maxLam, maxSrcDepth := max s.maxSrcDepth t.maxSrcDepth
    maxSrcVisits := max s.maxSrcVisits t.maxSrcVisits, maxLamDepth := max s.maxLamDepth t.maxLamDepth
    maxDepth := max s.maxDepth t.maxDepth, maxCopyDepth := max s.maxCopyDepth t.maxCopyDepth
    maxBackWork := max s.maxBackWork t.maxBackWork, maxEditsAt := max s.maxEditsAt t.maxEditsAt
    maxEditPermille := max s.maxEditPermille t.maxEditPermille
    maxFactPermille := max s.maxFactPermille t.maxFactPermille, maxSlotsOver := max s.maxSlotsOver t.maxSlotsOver
    stepsOver := s.stepsOver + t.stepsOver, walks := s.walks + t.walks
    pendRounds := s.pendRounds + t.pendRounds, pendWorse := s.pendWorse + t.pendWorse
    pendMoreCopies := s.pendMoreCopies + t.pendMoreCopies, pendGains := s.pendGains + t.pendGains
    pendInline := s.pendInline + t.pendInline
    programs := s.programs + t.programs, declined := s.declined + t.declined }

/-- Count one shrink round walked with the pending choice the walk makes
(`dec`) and with it forced off (`off`), on the same input. -/
def Stats.pend (s : Stats) (dec off : Except String (Anf.GDef × Anf.Walk.Fires)) : Stats :=
  let s := { s with pendRounds := s.pendRounds + 1 }
  match dec, off with
  | .error _, .ok (_, fo) => if fo.total > 0 then { s with pendWorse := s.pendWorse + 1 } else s
  | .error _, .error _ => s
  | .ok (_, f), .ok (_, fo) =>
    { s with pendMoreCopies := s.pendMoreCopies + (if f.copied > fo.copied then 1 else 0)
             pendInline := s.pendInline + f.pendInline }
  | .ok (_, f), .error _ => { s with pendGains := s.pendGains + 1, pendInline := s.pendInline + f.pendInline }

/-- Count one walk of a global of body `b` against the step bound. -/
def Stats.walk (s : Stats) (b : Anf.Exp) (f : Anf.Walk.Fires) : Stats :=
  { s with walks := s.walks + 1
           stepsOver := s.stepsOver + (if f.steps ≤ b.nodes + f.copied then 0 else 1) }

/-- The largest global's nodes and the program's. -/
def sizes (P : Anf.Program) : Nat × Nat :=
  P.globalList.foldl (fun (m, t) (_, gd) => (max m gd.body.nodes, t + gd.body.nodes)) (0, 0)

/-- The deepest global of a program (uncapped). -/
def anfDepth (P : Anf.Program) : Nat :=
  P.globalList.foldl (fun m (_, gd) => max m (gd.body.depthUpTo 1000000000 1000000000)) 0

/-- The nodes of a source term's tree (each use of a shared term counted). -/
def srcNodes (t : Src.Term) : Nat := Id.run do
  let mut stack : List Src.Term := [t]
  let mut n := 0
  for _ in [0:1 <<< 28] do
    match stack with
    | [] => break
    | t :: rest =>
      stack := rest
      n := n + 1
      match t with
      | .app f a _ _ => stack := f :: a :: stack
      | .lam _ dom b | .pi _ _ dom b => stack := dom :: b :: stack
      | .letE _ _ ty v b => stack := ty :: v :: b :: stack
      | .proj _ _ e => stack := e :: stack
      | _ => pure ()
  return n

/-- The depth of a source term's tree, on an explicit stack (the terms are
share DAGs; this visits each tree node). -/
def srcDepth (t : Src.Term) : Nat := Id.run do
  let mut stack : List (Src.Term × Nat) := [(t, 1)]
  let mut best := 0
  for _ in [0:1 <<< 28] do
    match stack with
    | [] => break
    | (t, d) :: rest =>
      stack := rest
      best := max best d
      match t with
      | .app f a _ _ => stack := (f, d + 1) :: (a, d + 1) :: stack
      | .lam _ dom b | .pi _ _ dom b => stack := (dom, d + 1) :: (b, d + 1) :: stack
      | .letE _ _ ty v b => stack := (ty, d + 1) :: (v, d + 1) :: (b, d + 1) :: stack
      | .proj _ _ e => stack := (e, d + 1) :: stack
      | _ => pure ()
  return best

/-- `Specialize.run`, returning the work and nodes it charged. -/
def specWork (cert : Anf.Specialize.Cert) (P : Anf.Program) : Except String (Nat × Nat) := do
  let step := fun (st : Anf.Specialize.St) ((f, gd) : Anf.GlobalId × Anf.GDef) => do
    let D := (cert.decisions.filter (·.caller == f)).map fun d => (d.callee, d.mask)
    if D.isEmpty then pure st else
    let n := gd.ps.length
    let (body, st) ← (Anf.Specialize.rewrite P cert.inv gd.key D
      (4 * gd.body.nodesUpTo Anf.maxGlobalNodes + 64)
      (Src.NatMap.ofList ((List.range n).map (·, Anf.Specialize.Def.blank))) n gd.body).run
        { st with fns := 0 }
    let gs := st.prog.globalList.map fun (g, gd') => if g == f then { gd' with body } else gd'
    pure { st with prog := st.prog.withGlobals gs }
  let st ← P.globalList.foldlM step { prog := P }
  return (st.work, st.nodes)

/-- The middle end's replay of `cert` on `lam`, measured step by step. -/
def measure (lam : Lam.Program) (cert : Anf.Pipeline.Cert) : Except String Stats := do
  let mut P ← Anf.convert lam
  let (g, t) := sizes P
  let maxLam := lam.globalList.foldl (fun m (_, gl) => max m gl.body.nodes) 0
  let maxLamDepth := lam.globalList.foldl
    (fun m (_, gl) => max m (Anf.lamDepthUpTo 1000000000 1000000000 gl.body)) 0
  let mut s : Stats := { maxGlobal := g, maxProgram := t, programs := 1, maxLam, maxLamDepth,
                         maxDepth := anfDepth P, maxBackWork := Anf.backWork P }
  for step in cert.steps do
    match step with
    | .shrink c =>
      let mut stepWork := 0
      let C := Anf.Shrink.cfg P cert.shrink
      for (g, gd) in P.globalList do
        let mut cur := gd
        let n := c.getD g 0
        -- the certificate's rounds and the round after them, each also walked
        -- with the pending choice forced off
        for i in [0:n + 1] do
          let r := Anf.Shrink.round P cert.shrink cur
          s := s.pend r ((Anf.Walk.global { C with pendForce := some false } cur).run {})
          if i == n then break
          let (gd', f) ← r
          s := s.walk cur.body f
          s := { s with maxCopyShrink := max s.maxCopyShrink f.copied, maxFires := max s.maxFires f.total }
          s := { s with maxWalkWork := max s.maxWalkWork f.work, maxCopyDepth := max s.maxCopyDepth f.depth }
          stepWork := stepWork + f.work
          cur := gd'
      s := { s with maxStepWork := max s.maxStepWork stepWork }
    | .inline r =>
      let mut stepWork := 0
      for (g, gd) in P.globalList do
        match r.lookup g with
        | some cs@(_ :: _) =>
          let (_, f) ← (Anf.Walk.global { prog := P, inline := cs } gd).run {}
          s := s.walk gd.body f
          s := { s with maxCopyInline := max s.maxCopyInline f.copied, maxFires := max s.maxFires f.total }
          s := { s with maxWalkWork := max s.maxWalkWork f.work, maxCopyDepth := max s.maxCopyDepth f.depth }
          stepWork := stepWork + f.work
        | _ => pure ()
      s := { s with maxStepWork := max s.maxStepWork stepWork }
    | .specialize c =>
      let (w, n) ← specWork c P
      s := { s with maxSpecWork := max s.maxSpecWork w, maxSpecNodes := max s.maxSpecNodes n }
    | .prune => pure ()
    P ← step.run cert.shrink P
    let (g, t) := sizes P
    s := { s with maxGlobal := max s.maxGlobal g, maxProgram := max s.maxProgram t,
                  maxDepth := max s.maxDepth (anfDepth P), maxBackWork := max s.maxBackWork (Anf.backWork P) }
  return s

/-- The honest allocation certificate against the functions it allocates: the most
edits at one position, edits per register mention or block and one block's fact
entries per register mention (in thousandths), and frame slots beyond the
register mentions. -/
def allocStats (cfg : Config) (P : Src.Program) (cert : Recheck.Cert) : Stats := Id.run do
  let some f := (Recheck.runLir cfg P cert).toOption | return {}
  let some xv := (Xv.Select.select f.lowered.program).toOption | return {}
  let mut s : Stats := {}
  for (fn, o) in xv.funcs.toList.zip cert.alloc do
    let r := Xv.Validate.regMentions fn
    let m := r + fn.blocks.size
    let edits := o.blocks.foldl (fun n bo => n + bo.edits.length) 0
    let facts := o.blocks.foldl (fun n bo => max n (Xv.Validate.factEntries bo.cert)) 0
    let run := o.blocks.foldl (fun n bo => max n (Xv.Validate.maxRun bo.edits 0 0 0)) 0
    s := { s with maxEditsAt := max s.maxEditsAt run
                  maxEditPermille := max s.maxEditPermille (edits * 1000 / max m 1)
                  maxFactPermille := max s.maxFactPermille (facts * 1000 / (r + 1))
                  maxSlotsOver := max s.maxSlotsOver (o.numSlots - Xv.Validate.regMentions fn) }
  return s

/-- One program: its honest certificate's middle end, measured (none if the
compiler declines it before the middle end, as the corpus expects of some). -/
def program (bytes : ByteArray) (json : Lean.Json) (roots : List String) : IO (Option Stats) := do
  match ingress bytes json roots with
  | .error _ => return none
  | .ok inp =>
    let P := inp.program
    -- every program ingress accepts, compiled or declined later
    let depth := (List.range P.size).foldl (fun m c => match P.decl? c with
      | some d => (Src.Table.declTerms d).foldl (fun m t => max m (srcDepth t)) m
      | none => m) 0
    let visits := (List.range P.size).foldl (fun m c => match P.decl? c with
      | some d => (Src.Table.declTerms d).foldl (fun m t => m + srcNodes t) m
      | none => m) 0
    let declined : Stats := { maxSrcDepth := depth, maxSrcVisits := visits, declined := 1 }
    let cfg := ({} : Config).forInput inp
    match produce cfg inp with
    | .error _ => return some declined
    | .ok cert =>
      match front cfg inp.program cert with
      | .error _ => return some declined
      | .ok (src, checked) =>
        match Lam.erase src checked with
        | .error _ => return some declined
        | .ok (lam, _) =>
          let s ← IO.ofExcept (measure lam cert.mid)
          return some ({ s with maxSrcDepth := depth, maxSrcVisits := visits }.merge (allocStats cfg inp.program cert))

def file (path : FilePath) (equations : FilePath) (roots : List String := []) : IO (Option Stats) := do
  program (← IO.FS.readBinFile path) (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile equations))) roots

/-- The committed closures outside the corpus families, with all their roots:
the role-bound ones ingress accepts (not `src-diag`'s `sorry.ixe`, which the
kernel declines whole). -/
def extraFixtures : IO (List (FilePath × FilePath)) := do
  let mut out : List (FilePath × FilePath) := [
    ("fixtures/ixon-v4/k1/k1.ixe", "fixtures/ixon-v4/k1/equations.json"),
    ("fixtures/ixon-v4/src-sortpoly/sortpoly.ixe", "fixtures/ixon-v4/src-sortpoly/sortpoly.equations.json"),
    ("fixtures/ixon-v4/src-diag/diag.ixe", "fixtures/ixon-v4/src-diag/diag.equations.json"),
    ("fixtures/rc/real-source/anonymous.ixe", "fixtures/rc/real-source/consumer.equations.json")]
  for dir in ["fixtures/ownership"] do
    let entries ← (dir : FilePath).readDir
    for e in entries.qsort (fun a b => a.fileName < b.fileName) do
      if e.fileName.endsWith ".ixe" then
        let eqs := e.path.withExtension "equations.json"
        if ← eqs.pathExists then out := out ++ [(e.path, eqs)]
  return out

/-- `budget / got` to one decimal, rounded down (`7.3×`). -/
def headroom (budget got : Nat) : String :=
  let t := budget * 10 / got
  s!"{t / 10}.{t % 10}×"

def survey (a : Assert) : IO (Array String) := do
  let mut s : Stats := {}
  -- each measured program with its stats, to name the one that sets each maximum
  let mut each : Array (String × Stats) := #[]
  for path in families do
    let m ← Family.read path
    let dir : FilePath := m.directory
    for f in m.fixtures do
      for r in f.roots do
        match ← file (dir / f.closure.path) (dir / f.equations.path) (r.name :: r.together) with
        | some t =>
          s := s.merge t
          each := each.push (s!"{m.family}/{r.name}", t)
        | none => s := { s with declined := s.declined + 1 }
  for (ixe, eqs) in ← extraFixtures do
    match ← file ixe eqs with
    | some t =>
      s := s.merge t
      each := each.push (ixe.toString, t)
    | none => s := { s with declined := s.declined + 1 }
  let rows : List (String × (Stats → Nat) × Nat) := [
    ("largest global", (·.maxGlobal), Anf.maxGlobalNodes),
    ("largest program", (·.maxProgram), Anf.maxProgramNodes),
    ("largest copy in an inline walk", (·.maxCopyInline), Anf.Walk.maxCopy),
    ("largest copy in a shrink round", (·.maxCopyShrink), Anf.Walk.maxCopy),
    ("most firings in one walk", (·.maxFires), Anf.Walk.maxFires),
    ("most work in a specialisation step", (·.maxSpecWork), Anf.Specialize.maxWork),
    ("most nodes charged in a specialisation step", (·.maxSpecNodes), Anf.Specialize.maxNodes),
    ("most work in one walk", (·.maxWalkWork), Anf.Walk.maxWalkWork),
    ("most walk work in one inline or shrink step", (·.maxStepWork), Anf.maxStepWork),
    ("largest Lam global", (·.maxLam), Anf.maxLamNodes),
    ("deepest source term", (·.maxSrcDepth), Src.maxTermDepth),
    ("most source nodes, counted as trees", (·.maxSrcVisits), Recheck.maxSrcVisits),
    ("deepest Lam global", (·.maxLamDepth), Anf.maxLamDepth),
    ("deepest Anf global", (·.maxDepth), Anf.maxDepth),
    ("most walk steps on the stack at once", (·.maxCopyDepth), Anf.Walk.maxWalkDepth),
    ("most back-end work (nodes squared, and table searches)", (·.maxBackWork), Anf.maxBackWork),
    ("most allocation edits at one position", (·.maxEditsAt), Xv.Validate.maxEditsAt),
    ("most allocation edits per register mention or block, in thousandths", (·.maxEditPermille),
      Xv.Validate.editFactor * 1000),
    ("most allocation fact entries in one block per register mention, in thousandths", (·.maxFactPermille),
      Xv.Validate.factFactor * 1000),
    ("most frame slots beyond the register mentions", (·.maxSlotsOver), Xv.Validate.slotSlack)]
  let mut out := #[s!"{s.programs} programs measured, {s.declined} declined before the middle end"]
  expect a (s.stepsOver == 0 && s.walks > 0)
    s!"{s.stepsOver} of {s.walks} walks took more steps than their global's nodes plus their copies"
  out := out.push s!"walks within their step bound (steps at most the global's nodes plus the copies): {s.walks} of {s.walks}"
  -- the pending join entry against the walk without it, round by round
  let firstWith := fun (get : Stats → Nat) =>
    ((each.find? fun (_, t) => get t > 0).map (·.1)).getD "none"
  expect a (s.pendRounds > 0) "no shrink round was walked with the pending choice forced off"
  expect a (s.pendWorse == 0)
    s!"{s.pendWorse} shrink rounds refused with the pending choice where the walk without it fires \
      (first: {firstWith (·.pendWorse)})"
  expect a (s.pendMoreCopies == 0)
    s!"{s.pendMoreCopies} shrink rounds copy more with the pending choice than without it \
      (first: {firstWith (·.pendMoreCopies)})"
  expect a (s.pendInline == 0)
    s!"{s.pendInline} jumps to a pending join point found no known constructor (the pre-check \
      `Walk.pendOk` admitted a scope it should not; first: {firstWith (·.pendInline)})"
  out := out.push s!"the pending join entry against the walk without it, on {s.pendRounds} shrink rounds: \
    refused where the walk without it fires {s.pendWorse}, copying more {s.pendMoreCopies} (both must be \
    none); refused without it and walked with it {s.pendGains}; jumps to a pending join point without a \
    known constructor {s.pendInline} (must be none)"
  for (label, get, budget) in rows do
    let got := get s
    expect a (got < budget) s!"{label}: {got} reaches its budget {budget}"
    let who := match each.find? (fun (_, t) => get t == got) with
      | some (p, _) => if got == 0 then "" else s!"; {p}"
      | none => ""
    out := out.push s!"{label}: {got} (budget {budget}, {if got == 0 then "unused" else headroom budget got}{who})"
  return out

end IxCCTests.Corpus.Budget
