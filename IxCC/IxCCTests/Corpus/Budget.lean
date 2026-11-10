import IxCCTests.Corpus.Manifest
import IxCCTests.Src.Support
import IxCC.Recheck

/-! The middle end's budgets against every committed program (REPORT item 2).

The replay refuses a middle-end step that passes a node or work budget
(`IxCC.Anf.Budget`). The budgets must leave every committed fixture and corpus
program far inside them, so this survey replays each program's honest
certificate step by step and records, over all of them, the largest

* global and program, after P1 and after every step (`maxGlobalNodes`,
  `maxProgramNodes`);
* nodes one walk copies, in an inline step and in a shrink round
  (`Walk.maxCopy`), and rule firings in one walk (`Walk.maxFires`);
* work and nodes a specialisation step charges (`Specialize.maxWork`,
  `Specialize.maxNodes`).

It fails if any reaches its budget, and prints the maxima with the headroom
factor; `docs/compiler-design.md` ("Middle-end budgets") records them. The
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
  programs : Nat := 0
  declined : Nat := 0

def Stats.merge (s t : Stats) : Stats :=
  { maxGlobal := max s.maxGlobal t.maxGlobal, maxProgram := max s.maxProgram t.maxProgram
    maxCopyInline := max s.maxCopyInline t.maxCopyInline
    maxCopyShrink := max s.maxCopyShrink t.maxCopyShrink
    maxFires := max s.maxFires t.maxFires, maxSpecWork := max s.maxSpecWork t.maxSpecWork
    maxSpecNodes := max s.maxSpecNodes t.maxSpecNodes
    programs := s.programs + t.programs, declined := s.declined + t.declined }

/-- The largest global's nodes and the program's. -/
def sizes (P : Anf.Program) : Nat × Nat :=
  P.globalList.foldl (fun (m, t) (_, gd) => (max m gd.body.nodes, t + gd.body.nodes)) (0, 0)

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
  let mut s : Stats := { maxGlobal := g, maxProgram := t, programs := 1 }
  for step in cert.steps do
    match step with
    | .shrink c =>
      for (g, gd) in P.globalList do
        let mut cur := gd
        for _ in [0:c.getD g 0] do
          let (gd', f) ← Anf.Shrink.round P cert.shrink cur
          s := { s with maxCopyShrink := max s.maxCopyShrink f.copied, maxFires := max s.maxFires f.total }
          cur := gd'
    | .inline r =>
      for (g, gd) in P.globalList do
        match r.lookup g with
        | some cs@(_ :: _) =>
          let (_, f) ← (Anf.Walk.global { prog := P, inline := cs } gd).run {}
          s := { s with maxCopyInline := max s.maxCopyInline f.copied, maxFires := max s.maxFires f.total }
        | _ => pure ()
    | .specialize c =>
      let (w, n) ← specWork c P
      s := { s with maxSpecWork := max s.maxSpecWork w, maxSpecNodes := max s.maxSpecNodes n }
    | .prune => pure ()
    P ← step.run cert.shrink P
    let (g, t) := sizes P
    s := { s with maxGlobal := max s.maxGlobal g, maxProgram := max s.maxProgram t }
  return s

/-- One program: its honest certificate's middle end, measured (none if the
compiler declines it before the middle end, as the corpus expects of some). -/
def program (bytes : ByteArray) (json : Lean.Json) (roots : List String) : IO (Option Stats) := do
  match ingress bytes json roots (typecheck := false) with
  | .error _ => return none
  | .ok inp =>
    let cfg := ({} : Config).forInput inp
    match produce cfg inp with
    | .error _ => return none
    | .ok cert =>
      match front cfg inp.program cert with
      | .error _ => return none
      | .ok (src, checked) =>
        match Lam.erase src checked with
        | .error _ => return none
        | .ok (lam, _) => return some (← IO.ofExcept (measure lam cert.mid))

def file (path : FilePath) (equations : FilePath) (roots : List String := []) : IO (Option Stats) := do
  program (← IO.FS.readBinFile path) (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile equations))) roots

/-- The committed closures outside the corpus families, with all their roots. -/
def extraFixtures : IO (List (FilePath × FilePath)) := do
  let mut out : List (FilePath × FilePath) := [
    ("fixtures/ixon-v4/k1/k1.ixe", "fixtures/ixon-v4/k1/equations.json"),
    ("fixtures/ixon-v4/src-sortpoly/sortpoly.ixe", "fixtures/ixon-v4/src-sortpoly/sortpoly.equations.json"),
    ("fixtures/ixon-v4/src-diag/diag.ixe", "fixtures/ixon-v4/src-diag/diag.equations.json"),
    ("fixtures/rc/real-source/anonymous.ixe", "fixtures/rc/real-source/consumer.equations.json")]
  for dir in ["fixtures/ownership", "fixtures/ownership/historical/annotated-recursion-cb68"] do
    let entries ← (dir : FilePath).readDir
    for e in entries.qsort (fun a b => a.fileName < b.fileName) do
      if e.fileName.endsWith ".ixe" then
        let eqs := e.path.withExtension "equations.json"
        if ← eqs.pathExists then out := out ++ [(e.path, eqs)]
  return out

def survey (a : Assert) : IO (Array String) := do
  let mut s : Stats := {}
  for path in families do
    let m ← Family.read path
    let dir : FilePath := m.directory
    for f in m.fixtures do
      for r in f.roots do
        match ← file (dir / f.closure.path) (dir / f.equations.path) (r.name :: r.together) with
        | some t => s := s.merge t
        | none => s := { s with declined := s.declined + 1 }
  for (ixe, eqs) in ← extraFixtures do
    match ← file ixe eqs with
    | some t => s := s.merge t
    | none => s := { s with declined := s.declined + 1 }
  let rows : List (String × Nat × Nat) := [
    ("largest global", s.maxGlobal, Anf.maxGlobalNodes),
    ("largest program", s.maxProgram, Anf.maxProgramNodes),
    ("largest copy in an inline walk", s.maxCopyInline, Anf.Walk.maxCopy),
    ("largest copy in a shrink round", s.maxCopyShrink, Anf.Walk.maxCopy),
    ("most firings in one walk", s.maxFires, Anf.Walk.maxFires),
    ("most work in a specialisation step", s.maxSpecWork, Anf.Specialize.maxWork),
    ("most nodes charged in a specialisation step", s.maxSpecNodes, Anf.Specialize.maxNodes)]
  let mut out := #[s!"{s.programs} programs measured, {s.declined} declined before the middle end"]
  for (label, got, budget) in rows do
    expect a (got < budget) s!"{label}: {got} reaches its budget {budget}"
    out := out.push s!"{label}: {got} (budget {budget}, {if got == 0 then "unused" else s!"{budget / got}×"})"
  return out

end IxCCTests.Corpus.Budget
