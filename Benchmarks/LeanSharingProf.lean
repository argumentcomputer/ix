import Ix.Ixon
import Ix.Sharing.Exact

/-!
# Phase profiler for the Lean tiered sharing construction

```
lake exe lean-sharing-prof <corpus.ixe> full  [select-file]
lake exe lean-sharing-prof <corpus.ixe> split [select-file]
lake exe lean-sharing-prof <corpus.ixe> hash  [select-file]
```

Every mode runs `normalizeConstantSharingTiered .tagN` on each constant of the
corpus (or those whose hex addresses are listed in the select file), checks
that the output serializes to the stored bytes (the corpus is canonical), and
prints the total time and the slowest constants. `split` first replays each
width's phases separately (`profWidth`, a copy of `tieredAtWidth` and the
uniform optimizer's stages) and prints the time per phase, summed over the
constants and the three widths, plus phase-3 statistics (`stat.*`, counts
scaled by 10^6 in the ms column). `hash` also prints each output's address.
A development tool: it replicates internal stages and must follow them.
-/

open Ixon Ix.Sharing.Exact

namespace Benchmarks.LeanSharingProf

abbrev Acc := IO.Ref (Std.HashMap String Nat)

@[noinline] def timeIt {α} (acc : Acc) (key : String) (f : Unit → α) : IO α := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  acc.modify fun m => m.insert key (m.getD key 0 + (t1 - t0))
  return r

def must {α} [Inhabited α] (key : String) : Except SharingError α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{key}: {reprStr e}")

/-- Phase-split replica of `tieredAtWidth`. -/
def profWidth (acc : Acc) (limits : Limits) (ex : Expanded) (w : Nat) :
    IO TieredSharingResult := do
  let layout := ShareLayout.tagN
  let p ← timeIt acc "u0.prep" fun _ => Prep.ofDag ex.dag
  let _ ← timeIt acc "u0.checks" fun _ =>
    childrenPrecede ex.dag.nodes && ex.dag.nodes.all (fun node => node.children.size == node.head.arity) &&
    ex.roots.all (· < ex.dag.size) && (reachMarks ex.dag.nodes ex.roots).all id &&
    (List.range ex.dag.size).all (fun t => p.spineLen[t]! < teleSubaddEnd)
  -- stage, split
  let f ← timeIt acc "u1.facts" fun _ => graphFacts ex.dag ex.roots
  let cand ← timeIt acc "u1.cand" fun _ => searchCandidates p f w
  let b0 ← timeIt acc "u1.bounds" fun _ => uniformBounds p w cand
  let _ ← timeIt acc "u1.vis" fun _ => visibleCounts ex.dag ex.roots cand
  let sg ← timeIt acc "u1.stage" fun _ => uniformStage w ex p
  let _ := b0
  let _ ← timeIt acc "u1.upmk" fun _ => UPrep.mk' p w sg.opaq
  let _ ← timeIt acc "u1.baseEv" fun _ => p.eval sg.widthCs sg.allTrue
  let _ ← timeIt acc "u1.comps" fun _ => uncertainComponents ex.dag sg.cls
  let ok ← timeIt acc "u2.compCheck" fun _ =>
    componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps)
  unless ok do throw (IO.userError "components")
  -- search, split mkSCtx / search
  let mut results : Array CompResult := #[]
  let mut states := 0
  let mut costEvals := 0
  for members in sg.comps do
    let cx ← timeIt acc "u3.mkSCtx" fun _ => mkSCtx ex sg.f sg.up sg.cand sg.b0 sg.vis0 sg.rootCount sg.slack sg.theta
          sg.baseEv sg.widthCs sg.allTrue sg.unc members
    let (r, s, c) ← must "search" (← timeIt acc "u3.search" fun _ => searchComponent cx limits states costEvals)
    results := results.push r
    states := s
    costEvals := c
  let (chosenDelta, chosenX, lowerBracket) ← must "knap"
    (← timeIt acc "u4.knap" fun _ => uniformKnapsack limits sg.cs.size results)
  let csb ← timeIt acc "u4.csBase" fun _ => csBase ex p sg
  let modelInt : _root_.Int := (csb : Nat) + chosenDelta + (tag0Size (sg.cs.size + chosenX.size) : _root_.Int)
  let model := modelInt.toNat
  let c : UniformChoice :=
    { facts := sg.f, certainStored := sg.cs, certainExcluded := sg.ce, uncertain := sg.unc,
      lowDegree := sg.low, components := sg.comps, stored := mergeSorted sg.cs chosenX, model := model,
      states := states, costEvals := costEvals, lowerBracket := lowerBracket }
  -- finish, split
  let _ ← timeIt acc "u5.inClass" fun _ => inClassCheck ex.dag ex.roots c.stored
  let order ← timeIt acc "u5.pinned" fun _ => pinnedOrder ex.dag c.facts.deg c.stored
  let n := ex.dag.size
  let width := c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none)
  let (entries, roots, _, _) ← must "matdep"
    (← timeIt acc "u5.matDep" fun _ => p.materializeDependent order ex.roots width limits)
  let _ ← must "reexp1" (← timeIt acc "u5.reexpand" fun _ => reexpand limits ex.dag entries roots)
  let _ ← timeIt acc "u5.measure" fun _ => tag0Size entries.size + exprsSize entries + exprsSize roots
  let u ← must "finish" (← timeIt acc "u5.finishAll" fun _ => uniformFinish w limits ex p c)
  -- phase 2
  let deg ← timeIt acc "p2.facts" fun _ => (graphFacts ex.dag ex.roots).deg
  let wm ← timeIt acc "p2.weights" fun _ => tierWeights u.result.tableTerms u.result.sharing u.result.roots
  let dm ← timeIt acc "p2.deps" fun _ => tierDeps u.result.tableTerms u.result.sharing
  let weight := fun t => wm.getD t 0
  let deps := fun t => dm.getD t []
  let order1 := u.result.tableTerms
  let (tier, _) ← must "tier" (← timeIt acc "p2.firstTier" fun _ =>
    firstTier order1 weight deps (min 8 order1.size) limits)
  let stored := (order1.toList.mergeSort (· ≤ ·)).toArray
  let rest := stored.filter (!tier.contains ·)
  let _ ← timeIt acc "p2.kahn" fun _ => kahnOrder weight deps rest
  let a ← must "alloc" (← timeIt acc "p2.allocAll" fun _ =>
    allocate layout limits ex.dag deg u.result.tableTerms u.result.sharing u.result.roots)
  -- phase 3
  let phase1Layout ← timeIt acc "p3.layout1" fun _ => layoutBytes layout u.result.sharing u.result.roots
  let (es, rs, _, _) ← must "mat" (← timeIt acc "p3.matTable" fun _ =>
    materializeTable (Prep.ofDag ex.dag) a.order ex.roots limits layout.widthAt)
  let _ ← timeIt acc "p3.layout" fun _ => layoutBytes layout es rs
  let _ ← must "reexp3" (← timeIt acc "p3.reexpand" fun _ => reexpand limits ex.dag es rs)
  let _ ← timeIt acc "p3.measure" fun _ => tag0Size es.size + (es ++ rs).foldl (fun acc e => acc + (serExpr e).size) 0
  let _ ← timeIt acc "p3.wire" fun _ => (es ++ rs).all fun e => (wireCounts e).isSome
  let m ← must "remat" (← timeIt acc "p3.rematAll" fun _ => rematerialize layout limits ex a.order phase1Layout)
  -- statistics: ancestors per entry vs the scanned range
  let nn := ex.dag.size
  let (ancSum, scanSum) := a.order.foldl (fun (acc : Nat × Nat) t =>
    let mk := ancestorMarks ex.dag t
    (acc.1 + (mk.filter id).size, acc.2 + (nn - t))) (0, 0)
  acc.modify fun mm => (((mm.insert "stat.anc" (mm.getD "stat.anc" 0 + ancSum * 1000000)).insert
    "stat.scan" (mm.getD "stat.scan" 0 + scanSum * 1000000)).insert "stat.work" (mm.getD "stat.work" 0 + m.work * 1000000)).insert
    "stat.kn" (mm.getD "stat.kn" 0 + a.order.size * nn * 1000000)
  timeIt acc "z.result" fun _ => tieredResult layout ex w u a m

def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ (if x < 16 then "0" else "") ++ (Nat.toDigits 16 x.toNat |> String.ofList)) ""

def main (args : List String) : IO UInt32 := do
  let path : String := args[0]!
  let mode : String := args[1]!
  let selPath : Option String := args[2]?
  let bytes ← IO.FS.readBinFile path
  let env ← IO.ofExcept (Ixon.deEnvAnon bytes)
  let entries := env.consts.toArray.qsort fun a b => Address.cmpBytes a.1 b.1 == .lt
  let entries ← match selPath with
    | some p => do
      let lines := (← IO.FS.readFile p).splitOn "\n" |>.map (String.trimAscii · |>.toString) |>.filter (· != "")
      let s := lines.foldl (fun (s : Std.HashSet String) l => s.insert l) {}
      pure (entries.filter fun e => s.contains (toString e.1))
    | none => pure entries
  let acc ← IO.mkRef ({} : Std.HashMap String Nat)
  let mut total := 0
  let mut same := 0
  let mut differ := 0
  let mut failed := 0
  let mut perConst : Array (Nat × String × Nat) := #[]
  for (addr, lc) in entries do
    let c ← match lc.get with
      | .ok c => pure c
      | .error _ => continue
    let raw := lc.rawBytes
    let label := match env.addrToName.get? addr with
      | some n => s!"{n}"
      | none => s!"{addr}"
    let t0 ← IO.monoNanosNow
    if mode == "split" then
      let limits : Limits := {}
      let roots := constantInfoRoots c.info
      let ex ← must "expand" (← timeIt acc "a.expand" fun _ => expand limits c.sharing roots true)
      for w in [1, 2, 3] do
        try
          let _ ← profWidth acc limits ex w
        catch e => IO.eprintln s!"{label} w{w}: {e}"
    let r ← timeIt acc "TOTAL.normalize" fun _ => normalizeConstantSharingTiered .tagN c {}
    let t1 ← IO.monoNanosNow
    total := total + (t1 - t0)
    perConst := perConst.push (t1 - t0, label, c.sharing.size)
    match r with
    | .ok n =>
      let out := serConstant n
      if out == raw then same := same + 1 else
        differ := differ + 1
        IO.println s!"DIFFER {label} ({addr})"
      if mode == "hash" then
        IO.println s!"H {addr} {(Address.blake3 out)}"
    | .error e =>
      failed := failed + 1
      IO.println s!"FAIL {label}: {reprStr e}"
  IO.println s!"constants {entries.size}: same {same}, differ {differ}, failed {failed}; total {total / 1000000} ms"
  let m ← acc.get
  let keys := m.toArray.qsort fun a b => a.1 < b.1
  for (k, v) in keys do
    IO.println s!"  {k}: {v / 1000000} ms"
  let slow := (perConst.qsort fun a b => a.1 > b.1).extract 0 15
  for (t, l, k) in slow do
    IO.println s!"  slow {t / 1000000} ms {l} (k {k})"
  return 0

end Benchmarks.LeanSharingProf

def main (args : List String) : IO UInt32 := Benchmarks.LeanSharingProf.main args
