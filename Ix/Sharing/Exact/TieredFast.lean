/-
  The compiled tiered construction.

  `@[csimp]` replaces a call only in code compiled after the replacement
  theorem, so the fast parts proved equal in the modules this one imports
  (`Exact.TierFast` for `firstTier`, `Exact.PinnedFast` for `pinnedOrder`,
  `Exact.KnapsackFast` for `uniformKnapsack`) do not reach `allocate`,
  `tieredAtWidth`, `canonicalTieredCore`, `canonicalTieredExpanded` and
  `optimizeUniformExpanded`, which `Exact.Tiered` and `Exact.Uniform`
  compiled earlier. This module compiles each of them again and attaches the
  copy with `@[csimp]`, so every caller compiled after it (`Ix.Sharing.Exact`
  and everything that imports it, including the compiler) runs the fast
  parts. The copies also compute the width-independent tables (`Prep.ofDag`,
  `graphFacts`, the DAG checks and the candidate count) once per constant
  instead of once per width and phase; each copy is the specification's
  body with those tables passed in, and each equality is proved by unfolding.
  For a DAG of at least `tieredParMin` terms the three candidates run as
  parallel tasks and are combined in width order, which is the same value
  (`tieredCandidates_eq`); only the latency of a large constant changes.
-/
module

public import Ix.Sharing.Exact.TierFast
public import Ix.Sharing.Exact.PinnedFast
public import Ix.Sharing.Exact.KnapsackFast
import all Ix.Sharing.Exact.Tiered
import all Ix.Sharing.Exact.Uniform
import all Ix.Sharing.Exact.UniformSearch

public section

namespace Ix.Sharing.Exact

/-- `allocate`, compiled with the fast first tier. -/
def allocateC (layout : ShareLayout) (limits : Limits) (dag : Dag) (deg : Array Nat)
    (order1 : Array Nat) (entries1 roots1 : Array Ixon.Expr) :
    Except SharingError Allocation := do
  let wm := tierWeights order1 entries1 roots1
  let dm := tierDeps order1 entries1
  let weight := fun t => wm.getD t 0
  let deps := fun t => dm.getD t []
  let stored := (order1.toList.mergeSort (· ≤ ·)).toArray
  let (tier, slotStates) ← firstTier order1 weight deps (min 8 order1.size) limits
  let rest := stored.filter (!tier.contains ·)
  let order2 := pinnedOrder dag deg tier ++ kahnOrder weight deps rest
  checkInternal ((order2.toList.mergeSort (· ≤ ·)).toArray == stored)
    "the allocated order is not a permutation of the phase-1 table"
  let kept : Bool := refCost layout weight order2 > refCost layout weight order1
  let order := if kept then order1 else order2
  checkInternal (respectsDeps order deps) "the allocated order places a body reference after its user"
  return { tier, slotStates, order, kept, refCost1 := refCost layout weight order1,
           refCostFinal := refCost layout weight order }

@[csimp] theorem allocate_eq_C : @allocate = @allocateC := by
  funext layout limits dag deg order1 entries1 roots1
  unfold allocate allocateC
  rfl

/-! ## Width-independent tables, computed once per constant

The three candidates of `canonicalTieredCore` run phases 1-3 on the same
DAG. `Prep.ofDag`, `graphFacts`, the DAG checks of `optimizeUniformExpanded`
and the candidate count of `tieredResult` do not depend on the width; the
copies below take them as arguments, and `canonicalTieredCoreC` computes
them once. Each copy is the specification's body with the table passed in
(the equalities are definitional, plus the order of the checks). -/

/-- The DAG checks of `optimizeUniformExpanded` that come before
`Prep.ofDag`. -/
def uniformDagChecks (ex : Expanded) : Except SharingError Unit := do
  unless childrenPrecede ex.dag.nodes do
    throw (.internal "DAG children do not precede their parents")
  unless ex.dag.nodes.all (fun node => node.children.size == node.head.arity) do
    throw (.internal "DAG node arity")
  unless ex.roots.all (· < ex.dag.size) do
    throw (.internal "root ID out of range")
  unless (reachMarks ex.dag.nodes ex.roots).all id do
    throw (.internal "DAG term unreachable from the roots")

/-- The telescope-spine check of `optimizeUniformExpanded`. -/
def uniformSpineCheck (ex : Expanded) (p : Prep) : Except SharingError Unit := do
  unless (List.range ex.dag.size).all (fun t => p.spineLen[t]! < teleSubaddEnd) do
    throw (.formatBound "telescope spine length" teleSubaddEnd)

/-- `uniformStage` with the graph facts `f` passed in. -/
def uniformStageF (w : Nat) (ex : Expanded) (p : Prep) (f : GraphFacts) : UStage :=
  let n := ex.dag.size
  let cand := searchCandidates p f w
  let b0 := uniformBounds p w cand
  let vis0 := visibleCounts ex.dag ex.roots cand
  let nCand := (cand.filter id).size
  let thetaMax : _root_.Int := tag0StepBound nCand + 1
  let clsMax := classifyWith p f w b0 vis0 thetaMax
  let nCsMax := (clsMax.filter (· == .certainStored)).size
  let theta : _root_.Int := if tag0Size nCand == tag0Size nCsMax then 1 else thetaMax
  let cls := if theta == 1 then classifyWith p f w b0 vis0 1 else clsMax
  let pick (c : UClass) := (Array.range n).filter (cls[·]! == c)
  let cs := pick .certainStored
  let unc := pick .uncertain
  let opaq := cs.foldl (fun acc t => acc.set! t true) (Array.replicate n false)
  let widthCs : Array (Option Nat) :=
    cs.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none)
  let allTrue := Array.replicate n true
  { f, cand, b0, vis0, theta, cls, cs, ce := pick .certainExcluded, unc,
    low := pick .lowDegree, opaq, up := UPrep.mk' p w opaq, widthCs, allTrue,
    baseEv := p.eval widthCs allTrue, comps := uncertainComponents ex.dag cls,
    slack := tag0Size (cs.size + unc.size) - tag0Size cs.size,
    rootCount := ex.roots.foldl (fun acc r => acc.modify r (· + 1)) (Array.replicate n 0) }

theorem uniformStage_eq_F (w : Nat) (ex : Expanded) (p : Prep) :
    uniformStage w ex p = uniformStageF w ex p (graphFacts ex.dag ex.roots) := by
  unfold uniformStage uniformStageF
  rfl

/-- `uniformChoose` with the graph facts `f` passed in. -/
def uniformChooseF (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) (f : GraphFacts) :
    Except SharingError UniformChoice := do
  let sg := uniformStageF w ex p f
  unless componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) do
    throw (.internal "uncertain components are not a separated partition")
  let (results, states, costEvals) ← searchComponents limits ex sg
  let (chosenDelta, chosenX, lowerBracket) ← uniformKnapsack limits sg.cs.size results
  let modelInt : _root_.Int := (csBase ex p sg : Nat) + chosenDelta +
    (tag0Size (sg.cs.size + chosenX.size) : _root_.Int)
  if modelInt < 0 then throw (.internal "negative model length")
  let model := modelInt.toNat
  if model > limits.maxOutputBytes then
    throw (.resourceExhausted .outputBytes limits.maxOutputBytes)
  return { facts := sg.f, certainStored := sg.cs, certainExcluded := sg.ce, uncertain := sg.unc,
           lowDegree := sg.low, components := sg.comps, stored := mergeSorted sg.cs chosenX, model,
           states, costEvals, lowerBracket }

theorem uniformChoose_eq_F (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) :
    uniformChoose w limits ex p = uniformChooseF w limits ex p (graphFacts ex.dag ex.roots) := by
  unfold uniformChoose uniformChooseF
  rw [uniformStage_eq_F]

/-- `inClassCheck` with the in-degrees `deg` passed in. -/
def inClassCheckD (deg : Array Nat) (stored : Array Nat) : Bool :=
  (List.range stored.size).all (fun i => decide (i + 1 < stored.size → stored[i]! < stored[i + 1]!)) &&
    stored.all (fun t => decide (2 ≤ deg[t]!))

/-- `uniformFinish` with the in-degrees `deg` passed in. -/
def uniformFinishF (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) (deg : Array Nat)
    (c : UniformChoice) : Except SharingError UniformSharingResult := do
  let n := ex.dag.size
  let stored := c.stored
  let model := c.model
  unless stored.all (· < n) do
    throw (.internal "stored term out of range")
  unless inClassCheckD deg stored do
    throw (.internal "stored terms are not increasing terms of in-degree at least 2")
  let order := pinnedOrder ex.dag c.facts.deg stored
  let width := stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none)
  let (entries, roots, predicted, work) ← p.materializeDependent order ex.roots width limits
  unless predicted == model do
    throw (.internal s!"uniform model length {model} differs from the full evaluation {predicted}")
  let (entryIds, rootIds, _) ← reexpand limits ex.dag entries roots
  unless entryIds == order do
    throw (.internal "materialized entries do not expand to the stored terms")
  unless rootIds == ex.roots do
    throw (.internal "materialized roots do not expand to the input roots")
  let measured := tag0Size entries.size + exprsSize entries + exprsSize roots
  let unshared := tag0Size 0 + rootsCost p.base ex.roots
  let stats : Stats :=
    { exprVisits := ex.visits, internedNodes := ex.internedNodes, distinctSubterms := n,
      candidates := c.certainStored.size + c.uncertain.size, statesExpanded := c.states,
      costEvals := c.costEvals, materializedNodes := work, outputBytes := measured }
  return {
    result := { roots, sharing := entries, tableTerms := order, variableBytes := measured,
                modelBytes := model, unsharedBytes := unshared, stats }
    stored, certainStored := c.certainStored, certainExcluded := c.certainExcluded,
    uncertain := c.uncertain, lowDegree := c.lowDegree, components := c.components,
    statesVisited := c.states, lowerBracket := c.lowerBracket }

theorem uniformFinish_eq_F (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep)
    (c : UniformChoice) :
    uniformFinish w limits ex p c =
      uniformFinishF w limits ex p (graphFacts ex.dag ex.roots).deg c := by
  unfold uniformFinish uniformFinishF inClassCheck inClassCheckD
  rfl

/-- `optimizeUniformExpanded` after its DAG checks, with the DAG tables `p`,
the graph facts `f` and the outcome of the spine check passed in. -/
def optimizeUniformF (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) (f : GraphFacts)
    (spine : Except SharingError Unit) : Except SharingError UniformSharingResult := do
  spine
  let c ← uniformChooseF w limits ex p f
  uniformFinishF w limits ex p f.deg c

theorem optimizeUniformExpanded_eq_F (w : Nat) (limits : Limits) (ex : Expanded) :
    optimizeUniformExpanded w limits ex =
      if w == 0 then throw (.formatBound "uniform Share width" 0)
      else (uniformDagChecks ex).bind fun _ =>
        optimizeUniformF w limits ex (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
          (uniformSpineCheck ex (Prep.ofDag ex.dag)) := by
  unfold optimizeUniformExpanded optimizeUniformF uniformDagChecks uniformSpineCheck
  simp only [uniformChoose_eq_F, uniformFinish_eq_F]
  cases (w == 0) <;>
  cases childrenPrecede ex.dag.nodes <;>
  cases ex.dag.nodes.all (fun node => node.children.size == node.head.arity) <;>
  cases ex.roots.all (· < ex.dag.size) <;>
  cases (reachMarks ex.dag.nodes ex.roots).all id <;>
  cases (List.range ex.dag.size).all (fun t => (Prep.ofDag ex.dag).spineLen[t]! < teleSubaddEnd) <;>
  rfl

/-- `tieredResult` with the candidate count `k` and the phase-1 layout length
passed in. -/
def tieredResultF (layout : ShareLayout) (w : Nat) (u : UniformSharingResult) (a : Allocation)
    (m : Rematerialized) (k phase1Layout : Nat) : TieredSharingResult :=
  let stats : TieredStats :=
    { layout := layout, candidateCount := k, w := w,
      candidateLengths := #[(w, m.bytes)], phase1ModelBytes := u.result.modelBytes,
      phase1LayoutBytes := phase1Layout, slotStates := a.slotStates, firstTier := a.tier,
      keptPhase1Order := a.kept, phase1RefCost := a.refCost1, finalRefCost := a.refCostFinal,
      phase3LayoutBytes := m.bytes, savings := phase1Layout - m.bytes }
  let rstats : Stats :=
    { u.result.stats with materializedNodes := m.work, outputBytes := m.measured }
  let res : ExactSharingResult :=
    { u.result with
      roots := m.roots, sharing := m.entries, tableTerms := a.order,
      variableBytes := m.measured, modelBytes := m.bytes, stats := rstats }
  { result := res, phase1 := u, stats := stats }

/-- The candidate count of `tieredResult`: terms with in-degree at least 2
and unshared length at least 2. -/
def tieredCandidateCount (n : Nat) (p : Prep) (f : GraphFacts) : Nat :=
  ((Array.range n).filter fun t => f.deg[t]! ≥ 2 && p.base[t]! ≥ 2).size

theorem tieredResult_eq_F (layout : ShareLayout) (ex : Expanded) (w : Nat)
    (u : UniformSharingResult) (a : Allocation) (m : Rematerialized) :
    tieredResult layout ex w u a m =
      tieredResultF layout w u a m
        (tieredCandidateCount ex.dag.size (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots))
        (layoutBytes layout u.result.sharing u.result.roots) := by
  unfold tieredResult tieredResultF tieredCandidateCount
  rfl

/-- `rematerialize` with the DAG tables `p` passed in. -/
def rematerializeP (p : Prep) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (order : Array Nat) (phase1Layout : Nat) : Except SharingError Rematerialized := do
  let (entries, roots, predicted, work) ←
    materializeTableOnePass p order ex.roots limits layout.widthAt
  let priced := layoutBytes layout entries roots
  checkInternal (priced == predicted)
    s!"layout length {priced} differs from the evaluation {predicted}"
  checkInternal (predicted ≤ phase1Layout)
    s!"re-materialization {predicted} is longer than phase 1 {phase1Layout}"
  let (entryIds, rootIds, _) ← reexpand limits ex.dag entries roots
  checkInternal (entryIds == order) "re-materialized entries do not expand to the stored terms"
  checkInternal (rootIds == ex.roots) "re-materialized roots do not expand to the input roots"
  checkInternal ((entries ++ roots).all fun e => (wireCounts e).isSome)
    "a re-materialized expression has a count outside the wire domain"
  return { entries, roots, bytes := predicted, work, measured := priced }

theorem rematerialize_eq_P (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (order : Array Nat) (phase1Layout : Nat) :
    rematerialize layout limits ex order phase1Layout =
      rematerializeP (Prep.ofDag ex.dag) layout limits ex order phase1Layout := by
  unfold rematerialize rematerializeP
  rfl

/-- One candidate (`tieredAtWidth`) after the DAG checks, with the
width-independent tables passed in. -/
def tieredAtWidthF (layout : ShareLayout) (limits : Limits) (ex : Expanded) (w : Nat)
    (p : Prep) (f : GraphFacts) (spine : Except SharingError Unit) (k : Nat) :
    Except SharingError TieredSharingResult := do
  let u ← optimizeUniformF w limits ex p f spine
  let a ← allocate layout limits ex.dag f.deg u.result.tableTerms u.result.sharing u.result.roots
  let phase1Layout := layoutBytes layout u.result.sharing u.result.roots
  let m ← rematerializeP p layout limits ex a.order phase1Layout
  return tieredResultF layout w u a m k phase1Layout

theorem tieredAtWidth_eq_F (layout : ShareLayout) (limits : Limits) (ex : Expanded) (w : Nat)
    (hw : (w == 0) = false) :
    tieredAtWidth layout limits ex w =
      (uniformDagChecks ex).bind fun _ =>
        tieredAtWidthF layout limits ex w (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)
          (uniformSpineCheck ex (Prep.ofDag ex.dag))
          (tieredCandidateCount ex.dag.size (Prep.ofDag ex.dag) (graphFacts ex.dag ex.roots)) := by
  unfold tieredAtWidth tieredAtWidthF
  rw [optimizeUniformExpanded_eq_F]
  simp only [hw, Bool.false_eq_true, if_false, tieredResult_eq_F, rematerialize_eq_P]
  cases uniformDagChecks ex <;> rfl

/-- `tieredAtWidth` with the width-independent tables computed once for its
three phases. -/
def tieredAtWidthC (layout : ShareLayout) (limits : Limits) (ex : Expanded) (w : Nat) :
    Except SharingError TieredSharingResult :=
  if w == 0 then throw (.formatBound "uniform Share width" 0)
  else
    (uniformDagChecks ex).bind fun _ =>
      let p := Prep.ofDag ex.dag
      let f := graphFacts ex.dag ex.roots
      tieredAtWidthF layout limits ex w p f (uniformSpineCheck ex p)
        (tieredCandidateCount ex.dag.size p f)

@[csimp] theorem tieredAtWidth_eq_C : @tieredAtWidth = @tieredAtWidthC := by
  funext layout limits ex w
  unfold tieredAtWidthC
  split
  · rename_i hw
    unfold tieredAtWidth
    rw [optimizeUniformExpanded_eq_F]
    simp only [hw, if_true]
    rfl
  · rename_i hw
    exact tieredAtWidth_eq_F layout limits ex w (by simpa using hw)

/-- The best of the three candidates with every candidate's length (the tail
of `canonicalTieredCore`). -/
def tieredPick (c1 c2 c3 : TieredSharingResult) : TieredSharingResult :=
  let best := #[c2, c3].foldl (fun b c => if tieredBetter c b then c else b) c1
  let lengths := #[c1, c2, c3].map fun c => (c.stats.w, c.stats.phase3LayoutBytes)
  { best with stats := { best.stats with candidateLengths := lengths } }

/-- Constants with at least this many distinct subterms compute their three
candidates as parallel tasks. -/
def tieredParMin : Nat := 1024

/-- The three candidates `run 1`, `run 2`, `run 3`, combined in width order
(the first failure in width order is the result). For a DAG of at least
`tieredParMin` terms the three are spawned as tasks before the first is
awaited; the value is the same (`(Task.spawn f).get = f ()`). -/
def tieredCandidates (n : Nat) (run : Nat → Except SharingError TieredSharingResult) :
    Except SharingError TieredSharingResult :=
  if n < tieredParMin then do
    let c1 ← run 1
    let c2 ← run 2
    let c3 ← run 3
    return tieredPick c1 c2 c3
  else
    let ts := #[1, 2, 3].map fun w => Task.spawn fun _ => run w
    do
      let c1 ← ts[0]!.get
      let c2 ← ts[1]!.get
      let c3 ← ts[2]!.get
      return tieredPick c1 c2 c3

theorem tieredCandidates_eq (n : Nat) (run : Nat → Except SharingError TieredSharingResult) :
    tieredCandidates n run = do
      let c1 ← run 1
      let c2 ← run 2
      let c3 ← run 3
      return tieredPick c1 c2 c3 := by
  unfold tieredCandidates
  split
  · rfl
  · simp [Task.spawn]

/-- `canonicalTieredCore` with the DAG checks run once, the width-independent
tables computed once for the three candidates, and the candidates of a large
DAG computed in parallel. -/
def canonicalTieredCoreC (layout : ShareLayout) (limits : Limits) (dag : Dag)
    (roots : Array Nat) : Except SharingError TieredSharingResult :=
  let ex : Expanded := { dag, roots, visits := 0, internedNodes := 0 }
  (uniformDagChecks ex).bind fun _ =>
    let p := Prep.ofDag dag
    let f := graphFacts dag roots
    let spine := uniformSpineCheck ex p
    let k := tieredCandidateCount dag.size p f
    tieredCandidates dag.size fun w => tieredAtWidthF layout limits ex w p f spine k

@[csimp] theorem canonicalTieredCore_eq_C : @canonicalTieredCore = @canonicalTieredCoreC := by
  funext layout limits dag roots
  unfold canonicalTieredCore canonicalTieredCoreC
  simp only [tieredAtWidth_eq_F _ _ _ 1 rfl, tieredAtWidth_eq_F _ _ _ 2 rfl,
    tieredAtWidth_eq_F _ _ _ 3 rfl, tieredCandidates_eq]
  cases uniformDagChecks { dag, roots, visits := 0, internedNodes := 0 } <;> rfl

/-- `canonicalTieredExpanded`, compiled with the parts above. -/
def canonicalTieredExpandedC (layout : ShareLayout) (limits : Limits) (ex : Expanded) :
    Except SharingError TieredSharingResult := do
  let r ← canonicalTieredCore layout limits ex.dag ex.roots
  return withExpansionStats ex r

@[csimp] theorem canonicalTieredExpanded_eq_C :
    @canonicalTieredExpanded = @canonicalTieredExpandedC := by
  funext layout limits ex
  unfold canonicalTieredExpanded canonicalTieredExpandedC
  rfl

/-- `optimizeUniformExpanded` with `Prep.ofDag` and the graph facts computed
once for its stages. -/
def optimizeUniformExpandedC (w : Nat) (limits : Limits) (ex : Expanded) :
    Except SharingError UniformSharingResult :=
  if w == 0 then throw (.formatBound "uniform Share width" 0)
  else (uniformDagChecks ex).bind fun _ =>
    let p := Prep.ofDag ex.dag
    optimizeUniformF w limits ex p (graphFacts ex.dag ex.roots) (uniformSpineCheck ex p)

@[csimp] theorem optimizeUniformExpanded_eq_C :
    @optimizeUniformExpanded = @optimizeUniformExpandedC := by
  funext w limits ex
  exact optimizeUniformExpanded_eq_F w limits ex

end Ix.Sharing.Exact

end
