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
  The copies run the component loop of the uniform stages as
  `searchComponentsArea` (`Exact.AreaSearch`, the search on each component's
  area), which is the specification's loop once the DAG checks have passed
  (`uniformChoose_eq_G`, from `AreaProof.searchComponentsArea_eq`).
  For a DAG of at least `tieredParMin` terms the three candidates run as
  parallel tasks and are combined in width order, which is the same value
  (`tieredCandidates_eq`); only the latency of a large constant changes.
-/
module

public import Ix.Sharing.Exact.TierFast
public import Ix.Sharing.Exact.PinnedFast
public import Ix.Sharing.Exact.KnapsackFast
public import Ix.Sharing.Exact.AreaSearch
import all Ix.Sharing.Exact.Tiered
import all Ix.Sharing.Exact.Uniform
import all Ix.Sharing.Exact.UniformSearch
import all Ix.Sharing.Exact.Dictionary
import all Ix.Sharing.Exact.Dag
import all Ix.Sharing.Exact.Basic
import all Ix.Sharing.Exact.Reexpand
import all Ix.Sharing.Exact.Search
import all Ix.Sharing.Exact.Phase3
import Ix.Sharing.Exact.AreaSearchEq

public section

namespace Ix.Sharing.Exact

/-- Increment reference counts in `refs` directly for every `Share(i)` in `e`,
without allocating an intermediate `shareIndices` array. -/
def countShares : Ixon.Expr → Array Nat → Array Nat
  | .share i, refs =>
    let idx := i.toNat
    if idx < refs.size then refs.modify idx (· + 1) else refs
  | .prj _ _ v, refs => countShares v refs
  | .app f a, refs => countShares a (countShares f refs)
  | .lam _ t b, refs => countShares b (countShares t refs)
  | .all _ _ t b, refs => countShares b (countShares t refs)
  | .letE _ t v b, refs => countShares b (countShares v (countShares t refs))
  | _, refs => refs

private theorem shareIndices_foldl (e : Ixon.Expr) (acc refs : Array Nat) :
    (shareIndices e acc).foldl
        (fun refs i => if i < refs.size then refs.modify i (· + 1) else refs) refs =
      countShares e (acc.foldl
        (fun refs i => if i < refs.size then refs.modify i (· + 1) else refs) refs) := by
  induction e generalizing acc refs with
  | share i =>
    unfold shareIndices countShares
    rw [← Array.foldl_toList, Array.toList_push, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Array.foldl_toList]
  | prj _ _ v ih =>
    unfold shareIndices countShares
    exact ih acc refs
  | app f a ihf iha =>
    unfold shareIndices countShares
    rw [iha, ihf]
  | lam _ t b iht ihb =>
    unfold shareIndices countShares
    rw [ihb, iht]
  | all _ _ t b iht ihb =>
    unfold shareIndices countShares
    rw [ihb, iht]
  | letE _ t v b iht ihv ihb =>
    unfold shareIndices countShares
    rw [ihb, ihv, iht]
  | _ => rfl

/-- `tierWeights` folding `countShares` directly over `entries1` and `roots1`
without allocating `entries1 ++ roots1` or per-expression `shareIndices` arrays. -/
def tierWeightsFast (order1 : Array Nat) (entries1 roots1 : Array Ixon.Expr) :
    Std.HashMap Nat Nat :=
  if order1.isEmpty then {}
  else
    let init := Array.replicate order1.size 0
    let refs := entries1.foldl (fun refs e => countShares e refs) init
    let refs := roots1.foldl (fun refs e => countShares e refs) refs
    (List.range order1.size).foldl (fun m i => m.insert order1[i]! refs[i]!) {}

private theorem array_foldl_append {α β : Type} (f : β → α → β) (init : β) (a b : Array α) :
    (a ++ b).foldl f init = b.foldl f (a.foldl f init) := by
  rw [← Array.foldl_toList, Array.toList_append, List.foldl_append,
    Array.foldl_toList, Array.foldl_toList]

theorem tierWeightsFast_eq (order1 : Array Nat) (entries1 roots1 : Array Ixon.Expr) :
    tierWeightsFast order1 entries1 roots1 = tierWeights order1 entries1 roots1 := by
  unfold tierWeightsFast tierWeights shareCounts
  split
  · rename_i hEmpty
    rw [Array.isEmpty_iff] at hEmpty
    subst hEmpty
    rfl
  · have hstep : (fun (refs : Array Nat) (e : Ixon.Expr) =>
        (shareIndices e #[]).foldl
          (fun refs i => if i < refs.size then refs.modify i (· + 1) else refs) refs) =
        (fun refs e => countShares e refs) := by
      funext refs e
      exact shareIndices_foldl e #[] refs
    rw [hstep, array_foldl_append]

/-- `checkInternal` with a lazy message thunk so the error string is not
formatted when `ok` is `true`. -/
@[inline] def checkInternalLazy (ok : Bool) (msg : Unit → String) : Except SharingError Unit :=
  if ok then .ok () else .error (.internal (msg ()))

/-- `allocate`, compiled with the fast first tier and direct share counting. -/
def allocateC (layout : ShareLayout) (limits : Limits) (dag : Dag) (deg : Array Nat)
    (order1 : Array Nat) (entries1 roots1 : Array Ixon.Expr) :
    Except SharingError Allocation := do
  let wm := tierWeightsFast order1 entries1 roots1
  let dm := tierDeps order1 entries1
  let weight := fun t => wm.getD t 0
  let deps := fun t => dm.getD t []
  let stored := (order1.toList.mergeSort (· ≤ ·)).toArray
  let (tier, slotStates) ← firstTier order1 weight deps (min 8 order1.size) limits
  let rest := stored.filter (!tier.contains ·)
  let order2 := pinnedOrder dag deg tier ++ kahnOrder weight deps rest
  checkInternalLazy ((order2.toList.mergeSort (· ≤ ·)).toArray == stored)
    (fun _ => "the allocated order is not a permutation of the phase-1 table")
  let kept : Bool := refCost layout weight order2 > refCost layout weight order1
  let order := if kept then order1 else order2
  checkInternalLazy (respectsDeps order deps)
    (fun _ => "the allocated order places a body reference after its user")
  return { tier, slotStates, order, kept, refCost1 := refCost layout weight order1,
           refCostFinal := refCost layout weight order }

@[csimp] theorem allocate_eq_C : @allocate = @allocateC := by
  funext layout limits dag deg order1 entries1 roots1
  unfold allocate allocateC checkInternal checkInternalLazy
  rw [tierWeightsFast_eq]
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

/-! ## The component loop on the areas

`uniformChooseG` runs the component loop as `searchComponentsArea` (the
search on each component's area with the truncated evaluation), which is
`searchComponentsWith` when the stage's tables are those of `uniformStageF`
on `Prep.ofDag` of a DAG that passed `uniformDagChecks`
(`AreaProof.searchComponentsArea_eq`). -/

/-- `uniformChooseF` with the component loop on the areas. -/
def uniformChooseG (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) (f : GraphFacts) :
    Except SharingError UniformChoice := do
  let sg := uniformStageF w ex p f
  unless componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) do
    throw (.internal "uncertain components are not a separated partition")
  let (results, states, costEvals) ← searchComponentsArea limits ex sg.f sg.up sg.cand sg.b0
    sg.vis0 sg.rootCount sg.slack sg.theta sg.baseEv sg.widthCs sg.allTrue sg.unc sg.opaq sg.comps
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

theorem upPrep_fields (p : Prep) (w : Nat) (opaq : Array Bool) :
    (UPrep.mk' p w opaq).prep = p ∧ (UPrep.mk' p w opaq).w = w ∧
      (UPrep.mk' p w opaq).opaq = opaq := by
  unfold UPrep.mk'
  exact ⟨rfl, rfl, rfl⟩

/-- The widths of the certain-stored terms are `w` exactly where they are
marked opaque. -/
theorem widths_fold (w n : Nat) (cs : Array Nat) (u : Nat) :
    widthOf (cs.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none)) u =
      if (cs.foldl (fun acc t => acc.set! t true) (Array.replicate n false))[u]! then some w
      else none := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  have key : ∀ (l : List Nat) (W : Array (Option Nat)) (O : Array Bool), W.size = O.size →
      (∀ u, widthOf W u = if O[u]! then some w else none) →
      ∀ u, widthOf (l.foldl (fun acc t => acc.set! t (some w)) W) u =
        if (l.foldl (fun acc t => acc.set! t true) O)[u]! then some w else none := by
    intro l
    induction l with
    | nil => intro W O _ h; exact h
    | cons t l ih =>
      intro W O hs h
      simp only [List.foldl_cons]
      apply ih _ _ (by simp [hs])
      intro v
      rw [getElem!_setBang]
      by_cases hv : v = t ∧ t < O.size
      · rw [ite_eq_left hv]
        obtain ⟨rfl, ht⟩ := hv
        unfold widthOf
        simp [hs, ht]
      · rw [ite_eq_right hv, ← h v]
        unfold widthOf
        by_cases hvt : v = t
        · subst hvt
          have : ¬ v < W.size := by rw [hs]; exact fun h' => hv ⟨rfl, h'⟩
          simp [this]
        · simp [Ne.symm hvt]
  apply key _ _ _ (by simp)
  intro v
  unfold widthOf
  by_cases hv : v < n
  · rw [getElem!_pos _ v (by simpa using hv)]; simp [hv]
  · rw [getElem!_neg _ v (by simpa using hv)]; simp [hv]

/-- The facts of the stage that the area search relies on. -/
private theorem stageOK_F (w : Nat) (ex : Expanded) (f : GraphFacts) (hdag : AreaProof.DagOK ex.dag) :
    AreaProof.StageOK ex (uniformStageF w ex (Prep.ofDag ex.dag) f).up
      (uniformStageF w ex (Prep.ofDag ex.dag) f).baseEv
      (uniformStageF w ex (Prep.ofDag ex.dag) f).widthCs
      (uniformStageF w ex (Prep.ofDag ex.dag) f).allTrue := by
  have hf := upPrep_fields (Prep.ofDag ex.dag) w (uniformStageF w ex (Prep.ofDag ex.dag) f).opaq
  have hup : (uniformStageF w ex (Prep.ofDag ex.dag) f).up =
      UPrep.mk' (Prep.ofDag ex.dag) w (uniformStageF w ex (Prep.ofDag ex.dag) f).opaq := rfl
  rw [← hup] at hf
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨hdag, h1, fun u => ?_, rfl, by rw [h1]; rfl⟩
  rw [h3, h2]
  exact widths_fold w ex.dag.size _ u

private theorem uniformChoose_eq_G (w : Nat) (limits : Limits) (ex : Expanded) (f : GraphFacts)
    (hdag : AreaProof.DagOK ex.dag) :
    uniformChooseG w limits ex (Prep.ofDag ex.dag) f =
      uniformChooseF w limits ex (Prep.ofDag ex.dag) f := by
  unfold uniformChooseG uniformChooseF
  simp only [AreaProof.searchComponentsArea_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (stageOK_F w ex f hdag), searchComponents_eq_via, searchComponentsVia]

/-- The DAG checks give the facts of the DAG the area search relies on. -/
private theorem dagOK_of_checks {ex : Expanded} (h : uniformDagChecks ex = .ok ()) :
    AreaProof.DagOK ex.dag := by
  unfold uniformDagChecks at h
  by_cases h1 : childrenPrecede ex.dag.nodes = true
  · by_cases h2 : (ex.dag.nodes.all fun node => node.children.size == node.head.arity) = true
    · refine ⟨h1, fun t ht => ?_⟩
      have ht' : t < ex.dag.nodes.size := by simpa [Dag.size] using ht
      have := Array.all_eq_true.mp h2 t ht'
      have hn : ex.dag.node t = ex.dag.nodes[t] := by
        unfold Dag.node; simp [ht']
      rw [hn]
      simpa using this
    · simp [h1, h2] at h
      cases h
  · simp [h1] at h
    cases h

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

/-- `uniformFinishF` with `ReIndex.ofDag` passed in. -/
def uniformFinishIx (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) (deg : Array Nat)
    (reIx : ReIndex) (c : UniformChoice) : Except SharingError UniformSharingResult := do
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
  let (entryIds, rootIds, _) ← reexpandWithIndex limits ex.dag reIx entries roots
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

theorem uniformFinishIx_eq_F (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep)
    (deg : Array Nat) (c : UniformChoice) :
    uniformFinishIx w limits ex p deg (ReIndex.ofDag ex.dag) c =
      uniformFinishF w limits ex p deg c := by
  unfold uniformFinishIx uniformFinishF
  simp only [← reexpand_eq_withIndex]

theorem layoutBytes_eq_measured (layout : ShareLayout) (entries roots : Array Ixon.Expr) :
    layoutBytes layout entries roots =
      tag0Size entries.size + exprsSize entries + exprsSize roots := by
  cases layout
  rfl

theorem uniformFinishF_layoutBytes (layout : ShareLayout) (w : Nat) (limits : Limits)
    (ex : Expanded) (p : Prep) (deg : Array Nat) (c : UniformChoice)
    {u : UniformSharingResult} (hu : uniformFinishF w limits ex p deg c = .ok u) :
    u.result.variableBytes = layoutBytes layout u.result.sharing u.result.roots := by
  unfold uniformFinishF at hu
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hu
  split at hu <;> try cases hu
  split at hu <;> try cases hu
  split at hu <;> try cases hu
  split at hu <;> try cases hu
  split at hu <;> try cases hu
  split at hu <;> try cases hu
  split at hu <;> try cases hu
  exact (layoutBytes_eq_measured layout _ _).symm

/-- `optimizeUniformExpanded` after its DAG checks, with the DAG tables `p`,
the graph facts `f` and the outcome of the spine check passed in. -/
def optimizeUniformF (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) (f : GraphFacts)
    (spine : Except SharingError Unit) : Except SharingError UniformSharingResult := do
  spine
  let c ← uniformChooseF w limits ex p f
  uniformFinishF w limits ex p f.deg c

/-- `optimizeUniformF` with the component loop on the areas. -/
def optimizeUniformG (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) (f : GraphFacts)
    (spine : Except SharingError Unit) : Except SharingError UniformSharingResult := do
  spine
  let c ← uniformChooseG w limits ex p f
  uniformFinishF w limits ex p f.deg c

/-- `optimizeUniformG` with `ReIndex.ofDag` passed in. -/
def optimizeUniformIx (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) (f : GraphFacts)
    (reIx : ReIndex) (spine : Except SharingError Unit) :
    Except SharingError UniformSharingResult := do
  spine
  let c ← uniformChooseG w limits ex p f
  uniformFinishIx w limits ex p f.deg reIx c

theorem optimizeUniformIx_eq_G (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep)
    (f : GraphFacts) (spine : Except SharingError Unit) :
    optimizeUniformIx w limits ex p f (ReIndex.ofDag ex.dag) spine =
      optimizeUniformG w limits ex p f spine := by
  unfold optimizeUniformIx optimizeUniformG
  simp only [uniformFinishIx_eq_F]

theorem optimizeUniformG_layoutBytes (layout : ShareLayout) (w : Nat) (limits : Limits)
    (ex : Expanded) (p : Prep) (f : GraphFacts) (spine : Except SharingError Unit)
    {u : UniformSharingResult} (hu : optimizeUniformG w limits ex p f spine = .ok u) :
    u.result.variableBytes = layoutBytes layout u.result.sharing u.result.roots := by
  unfold optimizeUniformG at hu
  dsimp only [Bind.bind, Except.bind] at hu
  split at hu <;> try cases hu
  split at hu <;> try cases hu
  exact uniformFinishF_layoutBytes layout w limits ex p f.deg _ hu

private theorem optimizeUniform_eq_G (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep)
    (f : GraphFacts) (spine : Except SharingError Unit) (hp : p = Prep.ofDag ex.dag)
    (hdag : AreaProof.DagOK ex.dag) :
    optimizeUniformG w limits ex p f spine = optimizeUniformF w limits ex p f spine := by
  subst hp
  unfold optimizeUniformG optimizeUniformF
  rw [uniformChoose_eq_G w limits ex f hdag]

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
  checkInternalLazy (priced == predicted)
    (fun _ => s!"layout length {priced} differs from the evaluation {predicted}")
  checkInternalLazy (predicted ≤ phase1Layout)
    (fun _ => s!"re-materialization {predicted} is longer than phase 1 {phase1Layout}")
  let (entryIds, rootIds, _) ← reexpand limits ex.dag entries roots
  checkInternalLazy (entryIds == order)
    (fun _ => "re-materialized entries do not expand to the stored terms")
  checkInternalLazy (rootIds == ex.roots)
    (fun _ => "re-materialized roots do not expand to the input roots")
  checkInternalLazy ((entries ++ roots).all fun e => (wireCounts e).isSome)
    (fun _ => "a re-materialized expression has a count outside the wire domain")
  return { entries, roots, bytes := predicted, work, measured := priced }

theorem rematerialize_eq_P (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (order : Array Nat) (phase1Layout : Nat) :
    rematerialize layout limits ex order phase1Layout =
      rematerializeP (Prep.ofDag ex.dag) layout limits ex order phase1Layout := by
  unfold rematerialize rematerializeP checkInternal checkInternalLazy
  rfl

private theorem array_all_append {α : Type} (a b : Array α) (p : α → Bool) :
    (a ++ b).all p = (a.all p && b.all p) := by
  rw [← Array.all_toList, Array.toList_append, List.all_append, Array.all_toList, Array.all_toList]

/-- `rematerializeP` with `ReIndex.ofDag` and the spine parent lists passed in,
and avoiding `entries ++ roots` allocation. -/
def rematerializeIx (p : Prep) (reIx : ReIndex) (parents sp : Array (Array Nat))
    (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (order : Array Nat) (phase1Layout : Nat) : Except SharingError Rematerialized := do
  let (entries, roots, predicted, work) ←
    materializeTableOnePassWithSpines p parents sp order ex.roots limits layout.widthAt
  let priced := layoutBytes layout entries roots
  checkInternalLazy (priced == predicted)
    (fun _ => s!"layout length {priced} differs from the evaluation {predicted}")
  checkInternalLazy (predicted ≤ phase1Layout)
    (fun _ => s!"re-materialization {predicted} is longer than phase 1 {phase1Layout}")
  let (entryIds, rootIds, _) ← reexpandWithIndex limits ex.dag reIx entries roots
  checkInternalLazy (entryIds == order)
    (fun _ => "re-materialized entries do not expand to the stored terms")
  checkInternalLazy (rootIds == ex.roots)
    (fun _ => "re-materialized roots do not expand to the input roots")
  checkInternalLazy (entries.all (fun e => (wireCounts e).isSome) &&
      roots.all (fun e => (wireCounts e).isSome))
    (fun _ => "a re-materialized expression has a count outside the wire domain")
  return { entries, roots, bytes := predicted, work, measured := priced }

theorem rematerializeIx_eq_P (p : Prep) (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (order : Array Nat) (phase1Layout : Nat) :
    rematerializeIx p (ReIndex.ofDag ex.dag) (parentEdgeLists p.dag)
        (spineParentLists p.dag p.family) layout limits ex order phase1Layout =
      rematerializeP p layout limits ex order phase1Layout := by
  unfold rematerializeIx rematerializeP
  simp only [← materializeTableOnePass_eq_withSpines, ← reexpand_eq_withIndex, array_all_append]

/-- Cached unshared (empty-dictionary) evaluation and root materialization,
shared across widths 1, 2, 3 and between phases 1 and 3 whenever the stored
table is empty (`#[]`). -/
structure EmptyCache where
  noneArr : Array (Option Nat)
  ev : Thunk DictEval
  rootCost : Thunk Nat
  built : Thunk (Except SharingError
    (Array Ixon.Expr × Except SharingError (Array Nat × Array Nat × Nat) × Nat × Bool))

def mkEmptyCache (p : Prep) (limits : Limits) (ex : Expanded) (reIx : ReIndex) : EmptyCache :=
  let noneArr := Array.replicate ex.dag.size none
  let ev := Thunk.mk fun _ => p.evalAll noneArr
  let rootCost := Thunk.mk fun _ => ex.roots.foldl (fun acc r => acc + ev.get.cost[r]!) 0
  let built := Thunk.mk fun _ =>
    (ex.roots.mapM fun r => p.build ev.get noneArr noneArr false (p.dag.size + 1) r).map fun rs =>
      (rs, reexpandWithIndex limits ex.dag reIx #[] rs,
       tag0Size 0 + exprsSize #[] + exprsSize rs,
       rs.all (fun e => (wireCounts e).isSome))
  { noneArr, ev, rootCost, built }

private theorem widthCs_empty_eq (w n : Nat) (cs : Array Nat) :
    (if cs.isEmpty then Array.replicate n none
     else cs.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none)) =
    cs.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none) := by
  split
  · rename_i h
    rw [Array.isEmpty_iff] at h
    subst h
    rfl
  · rfl

private theorem baseEv_empty_eq (w : Nat) (ex : Expanded) (cs : Array Nat) :
    (if cs.isEmpty then (Prep.ofDag ex.dag).evalAll (Array.replicate ex.dag.size none)
     else (Prep.ofDag ex.dag).eval
       (cs.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none))
       (Array.replicate ex.dag.size true)) =
    (Prep.ofDag ex.dag).eval
      (cs.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none))
      (Array.replicate ex.dag.size true) := by
  split
  · rename_i h
    rw [Array.isEmpty_iff] at h
    subst h
    rfl
  · rfl

/-- `uniformStageF` reusing the cached empty-dictionary evaluation when `cs` is empty. -/
def uniformStageCached (w : Nat) (ex : Expanded) (p : Prep) (f : GraphFacts)
    (cache : EmptyCache) : UStage :=
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
    if cs.isEmpty then cache.noneArr
    else cs.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none)
  let allTrue := Array.replicate n true
  let baseEv :=
    if cs.isEmpty then cache.ev.get
    else p.eval widthCs allTrue
  { f, cand, b0, vis0, theta, cls, cs, ce := pick .certainExcluded, unc,
    low := pick .lowDegree, opaq, up := UPrep.mk' p w opaq, widthCs, allTrue,
    baseEv, comps := uncertainComponents ex.dag cls,
    slack := tag0Size (cs.size + unc.size) - tag0Size cs.size,
    rootCount := ex.roots.foldl (fun acc r => acc.modify r (· + 1)) (Array.replicate n 0) }

theorem uniformStageCached_eq_F (w : Nat) (limits : Limits) (ex : Expanded)
    (f : GraphFacts) (reIx : ReIndex) :
    uniformStageCached w ex (Prep.ofDag ex.dag) f
        (mkEmptyCache (Prep.ofDag ex.dag) limits ex reIx) =
      uniformStageF w ex (Prep.ofDag ex.dag) f := by
  unfold uniformStageCached uniformStageF mkEmptyCache
  dsimp only [Thunk.get]
  simp only [widthCs_empty_eq, baseEv_empty_eq]

/-- `Prep.materializeDependent` with a precomputed dictionary evaluation `ev`. -/
def Prep.materializeDependentWithEv (p : Prep) (table roots : Array Nat)
    (width : Array (Option Nat)) (ev : DictEval) (limits : Limits) :
    Except SharingError (Array Ixon.Expr × Array Ixon.Expr × Nat × Nat) := do
  if table.size ≥ wordBound then throw (.formatBound "share index" table.size)
  let index := indexOfPairs p.dag.size table.toList.zipIdx
  let entryCost := table.foldl (fun acc t => acc + p.inlineCost ev index width t) 0
  let rootCost := roots.foldl (fun acc r => acc + ev.cost[r]!) 0
  let total := tag0Size table.size + entryCost + rootCost
  if total > limits.maxMaterialize then
    throw (.resourceExhausted .materialize limits.maxMaterialize)
  let es ← table.mapM fun t => p.build ev index width true (p.dag.size + 1) t
  let rs ← roots.mapM fun r => p.build ev index width false (p.dag.size + 1) r
  return (es, rs, total, ev.work + total)

theorem materializeDependent_eq_withEv (p : Prep) (table roots : Array Nat)
    (width : Array (Option Nat)) (limits : Limits) :
    p.materializeDependent table roots width limits =
      p.materializeDependentWithEv table roots width (p.evalAll width) limits := by
  unfold Prep.materializeDependent Prep.materializeDependentWithEv
  rfl

/-- `uniformFinishIx` when `c.stored` is empty, reusing `cache`. -/
def uniformFinishEmpty (limits : Limits) (ex : Expanded) (p : Prep)
    (c : UniformChoice) (cache : EmptyCache) : Except SharingError UniformSharingResult := do
  let n := ex.dag.size
  let model := c.model
  let total := tag0Size 0 + cache.rootCost.get
  if total > limits.maxMaterialize then
    throw (.resourceExhausted .materialize limits.maxMaterialize)
  let (roots, reex, measured, _) ← cache.built.get
  let work := cache.ev.get.work + total
  unless total == model do
    throw (.internal s!"uniform model length {model} differs from the full evaluation {total}")
  let (entryIds, rootIds, _) ← reex
  unless entryIds == #[] do
    throw (.internal "materialized entries do not expand to the stored terms")
  unless rootIds == ex.roots do
    throw (.internal "materialized roots do not expand to the input roots")
  let unshared := tag0Size 0 + rootsCost p.base ex.roots
  let stats : Stats :=
    { exprVisits := ex.visits, internedNodes := ex.internedNodes, distinctSubterms := n,
      candidates := c.certainStored.size + c.uncertain.size, statesExpanded := c.states,
      costEvals := c.costEvals, materializedNodes := work, outputBytes := measured }
  return {
    result := { roots, sharing := #[], tableTerms := #[], variableBytes := measured,
                modelBytes := model, unsharedBytes := unshared, stats }
    stored := #[], certainStored := c.certainStored, certainExcluded := c.certainExcluded,
    uncertain := c.uncertain, lowDegree := c.lowDegree, components := c.components,
    statesVisited := c.states, lowerBracket := c.lowerBracket }

theorem uniformFinishEmpty_eq_Ix (w : Nat) (limits : Limits) (ex : Expanded)
    (deg : Array Nat) (reIx : ReIndex) (c : UniformChoice) (hc : c.stored = #[]) :
    uniformFinishEmpty limits ex (Prep.ofDag ex.dag) c
        (mkEmptyCache (Prep.ofDag ex.dag) limits ex reIx) =
      uniformFinishIx w limits ex (Prep.ofDag ex.dag) deg reIx c := by
  unfold uniformFinishEmpty uniformFinishIx mkEmptyCache Prep.materializeDependent
  rw [hc]
  have h0 : (#[] : Array Nat).size = 0 := rfl
  have h1 : ((#[] : Array Nat).all (· < ex.dag.size)) = true := by simp
  have h2 : inClassCheckD deg #[] = true := by unfold inClassCheckD; simp
  have h3 : pinnedOrder ex.dag c.facts.deg #[] = #[] := rfl
  have h4 : (#[] : Array Nat).foldl (fun acc t => acc.set! t (some w))
      (Array.replicate ex.dag.size none) = Array.replicate ex.dag.size none := by simp
  have h5 : ¬ (0 ≥ wordBound) := by decide
  have h6 : indexOfPairs (Prep.ofDag ex.dag).dag.size (#[] : Array Nat).toList.zipIdx =
      Array.replicate ex.dag.size none := rfl
  have h8 : (#[] : Array Nat).foldl
      (fun acc t => acc + (Prep.ofDag ex.dag).inlineCost
        ((Prep.ofDag ex.dag).evalAll (Array.replicate ex.dag.size none))
        (Array.replicate ex.dag.size none) (Array.replicate ex.dag.size none) t) 0 = 0 := by simp
  have h9 : ((#[] : Array Nat).mapM fun t =>
      (Prep.ofDag ex.dag).build ((Prep.ofDag ex.dag).evalAll (Array.replicate ex.dag.size none))
        (Array.replicate ex.dag.size none) (Array.replicate ex.dag.size none)
        true ((Prep.ofDag ex.dag).dag.size + 1) t) =
      (.ok #[] : Except SharingError (Array Ixon.Expr)) := by simp; rfl
  dsimp only [Thunk.get, Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]
  simp only [h1, h2, h3, h4, h6, h8, h9, Nat.add_zero, ite_true]
  simp only [h0, h5, ite_false]
  by_cases hmat :
      tag0Size 0 +
        ex.roots.foldl
          (fun acc r => acc + ((Prep.ofDag ex.dag).evalAll (Array.replicate ex.dag.size none)).cost[r]!) 0 >
        limits.maxMaterialize
  · simp only [hmat, ite_true]
    rfl
  · simp only [hmat, ite_false]
    cases ex.roots.mapM fun r =>
        (Prep.ofDag ex.dag).build ((Prep.ofDag ex.dag).evalAll (Array.replicate ex.dag.size none))
          (Array.replicate ex.dag.size none) (Array.replicate ex.dag.size none)
          false ((Prep.ofDag ex.dag).dag.size + 1) r with
    | error e => rfl
    | ok rs => rfl

/-- `uniformFinishIx` reusing `cache` when `c.stored` is empty, and reusing
`(stage.widthCs, stage.baseEv)` when `c.stored == stage.cs`. -/
def uniformFinishCached (w : Nat) (limits : Limits) (ex : Expanded) (p : Prep) (deg : Array Nat)
    (reIx : ReIndex) (stage : UStage) (cache : EmptyCache) (c : UniformChoice) :
    Except SharingError UniformSharingResult := do
  if c.stored.isEmpty then
    uniformFinishEmpty limits ex p c cache
  else
    let n := ex.dag.size
    let stored := c.stored
    let model := c.model
    unless stored.all (· < n) do
      throw (.internal "stored term out of range")
    unless inClassCheckD deg stored do
      throw (.internal "stored terms are not increasing terms of in-degree at least 2")
    let order := pinnedOrder ex.dag c.facts.deg stored
    let width :=
      if stored == stage.cs then stage.widthCs
      else stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate n none)
    let ev :=
      if stored == stage.cs then stage.baseEv
      else p.evalAll width
    let (entries, roots, predicted, work) ←
      p.materializeDependentWithEv order ex.roots width ev limits
    unless predicted == model do
      throw (.internal s!"uniform model length {model} differs from the full evaluation {predicted}")
    let (entryIds, rootIds, _) ← reexpandWithIndex limits ex.dag reIx entries roots
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

theorem uniformFinishCached_eq_Ix (w : Nat) (limits : Limits) (ex : Expanded)
    (f : GraphFacts) (reIx : ReIndex) (c : UniformChoice) :
    uniformFinishCached w limits ex (Prep.ofDag ex.dag) f.deg reIx
        (uniformStageF w ex (Prep.ofDag ex.dag) f)
        (mkEmptyCache (Prep.ofDag ex.dag) limits ex reIx) c =
      uniformFinishIx w limits ex (Prep.ofDag ex.dag) f.deg reIx c := by
  unfold uniformFinishCached
  split
  · rename_i hEmpty
    exact uniformFinishEmpty_eq_Ix w limits ex f.deg reIx c (Array.isEmpty_iff.mp hEmpty)
  · unfold uniformFinishIx
    have hwidth :
        (if c.stored == (uniformStageF w ex (Prep.ofDag ex.dag) f).cs then
          (uniformStageF w ex (Prep.ofDag ex.dag) f).widthCs
        else
          c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)) =
        c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none) := by
      split
      · rename_i hcs
        rw [eq_of_beq hcs]
        rfl
      · rfl
    have hev :
        (if c.stored == (uniformStageF w ex (Prep.ofDag ex.dag) f).cs then
          (uniformStageF w ex (Prep.ofDag ex.dag) f).baseEv
        else
          (Prep.ofDag ex.dag).evalAll
            (c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none))) =
        (Prep.ofDag ex.dag).evalAll
          (c.stored.foldl (fun acc t => acc.set! t (some w)) (Array.replicate ex.dag.size none)) := by
      split
      · rename_i hcs
        rw [eq_of_beq hcs]
        rfl
      · rfl
    dsimp only []
    simp only [hwidth, hev, materializeDependent_eq_withEv]

private theorem checks_facts {ex : Expanded} (h : uniformDagChecks ex = .ok ()) :
    childrenPrecede ex.dag.nodes = true ∧
      (ex.dag.nodes.all fun node => node.children.size == node.head.arity) = true ∧
      ex.roots.all (· < ex.dag.size) = true := by
  unfold uniformDagChecks at h
  by_cases h1 : childrenPrecede ex.dag.nodes = true
  · by_cases h2 : (ex.dag.nodes.all fun node => node.children.size == node.head.arity) = true
    · by_cases h3 : ex.roots.all (· < ex.dag.size) = true
      · exact ⟨h1, h2, h3⟩
      · simp [h1, h2, h3] at h; cases h
    · simp [h1, h2] at h; cases h
  · simp [h1] at h; cases h

/-- `rematerializeIx` when `order` is empty, reusing `cache`. -/
def rematerializeEmpty (p : Prep) (limits : Limits) (ex : Expanded)
    (phase1Layout : Nat) (cache : EmptyCache) : Except SharingError Rematerialized := do
  let rootCost := cache.rootCost.get
  if rootCost > limits.maxMaterialize then
    throw (.resourceExhausted .materialize limits.maxMaterialize)
  let (roots, reex, priced, wireOK) ← cache.built.get
  let work := p.dag.size + rootCost
  if work > limits.maxMaterializeWork then
    throw (.resourceExhausted .materializeWork limits.maxMaterializeWork)
  let predicted := tag0Size 0 + rootsCost cache.ev.get.cost ex.roots
  checkInternalLazy (priced == predicted)
    (fun _ => s!"layout length {priced} differs from the evaluation {predicted}")
  checkInternalLazy (predicted ≤ phase1Layout)
    (fun _ => s!"re-materialization {predicted} is longer than phase 1 {phase1Layout}")
  let (entryIds, rootIds, _) ← reex
  checkInternalLazy (entryIds == #[])
    (fun _ => "re-materialized entries do not expand to the stored terms")
  checkInternalLazy (rootIds == ex.roots)
    (fun _ => "re-materialized roots do not expand to the input roots")
  checkInternalLazy wireOK
    (fun _ => "a re-materialized expression has a count outside the wire domain")
  return { entries := #[], roots, bytes := predicted, work, measured := priced }

theorem rematerializeEmpty_eq_Ix (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (reIx : ReIndex) (parents sp : Array (Array Nat)) (phase1Layout : Nat)
    (hchecks : uniformDagChecks ex = .ok ()) :
    rematerializeEmpty (Prep.ofDag ex.dag) limits ex phase1Layout
        (mkEmptyCache (Prep.ofDag ex.dag) limits ex reIx) =
      rematerializeIx (Prep.ofDag ex.dag) reIx parents sp layout limits ex #[] phase1Layout := by
  obtain ⟨hcp, har, hrt⟩ := checks_facts hchecks
  unfold rematerializeEmpty rematerializeIx mkEmptyCache materializeTableOnePassWithSpines
  have h0 : (#[] : Array Nat).size = 0 := rfl
  have h1 : ¬ (0 ≥ wordBound) := by decide
  have h2 : ((#[] : Array Nat).all (· < (Prep.ofDag ex.dag).dag.size)) = true := by simp
  have h3 : indexOfPrefix (Prep.ofDag ex.dag).dag.size #[] 0 =
      Array.replicate ex.dag.size none := rfl
  have h4 : onePassOrder (Prep.ofDag ex.dag).dag #[] ex.roots
      (Array.replicate ex.dag.size none) = true := by
    unfold onePassOrder
    have hd : (Prep.ofDag ex.dag).dag = ex.dag := rfl
    rw [hd, hcp, har, hrt]
    rfl
  have h5 : (Array.replicate ex.dag.size (none : Option Nat)).map (·.map layout.widthAt) =
      Array.replicate ex.dag.size none := by
    rw [Array.map_replicate]
    rfl
  have h7 : ((#[] : Array Ixon.Expr).all fun e => (wireCounts e).isSome) = true := by simp
  dsimp only [Thunk.get, Bind.bind, Except.bind, Pure.pure, Except.pure,
    Functor.map, Except.map]
  simp only [h2, Bool.not_true, Bool.false_eq_true, ite_false, layoutBytes_eq_measured]
  simp only [h0, h1, h3, h4, h5, onePassLoop, Bool.not_true, Bool.false_eq_true,
    ite_false, Nat.zero_add]
  by_cases hmat :
      ex.roots.foldl
        (fun acc r => acc + ((Prep.ofDag ex.dag).evalAll (Array.replicate ex.dag.size none)).cost[r]!) 0 >
        limits.maxMaterialize
  · simp only [hmat, ite_true]
    rfl
  · simp only [hmat, ite_false]
    cases ex.roots.mapM fun r =>
        (Prep.ofDag ex.dag).build ((Prep.ofDag ex.dag).evalAll (Array.replicate ex.dag.size none))
          (Array.replicate ex.dag.size none) (Array.replicate ex.dag.size none)
          false ((Prep.ofDag ex.dag).dag.size + 1) r with
    | error e => rfl
    | ok rs =>
      by_cases hwork :
          (Prep.ofDag ex.dag).dag.size +
            ex.roots.foldl
              (fun acc r => acc + ((Prep.ofDag ex.dag).evalAll (Array.replicate ex.dag.size none)).cost[r]!) 0 >
            limits.maxMaterializeWork
      · simp only [hwork, ite_true]
        rfl
      · simp only [hwork, ite_false, h7, Bool.true_and]
        rfl

/-- `rematerializeIx` reusing `cache` when `order` is empty. -/
def rematerializeCached (p : Prep) (reIx : ReIndex) (parents sp : Array (Array Nat))
    (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (order : Array Nat) (phase1Layout : Nat) (cache : EmptyCache) :
    Except SharingError Rematerialized :=
  if order.isEmpty then
    rematerializeEmpty p limits ex phase1Layout cache
  else
    rematerializeIx p reIx parents sp layout limits ex order phase1Layout

theorem rematerializeCached_eq_Ix (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (reIx : ReIndex) (parents sp : Array (Array Nat)) (order : Array Nat) (phase1Layout : Nat)
    (hchecks : uniformDagChecks ex = .ok ()) :
    rematerializeCached (Prep.ofDag ex.dag) reIx parents sp layout limits ex order phase1Layout
        (mkEmptyCache (Prep.ofDag ex.dag) limits ex reIx) =
      rematerializeIx (Prep.ofDag ex.dag) reIx parents sp layout limits ex order phase1Layout := by
  unfold rematerializeCached
  split
  · rename_i hEmpty
    rw [Array.isEmpty_iff.mp hEmpty]
    exact rematerializeEmpty_eq_Ix layout limits ex reIx parents sp phase1Layout hchecks
  · rfl

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
  simp only [hw, Bool.false_eq_true, ite_false, tieredResult_eq_F, rematerialize_eq_P]
  cases uniformDagChecks ex <;> rfl

/-- `tieredAtWidthF` with the component loop on the areas. -/
def tieredAtWidthG (layout : ShareLayout) (limits : Limits) (ex : Expanded) (w : Nat)
    (p : Prep) (f : GraphFacts) (spine : Except SharingError Unit) (k : Nat) :
    Except SharingError TieredSharingResult := do
  let u ← optimizeUniformG w limits ex p f spine
  let a ← allocate layout limits ex.dag f.deg u.result.tableTerms u.result.sharing u.result.roots
  let phase1Layout := layoutBytes layout u.result.sharing u.result.roots
  let m ← rematerializeP p layout limits ex a.order phase1Layout
  return tieredResultF layout w u a m k phase1Layout

/-- `tieredAtWidthG` with `ReIndex.ofDag` and the spine parent lists passed in,
and reusing `u.result.variableBytes` instead of recomputing `layoutBytes`. -/
def tieredAtWidthIx (layout : ShareLayout) (limits : Limits) (ex : Expanded) (w : Nat)
    (p : Prep) (f : GraphFacts) (reIx : ReIndex) (parents sp : Array (Array Nat))
    (spine : Except SharingError Unit) (k : Nat) :
    Except SharingError TieredSharingResult := do
  let u ← optimizeUniformIx w limits ex p f reIx spine
  let a ← allocate layout limits ex.dag f.deg u.result.tableTerms u.result.sharing u.result.roots
  let phase1Layout := u.result.variableBytes
  let m ← rematerializeIx p reIx parents sp layout limits ex a.order phase1Layout
  return tieredResultF layout w u a m k phase1Layout

theorem tieredAtWidthIx_eq_G (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (w : Nat) (p : Prep) (f : GraphFacts) (spine : Except SharingError Unit) (k : Nat) :
    tieredAtWidthIx layout limits ex w p f (ReIndex.ofDag ex.dag)
        (parentEdgeLists p.dag) (spineParentLists p.dag p.family) spine k =
      tieredAtWidthG layout limits ex w p f spine k := by
  unfold tieredAtWidthIx tieredAtWidthG
  rw [optimizeUniformIx_eq_G]
  cases hu : optimizeUniformG w limits ex p f spine with
  | error e => rfl
  | ok u =>
    simp only [Bind.bind, Except.bind,
      optimizeUniformG_layoutBytes layout w limits ex p f spine hu,
      rematerializeIx_eq_P]

/-- `uniformChooseG` taking a prebuilt `UStage`. -/
def uniformChooseStage (limits : Limits) (ex : Expanded) (p : Prep) (sg : UStage) :
    Except SharingError UniformChoice := do
  unless componentsChecked ex.dag sg.cls sg.opaq sg.comps (componentLabels ex.dag.size sg.comps) do
    throw (.internal "uncertain components are not a separated partition")
  let (results, states, costEvals) ← searchComponentsArea limits ex sg.f sg.up sg.cand sg.b0
    sg.vis0 sg.rootCount sg.slack sg.theta sg.baseEv sg.widthCs sg.allTrue sg.unc sg.opaq sg.comps
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

/-- `optimizeUniformIx` reusing `EmptyCache`. -/
def optimizeUniformCached (w : Nat) (limits : Limits) (ex : Expanded)
    (p : Prep) (f : GraphFacts) (reIx : ReIndex) (spine : Except SharingError Unit)
    (cache : EmptyCache) : Except SharingError UniformSharingResult := do
  spine
  let stage := uniformStageCached w ex p f cache
  let c ← uniformChooseStage limits ex p stage
  uniformFinishCached w limits ex p f.deg reIx stage cache c

theorem optimizeUniformCached_eq_Ix (w : Nat) (limits : Limits) (ex : Expanded)
    (f : GraphFacts) (reIx : ReIndex) (spine : Except SharingError Unit) :
    optimizeUniformCached w limits ex (Prep.ofDag ex.dag) f reIx spine
        (mkEmptyCache (Prep.ofDag ex.dag) limits ex reIx) =
      optimizeUniformIx w limits ex (Prep.ofDag ex.dag) f reIx spine := by
  have hchoose : uniformChooseStage limits ex (Prep.ofDag ex.dag)
      (uniformStageF w ex (Prep.ofDag ex.dag) f) =
      uniformChooseG w limits ex (Prep.ofDag ex.dag) f := by
    unfold uniformChooseStage uniformChooseG; rfl
  unfold optimizeUniformCached optimizeUniformIx
  dsimp only [Bind.bind, Except.bind]
  rw [uniformStageCached_eq_F, hchoose]
  cases spine with
  | error e => rfl
  | ok _ =>
    cases uniformChooseG w limits ex (Prep.ofDag ex.dag) f with
    | error e => rfl
    | ok c =>
      exact uniformFinishCached_eq_Ix w limits ex f reIx c

/-- `tieredAtWidthIx` reusing `EmptyCache` across Phase 1 and Phase 3. -/
def tieredAtWidthCached (layout : ShareLayout) (limits : Limits) (ex : Expanded) (w : Nat)
    (p : Prep) (f : GraphFacts) (reIx : ReIndex) (parents sp : Array (Array Nat))
    (spine : Except SharingError Unit) (k : Nat) (cache : EmptyCache) :
    Except SharingError TieredSharingResult := do
  let u ← optimizeUniformCached w limits ex p f reIx spine cache
  let a ← allocate layout limits ex.dag f.deg u.result.tableTerms u.result.sharing u.result.roots
  let phase1Layout := u.result.variableBytes
  let m ← rematerializeCached p reIx parents sp layout limits ex a.order phase1Layout cache
  return tieredResultF layout w u a m k phase1Layout

theorem tieredAtWidthCached_eq_Ix (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (w : Nat) (f : GraphFacts) (reIx : ReIndex) (parents sp : Array (Array Nat))
    (spine : Except SharingError Unit) (k : Nat)
    (hchecks : uniformDagChecks ex = .ok ()) :
    tieredAtWidthCached layout limits ex w (Prep.ofDag ex.dag) f reIx parents sp spine k
        (mkEmptyCache (Prep.ofDag ex.dag) limits ex reIx) =
      tieredAtWidthIx layout limits ex w (Prep.ofDag ex.dag) f reIx parents sp spine k := by
  unfold tieredAtWidthCached tieredAtWidthIx
  rw [optimizeUniformCached_eq_Ix]
  cases optimizeUniformIx w limits ex (Prep.ofDag ex.dag) f reIx spine with
  | error e => rfl
  | ok u =>
    dsimp only [Bind.bind, Except.bind]
    cases allocate layout limits ex.dag f.deg u.result.tableTerms u.result.sharing u.result.roots with
    | error e => rfl
    | ok a =>
      dsimp only []
      rw [rematerializeCached_eq_Ix layout limits ex reIx parents sp a.order
        u.result.variableBytes hchecks]

private theorem tieredAtWidth_eq_G (layout : ShareLayout) (limits : Limits) (ex : Expanded)
    (w : Nat) (p : Prep) (f : GraphFacts) (spine : Except SharingError Unit) (k : Nat)
    (hp : p = Prep.ofDag ex.dag) (hdag : AreaProof.DagOK ex.dag) :
    tieredAtWidthG layout limits ex w p f spine k = tieredAtWidthF layout limits ex w p f spine k := by
  unfold tieredAtWidthG tieredAtWidthF
  rw [optimizeUniform_eq_G w limits ex p f spine hp hdag]

/-- A computation after the DAG checks may assume the facts they give. -/
private theorem checks_bind {α : Type} (ex : Expanded) (g g' : Unit → Except SharingError α)
    (h : AreaProof.DagOK ex.dag → g () = g' ()) :
    (uniformDagChecks ex).bind g = (uniformDagChecks ex).bind g' := by
  cases hc : uniformDagChecks ex with
  | error e => rfl
  | ok u => cases u; exact h (dagOK_of_checks hc)

/-- `tieredAtWidth` with the width-independent tables computed once for its
three phases. -/
def tieredAtWidthC (layout : ShareLayout) (limits : Limits) (ex : Expanded) (w : Nat) :
    Except SharingError TieredSharingResult :=
  if w == 0 then throw (.formatBound "uniform Share width" 0)
  else
    (uniformDagChecks ex).bind fun _ =>
      let p := Prep.ofDag ex.dag
      let f := graphFacts ex.dag ex.roots
      let parents := parentEdgeLists ex.dag
      let reIx : ReIndex := { parents, leaves := leafIndex ex.dag }
      let sp := spineParentLists ex.dag p.family
      tieredAtWidthIx layout limits ex w p f reIx parents sp (uniformSpineCheck ex p)
        (tieredCandidateCount ex.dag.size p f)

@[csimp] theorem tieredAtWidth_eq_C : @tieredAtWidth = @tieredAtWidthC := by
  funext layout limits ex w
  unfold tieredAtWidthC
  split
  · rename_i hw
    unfold tieredAtWidth
    rw [optimizeUniformExpanded_eq_F]
    simp only [hw, ite_true]
    rfl
  · rename_i hw
    rw [tieredAtWidth_eq_F layout limits ex w (by simpa using hw)]
    exact checks_bind ex _ _ (fun hdag =>
      ((tieredAtWidthIx_eq_G layout limits ex w (Prep.ofDag ex.dag)
        (graphFacts ex.dag ex.roots) _ _).trans
        (tieredAtWidth_eq_G layout limits ex w _ _ _ _ rfl hdag)).symm)

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
tables and empty-dictionary cache computed once for the three candidates, and
the candidates of a large DAG computed in parallel. -/
def canonicalTieredCoreC (layout : ShareLayout) (limits : Limits) (dag : Dag)
    (roots : Array Nat) : Except SharingError TieredSharingResult :=
  let ex : Expanded := { dag, roots, visits := 0, internedNodes := 0 }
  (uniformDagChecks ex).bind fun _ =>
    let p := Prep.ofDag dag
    let f := graphFacts dag roots
    let parents := parentEdgeLists dag
    let reIx : ReIndex := { parents, leaves := leafIndex dag }
    let sp := spineParentLists dag p.family
    let spine := uniformSpineCheck ex p
    let k := tieredCandidateCount dag.size p f
    let cache := mkEmptyCache p limits ex reIx
    tieredCandidates dag.size fun w =>
      tieredAtWidthCached layout limits ex w p f reIx parents sp spine k cache

@[csimp] theorem canonicalTieredCore_eq_C : @canonicalTieredCore = @canonicalTieredCoreC := by
  funext layout limits dag roots
  unfold canonicalTieredCore canonicalTieredCoreC
  simp only [tieredAtWidth_eq_F _ _ _ 1 rfl, tieredAtWidth_eq_F _ _ _ 2 rfl,
    tieredAtWidth_eq_F _ _ _ 3 rfl, tieredCandidates_eq]
  cases hc : uniformDagChecks { dag, roots, visits := 0, internedNodes := 0 } with
  | error e => rfl
  | ok u =>
    have hdag := dagOK_of_checks hc
    have hRe : ({ parents := parentEdgeLists dag, leaves := leafIndex dag } : ReIndex) =
        ReIndex.ofDag dag := rfl
    have hCached : ∀ w, tieredAtWidthCached layout limits { dag, roots, visits := 0, internedNodes := 0 } w
        (Prep.ofDag dag) (graphFacts dag roots) (ReIndex.ofDag dag)
        (parentEdgeLists dag) (spineParentLists dag (Prep.ofDag dag).family)
        (uniformSpineCheck { dag, roots, visits := 0, internedNodes := 0 } (Prep.ofDag dag))
        (tieredCandidateCount dag.size (Prep.ofDag dag) (graphFacts dag roots))
        (mkEmptyCache (Prep.ofDag dag) limits { dag, roots, visits := 0, internedNodes := 0 }
          (ReIndex.ofDag dag)) =
        tieredAtWidthF layout limits { dag, roots, visits := 0, internedNodes := 0 } w
        (Prep.ofDag dag) (graphFacts dag roots)
        (uniformSpineCheck { dag, roots, visits := 0, internedNodes := 0 } (Prep.ofDag dag))
        (tieredCandidateCount dag.size (Prep.ofDag dag) (graphFacts dag roots)) :=
      fun w => (tieredAtWidthCached_eq_Ix layout limits
        { dag, roots, visits := 0, internedNodes := 0 } w (graphFacts dag roots)
        (ReIndex.ofDag dag) (parentEdgeLists dag)
        (spineParentLists dag (Prep.ofDag dag).family) _ _ hc).trans
        ((tieredAtWidthIx_eq_G layout limits { dag, roots, visits := 0, internedNodes := 0 }
          w (Prep.ofDag dag) (graphFacts dag roots) _ _).trans
          (tieredAtWidth_eq_G _ _ _ w _ _ _ _ rfl hdag))
    simp only [hRe, hCached]
    rfl

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
    let reIx : ReIndex := { parents := parentEdgeLists ex.dag, leaves := leafIndex ex.dag }
    optimizeUniformIx w limits ex p (graphFacts ex.dag ex.roots) reIx (uniformSpineCheck ex p)

@[csimp] theorem optimizeUniformExpanded_eq_C :
    @optimizeUniformExpanded = @optimizeUniformExpandedC := by
  funext w limits ex
  rw [optimizeUniformExpanded_eq_F w limits ex]
  unfold optimizeUniformExpandedC
  by_cases hw : (w == 0) = true
  · simp only [hw, ite_true]
  · simp only [hw, Bool.false_eq_true, ite_false]
    exact checks_bind ex _ _ (fun hdag => by
      have hRe : ({ parents := parentEdgeLists ex.dag, leaves := leafIndex ex.dag } : ReIndex) =
          ReIndex.ofDag ex.dag := rfl
      rw [hRe, optimizeUniformIx_eq_G]
      exact (optimizeUniform_eq_G w limits ex _ _ _ rfl hdag).symm)

end Ix.Sharing.Exact

end
