module

public import Ix.Sharing.Exact
import all Ix.Sharing.FamilyContext
import all Ix.Sharing.Exact.Search
import all Ix.Sharing.Exact.TieredFast

/-! Isolated staged canonical construction. No compiler replacement selects
this module. The final-length planner and the sufficient-budget guard must
be related to the existing materializer before production use. Tight budgets
and unsupported orders run the original materializer in candidate order. -/

public section

namespace Ix.Sharing.Deferred

open Ix.Sharing.Exact Ix.Sharing.Family

/-- A decidable version of the existing materializer's wire-domain premise. -/
def wireReady (expanded : Expanded) : Bool :=
  expanded.dag.size < UInt64.size && expanded.dag.nodes.all fun node =>
    match node.head with
    | .ref _ universes | .recur _ universes => universes.size < UInt64.size
    | _ => true

/-- Conservative sufficient room from `Totality.rematerialize_within`.
A failed guard is a fallback condition, never a new refusal. -/
def budgetCovered (nodes phase1Bytes : Nat) (limits : Limits) : Bool :=
  phase1Bytes ≤ limits.maxMaterialize &&
    (nodes + 1) * (nodes * (nodes + 1)) + phase1Bytes ≤ limits.maxMaterializeWork &&
    2 * phase1Bytes ≤ limits.maxExprVisits &&
    2 * phase1Bytes ≤ limits.maxDepth &&
    nodes + 2 * phase1Bytes ≤ limits.maxNodes

/-- Price a descendant-closed table from one whole-dictionary evaluation.
This does not build expressions or walk ancestors to count materialization
work. The guard above proves room using a conservative work bound instead. -/
def finalLength? (prep : Prep) (layout : ShareLayout) (table roots : Array Nat) : Option Nat := do
  if table.size ≥ wordBound || !table.all (· < prep.dag.size) then none
  else
    let index := indexOfPrefix prep.dag.size table table.size
    if !onePassOrder prep.dag table roots index then none
    else
      let width := index.map (·.map layout.widthAt)
      let evaluation := prep.evalAll width
      let allTrue := Array.replicate prep.dag.size true
      let entries := table.foldl (fun total term => total +
        evalHidden prep.dag prep.family prep.spineLen prep.tail width allTrue evaluation term) 0
      some (tag0Size table.size + entries + rootsCost evaluation.cost roots)

structure Candidate where
  width : Nat
  uniform : UniformSharingResult
  allocation : Allocation
  phase1Bytes : Nat
  predicted : Nat
  materialized : Option Rematerialized
  deriving Inhabited

def prepareCandidate (config : Config) (layout : ShareLayout) (limits : Limits)
    (expanded : Expanded) (prep : Prep) (facts : GraphFacts) (parents : Array (Array Nat))
    (wire : Bool) (width : Nat) : Except SharingError Candidate := do
  let uniform ← LightContext.uniform config limits expanded prep facts parents width
  let allocation ← allocate layout limits expanded.dag facts.deg uniform.result.tableTerms
    uniform.result.sharing uniform.result.roots
  let phase1Bytes := layoutBytes layout uniform.result.sharing uniform.result.roots
  if wire && budgetCovered expanded.dag.size phase1Bytes limits then
    if let some predicted := finalLength? prep layout allocation.order expanded.roots then
      if predicted ≤ phase1Bytes then
        return { width, uniform, allocation, phase1Bytes, predicted, materialized := none }
  let materialized ← rematerializeP prep layout limits expanded allocation.order phase1Bytes
  return { width, uniform, allocation, phase1Bytes, predicted := materialized.bytes,
    materialized := some materialized }

def better (a b : Candidate) : Bool :=
  a.predicted < b.predicted || (a.predicted == b.predicted &&
    (a.width < b.width || (a.width == b.width && setPrec a.uniform.stored b.uniform.stored)))

def prepareCandidates (nodes : Nat) (run : Nat → Except SharingError Candidate) :
    Except SharingError (Candidate × Candidate × Candidate) :=
  if nodes < tieredParMin then do
    let first ← run 1
    let second ← run 2
    let third ← run 3
    return (first, second, third)
  else
    let tasks := #[1, 2, 3].map fun width => Task.spawn fun _ => run width
    do
      let first ← tasks[0]!.get
      let second ← tasks[1]!.get
      let third ← tasks[2]!.get
      return (first, second, third)

def finish (layout : ShareLayout) (limits : Limits) (expanded : Expanded) (prep : Prep)
    (count : Nat) (first second third : Candidate) : Except SharingError TieredSharingResult := do
  let selected := #[second, third].foldl (fun best next => if better next best then next else best) first
  let materialized ← match selected.materialized with
    | some value => pure value
    | none => rematerializeP prep layout limits expanded selected.allocation.order selected.phase1Bytes
  let result := tieredResultF layout selected.width selected.uniform selected.allocation
    materialized count selected.phase1Bytes
  return { result with stats := { result.stats with
    candidateLengths := #[(first.width, first.predicted), (second.width, second.predicted),
      (third.width, third.predicted)] } }

private def expanded (config : Config) (layout : ShareLayout) (limits : Limits)
    (input : Expanded) : Except SharingError TieredSharingResult := do
  uniformDagChecks input
  let prep := Prep.ofDag input.dag
  let facts := graphFacts input.dag input.roots
  let parents := parentsOf input.dag
  let count := tieredCandidateCount input.dag.size prep facts
  let (first, second, third) ← prepareCandidates input.dag.size
    (prepareCandidate config layout limits input prep facts parents (wireReady input))
  let result ← finish layout limits input prep count first second third
  return withExpansionStats input result

/-- Start from the ordinary checked expansion so the internal candidate path
receives the canonical DAG. No arbitrary external Expanded value enters it. -/
def normalize (layout : ShareLayout) (constant : Ixon.Constant) (limits : Limits := {}) :
    Except SharingError (Ixon.Constant × TieredSharingResult) := do
  let input ← expand limits constant.sharing (constantInfoRoots constant.info) true
  let result ← expanded canonicalFamilyConfig layout limits input
  let info ← withRoots constant.info result.result.roots
  return ({ constant with info, sharing := result.result.sharing }, result)

end Ix.Sharing.Deferred
