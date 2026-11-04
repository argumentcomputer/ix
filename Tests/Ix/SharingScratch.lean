import Ix.Sharing.FamilyContext

/-! A sharing fixture whose small uncertain components stay fixed while an
unrelated balanced subtree increases the full-DAG scratch-buffer size. -/

namespace Tests.SharingScratch

open Ix.Sharing.Exact Ix.Sharing.Family

private def balanced : Nat → Nat → Ixon.Expr
  | 0, start => .var (1000000 + start).toUInt64
  | depth + 1, start => .app (balanced depth start) (balanced depth (start + 2 ^ depth))

private def pack : Nat → Array Ixon.Expr → Ixon.Expr
  | 0, _ => .sort 0
  | fuel + 1, expressions =>
    if expressions.isEmpty then .sort 0
    else if expressions.size == 1 then expressions[0]!
    else
      let middle := expressions.size / 2
      .app (pack fuel (expressions.extract 0 middle))
        (pack fuel (expressions.extract middle expressions.size))

/-- Each prefix chain supplies twelve uncertain members at width three.
The extra subtree contains distinct variables, so increasing its depth adds
DAG nodes without adding uncertain members or changing their areas. -/
def roots (copies paddingDepth : Nat) : Array Ixon.Expr := Id.run do
  let mut expressions := #[]
  for copy in [:copies] do
    let mut chain : Ixon.Expr := .var (100 + copy).toUInt64
    for argument in [:12] do
      chain := .app chain (.var (argument % 5).toUInt64)
      expressions := expressions.push (.app chain (.sort 1))
    expressions := expressions.push chain
  return #[.app (pack expressions.size expressions) (balanced paddingDepth 0)]

structure Prepared where
  expanded : Expanded
  stage : UStage
  parents : Array (Array Nat)
  base : TBase

def prepare (copies paddingDepth : Nat) : Except SharingError Prepared := do
  let expanded ← expand {} #[] (roots copies paddingDepth) false
  let prep := Prep.ofDag expanded.dag
  let stage := uniformStageF 3 expanded prep (graphFacts expanded.dag expanded.roots)
  return ⟨expanded, stage, parentsOf expanded.dag,
    TBase.ofPrep stage.up.prep stage.up.w stage.up.opaq⟩

/-- Run the production component steps after common graph/base preparation.
Distinct position buffers avoid an incidental first-step alias from CSE. -/
def Prepared.run (prepared : Prepared) (cfg : Config := ⟨16⟩) (limits : Limits := {}) :
    Except SharingError MeterState :=
  let ex := prepared.expanded
  let initial : FamilyState := ((#[], 0, 0), Array.replicate ex.dag.size 0,
    (Array.replicate (ex.dag.size + 1) 0).pop)
  (prepared.stage.comps.foldlM
    (LightContext.step cfg limits ex prepared.stage 3 prepared.parents prepared.base) initial).map (·.1)

def Prepared.parallelComponents (prepared : Prepared) (cfg : Config := ⟨16⟩) : Nat :=
  prepared.stage.comps.foldl (fun count members =>
    let area := componentArea prepared.stage.up prepared.stage.f members
    if Parallel.areaParallel cfg prepared.expanded.dag.size area.size members.size then count + 1
    else count) 0

end Tests.SharingScratch
