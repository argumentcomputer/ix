import Tests.Ix.SharingExact
import Ix.Sharing.FamilyContext

set_option compiler.extract_closed false

namespace Tests.SharingContext

open LSpec Ixon Ix.Sharing.Exact Ix.Sharing.Family Tests.SharingExact

deriving instance BEq for CompResult
deriving instance BEq for ExactSharingResult
deriving instance BEq for UniformSharingResult
deriving instance BEq for TieredStats
deriving instance BEq for TieredSharingResult

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def sameOutcome [BEq α] : Except SharingError α → Except SharingError α → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

/-- Keep the old native evaluator below the replaced entry: this call uses
the unchanged `familyAtWidthArea`, so csimp cannot turn both sides into the twin. -/
private def originalNormalize (cfg : Config) (constant : Constant) (limits : Limits) :
    Except SharingError (Constant × TieredSharingResult) := do
  let ex ← expand limits constant.sharing (constantInfoRoots constant.info) true
  uniformDagChecks ex
  let prep := Prep.ofDag ex.dag
  let facts := graphFacts ex.dag ex.roots
  let parents := parentsOf ex.dag
  let candidates := tieredCandidateCount ex.dag.size prep facts
  let result ← tieredCandidates ex.dag.size
    (familyAtWidthArea cfg .tagN limits ex prep facts parents candidates)
  let info ← withRoots constant.info result.result.roots
  return ({ constant with info, sharing := result.result.sharing }, withExpansionStats ex result)

private def normalizationControls : IO Nat := do
  let generated := runGen 1931 ((List.range 18).mapM fun _ => genRoots 6 6 4)
  let roots := #[#[], #[.var 20, .var 20], #[.var 1048, .var 1048]] ++ generated.toArray
  let mut tested := 0
  for (root, index) in roots.zipIdx do
    let constant := wrapRoots root index
    for cfg in [({ exactLimit := 0 } : Config), ⟨3⟩, canonicalFamilyConfig] do
      for limits in [({} : Limits), { maxStates := 0 }, { maxCostEvals := 0 },
          { maxOutputBytes := 0 }, { maxMaterializeWork := 0 }, { maxNodes := 0 },
          { maxExprVisits := 0 }, { maxDepth := 0 }, { maxKnapsackCells := 0 }] do
        let original := originalNormalize cfg constant limits
        let candidate := normalizeFamily cfg .tagN constant limits
        ensure (sameOutcome original candidate) "light context changed a result field, charge or refusal"
        match original, candidate with
        | .ok (before, _), .ok (after, _) =>
          ensure (serConstant before == serConstant after) "light context changed complete constant bytes"
        | _, _ => pure ()
        tested := tested + 1
    let canonical := normalizeConstantSharingTiered .tagN constant
    let report := (normalizeFamily canonicalFamilyConfig .tagN constant).map (·.1)
    ensure (sameOutcome canonical report) "canonical and parameterized context entries disagree"
    let malformed := { constant with sharing := #[.share 0] }
    ensure (sameOutcome (originalNormalize canonicalFamilyConfig malformed {})
      (normalizeFamily canonicalFamilyConfig .tagN malformed)) "backward-sharing refusal changed"
  return tested

/-- These altered contexts test defensive branches and internal counters;
they are not claims that the corresponding values are admitted artifacts. -/
private def componentControls : IO Nat := do
  let shared : Expr := .app (.var 20) (.var 1048)
  let roots : Array Expr := #[.app shared (.var 2), .app shared (.var 3), .var 20]
  let ex ← IO.ofExcept ((expand {} #[] roots false).mapError toString)
  let prep := Prep.ofDag ex.dag
  let facts := graphFacts ex.dag ex.roots
  let parents := parentsOf ex.dag
  let zeroArea := Array.replicate prep.dag.size 0
  let zeroClosure := Array.replicate ex.dag.size 0
  let mut tested := 0
  let mut eligible := 0
  let mut longerClosure := 0
  for width in #[1, 2, 3] do
    let stage := uniformStageF width ex prep facts
    let base := TBase.ofPrep stage.up.prep stage.up.w stage.up.opaq
    for members in stage.comps do
      let area := componentArea stage.up stage.f members
      let positions := setPositions zeroArea area
      let (marks, found, stack) := upWalk parents members zeroClosure
      if members.all (fun m => decide (m < ex.dag.size) && !stage.up.opaq[m]!) &&
          areaOK ex.dag.size stage.up.opaq parents members area positions &&
          stack.isEmpty && area.all (fun y => marks[y]! != 0) &&
          localSearchOK (LightContext.context stage members area) then
        eligible := eligible + 1
        if found.size > area.size then longerClosure := longerClosure + 1
      let shortCandidates := { stage with cand := #[] }
      let opaqueMembers :=
        { stage with up := { stage.up with opaq := Array.replicate prep.dag.size true } }
      let charged := familyWork canonicalFamilyConfig members.size found.size
      let configurations : Array (Limits × MeterState) :=
        #[({}, (#[], 0, 0)), ({ maxStates := 0 }, (#[], 0, 0)),
          ({ maxCostEvals := 0 }, (#[], 0, 0)), ({}, (#[default], 7, 11)),
          ({ maxCostEvals := charged - 1 }, (#[], 0, 0)),
          ({ maxCostEvals := charged }, (#[], 0, 0)),
          ({ maxStates := 2 ^ 100, maxCostEvals := 2 ^ 100 }, (#[], 2 ^ 80, 2 ^ 80))]
      for contextStage in #[stage, shortCandidates, opaqueMembers] do
        for (limits, initial) in configurations do
          let original := familyStepArea canonicalFamilyConfig limits ex contextStage width parents base
            (initial, zeroArea, zeroClosure) members
          let candidate := LightContext.step canonicalFamilyConfig limits ex contextStage width parents base
            (initial, zeroArea, zeroClosure) members
          ensure (sameOutcome original candidate) "context fallback changed counters or cleared buffers"
          tested := tested + 1
      let full := LightContext.fullContext ex stage members
      let cached := Thunk.mk fun _ => LightContext.fullContext ex stage members
      let light := LightContext.context stage members #[]
      let zeroInline := { base with inl := Array.replicate ex.dag.size 0 }
      let aux : AAux := { csize := full.1.closure.size, K := 0, rootsA := #[], storedA := #[0] }
      for stored in #[#[], members] do
        let expected := phiEL2 full.1 zeroArea full.2 (fun _ => false) stored
        let actual := phiA light zeroArea zeroInline aux (LightContext.forceContext cached)
          (fun _ => false) stored
        ensure (actual == expected) "memoized opacity fallback changed the complete cost/work pair"
        tested := tested + 1
  ensure (eligible > 0) "context controls did not reach the checked area path"
  ensure (longerClosure > 0) "context controls did not distinguish closure work from area work"
  return tested

def suite : List TestSeq := [
  .individualIO "checked light context preserves full results and exact refusals" none (do
    let normalized ← normalizationControls
    let components ← componentControls
    return (true, normalized + components, 0, none)) .done]

end Tests.SharingContext
