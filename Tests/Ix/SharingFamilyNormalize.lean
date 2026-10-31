import Tests.Ix.SharingUniform
import Ix.Sharing.FamilyNormalizeArea

namespace Tests.SharingFamilyNormalize

open LSpec Ixon Ix.Sharing.Exact Ix.Sharing.Family Tests.SharingExact

private def ensure (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

/-- Keep a native closure-evaluator reference: `familyAtWidth` has no csimp
replacement. Calling the public reference entry here would run the new twin. -/
private def closureNormalize (cfg : Config) (constant : Constant) (limits : Limits) :
    Except SharingError (Constant × TieredSharingResult) := do
  let ex ← expand limits constant.sharing (constantInfoRoots constant.info) true
  uniformDagChecks ex
  let prep := Prep.ofDag ex.dag
  let facts := graphFacts ex.dag ex.roots
  let parents := parentsOf ex.dag
  let candidates := tieredCandidateCount ex.dag.size prep facts
  let result ← tieredCandidates ex.dag.size (familyAtWidth cfg .tagN limits ex prep facts parents candidates)
  let info ← withRoots constant.info result.result.roots
  return ({ constant with info, sharing := result.result.sharing }, withExpansionStats ex result)

private def outcomeImage (outcome : Except SharingError (Constant × TieredSharingResult)) :=
  outcome.map fun (constant, report) =>
    (serConstant constant, report.phase1.statesVisited, report.phase1.result.stats.costEvals)

private def sameOutcome [BEq α] (a b : Except SharingError α) : Bool :=
  match a, b with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def budgetControls : IO Unit := do
  -- Independent small enumerations of calls and the actual phiE work field.
  for m in [0:9] do
    for k in [0, m, m + 1] do
      for closure in [0, 3, 7] do
        let mut calls := 0
        let mut work := closure -- empty baseline
        if m ≤ k then
          for mask in [0:2 ^ m] do
            let size := ((List.range m).filter mask.testBit).length
            calls := calls + 1
            work := work + closure + size
        else
          for q in [1:m + 1] do
            for _ in [0:m - q + 1] do
              calls := calls + 1
              work := work + closure + q
          for q in [0:m + 1] do
            calls := calls + 1
            work := work + closure + q
        ensure (familyCalls ⟨k⟩ m == calls && familyWork ⟨k⟩ m closure == work)
          "precharged mathematical calls/work differ from independent enumeration"
  let witness := wrapRoots #[.var 20, .var 20] 0
  for limits in [({ maxStates := 0 } : Limits), { maxCostEvals := 0 }, { maxOutputBytes := 0 }] do
    ensure (sameOutcome (outcomeImage (normalizeFamily ⟨16⟩ .tagN witness limits))
      (outcomeImage (closureNormalize ⟨16⟩ witness limits))) "area and closure refused differently"
  ensure (isErr (normalizeFamily ⟨12⟩ .tagN witness { maxStates := 0 })
    (· == .resourceExhausted .states 0)) "family state budget did not refuse"
  ensure (isErr (normalizeFamily ⟨12⟩ .tagN witness { maxCostEvals := 0 })
    (· == .resourceExhausted .costEvals 0)) "family phi-work budget did not refuse"
  ensure (isErr (normalizeFamily ⟨12⟩ .tagN witness { maxOutputBytes := 0 })
    (· == .resourceExhausted .outputBytes 0)) "output budget did not refuse"
  ensure (isErr (normalizeFamily ⟨12⟩ .tagN { witness with sharing := #[.share 0] }) (fun _ => true))
    "malformed backward-sharing input was accepted"

private def normalizationControls : IO Nat := do
  let samples := runGen 811 ((List.range 36).mapM fun _ => genRoots 5 6 4)
  let mut tested := 0
  for (roots, index) in samples.zipIdx do
    let constant := wrapRoots roots index
    let before ← IO.ofExcept ((expand {} constant.sharing roots true).mapError toString)
    let exact ← IO.ofExcept ((Reference.normalizeConstantSharingTiered .tagN constant).mapError toString)
    let alternate ← IO.ofExcept ((normalizeConstantSharingUniform 1 constant).mapError toString)
    for k in [0, 3, 24] do
      let (candidate, report) ← IO.ofExcept ((normalizeFamily ⟨k⟩ .tagN constant).mapError toString)
      let reference ← IO.ofExcept ((closureNormalize ⟨k⟩ constant {}).mapError toString)
      ensure (sameOutcome (outcomeImage (.ok (candidate, report))) (outcomeImage (.ok reference)))
        "area normalization changed complete serialized bytes or mathematical charges"
      let after ← IO.ofExcept ((expand {} candidate.sharing (constantInfoRoots candidate.info) true).mapError toString)
      ensure (after.dag.nodes == before.dag.nodes && after.roots == before.roots)
        "family normalization changed the expanded terms"
      ensure (candidate.refs == constant.refs && candidate.univs == constant.univs &&
        (withRoots candidate.info roots).toOption == some constant.info)
        "family normalization changed fixed fields or source tables"
      ensure (report.result.variableBytes == tag0Size candidate.sharing.size +
        exprsSize candidate.sharing + exprsSize (constantInfoRoots candidate.info))
        "family output disagrees with serialized variable bytes"
      if k == 24 then
        ensure (serConstant candidate == serConstant exact) "all-exact bytes differ from the existing optimizer"
      let (again, _) ← IO.ofExcept ((normalizeFamily ⟨k⟩ .tagN candidate).mapError toString)
      ensure (serConstant again == serConstant candidate) "family normalization is not representation-stable"
      let (alternateResult, _) ← IO.ofExcept ((normalizeFamily ⟨k⟩ .tagN alternate).mapError toString)
      ensure (serConstant alternateResult == serConstant candidate)
        "another valid sharing representation changed the family output"
      tested := tested + 1
  let projection := wrapRoots #[] 0
  let (same, _) ← IO.ofExcept ((normalizeFamily ⟨0⟩ .tagN projection).mapError toString)
  ensure (serConstant same == serConstant projection) "empty-root projection changed"
  IO.println s!"family normalizer: {tested} whole constants; fixed fields, expansion, all-exact bytes and idempotence"
  return tested

def suite : List TestSeq := [
  .individualIO "family normalizer preserves bytes and checked failures" none (do
    budgetControls
    let tested ← normalizationControls
    return (true, tested, 0, none)) .done]

end Tests.SharingFamilyNormalize
