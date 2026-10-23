import Tests.Ix.SharingUniform
import Ix.Sharing.FamilyNormalize

namespace Tests.SharingFamilyNormalize

open LSpec Ixon Ix.Sharing.Exact Ix.Sharing.FamilyPrototype Tests.SharingExact

private def ensure (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

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
      let after ← IO.ofExcept ((expand {} candidate.sharing (constantInfoRoots candidate.info) true).mapError toString)
      ensure (after.dag.nodes == before.dag.nodes && after.roots == before.roots)
        "experimental normalization changed the expanded terms"
      ensure (candidate.refs == constant.refs && candidate.univs == constant.univs &&
        (withRoots candidate.info roots).toOption == some constant.info)
        "experimental normalization changed fixed fields or source tables"
      ensure (report.result.variableBytes == tag0Size candidate.sharing.size +
        exprsSize candidate.sharing + exprsSize (constantInfoRoots candidate.info))
        "experimental output disagrees with serialized variable bytes"
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
  .individualIO "experimental family normalizer preserves bytes and checked failures" none (do
    budgetControls
    let tested ← normalizationControls
    return (true, tested, 0, none)) .done]

end Tests.SharingFamilyNormalize
