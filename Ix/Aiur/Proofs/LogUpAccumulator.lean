/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LogUpFractions

/-! A complete row's checked grouped equations imply the sum-of-fractions
accumulator identity when its base-field messages avoid poles. The proof
telescopes every group, including the empty pass-through case, and retains
the caller's scaled last-row injection. -/

namespace Aiur.NativeAIR.LogUp

open ProofCodec (Extension)

def lookupFractions (beta gamma : Coordinates G) (lookups : List (G × List G)) : Extension :=
  fractionSum (fieldEntries (compress beta gamma lookups))

theorem fractionSum_flatMap (inputs : List α) (entries : α → List (Extension × Extension)) :
    fractionSum (inputs.flatMap entries) = sum (inputs.map fun input => fractionSum (entries input)) := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
    simp only [List.flatMap_cons, fractionSum_append, List.map_cons, sum, List.foldr_cons] at *
    rw [ih]

theorem fieldEntries_compress_chunk (beta gamma : Coordinates G) (lookups : List (G × List G))
    (groupSize index : Nat) :
    fieldEntries (compress beta gamma (chunk groupSize index lookups)) =
      chunk groupSize index (fieldEntries (compress beta gamma lookups)) := by
  simp only [fieldEntries, compress, chunk_map]

theorem lookupFractions_chunks (beta gamma : Coordinates G) (lookups : List (G × List G)) (groupSize : Nat) :
    sum ((List.range (groupCount groupSize lookups.length)).map
      (fun index => lookupFractions beta gamma (chunk groupSize index lookups))) = lookupFractions beta gamma lookups := by
  simp only [lookupFractions, fieldEntries_compress_chunk]
  rw [← fractionSum_flatMap]
  have length : (fieldEntries (compress beta gamma lookups)).length = lookups.length := by
    simp only [fieldEntries, compress, List.length_map]
  rw [← length, chunks_cover]

theorem equations_accumulator {lookups : List (G × List G)} {stageCurrent stageNext publics deltaScaled : Array G}
    {isLast : G} {groupSize : Nat} {result : List (Coordinates G)}
    {beta gamma : Coordinates G}
    (betaRead : Coordinates.read publics 0 = some beta) (gammaRead : Coordinates.read publics 1 = some gamma)
    (accepted : equations lookups stageCurrent stageNext publics deltaScaled isLast groupSize = some result)
    (zero : ∀ value ∈ result, value = 0)
    (free : PoleFree (fieldEntries (compress beta gamma lookups))) :
    ∃ first next delta, Coordinates.read stageCurrent 0 = some first ∧
      Coordinates.read stageNext 0 = some next ∧ Coordinates.read deltaScaled 0 = some delta ∧
      next.toExtension - first.toExtension + (delta.scale isLast).toExtension = lookupFractions beta gamma lookups := by
  obtain ⟨readBeta, readGamma, delta, next, hb, hg, hd, hn, groups⟩ := equations_zero accepted zero
  have sameBeta := Option.some.inj (hb.symm.trans betaRead)
  have sameGamma := Option.some.inj (hg.symm.trans gammaRead)
  subst readBeta
  subst readGamma
  let count := groupCount groupSize lookups.length
  let injection := delta.scale isLast
  let states := fun index => if index < count then
    ((Coordinates.read stageCurrent index).getD 0).toExtension else (next + injection).toExtension
  let increments := fun index => lookupFractions beta gamma (chunk groupSize index lookups)
  have steps : ∀ index, index < count → states (index + 1) - states index = increments index := by
    intro index bound
    obtain ⟨source, target, hs, ht, equation⟩ := groups index bound
    have localFree : PoleFree (fieldEntries (compress beta gamma (chunk groupSize index lookups))) := by
      rw [fieldEntries_compress_chunk]
      exact fun entry member => free entry (chunk_mem member)
    have fraction := (coordinate_polynomial_zero_iff _ _ localFree).mp equation
    rw [Coordinates.toExtension_sub] at fraction
    have sourceRead : states index = source.toExtension := by
      simp only [states, if_pos bound, hs, Option.getD_some]
    have targetRead : states (index + 1) = target.toExtension := by
      by_cases interior : index + 1 < count
      · rw [if_pos interior] at ht
        simp only [states, if_pos interior, ht, Option.getD_some]
      · rw [if_neg interior] at ht
        have same := Option.some.inj ht
        simp only [states, if_neg interior, injection, same]
    rw [sourceRead, targetRead]
    exact fraction
  have telescoped := telescope states increments count steps
  rw [lookupFractions_chunks] at telescoped
  obtain ⟨first, _, hf, _, _⟩ := groups 0 (groupCount_positive _ _)
  have positive : 0 < count := groupCount_positive _ _
  have firstState : states 0 = first.toExtension := by
    simp only [states, if_pos positive, hf, Option.getD_some]
  have finalState : states count = next.toExtension + injection.toExtension := by
    simp only [states, Nat.lt_irrefl, ↓reduceIte, Coordinates.toExtension_add]
  rw [firstState, finalState] at telescoped
  exact ⟨first, next, delta, hf, hn, hd, by change _ + injection.toExtension = _; grind⟩

theorem constraintValues_accumulator {lookups : List Lookup} {nodeValues stageCurrent stageNext publics deltaScaled : Array G}
    {isLast : G} {groupSize : Nat} {result : List G} {beta gamma : Coordinates G}
    (betaRead : Coordinates.read publics 0 = some beta) (gammaRead : Coordinates.read publics 1 = some gamma)
    (accepted : constraintValues lookups nodeValues stageCurrent stageNext publics deltaScaled isLast groupSize = some result)
    (zero : ∀ value ∈ result, value = 0)
    (free : ∀ values, lookups.mapM (readLookup nodeValues) = some values →
      PoleFree (fieldEntries (compress beta gamma values))) :
    ∃ values first next delta, lookups.mapM (readLookup nodeValues) = some values ∧
      Coordinates.read stageCurrent 0 = some first ∧ Coordinates.read stageNext 0 = some next ∧
      Coordinates.read deltaScaled 0 = some delta ∧
      next.toExtension - first.toExtension + (delta.scale isLast).toExtension = lookupFractions beta gamma values := by
  obtain ⟨values, coordinates, hv, hc, rfl⟩ := constraintValues_success accepted
  have vanishes := (Coordinates.flatten_zero_iff coordinates).mp zero
  obtain ⟨first, next, delta, hf, hn, hd, equation⟩ := equations_accumulator betaRead gammaRead hc vanishes (free values hv)
  exact ⟨values, first, next, delta, hv, hf, hn, hd, equation⟩

end Aiur.NativeAIR.LogUp
