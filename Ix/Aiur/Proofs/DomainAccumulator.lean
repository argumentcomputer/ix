/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Selectors
import Ix.Aiur.Proofs.LogUpAccumulator

/-! Actual domain normalization discharges the scaled boundary injection.
Every checked group in every cyclic trace row contributes to the circuit's
lookup fraction sum, provided the compressed base-field messages avoid poles.
-/

namespace Aiur.NativeAIR.LogUp

open ProofCodec (Extension)

theorem normalized_injection (domain : Domain.Subgroup) (index : Fin (Domain.size domain))
    (delta : Coordinates G) :
    (delta.scale (Domain.normalizer domain).inverse).scale
      (Domain.Algebra.dividedPowers (Domain.point domain index) (Domain.lastPoint domain) (Domain.size domain)) =
      if index.val = Domain.size domain - 1 then delta else 0 := by
  rw [Domain.last_at_row]
  have cancel : (Domain.normalizer domain).inverse * Domain.normalizer domain = 1 := by
    rw [G.mul_comm]
    exact G.mul_inverse_cancel _ (Domain.normalizer_nonzero domain)
  by_cases last : index.val = Domain.size domain - 1
  · simp only [if_pos last]
    apply Coordinates.ext <;> simp only [Coordinates.scale] <;> rw [G.mul_assoc, cancel, G.mul_one]
  · simp only [if_neg last]
    apply Coordinates.ext <;> simp only [Coordinates.scale, G.mul_zero] <;> rfl

theorem equations_domain_row (domain : Domain.Subgroup) (index : Fin (Domain.size domain))
    {lookups : List (G × List G)} {stageCurrent stageNext publics deltaScaled : Array G}
    {groupSize : Nat} {result : List (Coordinates G)} {beta gamma delta : Coordinates G}
    (betaRead : Coordinates.read publics 0 = some beta) (gammaRead : Coordinates.read publics 1 = some gamma)
    (deltaRead : Coordinates.read deltaScaled 0 = some (delta.scale (Domain.normalizer domain).inverse))
    (accepted : equations lookups stageCurrent stageNext publics deltaScaled
      (Domain.Algebra.dividedPowers (Domain.point domain index) (Domain.lastPoint domain) (Domain.size domain))
      groupSize = some result)
    (zero : ∀ value ∈ result, value = 0)
    (free : PoleFree (fieldEntries (compress beta gamma lookups))) :
    ∃ first next, Coordinates.read stageCurrent 0 = some first ∧
      Coordinates.read stageNext 0 = some next ∧
      next.toExtension - first.toExtension +
        (if index.val = Domain.size domain - 1 then delta.toExtension else 0) =
          lookupFractions beta gamma lookups := by
  obtain ⟨first, next, scaled, hf, hn, hd, equation⟩ := equations_accumulator betaRead gammaRead accepted zero free
  have same := Option.some.inj (hd.symm.trans deltaRead)
  subst scaled
  rw [normalized_injection] at equation
  refine ⟨first, next, hf, hn, ?_⟩
  by_cases last : index.val = Domain.size domain - 1
  · simpa only [if_pos last] using equation
  · have zeroEmbed : (0 : Coordinates G).toExtension = 0 := (Coordinates.toExtension_zero_iff _).mpr rfl
    simpa only [if_neg last, zeroEmbed] using equation

theorem equations_domain_sum (domain : Domain.Subgroup)
    (lookups : Fin (Domain.size domain) → List (G × List G))
    (stageRows : Fin (Domain.size domain) → Array G) (publics deltaScaled : Array G)
    (groupSize : Nat) (beta gamma delta : Coordinates G)
    (betaRead : Coordinates.read publics 0 = some beta) (gammaRead : Coordinates.read publics 1 = some gamma)
    (deltaRead : Coordinates.read deltaScaled 0 = some (delta.scale (Domain.normalizer domain).inverse))
    (rows : ∀ index : Fin (Domain.size domain), ∃ result,
      equations (lookups index) (stageRows index)
        (stageRows ⟨(index.val + 1) % Domain.size domain, Nat.mod_lt _ (Domain.size_positive domain)⟩)
        publics deltaScaled
        (Domain.Algebra.dividedPowers (Domain.point domain index) (Domain.lastPoint domain) (Domain.size domain))
        groupSize = some result ∧ (∀ value ∈ result, value = 0))
    (free : ∀ index, PoleFree (fieldEntries (compress beta gamma (lookups index)))) :
    sum (List.ofFn fun index => lookupFractions beta gamma (lookups index)) = delta.toExtension := by
  let rowIndex := fun index => (⟨index % Domain.size domain, Nat.mod_lt _ (Domain.size_positive domain)⟩ :
    Fin (Domain.size domain))
  let states := fun index => ((Coordinates.read (stageRows (rowIndex index)) 0).getD 0).toExtension
  let fractions := fun index => lookupFractions beta gamma (lookups (rowIndex index))
  have wrap : states (Domain.size domain) = states 0 := by
    simp only [states, rowIndex, Nat.mod_self, Nat.zero_mod]
  have steps : ∀ index, index < Domain.size domain →
      states (index + 1) - states index +
        (if index + 1 = Domain.size domain then delta.toExtension else 0) = fractions index := by
    intro index bound
    let i : Fin (Domain.size domain) := ⟨index, bound⟩
    obtain ⟨result, accepted, zero⟩ := rows i
    obtain ⟨first, next, hf, hn, equation⟩ :=
      equations_domain_row domain i betaRead gammaRead deltaRead accepted zero (free i)
    dsimp only [i] at hf hn
    have source : states index = first.toExtension := by
      simp only [states, rowIndex, Nat.mod_eq_of_lt bound, hf, Option.getD_some]
    have target : states (index + 1) = next.toExtension := by
      simp only [states, rowIndex, hn, Option.getD_some]
    have fraction : fractions index = lookupFractions beta gamma (lookups i) := by
      simp only [fractions, rowIndex, Nat.mod_eq_of_lt bound, i]
    rw [source, target, fraction]
    have condition : (i.val = Domain.size domain - 1) ↔ (index + 1 = Domain.size domain) := by
      have := Domain.size_positive domain
      simp only [i]
      omega
    simpa only [condition] using equation
  have total := cyclic_accumulator states fractions (Domain.size domain) delta.toExtension
    (Domain.size_positive domain) wrap steps
  have enumeration : (List.range (Domain.size domain)).map fractions =
      List.ofFn (fun index => lookupFractions beta gamma (lookups index)) := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_ofFn]
    · intro index left right
      have bound : index < Domain.size domain := by simpa only [List.length_ofFn] using right
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
        fractions, rowIndex, Nat.mod_eq_of_lt bound]
  rwa [enumeration] at total

theorem constraintValues_domain_sum (domain : Domain.Subgroup) (lookups : List Lookup)
    (nodeRows stageRows : Fin (Domain.size domain) → Array G) (publics deltaScaled : Array G)
    (groupSize : Nat) (beta gamma delta : Coordinates G)
    (betaRead : Coordinates.read publics 0 = some beta) (gammaRead : Coordinates.read publics 1 = some gamma)
    (deltaRead : Coordinates.read deltaScaled 0 = some (delta.scale (Domain.normalizer domain).inverse))
    (rows : ∀ index : Fin (Domain.size domain), ∃ result,
      constraintValues lookups (nodeRows index) (stageRows index)
        (stageRows ⟨(index.val + 1) % Domain.size domain, Nat.mod_lt _ (Domain.size_positive domain)⟩)
        publics deltaScaled
        (Domain.Algebra.dividedPowers (Domain.point domain index) (Domain.lastPoint domain) (Domain.size domain))
        groupSize = some result ∧ (∀ value ∈ result, value = 0))
    (free : ∀ index values, lookups.mapM (readLookup (nodeRows index)) = some values →
      PoleFree (fieldEntries (compress beta gamma values))) :
    ∃ values : Fin (Domain.size domain) → List (G × List G),
      (∀ index, lookups.mapM (readLookup (nodeRows index)) = some (values index)) ∧
      sum (List.ofFn fun index => lookupFractions beta gamma (values index)) = delta.toExtension := by
  let values := fun index => (lookups.mapM (readLookup (nodeRows index))).getD []
  have reads : ∀ index, lookups.mapM (readLookup (nodeRows index)) = some (values index) := by
    intro index
    obtain ⟨result, accepted, _⟩ := rows index
    obtain ⟨readValues, _, read, _, _⟩ := constraintValues_success accepted
    simp only [values, read, Option.getD_some]
  refine ⟨values, reads, equations_domain_sum domain values stageRows publics deltaScaled groupSize
    beta gamma delta betaRead gammaRead deltaRead ?_ (fun index => free index (values index) (reads index))⟩
  intro index
  obtain ⟨result, accepted, zero⟩ := rows index
  obtain ⟨readValues, coordinates, read, equations, rfl⟩ := constraintValues_success accepted
  have same := Option.some.inj (read.symm.trans (reads index))
  subst readValues
  exact ⟨coordinates, equations, (Coordinates.flatten_zero_iff coordinates).mp zero⟩

end Aiur.NativeAIR.LogUp
