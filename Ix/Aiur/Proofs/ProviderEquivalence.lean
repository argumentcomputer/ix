/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitRowCounts
import Ix.Aiur.Proofs.CircuitPoolExecution

/-! Provider replacement preserves padded balance when multiplicities and
nonzero messages agree. A satisfying nonzero circuit provides an actual
return message before any operation or function-row interpretation. -/

namespace Aiur.AIR

/-- Providers have the same contribution to every padded-message balance.
The raw message of a zero-weight provider has no effect. -/
def Provider.PaddedEq (width : Nat) (left right : Provider (List G)) : Prop :=
  left.2 = right.2 ∧ (left.2 ≠ 0 → padMessage width left.1 = padMessage width right.1)

theorem Provider.PaddedEq.refl (width : Nat) (provider : Provider (List G)) :
    PaddedEq width provider provider := ⟨rfl, fun _ => rfl⟩

theorem Provider.PaddedEq.symm {width : Nat} {left right : Provider (List G)}
    (same : PaddedEq width left right) : PaddedEq width right left :=
  ⟨same.1.symm, fun nonzero => (same.2 (same.1 ▸ nonzero)).symm⟩

theorem Provider.PaddedEq.trans {width : Nat} {left middle right : Provider (List G)}
    (first : PaddedEq width left middle) (last : PaddedEq width middle right) : PaddedEq width left right :=
  ⟨first.1.trans last.1, fun nonzero => (first.2 nonzero).trans (last.2 (first.1 ▸ nonzero))⟩

theorem suppliedWeight_padded_congr {width : Nat} {left right : List (Provider (List G))}
    (related : List.Forall₂ (Provider.PaddedEq width) left right) (message : List G) :
    suppliedWeight message (mapProviders (padMessage width) left) =
      suppliedWeight message (mapProviders (padMessage width) right) := by
  induction related with
  | nil => rfl
  | @cons first last rest rest' head tail ih =>
    change (if padMessage width first.1 = message then
      first.2 + suppliedWeight message (mapProviders (padMessage width) rest)
      else suppliedWeight message (mapProviders (padMessage width) rest)) =
      (if padMessage width last.1 = message then
      last.2 + suppliedWeight message (mapProviders (padMessage width) rest')
      else suppliedWeight message (mapProviders (padMessage width) rest'))
    by_cases zero : first.2 = 0
    · have lastZero := head.1.symm.trans zero
      simp only [zero, lastZero, G.zero_add, ite_self, ih]
    · rw [head.2 zero, head.1, ih]

theorem PaddedLookupBalance.congr_providers {width : Nat} {queries : List (List G)}
    {left right : List (Provider (List G))} (balanced : PaddedLookupBalance width queries left)
    (related : List.Forall₂ (Provider.PaddedEq width) left right) :
    PaddedLookupBalance width queries right := fun message =>
  (balanced message).trans (suppliedWeight_padded_congr related message)

theorem paddedProviders_refl (width : Nat) (providers : List (Provider (List G))) :
    List.Forall₂ (Provider.PaddedEq width) providers providers := by
  induction providers with
  | nil => exact .nil
  | cons provider rest ih => exact .cons (Provider.PaddedEq.refl width provider) ih

def CircuitEmission.provider (emission : CircuitEmission) : Provider (List G) :=
  ((emission.lookup 0).2, emission.multiplicity)

theorem CircuitEmission.provider_multiplicity (emission : CircuitEmission) :
    (emission.lookup 0).1 = 0 - emission.provider.2 := rfl

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

theorem Circuit.emitRow_provider (row : Nat → G) (program : Toplevel) (circuit : Circuit)
    {emission : CircuitEmission} (emitted : circuit.emitRow row program = some emission)
    (validated : circuit.validateRowCounts program = true)
    (shape : ∀ part ∈ emission.members, part.function.body.lookupShapes program none = true)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (nonzero : emission.multiplicity ≠ 0) (width : Nat) :
    ∃ request : AIR.Call, (1, request) ∈ emission.returns ∧
      padMessage width (emission.lookup 0).2 = padMessage width (functionMessage request) := by
  obtain ⟨bounded, _, returnBound, single⟩ := circuit.emitRow_count_bounds row program emitted validated satisfied
  obtain ⟨description, indices, source⟩ := circuit.emitRow_spec row program emitted
  have size := congrArg List.length indices
  simp only [List.length_map, Array.length_toList] at size
  have valid : ∀ equation ∈ (circuitEmission row circuit emission.members).equations, equation = 0 := by
    rw [← description]
    exact satisfied
  have active : (circuitEmission row circuit emission.members).selector = 1 :=
    nonzero_multiplicity_selector_one (circuitEmission_activity valid) (by
      rw [← description]
      exact nonzero)
  have count := circuitEmission_return_count source shape (by omega) returnBound valid active
  rw [← description] at count
  have present : (1 : G) ∈ emission.returns.map Prod.fst := List.count_pos_iff.mp (by rw [count]; decide)
  obtain ⟨⟨gate, request⟩, member, gateEq⟩ := List.mem_map.mp present
  change gate = 1 at gateEq
  subst gate
  refine ⟨request, member, ?_⟩
  have message := circuitEmission_return_message source shape (by omega) returnBound valid active width
    (by rw [← description]; exact single) (by rw [← description]; exact member)
  rw [← description] at message
  exact message

end Aiur.Bytecode
