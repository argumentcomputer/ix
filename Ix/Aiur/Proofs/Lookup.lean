/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CallOrder

/-! Exact lookup balance over the actual Goldilocks representation.

Consumer queries have unit weight; providers may have arbitrary field
multiplicities. A query count below the characteristic cannot disappear by
modular cancellation, so every queried message has a nonzero provider.
Instantiating this result with the fixed 256-by-256 byte table recovers byte
bounds, including the six bytes used by the call-order constraint.

These theorems assume exact message balance. They do not extract that
balance from a cryptographic transcript or identify the Rust emitter with
this mathematical interface.
-/

namespace Aiur

theorem G.zero_add (a : G) : 0 + a = a := by
  change G.ofNat (0 + a.n) = a
  simpa only [Nat.zero_add] using G.ofNat_n a

theorem G.ofNat_ne_zero_of_lt {n : Nat} (positive : 0 < n)
    (bounded : n < gSize.toNat) : G.ofNat n ≠ 0 := by
  intro h
  have hn := congrArg G.n h
  rw [G.n_ofNat, Nat.mod_eq_of_lt bounded] at hn
  change n = 0 at hn
  omega

namespace AIR

/-- A supplied message and its return/pull multiplicity. -/
abbrev Provider (α : Type u) := α × G

/-- Total supplied weight for one exact message. -/
def suppliedWeight [DecidableEq α] (message : α) (providers : List (Provider α)) : G :=
  providers.foldr (fun provider rest =>
    if provider.1 = message then provider.2 + rest else rest) 0

/-- Exact tuple balance, before randomized message compression. Each
consumer contributes one; arbitrary provider weights are field elements. -/
def ExactLookupBalance [DecidableEq α] (queries : List α)
    (providers : List (Provider α)) : Prop :=
  ∀ message, G.ofNat (queries.count message) = suppliedWeight message providers

/-- The count bound is necessary: exactly one characteristic's worth of
identical queries has zero field weight, even with no providers. -/
theorem characteristic_queries_balance [DecidableEq α] (message : α) :
    ExactLookupBalance (List.replicate gSize.toNat message) [] := by
  intro query
  simp only [List.count_replicate, suppliedWeight]
  split <;> rfl

theorem suppliedWeight_nonzero_provider [DecidableEq α] (message : α)
    (providers : List (Provider α))
    (nonzero : suppliedWeight message providers ≠ 0) :
    ∃ provider ∈ providers, provider.1 = message ∧ provider.2 ≠ 0 := by
  induction providers with
  | nil => exact False.elim (nonzero rfl)
  | cons provider rest ih =>
    obtain ⟨provided, multiplicity⟩ := provider
    by_cases same : provided = message
    · by_cases zero : multiplicity = 0
      · have hn : suppliedWeight message rest ≠ 0 := by
          simpa only [suppliedWeight, List.foldr_cons, if_pos same, zero, G.zero_add] using nonzero
        obtain ⟨provider, member, hm, hw⟩ := ih hn
        exact ⟨provider, List.mem_cons_of_mem _ member, hm, hw⟩
      · exact ⟨(provided, multiplicity), List.mem_cons_self, same, zero⟩
    · have hn : suppliedWeight message rest ≠ 0 := by
        simpa only [suppliedWeight, List.foldr_cons, if_neg same] using nonzero
      obtain ⟨provider, member, hm, hw⟩ := ih hn
      exact ⟨provider, List.mem_cons_of_mem _ member, hm, hw⟩

/-- A bounded positive request cannot be supplied solely by zero weights,
even when other providers use negative field multiplicities. -/
theorem exactLookupBalance_provider [DecidableEq α]
    {queries : List α} {providers : List (Provider α)}
    (balanced : ExactLookupBalance queries providers)
    (bounded : queries.length < gSize.toNat) {message : α}
    (queried : message ∈ queries) :
    ∃ provider ∈ providers, provider.1 = message ∧ provider.2 ≠ 0 := by
  have positive : 0 < queries.count message := List.count_pos_iff.mpr queried
  have countBound : queries.count message < gSize.toNat :=
    Nat.lt_of_le_of_lt List.count_le_length bounded
  have nonzero := G.ofNat_ne_zero_of_lt positive countBound
  rw [balanced message] at nonzero
  exact suppliedWeight_nonzero_provider message providers nonzero

/-- Row order of the two-byte preprocessed table: outer first byte, inner
second byte, each ranging from 0 through 255. -/
def byteRangeMessage (row : Fin 65536) : G × G :=
  (G.ofNat (row.val / 256), G.ofNat (row.val % 256))

def byteRangeProviders (weights : Fin 65536 → G) : List (Provider (G × G)) :=
  List.ofFn fun row => (byteRangeMessage row, weights row)

theorem byteRangeMessage_bounded (row : Fin 65536) :
    (byteRangeMessage row).1.n < 256 ∧ (byteRangeMessage row).2.n < 256 := by
  have first : row.val / 256 < 256 := by omega
  have second : row.val % 256 < 256 := Nat.mod_lt _ (by decide)
  have firstField : row.val / 256 < gSize.toNat := by
    exact Nat.lt_trans first (by decide)
  have secondField : row.val % 256 < gSize.toNat := by
    exact Nat.lt_trans second (by decide)
  simpa only [byteRangeMessage, G.n_ofNat, Nat.mod_eq_of_lt firstField,
    Nat.mod_eq_of_lt secondField] using And.intro first second

/-- Exact balance against the fixed byte table establishes both byte
bounds. The table's multiplicity column remains arbitrary. -/
theorem exactLookupBalance_byteRange {queries : List (G × G)}
    (weights : Fin 65536 → G)
    (balanced : ExactLookupBalance queries (byteRangeProviders weights))
    (bounded : queries.length < gSize.toNat) {a b : G}
    (queried : (a, b) ∈ queries) : a.n < 256 ∧ b.n < 256 := by
  obtain ⟨provider, member, message, _⟩ :=
    exactLookupBalance_provider balanced bounded queried
  obtain ⟨row, hrow⟩ := List.mem_ofFn.mp member
  have same : byteRangeMessage row = (a, b) := by
    exact (congrArg Prod.fst hrow).trans message
  simpa only [same] using byteRangeMessage_bounded row

/-- The three pair queries emitted for one six-byte rank or gap. -/
def rankByteQueries (bytes : Fin 6 → G) : List (G × G) :=
  [(bytes 0, bytes 1), (bytes 2, bytes 3), (bytes 4, bytes 5)]

theorem exactLookupBalance_rankBytes {queries : List (G × G)}
    (weights : Fin 65536 → G)
    (balanced : ExactLookupBalance queries (byteRangeProviders weights))
    (bounded : queries.length < gSize.toNat) (bytes : Fin 6 → G)
    (queried : rankByteQueries bytes ⊆ queries) :
    ∀ i, (bytes i).n < 256 := by
  have p0 := exactLookupBalance_byteRange weights balanced bounded
    (queried (by simp [rankByteQueries] : (bytes 0, bytes 1) ∈ rankByteQueries bytes))
  have p1 := exactLookupBalance_byteRange weights balanced bounded
    (queried (by simp [rankByteQueries] : (bytes 2, bytes 3) ∈ rankByteQueries bytes))
  have p2 := exactLookupBalance_byteRange weights balanced bounded
    (queried (by simp [rankByteQueries] : (bytes 4, bytes 5) ∈ rankByteQueries bytes))
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact p0.1
  · exact p0.2
  · exact p1.1
  · exact p1.2
  · exact p2.1
  · exact p2.2

theorem exactLookupBalance_call_order {queries : List (G × G)}
    (weights : Fin 65536 → G)
    (balanced : ExactLookupBalance queries (byteRangeProviders weights))
    (bounded : queries.length < gSize.toNat) (parent child gap : Fin 6 → G)
    (hp : rankByteQueries parent ⊆ queries)
    (hc : rankByteQueries child ⊆ queries)
    (hg : rankByteQueries gap ⊆ queries)
    (satisfied : callOrderConstraint (packRank parent) (packRank child) (packRank gap) = 0) :
    (packRank parent).n < (packRank child).n :=
  packed_call_order_strict parent child gap
    (exactLookupBalance_rankBytes weights balanced bounded parent hp)
    (exactLookupBalance_rankBytes weights balanced bounded child hc)
    (exactLookupBalance_rankBytes weights balanced bounded gap hg) satisfied

end AIR
end Aiur
