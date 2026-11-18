import Aiur.Tiling.Copy

/-!
# Keyed chunks

A wide message split into `J` chunks travels as `J` lookups `(j, key, chunk_j)`.
If every receiver key is unique (invocation id, table row, ROM address, all
fixed) and every sender multiplicity is boolean (`m² - m = 0`), balance of
every chunk implies balance of every whole tuple: an enabled sender with key
`k` agrees chunk by chunk with the unique receiver of `k`, so no tuple can be
assembled from chunks of different senders.
-/

namespace Aiur.Tiling

variable {F : Type} [Field F] [DecidableEq F]

section

variable {σ ρ K V : Type} [DecidableEq K] [DecidableEq V]

theorem zero_one_finset_sum {bound : Nat} (small : SmallCast F bound) {ι : Type} [DecidableEq ι]
    (S : Finset ι) (m : ι → F) (bits : ∀ s ∈ S, m s = 0 ∨ m s = 1) (short : S.card < bound)
    {s₀ : ι} (h₀ : s₀ ∈ S) (one : m s₀ = 1) : ∑ s ∈ S, m s ≠ 0 := by
  have count : ∑ s ∈ S, m s = ((S.filter fun s => m s = 1).card : F) := by
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rcases bits s hs with h | h <;> simp [h]
  rw [count]
  intro h
  have pos : 0 < (S.filter fun s => m s = 1).card :=
    Finset.card_pos.mpr ⟨s₀, Finset.mem_filter.mpr ⟨h₀, one⟩⟩
  have le := Finset.card_filter_le S fun s => m s = 1
  have := small _ (by omega) h
  omega

variable [DecidableEq σ] [DecidableEq ρ]
  (S : Finset σ) (key : σ → K) (chunk : σ → Nat → V) (m : σ → F)
  (R : Finset ρ) (rkey : ρ → K) (rchunk : ρ → Nat → V) (μ : ρ → Nat → F) (J : Nat)

/-- Balance of every chunk `j < J` at every key and value. A receiver may weigh
its chunks differently (`μ r j`); senders weigh all their chunks alike. -/
def ChunkBalance : Prop :=
  ∀ j < J, ∀ k v, (∑ s ∈ S.filter (fun s => key s = k ∧ chunk s j = v), m s) =
    ∑ r ∈ R.filter (fun r => rkey r = k ∧ rchunk r j = v), μ r j

variable {S key chunk m R rkey rchunk μ J}

theorem chunk_sender_matches (balance : ChunkBalance S key chunk m R rkey rchunk μ J)
    (unique : Set.InjOn rkey R) (bits : ∀ s ∈ S, m s = 0 ∨ m s = 1)
    {bound : Nat} (small : SmallCast F bound) (short : S.card < bound) (nonempty : 0 < J)
    {s : σ} (hs : s ∈ S) (on : m s = 1) :
    ∃ r ∈ R, rkey r = key s ∧ ∀ j < J, chunk s j = rchunk r j := by
  have receiver : ∀ j < J, ∃ r ∈ R, rkey r = key s ∧ rchunk r j = chunk s j := by
    intro j hj
    have ne : ∑ s' ∈ S.filter (fun s' => key s' = key s ∧ chunk s' j = chunk s j), m s' ≠ 0 :=
      zero_one_finset_sum small _ m (fun s' h => bits s' (Finset.mem_filter.mp h).1)
        (lt_of_le_of_lt (Finset.card_filter_le _ _) short)
        (Finset.mem_filter.mpr ⟨hs, rfl, rfl⟩) on
    rw [balance j hj] at ne
    obtain ⟨r, hr, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero ne
    obtain ⟨hr, k, v⟩ := Finset.mem_filter.mp hr
    exact ⟨r, hr, k, v⟩
  obtain ⟨r, hr, k, _⟩ := receiver 0 nonempty
  refine ⟨r, hr, k, fun j hj => ?_⟩
  obtain ⟨r', hr', k', v'⟩ := receiver j hj
  have := unique hr' hr (k'.trans k.symm)
  rw [← this, v']

/-- **Chunk soundness.** Whole tuples balance. -/
theorem chunks_sound (balance : ChunkBalance S key chunk m R rkey rchunk μ J)
    (unique : Set.InjOn rkey R) (bits : ∀ s ∈ S, m s = 0 ∨ m s = 1)
    {bound : Nat} (small : SmallCast F bound) (short : S.card < bound) (nonempty : 0 < J)
    (k : K) (vs : Nat → V) :
    (∑ s ∈ S.filter (fun s => key s = k ∧ ∀ j < J, chunk s j = vs j), m s) =
      ∑ r ∈ R.filter (fun r => rkey r = k ∧ ∀ j < J, rchunk r j = vs j), μ r 0 := by
  have agrees : ∀ {s}, s ∈ S → m s = 1 → ∃ r ∈ R, rkey r = key s ∧ ∀ j < J, chunk s j = rchunk r j := fun {s} hs on =>
    chunk_sender_matches balance unique bits small short nonempty (s := s) hs on
  by_cases hk : ∃ r₀ ∈ R, rkey r₀ = k
  · obtain ⟨r₀, hr₀, rk₀⟩ := hk
    have onlyR : ∀ r ∈ R, rkey r = k → r = r₀ := fun r hr h => unique hr hr₀ (h.trans rk₀.symm)
    by_cases full : ∀ j < J, rchunk r₀ j = vs j
    · have rhs : (∑ r ∈ R.filter (fun r => rkey r = k ∧ ∀ j < J, rchunk r j = vs j), μ r 0) = μ r₀ 0 := by
        rw [Finset.sum_eq_single_of_mem r₀ (Finset.mem_filter.mpr ⟨hr₀, rk₀, full⟩)]
        intro r hr ne
        exact absurd (onlyR r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2.1) ne
      have rhs0 : (∑ r ∈ R.filter (fun r => rkey r = k ∧ rchunk r 0 = vs 0), μ r 0) = μ r₀ 0 := by
        rw [Finset.sum_eq_single_of_mem r₀ (Finset.mem_filter.mpr ⟨hr₀, rk₀, full 0 nonempty⟩)]
        intro r hr ne
        exact absurd (onlyR r (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2.1) ne
      rw [rhs, ← rhs0, ← balance 0 nonempty, Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases on : m s = 1
      · by_cases ks : key s = k
        · obtain ⟨r, hr, rk, agree⟩ := agrees hs on
          have := onlyR r hr (rk.trans ks)
          subst this
          have all : ∀ j < J, chunk s j = vs j := fun j hj => (agree j hj).trans (full j hj)
          have all' : (∀ j < J, chunk s j = vs j) = True := eq_true all
          simp only [ks, all', all 0 nonempty, and_self, ite_true]
        · simp [ks]
      · rcases bits s hs with h | h
        · simp [h]
        · exact absurd h on
    · have rhs : (∑ r ∈ R.filter (fun r => rkey r = k ∧ ∀ j < J, rchunk r j = vs j), μ r 0) = 0 := by
        apply Finset.sum_eq_zero
        intro r hr
        obtain ⟨hr, rk, all⟩ := Finset.mem_filter.mp hr
        exact absurd (onlyR r hr rk ▸ all) full
      rw [rhs]
      apply Finset.sum_eq_zero
      intro s hs
      obtain ⟨hs, ks, all⟩ := Finset.mem_filter.mp hs
      rcases bits s hs with h | h
      · exact h
      · obtain ⟨r, hr, rk, agree⟩ := agrees hs h
        have := onlyR r hr (rk.trans ks)
        subst this
        exact absurd (fun j hj => (agree j hj).symm.trans (all j hj)) full
  · push Not at hk
    have rhs : (∑ r ∈ R.filter (fun r => rkey r = k ∧ ∀ j < J, rchunk r j = vs j), μ r 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      obtain ⟨hr, rk, _⟩ := Finset.mem_filter.mp hr
      exact absurd rk (hk r hr)
    rw [rhs]
    apply Finset.sum_eq_zero
    intro s hs
    obtain ⟨hs, ks, _⟩ := Finset.mem_filter.mp hs
    rcases bits s hs with h | h
    · exact h
    · obtain ⟨r, hr, rk, _⟩ := agrees hs h
      exact absurd (rk.trans ks) (hk r hr)

/-- **Whole-tuple balance.** Summed over keys, the senders of a payload balance
its receivers: chunk balance assembles into the balance of whole tuples,
with the key dropped. -/
theorem chunks_total (balance : ChunkBalance S key chunk m R rkey rchunk μ J)
    (unique : Set.InjOn rkey R) (bits : ∀ s ∈ S, m s = 0 ∨ m s = 1)
    {bound : Nat} (small : SmallCast F bound) (short : S.card < bound) (nonempty : 0 < J)
    (vs : Nat → V) :
    (∑ s ∈ S.filter (fun s => ∀ j < J, chunk s j = vs j), m s) =
      ∑ r ∈ R.filter (fun r => ∀ j < J, rchunk r j = vs j), μ r 0 := by
  let keys := S.image key ∪ R.image rkey
  have lhs := Finset.sum_fiberwise_of_maps_to (s := S.filter (fun s => ∀ j < J, chunk s j = vs j))
    (t := keys) (g := key) (fun s hs => Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_filter.mp hs).1)) m
  have rhs := Finset.sum_fiberwise_of_maps_to (s := R.filter (fun r => ∀ j < J, rchunk r j = vs j))
    (t := keys) (g := rkey) (fun r hr => Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_filter.mp hr).1)) (μ · 0)
  rw [← lhs, ← rhs]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.filter_filter, Finset.filter_filter]
  have := chunks_sound balance unique bits small short nonempty k vs
  convert this using 2 <;> ext x <;> simp [and_comm]

end

/-! ## Chunk balance from a ledger -/

section Ledger

variable {ι σ ρ K V : Type} [DecidableEq K] [DecidableEq V]

/-- One participant's chunk tuples: weight `w` at `u j k (chunk j)` for every
chunk `j < J`. -/
noncomputable def chunkLedger (u : Nat → K → V → List F) (J : Nat) (w : F) (k : K) (chunk : Nat → V) :
    Ledger F :=
  ∑ j ∈ Finset.range J, Finsupp.single (u j k (chunk j)) w

theorem chunkLedger_sum_apply {u : Nat → K → V → List F}
    (inj : ∀ {j j' k k' v v'}, u j k v = u j' k' v' → j = j' ∧ k = k' ∧ v = v')
    {J : Nat} (P : Finset ι) (w : ι → F) (keyOf : ι → K) (chunkOf : ι → Nat → V)
    {j : Nat} (hj : j < J) (k : K) (v : V) :
    (∑ p ∈ P, chunkLedger u J (w p) (keyOf p) (chunkOf p)) (u j k v) =
      ∑ p ∈ P.filter (fun p => keyOf p = k ∧ chunkOf p j = v), w p := by
  simp only [Finsupp.finsetSum_apply, chunkLedger, Finsupp.single_apply]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single j]
  · by_cases h : keyOf p = k ∧ chunkOf p j = v
    · simp [h.1, h.2]
    · rw [if_neg h, if_neg]
      intro e
      exact h ⟨(inj e).2.1, (inj e).2.2⟩
  · intro j' _ ne
    rw [if_neg]
    intro e
    exact ne (inj e).1
  · intro h
    exact absurd (Finset.mem_range.mpr hj) h

/-- **Chunked channel soundness on a ledger.** Senders with boolean weights
and receivers with unique keys whose chunk tuples, together with a rest that
has no weight at chunk tuples, sum to zero: summed over keys, senders and
receivers of every whole payload balance. -/
theorem chunks_total_of_ledger {u : Nat → K → V → List F}
    (inj : ∀ {j j' k k' v v'}, u j k v = u j' k' v' → j = j' ∧ k = k' ∧ v = v') {J : Nat}
    [DecidableEq σ] [DecidableEq ρ]
    {S : Finset σ} {key : σ → K} {chunk : σ → Nat → V} {m : σ → F}
    {R : Finset ρ} {rkey : ρ → K} {rchunk : ρ → Nat → V} {μ : ρ → F} {rest : Ledger F}
    (restZero : ∀ j < J, ∀ k v, rest (u j k v) = 0)
    (zero : (∑ s ∈ S, chunkLedger u J (m s) (key s) (chunk s)) -
      (∑ r ∈ R, chunkLedger u J (μ r) (rkey r) (rchunk r)) + rest = 0)
    (unique : Set.InjOn rkey R) (bits : ∀ s ∈ S, m s = 0 ∨ m s = 1)
    {bound : Nat} (small : SmallCast F bound) (short : S.card < bound) (nonempty : 0 < J)
    (vs : Nat → V) :
    (∑ s ∈ S.filter (fun s => ∀ j < J, chunk s j = vs j), m s) =
      ∑ r ∈ R.filter (fun r => ∀ j < J, rchunk r j = vs j), μ r := by
  refine chunks_total (key := key) (μ := fun r _ => μ r) (fun j hj k v => ?_) unique bits small short
    nonempty vs
  have := congrArg (fun L : Ledger F => L (u j k v)) zero
  simp only [Finsupp.add_apply, Finsupp.sub_apply, restZero j hj k v, add_zero, Finsupp.coe_zero,
    Pi.zero_apply, chunkLedger_sum_apply inj _ _ _ _ hj] at this
  exact sub_eq_zero.mp this

end Ledger

end Aiur.Tiling
