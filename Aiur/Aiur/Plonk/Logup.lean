import Aiur.Plonk.StageSound
import Mathlib.Algebra.Polynomial.Roots

/-!
# Fingerprint injectivity and the challenge-soundness count

`fp γ β u = β + (fpPoly u).eval γ` (`fp_eq`), where
`fpPoly u = n·X^n + Σ_i u_i·X^(expOf n i)` (`n = |u|`).

* `fpPoly_inj`: distinct tuples have distinct polynomials, when every
  length up to the larger one is nonzero in `Fr`. The coefficient at `X^n`
  separates lengths; for equal lengths, `expOf n` is injective on `[0, n)`
  (`expOf_inj`) and stays below `n`, so coefficient `expOf n i` is `u_i`.
* `card_gamma_collide_le`: for a finite set `S` of tuples of length at most
  `ℓ`, any finite set of `γ` at which two members of `S` share a fingerprint
  has at most `|S|²·ℓ` elements.
* `card_beta_bad_le`: for `γ` at which the members of `L`'s support have
  distinct fingerprints and `L ≠ 0`, any finite set of `β` with no zero
  fingerprint on the support and `logupEval γ β L = 0` has fewer than
  `|support|` elements (the numerator of `Σ_t L(t)/(β + a_t)` over the
  common denominator is a nonzero polynomial in `β` of degree below
  `|support|`).
* `card_fp_zero_le`: at most `|T|` values of `β` give some tuple of `T` a
  zero fingerprint.

Together: over uniform `(γ, β)`, `¬ ChallengeGood` for a fixed nonzero
ledger `L` with message tuples `T ⊇ supp L` has probability at most
`(|S|²·ℓ + |T| + |S|) / |Fr|`, `S = supp L`.
-/

namespace Aiur.Plonk

open Polynomial
open Lower (Fr)
open Aiur.Tiling (Ledger)

/-- The `β`-free part of `fp` as a polynomial in `γ`. -/
noncomputable def fpPoly (u : List Fr) : Fr[X] :=
  C (u.length : Fr) * X ^ u.length + ∑ i ∈ Finset.range u.length, C (u.getD i 0) * X ^ expOf u.length i

theorem sum_zipIdx_eq {β : Type} [AddCommMonoid β] (g : Fr → Nat → β) :
    ∀ (u : List Fr) (k : Nat),
      ((u.zipIdx k).map fun p => g p.1 p.2).sum = ∑ i ∈ Finset.range u.length, g (u.getD i 0) (i + k)
  | [], _ => by simp
  | a :: u, k => by
      rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx_eq g u (k + 1), List.length_cons,
        Finset.sum_range_succ', add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        simp only [List.getD_cons_succ]
        congr 1; omega
      · simp

theorem fp_eq (γ β : Fr) (u : List Fr) : fp γ β u = β + (fpPoly u).eval γ := by
  have := sum_zipIdx_eq (fun x i => x * γ ^ expOf u.length i) u 0
  simp only [Nat.add_zero] at this
  simp only [fp, fpPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_finset_sum, add_assoc]
  congr 2

theorem expOf_lt {n i : Nat} (h : i < n) : expOf n i < n := by
  unfold expOf
  split
  · exact h
  · exact Nat.mod_lt _ (by omega)

theorem expOf_inj {n i j : Nat} (hi : i < n) (hj : j < n) (h : expOf n i = expOf n j) : i = j := by
  unfold expOf at h
  split at h
  · exact h
  · rename_i hn
    have e : i + (n - 2) ≡ j + (n - 2) [MOD n] := by
      unfold Nat.ModEq
      rw [show i + (n - 2) = i + n - 2 by omega, show j + (n - 2) = j + n - 2 by omega]
      exact h
    have := Nat.ModEq.add_right_cancel' (n - 2) e
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

theorem coeff_fpPoly (u : List Fr) (k : Nat) :
    (fpPoly u).coeff k = (if k = u.length then (u.length : Fr) else 0) +
      ∑ i ∈ Finset.range u.length, if k = expOf u.length i then u.getD i 0 else 0 := by
  simp [fpPoly, coeff_C_mul_X_pow, finset_sum_coeff]

theorem coeff_fpPoly_exp {u : List Fr} {i : Nat} (hi : i < u.length) :
    (fpPoly u).coeff (expOf u.length i) = u.getD i 0 := by
  rw [coeff_fpPoly, if_neg (Nat.ne_of_lt (expOf_lt hi)), zero_add,
    Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    rw [if_neg]
    intro e
    exact hji (expOf_inj (Finset.mem_range.mp hj) hi e.symm)
  · intro h; exact absurd (Finset.mem_range.mpr hi) h

theorem coeff_fpPoly_above {u : List Fr} {k : Nat} (hk : u.length < k) : (fpPoly u).coeff k = 0 := by
  rw [coeff_fpPoly, if_neg (by omega), zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg]
  have := expOf_lt (Finset.mem_range.mp hi)
  omega

theorem coeff_fpPoly_length (u : List Fr) : (fpPoly u).coeff u.length = u.length := by
  rw [coeff_fpPoly, if_pos rfl]
  simp only [add_eq_left]
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg]
  have := expOf_lt (Finset.mem_range.mp hi)
  omega

/-- Distinct tuples have distinct fingerprint polynomials. -/
theorem fpPoly_inj {u v : List Fr} (hlen : ∀ k, 0 < k → k ≤ max u.length v.length → (k : Fr) ≠ 0)
    (h : fpPoly u = fpPoly v) : u = v := by
  rcases Nat.lt_trichotomy u.length v.length with hl | hl | hl
  · have e := congrArg (·.coeff v.length) h
    simp only [coeff_fpPoly_above hl, coeff_fpPoly_length] at e
    exact absurd e.symm (hlen _ (by omega) (le_max_right _ _))
  · apply List.ext_getElem hl
    intro i hu hv
    have e := congrArg (·.coeff (expOf u.length i)) h
    rw [coeff_fpPoly_exp hu, hl, coeff_fpPoly_exp hv] at e
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu, List.getElem?_eq_getElem hv] using e
  · have e := congrArg (·.coeff u.length) h
    simp only [coeff_fpPoly_above hl, coeff_fpPoly_length] at e
    exact absurd e (hlen _ (by omega) (le_max_left _ _))

theorem natDegree_fpPoly_le (u : List Fr) : (fpPoly u).natDegree ≤ u.length := by
  unfold fpPoly
  refine natDegree_add_le_of_degree_le ?_ ?_
  · exact (natDegree_C_mul_le _ _).trans (by simp)
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans
      (by simpa using (expOf_lt (Finset.mem_range.mp hi)).le))

theorem card_roots_le {p : Fr[X]} (hp : p ≠ 0) {Z : Finset Fr} (h : ∀ x ∈ Z, p.eval x = 0) :
    Z.card ≤ p.natDegree := by
  refine card_le_degree_of_subset_roots ?_
  intro x hx
  exact (mem_roots hp).mpr (h x hx)

/-- At most `ℓ` values of `γ` make two distinct tuples of length `≤ ℓ`
collide. -/
theorem card_collide_le {u v : List Fr} (huv : u ≠ v) {ℓ : Nat} (hu : u.length ≤ ℓ) (hv : v.length ≤ ℓ)
    (hlen : ∀ k, 0 < k → k ≤ ℓ → (k : Fr) ≠ 0) {Z : Finset Fr}
    (h : ∀ γ ∈ Z, (fpPoly u).eval γ = (fpPoly v).eval γ) : Z.card ≤ ℓ := by
  have hne : fpPoly u - fpPoly v ≠ 0 := fun e =>
    huv (fpPoly_inj (fun k hk hk' => hlen k hk (hk'.trans (max_le hu hv))) (sub_eq_zero.mp e))
  refine (card_roots_le hne (fun γ hγ => by simp [h γ hγ])).trans ?_
  exact (natDegree_sub_le _ _).trans (max_le ((natDegree_fpPoly_le u).trans hu) ((natDegree_fpPoly_le v).trans hv))

theorem card_gamma_collide_le {S : Finset (List Fr)} {ℓ : Nat} (hS : ∀ u ∈ S, u.length ≤ ℓ)
    (hlen : ∀ k, 0 < k → k ≤ ℓ → (k : Fr) ≠ 0) {Z : Finset Fr}
    (h : ∀ γ ∈ Z, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ (fpPoly u).eval γ = (fpPoly v).eval γ) :
    Z.card ≤ S.card * S.card * ℓ := by
  classical
  have sub : Z ⊆ S.offDiag.biUnion fun p => Z.filter fun γ => (fpPoly p.1).eval γ = (fpPoly p.2).eval γ := by
    intro γ hγ
    obtain ⟨u, hu, v, hv, huv, e⟩ := h γ hγ
    exact Finset.mem_biUnion.mpr ⟨(u, v), Finset.mem_offDiag.mpr ⟨hu, hv, huv⟩, Finset.mem_filter.mpr ⟨hγ, e⟩⟩
  refine (Finset.card_le_card sub).trans ((Finset.card_biUnion_le).trans ?_)
  have each : ∀ p ∈ S.offDiag, (Z.filter fun γ => (fpPoly p.1).eval γ = (fpPoly p.2).eval γ).card ≤ ℓ := by
    intro p hp
    obtain ⟨h1, h2, h12⟩ := Finset.mem_offDiag.mp hp
    exact card_collide_le h12 (hS _ h1) (hS _ h2) hlen fun γ hγ => (Finset.mem_filter.mp hγ).2
  refine (Finset.sum_le_card_nsmul _ _ _ each).trans ?_
  rw [smul_eq_mul]
  rw [Finset.offDiag_card]
  exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

theorem logupEval_eq_sum (γ β : Fr) (L : Ledger Fr) :
    logupEval γ β L = ∑ t ∈ L.support, L t * (fp γ β t)⁻¹ := by
  simp [logupEval, Finsupp.liftAddHom_apply, Finsupp.sum]

/-- For `γ` with distinct fingerprints on the support of `L ≠ 0`, fewer than
`|supp L|` values of `β` have no zero fingerprint on the support and a
vanishing LogUp sum. -/
theorem card_beta_bad_le {L : Ledger Fr} (hL : L ≠ 0) {γ : Fr}
    (distinct : ∀ u ∈ L.support, ∀ v ∈ L.support, (fpPoly u).eval γ = (fpPoly v).eval γ → u = v)
    {Z : Finset Fr}
    (h : ∀ β ∈ Z, (∀ t ∈ L.support, fp γ β t ≠ 0) ∧ logupEval γ β L = 0) :
    Z.card + 1 ≤ L.support.card := by
  classical
  set S := L.support
  let N : Fr[X] := ∑ t ∈ S, C (L t) * ∏ s ∈ S.erase t, (X + C ((fpPoly s).eval γ))
  obtain ⟨t0, ht0⟩ : S.Nonempty := Finsupp.support_nonempty_iff.mpr hL
  have hN0 : N.eval (-((fpPoly t0).eval γ)) ≠ 0 := by
    simp only [N, eval_finset_sum, eval_mul, eval_C, eval_prod, eval_add, eval_X]
    rw [Finset.sum_eq_single t0]
    · refine mul_ne_zero (Finsupp.mem_support_iff.mp ht0) (Finset.prod_ne_zero_iff.mpr fun s hs => ?_)
      obtain ⟨hst, hs'⟩ := Finset.mem_erase.mp hs
      intro e
      exact hst (distinct s hs' t0 ht0 (by linear_combination e))
    · intro t _ htt0
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm htt0, ht0⟩) (by ring), mul_zero]
    · intro h; exact absurd ht0 h
  have hN : N ≠ 0 := fun e => hN0 (by rw [e, eval_zero])
  have deg : N.natDegree ≤ S.card - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun t ht => (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 1 fun s _ => ?_).trans ?_
    · exact (natDegree_add_le _ _).trans (by simp)
    · simp [Finset.card_erase_of_mem ht]
  have roots : ∀ β ∈ Z, N.eval β = 0 := by
    intro β hβ
    obtain ⟨nz, ev⟩ := h β hβ
    rw [logupEval_eq_sum] at ev
    have key : N.eval β = (∏ s ∈ S, fp γ β s) * ∑ t ∈ S, L t * (fp γ β t)⁻¹ := by
      simp only [N, eval_finset_sum, eval_mul, eval_C, eval_prod, eval_add, eval_X, Finset.mul_sum, ← fp_eq]
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.mul_prod_erase S _ ht]
      have hinv := mul_inv_cancel₀ (nz t ht)
      linear_combination (-(L t * ∏ s ∈ S.erase t, fp γ β s)) * hinv
    rw [key, ev, mul_zero]
  have := (card_roots_le hN roots).trans deg
  have : 0 < S.card := Finset.card_pos.mpr ⟨t0, ht0⟩
  omega

/-- At most `|T|` values of `β` give some tuple of `T` a zero fingerprint. -/
theorem card_fp_zero_le (γ : Fr) (T : Finset (List Fr)) {Z : Finset Fr}
    (h : ∀ β ∈ Z, ∃ t ∈ T, fp γ β t = 0) : Z.card ≤ T.card := by
  classical
  refine (Finset.card_le_card (t := T.image fun t => -(fpPoly t).eval γ) ?_).trans Finset.card_image_le
  intro β hβ
  obtain ⟨t, ht, e⟩ := h β hβ
  rw [fp_eq] at e
  exact Finset.mem_image.mpr ⟨t, ht, by linear_combination -e⟩

/-- The bad `β` for one `γ` without collisions on `supp L`: fewer than
`|T| + |supp L|` values of `β` violate `ChallengeGood γ β (· ∈ T) L`. -/
theorem card_not_good_le {L : Ledger Fr} (hL : L ≠ 0) {γ : Fr}
    (distinct : ∀ u ∈ L.support, ∀ v ∈ L.support, (fpPoly u).eval γ = (fpPoly v).eval γ → u = v)
    (T : Finset (List Fr)) (hT : L.support ⊆ T) {Z : Finset Fr}
    (h : ∀ β ∈ Z, ¬ ChallengeGood γ β (· ∈ T) L) : Z.card + 1 ≤ T.card + L.support.card := by
  classical
  let Z1 := Z.filter fun β => ∃ t ∈ T, fp γ β t = 0
  let Z2 := Z.filter fun β => ¬ ∃ t ∈ T, fp γ β t = 0
  have h1 : Z1.card ≤ T.card := card_fp_zero_le γ T fun β hβ => (Finset.mem_filter.mp hβ).2
  have h2 : Z2.card + 1 ≤ L.support.card := by
    refine card_beta_bad_le hL distinct fun β hβ => ?_
    obtain ⟨hβZ, hnz⟩ := Finset.mem_filter.mp hβ
    have nz : ∀ t ∈ T, fp γ β t ≠ 0 := fun t ht e => hnz ⟨t, ht, e⟩
    refine ⟨fun t ht => nz t (hT ht), ?_⟩
    by_contra hev
    exact h β hβZ ⟨fun u hu => nz u hu, fun e => absurd e hev⟩
  have : Z1.card + Z2.card = Z.card := Finset.card_filter_add_card_filter_not _
  omega

end Aiur.Plonk
