import CertiFriProofs.Theory.Oracle.MerkleFrozen
import CertiFriProofs.Theory.Oracle.MerkleCommitted
import CertiFriProofs.Theory.Oracle.FiatShamirInterp
import CertiFriProofs.P3.GoldilocksExt3MultiAritySoundness
import Ix.Cert.MultiStark.PrunedSoundness
import Ix.Cert.MultiStark.SmallHeight
import Ix.Cert.MultiStark.AirSoundness
import Ix.Cert.MultiStark.LogUpSoundness

/-! # Shape-Independent Adaptive Multi-STARK ROM & `Settles`

CertiFRI's `Exec.soundness_uniqueDecoding` pins the `ClaimShape` statically in
the oracle's challenge type `Chal P.ldt P.queries`. In Multi-STARK, however,
the prover adaptively chooses the shard count, active-circuit bitmasks, and
per-circuit trace heights `logDegrees` *after* making ROM queries, committing
them into the batch preamble before `(β, γ)`, `α_air`, `ζ`, and the FRI
challenges are drawn.

This module establishes adaptive-shape ROM soundness and concrete `Fp^3`
instantiations:

1. **`DynChal` & `fractionLE_projectQueryIndex`:** Defines a shape-independent
   challenge space depending only on static `StarkSystem` security bounds, and
   proves that because `2^h ∣ 2^M` for every dynamic height `h ≤ M`, reducing a
   uniform query challenge `x : Fin (2^M)` to `x % 2^h : Fin (2^h)` preserves
   exact uniform probabilities (`FractionLE`), so dynamically chosen trace
   heights incur zero probability distortion.
2. **`settles_of_depends_on_digests`:** Any log interpretation `interp` that reads
   committed Merkle openings solely at roots listed in `digestsOf m` (for rounds `< r`)
   satisfies `CertiFri.Oracle.Settles interp (Hit digestsOf r)`.
3. **`soundness_dynamic_rom`:** Composes
   `CertiFri.Oracle.prob_fsExperiment_bind_interp_le` and `prob_hasBad_hit_le`
   for any `r`-round adaptive state function `doomed` that is round-by-round sound
   (`RbrSound`), giving the ROM bound
     `(Q + r + R) * εmax + (max M 3 + 3) * (Q + r + R) ^ 2 / (4 * |D|)`.
4. **Stage-by-stage `FractionLE` helpers** instantiating the per-round Multi-STARK
   soundness errors directly from our proved theorems:
   - `fractionLE_logup_beta` & `fractionLE_logup_pair` (linear single-point non-collision from
     `LogUpSoundness.card_logup_beta_bad_le` & `card_logup_pair_bad_le`),
   - `fractionLE_air_alpha` (from `AirSoundness.card_horner_bad_le`),
   - `fractionLE_zeta_in_domain_or_shift` (tight `2 * |D| / |K|` from
     `SmallHeight.card_zeta_in_domain_or_shift_le`),
   - `fractionLE_ood_poly_root` & `fractionLE_zeta_ood` (`(2 * |D| + d) / |K|`).
5. **Concrete `Fp^3` Tensor-STARK & Multi-Arity Instantiations (`Section 6`):**
   Discharges every hypothesis of `soundness_dynamic_rom` directly for
   `CertiFri.P3.GoldilocksExt3.starkModel` over shape-independent
   `UTensorChal Fp3Model fslots slots width` for BOTH binary tensor-batched FRI
   (`soundness_dynamic_rom_starkTensor_fp3_ud`) and multi-arity (`2^a`, covering
   8-ary folding) tensor-batched FRI (`soundness_dynamic_rom_starkTensorMulti_fp3_ud`).

Zero `sorry`, standard axioms only.
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.Oracle CertiFri.Oracle.MerkleRO Polynomial

/-! ## 1. Shape-Independent Multi-STARK Challenge Space -/

/-- Shape-independent Multi-STARK challenge type parameterized solely by static
`StarkSystem` bounds (`maxLogHeight`, `numQueries`, `commitPowBits`, `queryPowBits`),
completely independent of prover-chosen `active` masks, `logDegrees`, or `ClaimShape`:
- Round `0`: batch LogUp challenges `(β, γ) ∈ K × K`
- Round `1`: AIR constraint-batching challenge `α_air ∈ K`
- Round `2`: OOD evaluation point `ζ ∈ K`
- Round `3`: FRI batching challenge `α_fri ∈ K`
- Rounds `4 + i` (`i < maxLogHeight`): FRI folding round PoW + challenge `β_i ∈ K`
- Round `4 + maxLogHeight`: FRI query PoW + `numQueries` uniform indices in `Fin (2 ^ maxLogHeight)`
- Rounds `> 4 + maxLogHeight`: `PUnit` (unused padding rounds). -/
def DynChal (K : Type) (maxLogHeight numQueries commitPowBits queryPowBits : ℕ) : ℕ → Type
  | 0 => K × K
  | 1 => K
  | 2 => K
  | 3 => K
  | n + 4 =>
    if n < maxLogHeight then
      Fin (2 ^ commitPowBits) × K
    else if n = maxLogHeight then
      Fin (2 ^ queryPowBits) × (Fin numQueries → Fin (2 ^ maxLogHeight))
    else
      PUnit

/-- Total active Fiat–Shamir rounds in `DynChal`:
4 outer rounds (`(β, γ)`, `α_air`, `ζ`, `α_fri`) + `maxLogHeight` folding rounds + 1 query round. -/
def dynTotalRounds (maxLogHeight : ℕ) : ℕ := maxLogHeight + 5

instance dynChalFintype {K : Type} [Fintype K]
    (maxLogHeight numQueries commitPowBits queryPowBits : ℕ) :
    ∀ i, Fintype (DynChal K maxLogHeight numQueries commitPowBits queryPowBits i)
  | 0 => inferInstanceAs (Fintype (K × K))
  | 1 => inferInstanceAs (Fintype K)
  | 2 => inferInstanceAs (Fintype K)
  | 3 => inferInstanceAs (Fintype K)
  | n + 4 => by
    simp only [DynChal]
    split_ifs
    · exact inferInstanceAs (Fintype (Fin (2 ^ commitPowBits) × K))
    · exact inferInstanceAs (Fintype (Fin (2 ^ queryPowBits) × (Fin numQueries → Fin (2 ^ maxLogHeight))))
    · exact inferInstanceAs (Fintype PUnit)

instance dynChalNonempty {K : Type} [Nonempty K]
    (maxLogHeight numQueries commitPowBits queryPowBits : ℕ) :
    ∀ i, Nonempty (DynChal K maxLogHeight numQueries commitPowBits queryPowBits i)
  | 0 => inferInstanceAs (Nonempty (K × K))
  | 1 => inferInstanceAs (Nonempty K)
  | 2 => inferInstanceAs (Nonempty K)
  | 3 => inferInstanceAs (Nonempty K)
  | n + 4 => by
    simp only [DynChal]
    split_ifs
    · exact ⟨(⟨0, Nat.two_pow_pos _⟩, Classical.arbitrary K)⟩
    · exact ⟨(⟨0, Nat.two_pow_pos _⟩, fun _ => ⟨0, Nat.two_pow_pos _⟩)⟩
    · exact ⟨PUnit.unit⟩

instance dynChalDecidableEq {K : Type} [DecidableEq K]
    (maxLogHeight numQueries commitPowBits queryPowBits : ℕ) :
    ∀ i, DecidableEq (DynChal K maxLogHeight numQueries commitPowBits queryPowBits i)
  | 0 => inferInstanceAs (DecidableEq (K × K))
  | 1 => inferInstanceAs (DecidableEq K)
  | 2 => inferInstanceAs (DecidableEq K)
  | 3 => inferInstanceAs (DecidableEq K)
  | n + 4 => by
    simp only [DynChal]
    split_ifs
    · exact inferInstanceAs (DecidableEq (Fin (2 ^ commitPowBits) × K))
    · exact inferInstanceAs (DecidableEq (Fin (2 ^ queryPowBits) × (Fin numQueries → Fin (2 ^ maxLogHeight))))
    · exact inferInstanceAs (DecidableEq PUnit)

/-! ## 2. Exact Uniform Projection from `Fin (2^M)` to Any Dynamic Height `Fin (2^h)` (`h ≤ M`) -/

/-- Project a shape-independent query index `x : Fin (2^M)` onto a prover-chosen
LDE domain of log-height `h ≤ M` via exact remainder mod `2^h`. -/
def projectQueryIndex {M h : ℕ} (x : Fin (2 ^ M)) : Fin (2 ^ h) :=
  ⟨x.val % 2 ^ h, Nat.mod_lt x.val (Nat.two_pow_pos h)⟩

/-- Exact cardinality of every preimage fiber of `projectQueryIndex` when `h ≤ M`:
each `y : Fin (2^h)` has exactly `2 ^ (M - h)` preimages in `Fin (2^M)`. -/
theorem card_preimage_projectQueryIndex {M h : ℕ} (hle : h ≤ M) (y : Fin (2 ^ h)) :
    (Finset.univ.filter fun x : Fin (2 ^ M) => projectQueryIndex (h := h) x = y).card =
      2 ^ (M - h) := by
  have hmul : 2 ^ (M - h) * 2 ^ h = 2 ^ M := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  let f : Fin (2 ^ (M - h)) → Fin (2 ^ M) := fun q =>
    ⟨q.val * 2 ^ h + y.val, by
      have hq : q.val + 1 ≤ 2 ^ (M - h) := q.isLt
      have h1 : (q.val + 1) * 2 ^ h ≤ 2 ^ (M - h) * 2 ^ h := Nat.mul_le_mul_right _ hq
      rw [Nat.add_mul, Nat.one_mul, hmul] at h1
      have hy : y.val < 2 ^ h := y.isLt
      omega⟩
  have hfinj : Function.Injective f := by
    intro q₁ q₂ heq
    have hval := congrArg Fin.val heq
    dsimp only [f] at hval
    have hmul_eq : q₁.val * 2 ^ h = q₂.val * 2 ^ h := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos h) hmul_eq)
  have himg : (Finset.univ.filter fun x : Fin (2 ^ M) => projectQueryIndex (h := h) x = y) =
      Finset.univ.image f := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hproj
      have hmod : x.val % 2 ^ h = y.val := congrArg Fin.val hproj
      have hqlt : x.val / 2 ^ h < 2 ^ (M - h) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h), hmul]
        exact x.isLt
      refine ⟨⟨x.val / 2 ^ h, hqlt⟩, ?_⟩
      apply Fin.ext
      dsimp only [f]
      rw [← hmod, Nat.mul_comm, Nat.div_add_mod]
    · rintro ⟨q, rfl⟩
      apply Fin.ext
      dsimp only [projectQueryIndex, f]
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt y.isLt]
  rw [himg, Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]

/-- **Dynamic-height query fraction invariance:** if a bad query event `P` holds on at most a
fraction `ε` of `Fin (2^h)` (`h ≤ M`), then the pulled-back event `P ∘ projectQueryIndex` holds
on at most the EXACT same fraction `ε` of `Fin (2^M)`. -/
theorem fractionLE_projectQueryIndex {M h : ℕ} (hle : h ≤ M) {P : Fin (2 ^ h) → Prop} {ε : ℝ}
    (hP : FractionLE P ε) :
    FractionLE (fun x : Fin (2 ^ M) => P (projectQueryIndex x)) ε := by
  classical
  obtain ⟨S, hS_card, hS_mem⟩ := hP
  refine ⟨Finset.univ.filter fun x : Fin (2 ^ M) => projectQueryIndex (h := h) x ∈ S, ?_,
    fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS_mem _ hx⟩⟩
  have hpart : (Finset.univ.filter fun x : Fin (2 ^ M) => projectQueryIndex (h := h) x ∈ S).card =
      ∑ y ∈ S, (Finset.univ.filter fun x : Fin (2 ^ M) => projectQueryIndex (h := h) x = y).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact ⟨fun hmem => ⟨_, hmem, rfl⟩, fun ⟨_, hy, heq⟩ => heq ▸ hy⟩
    · intro y₁ _ y₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      exact hne (hx₁.symm.trans hx₂)
  rw [hpart]
  simp only [card_preimage_projectQueryIndex hle, Finset.sum_const, smul_eq_mul]
  rw [Fintype.card_fin] at hS_card ⊢
  have hmul : (2 ^ M : ℝ) = (2 ^ (M - h) : ℝ) * (2 ^ h : ℝ) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hpos : (0 : ℝ) ≤ (2 ^ (M - h) : ℝ) := by positivity
  push_cast at hS_card ⊢
  rw [hmul, mul_comm (S.card : ℝ)]
  nlinarith

/-! ## 3. Dynamic-Shape `Settles` for Adaptive Merkle Commitments -/

section DynamicSettles

variable {Msg : Type} {Chal : ℕ → Type} {T D : Type} [DecidableEq D]
  [DecidableEq (FSQuery Msg Chal (HashQuery T D))]

omit [DecidableEq D] in
/-- **Dynamic Merkle Commitment Stability (`Settles`):**
Suppose a log interpretation `interp l j m` depends on `l` ONLY through the openings
`Opens l root dims index rows` of roots `root ∈ digestsOf m` (for rounds `j < r`),
and ignores rounds `j ≥ r`. Then `interp` satisfies `CertiFri.Oracle.Settles`
with respect to `Hit digestsOf r`!

This works for ANY adaptive prover message type `Msg` whose `digestsOf m` extracts
all dynamically committed roots (batch `stage1` roots, shard `stage2` roots,
`quotient` roots, and FRI commit roots), without fixing `ClaimShape` in advance. -/
theorem settles_of_depends_on_digests {Msg₂ : Type}
    (digestsOf : ℕ → Msg → List D) (r : ℕ)
    (interp : Log (MerkleAnswer Msg Chal T D) → ℕ → Msg → Msg₂)
    (hge : ∀ l₁ l₂ j m, r ≤ j → interp l₁ j m = interp l₂ j m)
    (hcongr : ∀ (l₁ l₂ : Log (MerkleAnswer Msg Chal T D)) (j : ℕ) (m : Msg),
      j < r →
      (∀ root ∈ digestsOf j m, ∀ dims index rows,
        Opens l₁ root dims index rows ↔ Opens l₂ root dims index rows) →
      interp l₁ j m = interp l₂ j m) :
    Settles interp (Hit digestsOf r) := by
  refine ⟨?_, ?_⟩
  · intro l i t m c j m'
    by_cases hj : j < r
    · apply hcongr _ _ j m' hj
      intro root _ dims index rows
      exact opens_append_chal t m c
    · exact hge _ _ j m' (Nat.le_of_not_lt hj)
  · intro l e j m hment hnohit
    by_cases hj : j < r
    · apply hcongr _ _ j m hj
      intro root hroot dims index rows
      exact opens_concat_iff_of_not_hit (present_of_mentions hment hj hroot) hnohit
    · exact hge _ _ j m (Nat.le_of_not_lt hj)

end DynamicSettles

/-! ## 4. Unified Dynamic-Shape Adaptive ROM Soundness Theorem -/

section DynamicRomBound

open OracleComp

variable {Msg Msg₂ : Type} {Chal : ℕ → Type} {T D : Type}
  [DecidableEq Msg] [DecidableEq (FSQuery Msg Chal (HashQuery T D))]
  [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
  [Fintype D] [Nonempty D]

omit [DecidableEq Msg] in
/-- **Adaptive Dynamic-Shape ROM Soundness:**
Given:
- Any shape-independent challenge family `Chal : ℕ → Type`,
- A round-indexed digest extractor `digestsOf : ℕ → Msg → List D` bounded by `M` total digests per challenge query,
- A round-by-round sound state function `doomed` over `r` rounds with per-round error `≤ εmax`,
- A log interpretation `interp` settling on committed Merkle roots (`Settles interp (Hit digestsOf r)`),
- An adversary `adv` (`QueryBound Q`) outputting adaptive proof data `a` and raw messages `msgs a`,
- A verifier/extractor continuation `rest` (`QueryBound R`),

any event `E` that implies `¬ doomed r (out.2.mapIdx (interp l'))` on hit-free logs
occurs with probability at most:

    (Q + r + R) * εmax + (max M 3 + 3) * (Q + r + R) ^ 2 / (4 * |D|). -/
theorem soundness_dynamic_rom {α β : Type} {r M : ℕ}
    {digestsOf : ℕ → Msg → List D}
    (hM : ∀ (x : FSQuery Msg Chal (HashQuery T D)), (chalDigests digestsOf r x).length ≤ M)
    {doomed : ∀ i, Transcript Msg₂ Chal i → Prop}
    {interp : Log (MerkleAnswer Msg Chal T D) → ℕ → Msg → Msg₂}
    {ε : ℕ → ℝ} {εmax : ℝ}
    (hsound : RbrSound r doomed ε)
    (hε : ∀ i < r, ε i ≤ εmax) (h0 : 0 ≤ εmax) (hnil : doomed 0 .nil)
    (hset : Settles interp (Hit digestsOf r))
    {adv : OracleComp (MerkleAnswer Msg Chal T D) α} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : α → ℕ → Msg)
    {rest : α × Transcript Msg Chal r → OracleComp (MerkleAnswer Msg Chal T D) β} {R : ℕ}
    (hrest : ∀ out, (rest out).QueryBound R)
    {E : β → Log (MerkleAnswer Msg Chal T D) → Prop}
    (hE : ∀ out l b l', Outcome (fsExperiment r adv msgs) [] out l →
      Outcome (rest out) l b l' → E b l' → ¬ HasBad (Hit digestsOf r) l' →
      ¬ doomed r (out.2.mapIdx (interp l'))) :
    prob E ((fsExperiment r adv msgs).bind rest) [] ≤
      (Q + r + R) * εmax +
        ((max M 3 + 3 : ℕ) : ℝ) * (Q + r + R) ^ 2 / (4 * Fintype.card D) := by
  have h1 := prob_fsExperiment_bind_interp_le hsound hε h0 hnil hset hadv msgs hrest hE
  have hqb : ((fsExperiment r adv msgs).bind rest).QueryBound (Q + r + R) :=
    (queryBound_fsExperiment (r := r) hadv msgs).bind hrest
  have h2 := prob_hasBad_hit_le (digestsOf := digestsOf) (r := r) hM hqb
  have hsplit : prob E ((fsExperiment r adv msgs).bind rest) [] ≤
      prob (fun b l => E b l ∧ ¬ HasBad (Hit digestsOf r) l)
        ((fsExperiment r adv msgs).bind rest) [] +
      prob (fun _ l => HasBad (Hit digestsOf r) l)
        ((fsExperiment r adv msgs).bind rest) [] := by
    refine le_trans (prob_mono (fun b l h => ?_) _ _) (prob_or_le _ _ _ _)
    by_cases hbad : HasBad (Hit digestsOf r) l
    · exact Or.inr hbad
    · exact Or.inl ⟨h, hbad⟩
  refine hsplit.trans (add_le_add h1 ?_)
  simpa [Nat.cast_add] using h2

end DynamicRomBound

/-! ## 5. Per-Stage Multi-STARK Round Error Bounds (`FractionLE`) -/

section StageBounds

private lemma card_K_real_ne_zero : (Fintype.card K : ℝ) ≠ 0 := by
  rw [K.card_K]
  unfold CertiFri.P3.Goldilocks.order
  norm_num

/-- **Round 0 (`β` LogUp soundness, single-point separation) as `FractionLE`:**
When `m₀ ∈ S` has nonzero net weight `w m₀ ≠ 0` and no other `m' ∈ S` shares `fp m₀`,
at most a fraction `(S.card - 1) / |K|` of challenges `β : K` cancel the partial-fraction sum. -/
theorem fractionLE_logup_beta {α : Type*} [DecidableEq α] {S : Finset α}
    {fp : α → K} {w : α → K}
    {m₀ : α} (hm₀ : m₀ ∈ S) (hw : w m₀ ≠ 0)
    (hsep : ∀ m' ∈ S, m' ≠ m₀ → fp m' ≠ fp m₀) :
    FractionLE (fun β : K =>
      (∀ m ∈ S, β + fp m ≠ 0) ∧ (∑ m ∈ S, w m * (β + fp m)⁻¹) = 0)
      (((S.card - 1 : ℕ) : ℝ) / Fintype.card K) := by
  classical
  refine ⟨Finset.univ.filter fun β : K =>
      (∀ m ∈ S, β + fp m ≠ 0) ∧ (∑ m ∈ S, w m * (β + fp m)⁻¹) = 0, ?_,
    fun β hβ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hβ⟩
  rw [div_mul_cancel₀ _ card_K_real_ne_zero]
  exact_mod_cast card_logup_beta_bad_le hm₀ hw hsep

/-- **Round 0 (`(β, γ)` joint linear LogUp soundness) as `FractionLE` over `K × K`:**
When `m₀ ∈ S` has nonzero net weight `w m₀ ≠ 0` and distinct `fingerprintPoly` from all
other `m' ∈ S` (with every message length `≤ maxArity`), at most a **linear** fraction
`((S.card - 1) * (maxArity + 1)) / |K|` of challenge pairs `(β, γ) ∈ K × K` cancel the
LogUp sum — gaining `+27.4` formal bits on `RecV` over the quadratic pairwise bound! -/
theorem fractionLE_logup_pair {α : Type*} [DecidableEq α] {S : Finset α}
    {args : α → List Fp} {w : α → K} {maxArity : ℕ}
    {m₀ : α} (hm₀ : m₀ ∈ S) (hw : w m₀ ≠ 0)
    (hlen : ∀ m ∈ S, (args m).length ≤ maxArity)
    (hpoly : ∀ m' ∈ S, m' ≠ m₀ → fingerprintPoly (args m') ≠ fingerprintPoly (args m₀)) :
    FractionLE (fun p : K × K =>
      (∀ m ∈ S, p.1 + fingerprintEval p.2 (args m) ≠ 0) ∧
      (∑ m ∈ S, w m * (p.1 + fingerprintEval p.2 (args m))⁻¹) = 0)
      ((((S.card - 1) * (maxArity + 1) : ℕ) : ℝ) / Fintype.card K) := by
  classical
  refine ⟨Finset.univ.filter fun p : K × K =>
      (∀ m ∈ S, p.1 + fingerprintEval p.2 (args m) ≠ 0) ∧
      (∑ m ∈ S, w m * (p.1 + fingerprintEval p.2 (args m))⁻¹) = 0, ?_,
    fun p hp => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hp⟩
  have hmul : (((S.card - 1) * (maxArity + 1) : ℕ) : ℝ) / (Fintype.card K : ℝ) *
      (Fintype.card (K × K) : ℝ) =
      (((S.card - 1) * (maxArity + 1) * Fintype.card K : ℕ) : ℝ) := by
    rw [Fintype.card_prod]
    have hK := card_K_real_ne_zero
    push_cast
    field_simp [hK]
  rw [hmul]
  have hcard : (Finset.univ.filter fun p : K × K =>
      (∀ m ∈ S, p.1 + fingerprintEval p.2 (args m) ≠ 0) ∧
      (∑ m ∈ S, w m * (p.1 + fingerprintEval p.2 (args m))⁻¹) = 0).card ≤
      (S.card - 1) * (maxArity + 1) * Fintype.card K := by
    convert card_logup_pair_bad_le hm₀ hw hlen hpoly using 2
  exact_mod_cast hcard

/-- **Round 0 (`(β, γ)` complete linear LogUp soundness including zero-denominator events) as `FractionLE`:**
Covers BOTH the zero-denominator bad event across ALL trace lookup messages `S_all` (including
disabled/padding rows with `multiplicity = 0`, where `β + fp(γ, m) = 0` would collapse `np = nr = 0`
in `Air.lean`) AND LogUp partial-fraction cancellation on `S ⊆ S_all`.
Yields probability at most `((S.card - 1) * (maxArity + 1) + S_all.card) / |K|`
(`≤ S_all.card * (maxArity + 2) / |K|`). -/
theorem fractionLE_logup_pair_or_zero_denom {α : Type*} [DecidableEq α] {S S_all : Finset α}
    {args : α → List Fp} {w : α → K} {maxArity : ℕ}
    {m₀ : α} (hsub : S ⊆ S_all) (hm₀ : m₀ ∈ S) (hw : w m₀ ≠ 0)
    (hlen : ∀ m ∈ S, (args m).length ≤ maxArity)
    (hpoly : ∀ m' ∈ S, m' ≠ m₀ → fingerprintPoly (args m') ≠ fingerprintPoly (args m₀)) :
    FractionLE (fun p : K × K =>
      (∃ m ∈ S_all, p.1 + fingerprintEval p.2 (args m) = 0) ∨
      (∑ m ∈ S, w m * (p.1 + fingerprintEval p.2 (args m))⁻¹) = 0)
      ((((S.card - 1) * (maxArity + 1) + S_all.card : ℕ) : ℝ) / Fintype.card K) := by
  classical
  refine ⟨Finset.univ.filter fun p : K × K =>
      (∃ m ∈ S_all, p.1 + fingerprintEval p.2 (args m) = 0) ∨
      (∑ m ∈ S, w m * (p.1 + fingerprintEval p.2 (args m))⁻¹) = 0, ?_,
    fun p hp => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hp⟩
  have hmul : (((S.card - 1) * (maxArity + 1) + S_all.card : ℕ) : ℝ) / (Fintype.card K : ℝ) *
      (Fintype.card (K × K) : ℝ) =
      ((((S.card - 1) * (maxArity + 1) + S_all.card) * Fintype.card K : ℕ) : ℝ) := by
    rw [Fintype.card_prod]
    have hK := card_K_real_ne_zero
    push_cast
    field_simp [hK]
  rw [hmul]
  have hcard : (Finset.univ.filter fun p : K × K =>
      (∃ m ∈ S_all, p.1 + fingerprintEval p.2 (args m) = 0) ∨
      (∑ m ∈ S, w m * (p.1 + fingerprintEval p.2 (args m))⁻¹) = 0).card ≤
      ((S.card - 1) * (maxArity + 1) + S_all.card) * Fintype.card K := by
    convert card_logup_pair_bad_or_zero_denom_le hsub hm₀ hw hlen hpoly using 2
  exact_mod_cast hcard

/-- **Round 1 (`α_air` Horner constraint batching) as `FractionLE`:**
When at least one AIR constraint in `cs` is nonzero at the OOD point, at most a fraction
`(cs.length - 1) / |K|` of challenges `α : K` satisfy `hornerFold α cs = 0`. -/
theorem fractionLE_air_alpha {cs : List K} (h : ∃ c ∈ cs, c ≠ 0) :
    FractionLE (fun α : K => hornerFold α cs = 0)
      (((cs.length - 1 : ℕ) : ℝ) / Fintype.card K) := by
  classical
  refine ⟨Finset.univ.filter fun α : K => hornerFold α cs = 0, ?_,
    fun α hα => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hα⟩
  rw [div_mul_cancel₀ _ card_K_real_ne_zero]
  exact_mod_cast card_horner_bad_le h

/-- **Round 2a (coarse `ζ ∈ Fp`) as `FractionLE`:**
At most a fraction `1 / Goldilocks.order ^ 2` (`≈ 2^-128`) of challenges `ζ : K` land in the
base field (`ζ.c1 = 0 ∧ ζ.c2 = 0`). Prefer the tight `fractionLE_zeta_in_domain_or_shift`
(`2 * |D| / |K|`). -/
theorem fractionLE_zeta_in_base :
    FractionLE (fun ζ : K => ζ.c1 = 0 ∧ ζ.c2 = 0)
      (1 / ((CertiFri.P3.Goldilocks.order : ℝ) ^ 2)) := by
  classical
  refine ⟨Finset.univ.filter fun ζ : K => ζ.c1 = 0 ∧ ζ.c2 = 0, ?_,
    fun ζ hζ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hζ⟩
  have h := prob_in_baseField_eq
  rw [div_eq_iff card_K_real_ne_zero] at h
  exact le_of_eq h

/-- **Round 2a (tight `ζ ∈ D ∪ g⁻¹ • D`) as `FractionLE`:**
For any finite LDE domain `D : Finset K` and nonzero shift `g : K`, at most a fraction
`2 * |D| / |K|` of challenges `ζ : K` satisfy `ζ ∈ D ∨ ζ * g ∈ D`
(`169` bits in Goldilocks `Fp^3` at `|D| = 2^22`, vs `128` bits for `ζ ∈ Fp`). -/
theorem fractionLE_zeta_in_domain_or_shift (D : Finset K) {g : K} (hg : g ≠ 0) :
    FractionLE (fun ζ : K => ζ ∈ D ∨ ζ * g ∈ D)
      ((2 * D.card : ℝ) / Fintype.card K) := by
  classical
  refine ⟨Finset.univ.filter fun ζ : K => ζ ∈ D ∨ ζ * g ∈ D, ?_,
    fun ζ hζ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hζ⟩
  rw [div_mul_cancel₀ _ card_K_real_ne_zero]
  exact_mod_cast card_zeta_in_domain_or_shift_le D hg

/-- **Round 2b (`ζ` OOD polynomial root bound) as `FractionLE`:**
If the nonzero quotient-mismatch polynomial `P : K[X]` has `natDegree P ≤ d`, then at most a
fraction `d / |K|` of OOD points `ζ : K` satisfy `P.eval ζ = 0`. -/
theorem fractionLE_ood_poly_root {P : K[X]} {d : ℕ} (hP : P ≠ 0) (hdeg : P.natDegree ≤ d) :
    FractionLE (fun ζ : K => P.eval ζ = 0) ((d : ℝ) / Fintype.card K) := by
  classical
  refine ⟨P.roots.toFinset, ?_, fun ζ hζ =>
    Multiset.mem_toFinset.mpr ((mem_roots hP).mpr (IsRoot.def.mpr hζ))⟩
  rw [div_mul_cancel₀ _ card_K_real_ne_zero]
  exact_mod_cast (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hdeg)

/-- **Combined Round 2 (`ζ`) error bound:**
Union of `ζ ∈ D ∨ ζ * g ∈ D` (losing `2 * |D| / |K|`) and `P.eval ζ = 0` (losing `d / |K|`),
giving `(2 * |D| + d) / |K|` (`≈ 169` bits in `Fp^3` for `|D| = 2^22`, vs `128` bits from `ζ ∈ Fp`). -/
theorem fractionLE_zeta_ood (D : Finset K) {g : K} (hg : g ≠ 0)
    {P : K[X]} {d : ℕ} (hP : P ≠ 0) (hdeg : P.natDegree ≤ d) :
    FractionLE (fun ζ : K => (ζ ∈ D ∨ ζ * g ∈ D) ∨ P.eval ζ = 0)
      (((2 * D.card + d : ℕ) : ℝ) / Fintype.card K) := by
  have h := (fractionLE_zeta_in_domain_or_shift D hg).or (fractionLE_ood_poly_root hP hdeg)
  have heq : (2 * (D.card : ℝ)) / (Fintype.card K : ℝ) + (d : ℝ) / (Fintype.card K : ℝ) =
      (((2 * D.card + d : ℕ) : ℝ) / Fintype.card K) := by
    push_cast
    ring
  exact heq ▸ h

end StageBounds

/-! ## 6. Concrete `Fp^3` Tensor-STARK & Multi-Arity Instantiations of `soundness_dynamic_rom` -/

section ConcreteFp3DynamicRom

open CertiFri.Stark CertiFri.Exec CertiFri.Exec.Stark CertiFri.P3 CertiFri.P3.GoldilocksExt3 OracleComp

private lemma length_chalDigests_tensor_le {D : Type} [DecidableEq D]
    {fslots slots width : ℕ} (B : Bounds) (r : ℕ)
    (x : FSQuery (RawMsg Goldilocks GoldilocksExt3 D)
      (UTensorChal Fp3Model fslots slots width) (HashQuery Fp3Model D)) :
    (chalDigests (fun _ => digestsOf (F := Goldilocks) (EF := GoldilocksExt3) B) r x).length ≤
      (B.shards + 1) * r := by
  unfold chalDigests
  refine (MerkleRO.length_flatMap_zipIdx_le
    (fun _ => digestsOf (F := Goldilocks) (EF := GoldilocksExt3) B)
    (fun _ => B.shards + 1)
    (fun _ m => by unfold digestsOf; exact List.length_take_le _ _) _ 0).trans ?_
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (List.length_take_le _ _)

/-- **Concrete `Fp^3` Binary Tensor-STARK Adaptive Dynamic-ROM Soundness:**
Instantiates `soundness_dynamic_rom` directly for `CertiFri.P3.GoldilocksExt3.starkModel`
over the shape-independent challenge family `UTensorChal Fp3Model fslots slots width`,
discharging `RbrSound`, empty-transcript doom, and Merkle-hit `Settles` unconditionally
via `GoldilocksExt3.rbrSound_starkTensor_ud`, `sdoomedTensor_nil_fp3`, and
`settles_interpTensor_fp3`. -/
theorem soundness_dynamic_rom_starkTensor_fp3_ud
    {D : Type} [Inhabited D] [DecidableEq D] [Fintype D]
    {fslots slots width : ℕ}
    (sys : System Goldilocks D) (V : Variant Goldilocks GoldilocksExt3 D) (B : Bounds)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup ≤ 1)
    (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) {r : ℕ}
    {εmax : ℝ}
    (hε : ∀ i < r, roundErr starkModel sys B (pcsErrTensor (K := Fp3Model) sys 3 δ) i ≤ εmax)
    (h0 : 0 ≤ εmax)
    {α β : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) α}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → RawMsg Goldilocks GoldilocksExt3 D)
    {rest : α × Transcript (RawMsg Goldilocks GoldilocksExt3 D)
      (UTensorChal Fp3Model fslots slots width) r →
      OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) β}
    {R : ℕ} (hrest : ∀ out, (rest out).QueryBound R)
    {E : β → Log (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) → Prop}
    (hE : ∀ out l b l', Outcome (fsExperiment r adv msgs) [] out l →
      Outcome (rest out) l b l' → E b l' →
      ¬ HasBad (Hit (fun _ => digestsOf (F := Goldilocks) (EF := GoldilocksExt3) B) r) l' →
      ¬ sdoomedTensor (fslots := fslots) (slots := slots) (width := width)
          starkModel sys V (1 - δ) B r (out.2.mapIdx (interpTensor B r l'))) :
    prob E ((fsExperiment r adv msgs).bind rest) [] ≤
      (Q + r + R) * εmax +
        ((max ((B.shards + 1) * r) 3 + 3 : ℕ) : ℝ) * (Q + r + R) ^ 2 /
          (4 * Fintype.card D) :=
  soundness_dynamic_rom
    (digestsOf := fun _ => digestsOf (F := Goldilocks) (EF := GoldilocksExt3) B)
    (M := (B.shards + 1) * r)
    (length_chalDigests_tensor_le B r)
    (rbrSound_starkTensor_ud sys V B hδ hrate htwo hfslots hslots hcommit hquery hwidth r)
    hε h0
    (sdoomedTensor_nil_fp3 sys V (1 - δ) B)
    (settles_interpTensor_fp3 B r)
    hadv msgs hrest hE

/-- **Concrete `Fp^3` Multi-Arity (`2^a`, covering 8-ary folding) Tensor-STARK Adaptive
Dynamic-ROM Soundness:**
Instantiates `soundness_dynamic_rom` directly for `CertiFri.P3.GoldilocksExt3.starkModel`
with variable per-round folding arity `maxLogArity ≥ 1` (covering binary, 4-ary, and
8-ary FRI schedules) over shape-independent `UTensorChal Fp3Model fslots slots width`,
discharging `RbrSound`, empty-transcript doom, and Merkle-hit `Settles` unconditionally
via `GoldilocksExt3.rbrSound_starkTensorMulti_ud`, `sdoomedTensorMulti_nil_fp3`, and
`settles_interpTensor_fp3`. -/
theorem soundness_dynamic_rom_starkTensorMulti_fp3_ud
    {D : Type} [Inhabited D] [DecidableEq D] [Fintype D]
    {fslots slots width : ℕ}
    (sys : System Goldilocks D) (hcap : 0 < sys.fri.maxLogArity)
    (V : Variant Goldilocks GoldilocksExt3 D) (B : Bounds)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup ≤ 1)
    (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) {r : ℕ}
    {εmax : ℝ}
    (hε : ∀ i < r, roundErr starkModel sys B (pcsErrTensor (K := Fp3Model) sys 3 δ) i ≤ εmax)
    (h0 : 0 ≤ εmax)
    {α β : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) α}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → RawMsg Goldilocks GoldilocksExt3 D)
    {rest : α × Transcript (RawMsg Goldilocks GoldilocksExt3 D)
      (UTensorChal Fp3Model fslots slots width) r →
      OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) β}
    {R : ℕ} (hrest : ∀ out, (rest out).QueryBound R)
    {E : β → Log (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) → Prop}
    (hE : ∀ out l b l', Outcome (fsExperiment r adv msgs) [] out l →
      Outcome (rest out) l b l' → E b l' →
      ¬ HasBad (Hit (fun _ => digestsOf (F := Goldilocks) (EF := GoldilocksExt3) B) r) l' →
      ¬ sdoomedTensorMulti (fslots := fslots) (slots := slots) (width := width)
          starkModel sys hcap V (1 - δ) B r (out.2.mapIdx (interpTensor B r l'))) :
    prob E ((fsExperiment r adv msgs).bind rest) [] ≤
      (Q + r + R) * εmax +
        ((max ((B.shards + 1) * r) 3 + 3 : ℕ) : ℝ) * (Q + r + R) ^ 2 /
          (4 * Fintype.card D) :=
  soundness_dynamic_rom
    (digestsOf := fun _ => digestsOf (F := Goldilocks) (EF := GoldilocksExt3) B)
    (M := (B.shards + 1) * r)
    (length_chalDigests_tensor_le B r)
    (rbrSound_starkTensorMulti_ud sys hcap V B hδ hrate htwo hfslots hslots hcommit hquery hwidth r)
    hε h0
    (sdoomedTensorMulti_nil_fp3 sys hcap V (1 - δ) B)
    (settles_interpTensor_fp3 B r)
    hadv msgs hrest hE

end ConcreteFp3DynamicRom

end Ix.Cert.MultiStark
