import Ix.Cert.Compression.StarkShrinker
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! # Endpoint 1b: Native `Fp^3` `v6-zk` Hiding STARK Shrinker Certification

Models and certifies the 1-circuit fixed-layout Native `Fp^3` `v6-zk` hiding STARK Shrinker
matching `multi-stark/src/p3_adapter/{domain_blake3,zk}.rs` and `CertiFriProofs/Exec/SoundnessZk.lean`
byte-for-byte, in the **same pure Random Oracle Model** (ZERO elliptic curves, ZERO SRS,
ZERO `gnark` assumptions):

1. **16-Byte BLAKE3-CTR Leaf Salting & Strict `v6-zk` Domain Separation:**
   - `ZK_LEAF_SALT_BYTES = 16`, `PREPROCESSED_SALT_CONTEXT = "multi-stark/v6-zk/preprocessed-salt"`,
   - `salted_merkle_binding_of_no_collision`: salted Merkle openings bind BOTH `row` and `salt`,
   - `v6Zk_domains_disjoint_from_v6_and_plain`: all 5 `v6-zk` BLAKE3 `derive_key` domains
     (`zkMerkleLeaf`, `zkMerkleCompress`, `zkTranscriptSingle`, `zkTranscriptBatch`,
     `zkVerifyingKey`) are pairwise distinct and separated from `v6` and `plain` (`v5`).
2. **2× Interleaved Odd-Coset Witness Blinding & Half-Stride Telescoping Quotient Slicing:**
   - `zk_oddCoset_blinding_agrees_on_trace`, `zk_oddCoset_blinding_natDegree_lt`,
   - `zk_quotient_telescoping_sum`, `zk_blindedSlice_natDegree_lt`, `zk_quotient_degree_lt`.
3. **Exact Cubic Extension `Fp3Model = GF(p)[X]/(X^3 - X - 1)` & `W_R ≥ 4` Randomizer Span:**
   - Kernel-checked irreducibility proof `cubicTrinomial_no_root` (binary-powered Frobenius
     `X^p - X`, ZERO `native_decide`!),
   - `fp3_tensor4_spans_of_not_base` & `fp3_tensor4_span_failure_prob_le` (`≤ 2 / p^2 < 1 / 2^126`),
   - Constructive negative control `negControl_fp3_tensor3_span_failure_ge` (`≥ 1 / p > 1 / 2^64`).
4. **All 4 `v6-zk` Guardrails + Blinded Interior Accumulators & Pure-ROM 128-Bit Soundness:**
   - Guardrail 1: `N ≥ next_pow2(2Q + 2D)` (`minZkLogDegree`) & `logN + 1 + lb ≤ 32`,
   - Guardrail 2: `W_R ≥ 4` (`ZK_RANDOMIZER_WIDTH`),
   - Guardrail 3: `1 ≤ logBlowup ∧ zkQuotientDegree d ≤ 2 ^ logBlowup` (implies `d ≤ 2^logBlowup`),
   - Guardrail 4: Blinded interior `intermediate_accumulators`, 1-circuit zero-leakage layout,
     16B leaf salting, 2× odd-coset blinding, and strict `v6-zk` BLAKE3 `derive_key` domains.
   - `starkShrinker_v6zk_sound_128` & `starkShrinker_v6zk_concrete_prob_128`.
5. **5 Constructive Negative Controls:**
   - `negControl_zkShrinker_rejects_wr3` (`W_R = 3` + `≥ 1/p > 1/2^64` tensor span failure),
   - `negControl_zkShrinker_rejects_small_trace` (`N = 256 < 2*160 + 2*3`),
   - `negControl_zkShrinker_rejects_degree5_lb2` (`d = 5, lb = 2` since `zkQuotientDegree 5 = 8 > 4`),
   - `negControl_zkShrinker_rejects_cross_mode_replay` (`v6` ↔ `v6-zk` bidirectional rejection),
   - `negControl_zkShrinker_rejects_unblinded_accumulators` (unblinded interior accumulators /
     missing leaf salt / missing odd-coset blinding / multi-circuit leak).

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`,
strictly `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ix.Cert.Compression.StarkShrinkerZk

open Polynomial
open CertiFri.Oracle
open CertiFri.Oracle.OracleComp
open Ix.Cert.Aggr.MonolithicRom
open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.FriVerifier
open Ix.Cert.Compression.StarkShrinker

/-! ## 1. `v6-zk` Constants, 16-Byte Leaf Salting, & Salted Merkle Binding -/

/-- Mandatory minimum base-field randomizer width (`W_R ≥ 4`) in `multi-stark/v6-zk`. -/
def ZK_RANDOMIZER_WIDTH : ℕ := 4

/-- Mandatory leaf salt length in bytes (`16` bytes = 128 bits) in `multi-stark/v6-zk`. -/
def ZK_LEAF_SALT_BYTES : ℕ := 16

/-- Goldilocks two-adicity (`2 ^ 32 ∣ p - 1`). -/
def GOLDILOCKS_TWO_ADICITY : ℕ := 32

/-- Exact `derive_key` context string for deterministic preprocessed-matrix leaf salting
in `multi-stark/src/p3_adapter/zk.rs`. -/
def PREPROCESSED_SALT_CONTEXT : String := "multi-stark/v6-zk/preprocessed-salt"

/-- 16-byte per-leaf salt (`Salt16`, 128 bits of entropy). -/
structure Salt16 where
  bytes : Fin ZK_LEAF_SALT_BYTES → UInt8
  deriving DecidableEq

/-- Evaluating a Merkle authentication path bottom-up from leaf digest `acc`
along index `idx` and sibling path `path`. -/
def evalMerklePath {D : Type} (compress : D → D → D) : ℕ → D → List D → D
  | _, acc, [] => acc
  | idx, acc, sib :: rest =>
    let next := if idx % 2 = 0 then compress acc sib else compress sib acc
    evalMerklePath compress (idx / 2) next rest

/-- **Salted Merkle Binding (`salted_merkle_binding_of_no_collision`):**
A collision-free Merkle tree with 16-byte salted leaves `(row, salt)` binds BOTH `row` and
`salt`: two valid authentication paths at the same index against the same root must agree
on both the leaf row and the 16-byte salt. -/
theorem salted_merkle_binding_of_no_collision {Row Salt D : Type}
    (hashLeaf : Row × Salt → D) (compress : D → D → D)
    (hLeafInj : Function.Injective hashLeaf)
    (hCompInj : ∀ l₁ r₁ l₂ r₂, compress l₁ r₁ = compress l₂ r₂ → l₁ = l₂ ∧ r₁ = r₂)
    {idx : ℕ} {row₁ row₂ : Row} {salt₁ salt₂ : Salt} {path₁ path₂ : List D}
    (hlen : path₁.length = path₂.length)
    (hroot : evalMerklePath compress idx (hashLeaf (row₁, salt₁)) path₁ =
      evalMerklePath compress idx (hashLeaf (row₂, salt₂)) path₂) :
    row₁ = row₂ ∧ salt₁ = salt₂ := by
  have hpath : ∀ (n : ℕ) (p₁ p₂ : List D) (i : ℕ) (a₁ a₂ : D),
      p₁.length = n → p₂.length = n →
      evalMerklePath compress i a₁ p₁ = evalMerklePath compress i a₂ p₂ → a₁ = a₂ := by
    intro n
    induction n with
    | zero =>
      intro p₁ p₂ i a₁ a₂ hp₁ hp₂ heq
      cases p₁ with
      | nil =>
        cases p₂ with
        | nil => exact heq
        | cons _ _ => simp at hp₂
      | cons _ _ => simp at hp₁
    | succ n ih =>
      intro p₁ p₂ i a₁ a₂ hp₁ hp₂ heq
      cases p₁ with
      | nil => simp at hp₁
      | cons s₁ r₁ =>
        cases p₂ with
        | nil => simp at hp₂
        | cons s₂ r₂ =>
          simp only [evalMerklePath] at heq
          have hnext := ih r₁ r₂ (i / 2) _ _ (by simpa using hp₁) (by simpa using hp₂) heq
          split_ifs at hnext with hmod
          · exact (hCompInj a₁ s₁ a₂ s₂ hnext).1
          · exact (hCompInj s₁ a₁ s₂ a₂ hnext).2
  have hd : hashLeaf (row₁, salt₁) = hashLeaf (row₂, salt₂) :=
    hpath path₁.length path₁ path₂ idx _ _ rfl hlen.symm hroot
  have hpair := hLeafInj hd
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

/-- `PREPROCESSED_SALT_CONTEXT` is strictly distinct from every `Blake3Domain.context`. -/
theorem v6Zk_preprocessed_salt_context_distinct (d : Blake3Domain) :
    some PREPROCESSED_SALT_CONTEXT ≠ d.context := by
  cases d <;> decide

/-- All 5 `v6-zk` BLAKE3 `derive_key` domains are pairwise distinct from one another AND
from every `v6` and `plain` (`v5`) domain in both `keyWords` and `context`. -/
theorem v6Zk_domains_disjoint_from_v6_and_plain {dZk dOther : Blake3Domain}
    (hZk : dZk.isZk = true) (hOther : dOther.isZk = false) :
    dZk.keyWords ≠ dOther.keyWords ∧ dZk.context ≠ dOther.context := by
  refine ⟨Blake3Domain.v6Zk_keyWords_ne_nonZk hZk hOther, fun hctx => ?_⟩
  have h := Blake3Domain.context_injective hctx
  subst h
  rw [hZk] at hOther
  cases hOther

/-! ## 2. 2× Odd-Coset Witness Blinding, Half-Stride Telescoping Quotient Slicing, & Degree Arithmetic -/

section OddCosetAndTelescoping

variable {K : Type*} [Field K]

/-- **2× odd-coset witness blinding preserves trace evaluations:**
adding `(X^N - 1) * b(X)` to a trace polynomial `T₀(X)` leaves all evaluations
on the `N`-th roots of unity `H_N = {x | x^N = 1}` unchanged. -/
theorem zk_oddCoset_blinding_agrees_on_trace (N : ℕ) (T₀ b : K[X]) (x : K) (hx : x ^ N = 1) :
    (T₀ + (X ^ N - 1) * b).eval x = T₀.eval x := by
  simp [eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_one, hx]

/-- **2× odd-coset witness blinding degree bound:**
if `deg(T₀) < N` and `deg(b) < N` (`0 < N`), then `T(X) = T₀(X) + (X^N - 1) * b(X)`
has degree `< 2 * N` (matching the 2× doubled evaluation domain of `v6-zk`). -/
theorem zk_oddCoset_blinding_natDegree_lt {N : ℕ} (hN : 0 < N) {T₀ b : K[X]}
    (hT₀ : T₀.natDegree < N) (hb : b.natDegree < N) :
    (T₀ + (X ^ N - 1) * b).natDegree < 2 * N := by
  have hZ : ((X : K[X]) ^ N - 1).natDegree ≤ N :=
    (natDegree_sub_le ((X : K[X]) ^ N) 1).trans (max_le (natDegree_X_pow_le N) (by simp))
  have hmul : (((X : K[X]) ^ N - 1) * b).natDegree < 2 * N := by
    by_cases hb0 : b = 0
    · simp [hb0]; omega
    · refine lt_of_le_of_lt natDegree_mul_le ?_
      omega
  exact lt_of_le_of_lt (natDegree_add_le T₀ _) (max_lt (by omega) hmul)

/-- Extended telescoping randomizer sequence `ρ_ext(i)` (`0` at `i ≥ 2 * q - 1`). -/
noncomputable def zkTelescopeShift (q : ℕ) (ρ : Fin (2 * q - 1) → K[X]) (i : ℕ) : K[X] :=
  if h : i < 2 * q - 1 then ρ ⟨i, h⟩ else 0

/-- Half-stride blinded quotient slice `c'_k(X) = c_k(X) - ρ_{k-1}(X) + X^N * ρ_k(X)`
(matching `multi-stark/src/p3_adapter/zk.rs`). -/
noncomputable def zkBlindedSlice (N q : ℕ) (c : Fin (2 * q) → K[X]) (ρ : Fin (2 * q - 1) → K[X])
    (k : Fin (2 * q)) : K[X] :=
  c k - (if k.val = 0 then 0 else zkTelescopeShift q ρ (k.val - 1)) +
    X ^ N * zkTelescopeShift q ρ k.val

/-- **Exact half-stride telescoping quotient identity:**
for ANY `2 * q` quotient slices `c_k(X)` (`q ≥ 1`) and ANY `2 * q - 1`
blinding polynomials `ρ_k(X)`, `∑_{k < 2q} X^{kN} c'_k(X) = ∑_{k < 2q} X^{kN} c_k(X)`. -/
theorem zk_quotient_telescoping_sum (N q : ℕ) (hq : 1 ≤ q)
    (c : Fin (2 * q) → K[X]) (ρ : Fin (2 * q - 1) → K[X]) :
    ∑ k : Fin (2 * q), X ^ (k.val * N) * zkBlindedSlice N q c ρ k =
      ∑ k : Fin (2 * q), X ^ (k.val * N) * c k := by
  let g : ℕ → K[X] := fun i =>
    if i = 0 then 0 else X ^ (i * N) * zkTelescopeShift q ρ (i - 1)
  have hterm : ∀ k : Fin (2 * q),
      X ^ (k.val * N) * zkBlindedSlice N q c ρ k =
        X ^ (k.val * N) * c k + (g (k.val + 1) - g k.val) := by
    intro k
    unfold zkBlindedSlice
    have hsucc : g (k.val + 1) = X ^ (k.val * N) * (X ^ N * zkTelescopeShift q ρ k.val) := by
      dsimp only [g]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [Nat.add_mul, one_mul, pow_add, mul_assoc]
    have hcur : g k.val =
        X ^ (k.val * N) * (if k.val = 0 then 0 else zkTelescopeShift q ρ (k.val - 1)) := by
      dsimp only [g]
      split_ifs <;> ring
    rw [hsucc, hcur]
    ring
  simp_rw [hterm, Finset.sum_add_distrib]
  have htele : ∑ k : Fin (2 * q), (g (k.val + 1) - g k.val) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => g (i + 1) - g i) (2 * q)]
    rw [Finset.sum_range_sub g (2 * q)]
    have hg0 : g 0 = 0 := by simp [g]
    have hgtop : g (2 * q) = 0 := by
      dsimp only [g, zkTelescopeShift]
      have hne : 2 * q ≠ 0 := by omega
      simp [hne]
    rw [hg0, hgtop, sub_zero]
  rw [htele, add_zero]

/-- **Half-stride blinded quotient slices stay in the 2× doubled RS code (`deg < 2N`):** -/
theorem zk_blindedSlice_natDegree_lt {N q : ℕ} (hN : 0 < N)
    {c : Fin (2 * q) → K[X]} {ρ : Fin (2 * q - 1) → K[X]}
    (hc : ∀ k, (c k).natDegree < N) (hρ : ∀ j, (ρ j).natDegree < N) (k : Fin (2 * q)) :
    (zkBlindedSlice N q c ρ k).natDegree < 2 * N := by
  have hshift : ∀ i, (zkTelescopeShift q ρ i).natDegree < N := by
    intro i
    unfold zkTelescopeShift
    split_ifs with h
    · exact hρ ⟨i, h⟩
    · simp; exact hN
  unfold zkBlindedSlice
  have hleft : (c k - if k.val = 0 then 0 else zkTelescopeShift q ρ (k.val - 1)).natDegree < N := by
    refine lt_of_le_of_lt (natDegree_sub_le (c k) _) (max_lt (hc k) ?_)
    split_ifs
    · simp; exact hN
    · exact hshift (k.val - 1)
  have hright : ((X : K[X]) ^ N * zkTelescopeShift q ρ k.val).natDegree < 2 * N := by
    by_cases hz : zkTelescopeShift q ρ k.val = 0
    · simp [hz]; omega
    · refine lt_of_le_of_lt natDegree_mul_le ?_
      have h1 : ((X : K[X]) ^ N).natDegree ≤ N := natDegree_X_pow_le N
      have h2 := hshift k.val
      omega
  exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (by omega) hright)

end OddCosetAndTelescoping

/-- Ceiling base-2 logarithm `⌈log₂ n⌉` (matching Rust `n.next_power_of_two().trailing_zeros()`). -/
def nextPow2Log (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- `n ≤ 2 ^ nextPow2Log n` for every `n : ℕ`. -/
theorem le_two_pow_nextPow2Log (n : ℕ) : n ≤ 2 ^ nextPow2Log n := by
  unfold nextPow2Log
  split_ifs with h
  · simpa using h
  · have hpos : n - 1 ≠ 0 := by omega
    have h2 : n - 1 < 2 ^ (Nat.log2 (n - 1) + 1) :=
      (Nat.log2_lt hpos).mp (Nat.lt_succ_self _)
    omega

/-- Minimality of `nextPow2Log`: if `n ≤ 2 ^ k`, then `nextPow2Log n ≤ k`. -/
theorem nextPow2Log_le_of_le_pow {n k : ℕ} (h : n ≤ 2 ^ k) : nextPow2Log n ≤ k := by
  unfold nextPow2Log
  split_ifs with hle
  · exact Nat.zero_le _
  · have hlt : n - 1 < 2 ^ k := by omega
    have hlog : Nat.log2 (n - 1) < k := (Nat.log2_lt (by omega)).mpr hlt
    omega

/-- Minimum `v6-zk` trace log-height `log₂(next_pow2(2 * Q + 2 * D))`,
matching `multi-stark/src/p3_adapter/zk.rs::min_zk_log_degree`. -/
def minZkLogDegree (numQueries extDegree : ℕ) : ℕ :=
  nextPow2Log (2 * numQueries + 2 * extDegree)

/-- `v6-zk` quotient degree multiple `next_pow2(max(d, 1))`, matching
`multi-stark` `Circuit::quotient_degree_for(is_zk = true)`. -/
def zkQuotientDegree (maxConstraintDegree : ℕ) : ℕ :=
  2 ^ nextPow2Log (max maxConstraintDegree 1)

/-- Non-ZK `v6` quotient degree multiple `next_pow2(max(d, 2) - 1)`. -/
def nonZkQuotientDegree (maxConstraintDegree : ℕ) : ℕ :=
  2 ^ nextPow2Log (max maxConstraintDegree 2 - 1)

/-- Degree-bound justification for `zkQuotientDegree`: for constraints of degree `d ≥ 1`
evaluated on 2× odd-coset blinded trace polynomials of degree `< 2 * N`, after dividing
by `Z_H(X)` (`deg = N`), the quotient degree `(2 * d - 1) * N` is `< 2 * N * zkQuotientDegree d`. -/
theorem zk_quotient_degree_lt {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) :
    (2 * d - 1) * N < 2 * N * zkQuotientDegree d := by
  have hd_le : d ≤ zkQuotientDegree d := by
    unfold zkQuotientDegree
    exact (Nat.le_max_left d 1).trans (le_two_pow_nextPow2Log _)
  have h1 : 2 * d - 1 < 2 * zkQuotientDegree d := by omega
  calc (2 * d - 1) * N < (2 * zkQuotientDegree d) * N := Nat.mul_lt_mul_of_pos_right h1 hN
    _ = 2 * N * zkQuotientDegree d := by ring

/-! ## 3. Exact Cubic Extension `Fp3Model = GF(p)[X]/(X^3 - X - 1)` & `W_R ≥ 4` Tensor Span -/

/-- Exact Goldilocks cubic extension `Fp3Model = GF(p)[X] / (X^3 - X - 1)` over `GoldilocksF`. -/
@[ext]
structure Fp3Model where
  c0 : GoldilocksF
  c1 : GoldilocksF
  c2 : GoldilocksF
  deriving DecidableEq

namespace Fp3Model

/-- Embed a Goldilocks base-field element into `Fp3Model`. -/
def embed (a : GoldilocksF) : Fp3Model := ⟨a, 0, 0⟩

/-- Generator `X` of `GF(p)[X] / (X^3 - X - 1)`. -/
def genX : Fp3Model := ⟨0, 1, 0⟩

instance : Zero Fp3Model := ⟨⟨0, 0, 0⟩⟩
instance : One Fp3Model := ⟨⟨1, 0, 0⟩⟩
instance : Add Fp3Model := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩⟩
instance : Neg Fp3Model := ⟨fun a => ⟨-a.c0, -a.c1, -a.c2⟩⟩
instance : Sub Fp3Model := ⟨fun a b => ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩⟩

/-- Multiplication modulo `X^3 - X - 1` (`X^3 = X + 1`, `X^4 = X^2 + X`). -/
instance : Mul Fp3Model := ⟨fun a b =>
  ⟨a.c0 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1,
   a.c0 * b.c1 + a.c1 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1 + a.c2 * b.c2,
   a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + a.c2 * b.c2⟩⟩

@[simp] theorem zero_c0 : (0 : Fp3Model).c0 = 0 := rfl
@[simp] theorem zero_c1 : (0 : Fp3Model).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : Fp3Model).c2 = 0 := rfl
@[simp] theorem one_c0 : (1 : Fp3Model).c0 = 1 := rfl
@[simp] theorem one_c1 : (1 : Fp3Model).c1 = 0 := rfl
@[simp] theorem one_c2 : (1 : Fp3Model).c2 = 0 := rfl
@[simp] theorem embed_c0 (a : GoldilocksF) : (embed a).c0 = a := rfl
@[simp] theorem embed_c1 (a : GoldilocksF) : (embed a).c1 = 0 := rfl
@[simp] theorem embed_c2 (a : GoldilocksF) : (embed a).c2 = 0 := rfl
@[simp] theorem add_c0 (a b : Fp3Model) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 (a b : Fp3Model) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : Fp3Model) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem neg_c0 (a : Fp3Model) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 (a : Fp3Model) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : Fp3Model) : (-a).c2 = -a.c2 := rfl
@[simp] theorem sub_c0 (a b : Fp3Model) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 (a b : Fp3Model) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : Fp3Model) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem mul_c0 (a b : Fp3Model) :
    (a * b).c0 = a.c0 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1 := rfl
@[simp] theorem mul_c1 (a b : Fp3Model) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1 + a.c2 * b.c2 := rfl
@[simp] theorem mul_c2 (a b : Fp3Model) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + a.c2 * b.c2 := rfl

instance : CommRing Fp3Model where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := nsmulRec
  add_comm a b := by ext <;> simp <;> ring
  zsmul := zsmulRec
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  mul_comm a b := by ext <;> simp <;> ring
  npow := npowRec

/-- Equivalence `Fp3Model ≃ GoldilocksF × GoldilocksF × GoldilocksF`. -/
def toProdEquiv : Fp3Model ≃ GoldilocksF × GoldilocksF × GoldilocksF where
  toFun a := (a.c0, a.c1, a.c2)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv a := by cases a; rfl
  right_inv t := by rcases t with ⟨a, b, c⟩; rfl

instance : Fintype Fp3Model := Fintype.ofEquiv _ toProdEquiv.symm

theorem card_fp3Model : Fintype.card Fp3Model = CertiFri.P3.Goldilocks.order ^ 3 := by
  rw [Fintype.card_congr toProdEquiv, Fintype.card_prod, Fintype.card_prod]
  have hcard : Fintype.card GoldilocksF = CertiFri.P3.Goldilocks.order := ZMod.card _
  rw [hcard]
  ring

/-- Adjugate of multiplication by `a` in `GF(p)[X] / (X^3 - X - 1)`. -/
def adjugate (a : Fp3Model) : Fp3Model :=
  let a02 := a.c0 + a.c2
  ⟨a02 * a02 - a.c1 * (a.c1 + a.c2),
   a.c2 * a.c2 - a.c0 * a.c1,
   a.c1 * a.c1 - a.c2 * a02⟩

/-- Field norm `N_{Fp^3 / Fp}(a)` (determinant of multiplication by `a`). -/
def norm (a : Fp3Model) : GoldilocksF :=
  let adj := a.adjugate
  a.c0 * adj.c0 + a.c2 * adj.c1 + a.c1 * adj.c2

theorem mul_adjugate (a : Fp3Model) : a * a.adjugate = embed a.norm := by
  ext <;> simp [adjugate, norm, embed] <;> ring

/-! ### Fast Kernel-Checked Binary-Powering Proof of Irreducibility of `X^3 - X - 1` -/

private def ofNat3 (t : ℕ × ℕ × ℕ) : Fp3Model := ⟨(t.1 : GoldilocksF), (t.2.1 : GoldilocksF), (t.2.2 : GoldilocksF)⟩

private def subMod (p a b : ℕ) : ℕ := (a % p + p - b % p) % p

private theorem subMod_cast (a b : ℕ) :
    ((subMod goldilocksP a b : ℕ) : GoldilocksF) = (a : GoldilocksF) - (b : GoldilocksF) := by
  unfold subMod
  have hlt : b % goldilocksP < goldilocksP := Nat.mod_lt b (by decide)
  have hle : b % goldilocksP ≤ a % goldilocksP + goldilocksP := by omega
  rw [ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod]
  have hp0 : (goldilocksP : GoldilocksF) = 0 := ZMod.natCast_self _
  rw [hp0, add_zero]

private def fp3MulNat (p : ℕ) (a b : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let (a0, a1, a2) := a
  let (b0, b1, b2) := b
  ((a0 * b0 + a1 * b2 + a2 * b1) % p,
   (a0 * b1 + a1 * b0 + a1 * b2 + a2 * b1 + a2 * b2) % p,
   (a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2) % p)

private theorem ofNat3_fp3MulNat (a b : ℕ × ℕ × ℕ) :
    ofNat3 (fp3MulNat goldilocksP a b) = ofNat3 a * ofNat3 b := by
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  ext <;> simp [ofNat3, fp3MulNat, ZMod.natCast_mod]

private def frobSqChain : List (ℕ × ℕ × ℕ) := [
  (0, 1, 0),
  (0, 0, 1),
  (0, 1, 1),
  (2, 3, 2),
  (16, 28, 21),
  (1432, 2513, 1897),
  (11584946, 20330163, 15346786),
  (758216295635152, 1330576843394428, 1004422742303477),
  (17372766340139064469, 9557085918088446932, 15354445961624571197),
  (3509459721280925154, 11514812652314720115, 1200991702222341375),
  (6841103724816679185, 11222150267719621178, 15563510825788724668),
  (9440462931311328392, 13857090502216904544, 17589633011169988068),
  (16819528958367300955, 8615056102248217534, 569232632836573868),
  (17140222094744348464, 14165951618730066331, 17152841575636035006),
  (8418318907588004139, 22428703637656057, 6582359677925617020),
  (767722960220274515, 14627373815190563013, 8710411886900515978),
  (385693368393256935, 8603804293785492277, 6124110923987225995),
  (2853122117199794220, 7512198633866561946, 16971451762190044101),
  (12151902958023338546, 13484842841101145280, 3582304359794017908),
  (10224992181480688384, 16633454005149103480, 13033421829960845217),
  (13449938289856480782, 7374674915123898758, 5845395811342087090),
  (10696057721481665275, 8798528314102901544, 16917761466840770533),
  (13537386044881551521, 3705677173898304428, 8032460359406040182),
  (13859138746956445181, 1776075322834998865, 2909434198963183692),
  (14764577181388025928, 17746581676041222082, 12108162915781342237),
  (4003639200154987791, 15739832279603431212, 2427710258508434300),
  (1428184821664116465, 3486696471522010340, 16316167142954428440),
  (13079628040886172071, 557744702066876284, 11172352635674949692),
  (9787163918615041340, 15146493807739145252, 5331292245756089361),
  (9799591891816256491, 17330899312865648572, 13450600588678059457),
  (15598322179228703257, 9325043480286899252, 4648274645770861737),
  (628221846932513290, 4594102871486117174, 5907837206726511540),
  (4313033625783026847, 4123756567369592585, 13756005300681981762),
  (12607646404735112778, 13327610258238037934, 17734291532653803390),
  (925354551479961996, 12030666936299136886, 7461415465917693229),
  (13044331408263984252, 11461860201702712917, 573795447562038500),
  (3212809479733501104, 18163099207507449997, 9473894190016332280),
  (6791493080144351004, 14727176535711091984, 3066030207150266780),
  (873402866144866480, 10250051513113493641, 5897162659479242306),
  (6961751116629775684, 8264568878050814716, 3483752813938653528),
  (4358114576167036254, 14139296206291393548, 1451789787186608704),
  (14292943501030182470, 5274624153182619279, 2630426797643177756),
  (6900172909268517948, 12021914562984351733, 5679212788924843667),
  (11559249486530646911, 5799295627439068525, 10782907988370352600),
  (3927598984488543255, 18274156811450324139, 12277857525045962116),
  (8775030492173327093, 2935290626899303650, 311936205690203242),
  (15468691063565846067, 9976909525582568813, 17672104663686149782),
  (17532020344685104948, 18107403598486519936, 748845027959109220),
  (8854585105112987765, 13589489451603127301, 9357132992060661220),
  (5502671418524984555, 13850104363691969497, 138165383596815434),
  (13658946683378723015, 16220459973757844118, 15688061723879106835),
  (1954228645075490959, 2246885487649248541, 7915590249961340229),
  (4070455656583887321, 11541362485559587522, 7330029841607960957),
  (748266820931762279, 2106639283174989949, 5620466764628126715),
  (2410863489923985612, 3941615857195757976, 5548256865122182134),
  (3630708328067381459, 1747863527317022142, 9845007181724105359),
  (4715927453802294321, 9424413537322174545, 10212156649832762384),
  (9706472742729618523, 13146487865350974557, 18171348228166988615),
  (15974640668512086343, 7209491194420303510, 6060780110821425449),
  (15026713309929068331, 13862660483710538649, 12503989524729962017),
  (13211469218323652638, 11052365528177614630, 6686435503645086313),
  (14295561104199821264, 16851938212622414037, 9153851763062612586),
  (11527829033624401907, 1113397040867984224, 1261379089236372842),
  (17973959301433576331, 16711574814292626461, 2598692120067411561)
]

private def frobProdChain : List (ℕ × ℕ × ℕ) := [
  (0, 1, 0),
  (13756005300681981762, 18069038926465008609, 4123756567369592585),
  (14788276583284992632, 8624662332760850783, 16664750556704292885),
  (5648395988117470330, 11489871049659818264, 17938638662720282782),
  (152582786219834161, 3651534002201260491, 6510031807883927247),
  (7816523760977747343, 5487495084232784878, 5726929811366469537),
  (6473875601695286106, 7250402975713006707, 1643615404057431027),
  (2417065094252531395, 5064802584823705121, 5363070825360050648),
  (4700304545418720823, 9069446577355141834, 3889352830628654893),
  (7517982354384105320, 8379794758232866497, 9932282168703094968),
  (4041419698346949644, 4047713920395647522, 80945731623332076),
  (10305915652627155303, 8304588242045625342, 10221275072110923096),
  (5123695769270267454, 12122069449662226533, 8604823813282103939),
  (8462760899231792340, 1808573973663206075, 5224991730793090756),
  (13731033738556686815, 8337322273196182833, 7125303417532212055),
  (13544296421190429963, 4368513979953522887, 10185725551880715040),
  (7062317736847679890, 273982680656749754, 584849719765196763),
  (14769472413589966205, 9416344092730214773, 14128986140863883091),
  (2255220646195946601, 14240730180668909256, 17042745085532974169),
  (17961045964899708224, 5634196570782204891, 14530546398341862725),
  (728864376745618720, 7210668684118941395, 14771291465906418642),
  (16852160913527562802, 15842325830175187484, 17739867042803366574),
  (17192444078005075649, 6940239454699280941, 244307394227808025),
  (11201237148682570709, 9415976534514806667, 16487193729234643908),
  (10989308258477163207, 12823301331734201992, 210872546212437047),
  (18066636080420455369, 4832192216006151128, 17219199301267404537),
  (12589591097798671034, 8893995212420565976, 3122711287675573655),
  (991521261010686639, 17949223314271865966, 1172244867328587387),
  (3975397510050098427, 14772861818582861511, 7430779088538326180),
  (10380806728570174415, 1920500345583365085, 16121707541280195496),
  (7345957444685127115, 3862743107043666844, 3554028541125304450),
  (2966080377479370921, 15376424789583843415, 4341787508243352093),
  (10615703402128488253, 10050274602728160328, 11746561000929144102)
]

private def checkSqChain (p : ℕ) : List (ℕ × ℕ × ℕ) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (fp3MulNat p a a == b) && checkSqChain p (b :: rest)

private theorem checkSqChain_sound :
    ∀ (l : List (ℕ × ℕ × ℕ)) (x : Fp3Model) (i : ℕ) (hi : i < l.length),
      checkSqChain goldilocksP l = true →
      ofNat3 (l[0]'(Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) = x →
      ofNat3 (l[i]'hi) = x ^ (2 ^ i)
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | _ :: [], _, i, hi, _, h0 => by
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa using h0
  | _ :: _ :: _, _, 0, _, _, h0 => by simpa using h0
  | a :: b :: rest, x, i + 1, hi, hchk, h0 => by
    simp only [checkSqChain, Bool.and_eq_true, beq_iff_eq] at hchk
    simp only [List.getElem_cons_zero] at h0
    have hb : ofNat3 b = x ^ 2 := by
      rw [← hchk.1, ofNat3_fp3MulNat, h0, sq]
    have hrec := checkSqChain_sound (b :: rest) (x ^ 2) i (by simpa using hi) hchk.2 hb
    have hpow : (x ^ 2) ^ (2 ^ i) = x ^ (2 ^ (i + 1)) := by
      rw [← pow_mul, pow_succ']
    exact hrec.trans hpow

private def checkProdChain (p : ℕ) : List (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ) → Bool
  | [], _ => true
  | [_], _ => true
  | a :: b :: rest, s :: srest => (fp3MulNat p a s == b) && checkProdChain p (b :: rest) srest
  | _ :: _ :: _, [] => false

private theorem checkProdChain_sound :
    ∀ (ps ss : List (ℕ × ℕ × ℕ)) (k e0 : ℕ) (hlen : ps.length = ss.length + 1),
      checkProdChain goldilocksP ps ss = true →
      ofNat3 (ps[0]'(by omega)) = genX ^ e0 →
      (∀ m (hm : m < ss.length), ofNat3 (ss[m]'hm) = genX ^ (2 ^ (k + m))) →
      ofNat3 (ps[ss.length]'(by omega)) = genX ^ (e0 + (2 ^ ss.length - 1) * 2 ^ k)
  | [], _, _, _, hlen, _, _, _ => by simp at hlen
  | a :: [], [], k, e0, _, _, h0, _ => by simpa using h0
  | _ :: [], _ :: _, _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _ :: _, [], _, _, hlen, _, _, _ => by simp at hlen
  | a :: b :: rest, s :: srest, k, e0, hlen, hchk, h0, hss => by
    simp only [checkProdChain, Bool.and_eq_true, beq_iff_eq] at hchk
    simp only [List.getElem_cons_zero] at h0
    have hs : ofNat3 s = genX ^ (2 ^ k) := by
      have h := hss 0 (by simp)
      simpa using h
    have hb : ofNat3 b = genX ^ (e0 + 2 ^ k) := by
      rw [← hchk.1, ofNat3_fp3MulNat, h0, hs, ← pow_add]
    have hss' : ∀ m (hm : m < srest.length), ofNat3 (srest[m]'hm) = genX ^ (2 ^ (k + 1 + m)) := by
      intro m hm
      have h := hss (m + 1) (by simpa using Nat.succ_lt_succ hm)
      simpa [Nat.add_assoc, Nat.add_comm 1 m] using h
    have hrec := checkProdChain_sound (b :: rest) srest (k + 1) (e0 + 2 ^ k)
      (by simpa using hlen) hchk.2 hb hss'
    have hexp : e0 + 2 ^ k + (2 ^ srest.length - 1) * 2 ^ (k + 1) =
        e0 + (2 ^ (srest.length + 1) - 1) * 2 ^ k := by
      have hpos : 1 ≤ 2 ^ srest.length := Nat.one_le_pow _ _ (by decide)
      have hsub : (2 ^ srest.length - 1) * 2 + 1 = 2 ^ (srest.length + 1) - 1 := by
        rw [pow_succ]; omega
      calc e0 + 2 ^ k + (2 ^ srest.length - 1) * 2 ^ (k + 1)
          = e0 + ((2 ^ srest.length - 1) * 2 + 1) * 2 ^ k := by
            rw [pow_succ]; ring
        _ = e0 + (2 ^ (srest.length + 1) - 1) * 2 ^ k := by rw [hsub]
    simpa [hexp] using hrec

private def fp3NormNat (p : ℕ) (a : ℕ × ℕ × ℕ) : ℕ :=
  let (a0, a1, a2) := a
  let a02 := (a0 + a2) % p
  let adj0 := subMod p (a02 * a02) (a1 * ((a1 + a2) % p))
  let adj1 := subMod p (a2 * a2) (a0 * a1)
  let adj2 := subMod p (a1 * a1) (a2 * a02)
  (a0 * adj0 + a2 * adj1 + a1 * adj2) % p

private theorem fp3NormNat_cast (a : ℕ × ℕ × ℕ) :
    ((fp3NormNat goldilocksP a : ℕ) : GoldilocksF) = (ofNat3 a).norm := by
  rcases a with ⟨a0, a1, a2⟩
  simp only [fp3NormNat, norm, adjugate, ofNat3, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
    subMod_cast]

private def frobMinusXNat : ℕ × ℕ × ℕ :=
  (10615703402128488253, 10050274602728160327, 11746561000929144102)

private theorem ofNat3_frobMinusXNat :
    ofNat3 frobMinusXNat = genX ^ goldilocksP - genX := by
  have hsqOk : checkSqChain goldilocksP frobSqChain = true := by decide
  have hprodOk : checkProdChain goldilocksP frobProdChain (frobSqChain.drop 32) = true := by decide
  have hsq : ∀ m (hm : m < (frobSqChain.drop 32).length),
      ofNat3 ((frobSqChain.drop 32)[m]'hm) = genX ^ (2 ^ (32 + m)) := by
    intro m hm
    have hlt : 32 + m < frobSqChain.length := by
      simp only [List.length_drop] at hm; omega
    have hdrop : (frobSqChain.drop 32)[m]'hm = frobSqChain[32 + m]'hlt := by
      simp [List.getElem_drop]
    rw [hdrop]
    exact checkSqChain_sound frobSqChain genX (32 + m) hlt hsqOk (by ext <;> simp [frobSqChain, ofNat3, genX])
  have hlen : frobProdChain.length = (frobSqChain.drop 32).length + 1 := by decide
  have hprod := checkProdChain_sound frobProdChain (frobSqChain.drop 32) 32 1 hlen hprodOk
    (by ext <;> simp [frobProdChain, ofNat3, genX]) hsq
  have hexp : 1 + (2 ^ (frobSqChain.drop 32).length - 1) * 2 ^ 32 = goldilocksP := by decide
  have hlast : frobProdChain[(frobSqChain.drop 32).length]'(by decide) =
      (10615703402128488253, 10050274602728160328, 11746561000929144102) := by decide
  rw [hexp, hlast] at hprod
  rw [← hprod]
  ext
  · simp [frobMinusXNat, ofNat3, genX]
  · simp only [frobMinusXNat, ofNat3, genX, sub_c1]
    rw [show (10050274602728160328 : ℕ) = 10050274602728160327 + 1 by decide,
      Nat.cast_add, Nat.cast_one]
    ring
  · simp [frobMinusXNat, ofNat3, genX]

private theorem frobMinusX_norm_ne_zero : (genX ^ goldilocksP - genX).norm ≠ 0 := by
  rw [← ofNat3_frobMinusXNat, ← fp3NormNat_cast]
  intro h0
  have hval := congrArg ZMod.val h0
  rw [ZMod.val_natCast, ZMod.val_zero] at hval
  have hne : fp3NormNat goldilocksP frobMinusXNat % goldilocksP ≠ 0 := by decide
  exact hne hval

/-- Evaluation homomorphism `a ↦ a.c0 + a.c1 * r + a.c2 * r^2` at a hypothetical root `r` of `X^3 - X - 1`. -/
private def evalAt (r : GoldilocksF) (a : Fp3Model) : GoldilocksF :=
  a.c0 + a.c1 * r + a.c2 * r ^ 2

private theorem evalAt_mul {r : GoldilocksF} (hr : r ^ 3 - r - 1 = 0) (a b : Fp3Model) :
    evalAt r (a * b) = evalAt r a * evalAt r b := by
  unfold evalAt
  simp only [mul_c0, mul_c1, mul_c2]
  linear_combination -(a.c1 * b.c2 + a.c2 * b.c1 + a.c2 * b.c2 * r) * hr

private theorem evalAt_pow {r : GoldilocksF} (hr : r ^ 3 - r - 1 = 0) (a : Fp3Model) (k : ℕ) :
    evalAt r (a ^ k) = (evalAt r a) ^ k := by
  induction k with
  | zero => simp [evalAt]
  | succ k ih => rw [pow_succ, pow_succ, evalAt_mul hr, ih]

/-- **Kernel-Verified Irreducibility of `X^3 - X - 1` over Goldilocks `GF(p)` (`cubicTrinomial_no_root`):**
The Goldilocks cubic extension modulus `X^3 - X - 1` has NO root in `GF(p)` (proved via
Frobenius `norm(X^p - X) ≠ 0`, ZERO `native_decide`!). -/
theorem cubicTrinomial_no_root (r : GoldilocksF) : r ^ 3 - r - 1 ≠ 0 := by
  intro hr
  have : Fact (Nat.Prime goldilocksP) := ⟨Aiur.Library.U32.Goldilocks.modulus_prime⟩
  have hgen : evalAt r genX = r := by simp [evalAt, genX]
  have hsub : evalAt r (genX ^ goldilocksP - genX) = 0 := by
    have h1 : evalAt r (genX ^ goldilocksP - genX) =
        evalAt r (genX ^ goldilocksP) - evalAt r genX := by
      simp [evalAt]; ring
    rw [h1, evalAt_pow hr, hgen, ZMod.pow_card, sub_self]
  have hnorm0 : (genX ^ goldilocksP - genX).norm = 0 := by
    have h := congrArg (evalAt r) (mul_adjugate (genX ^ goldilocksP - genX))
    rw [evalAt_mul hr, hsub, zero_mul] at h
    simpa [evalAt, embed] using h.symm
  exact frobMinusX_norm_ne_zero hnorm0

end Fp3Model

/-! ### `W_R ≥ 4` Tensor Randomizer Span Theorem & `W_R = 3` Negative Control -/

/-- `v : Fin W → Fp3Model` spans `Fp3Model` over the Goldilocks base field `Fp`. -/
def FpSpan3 {W : ℕ} (v : Fin W → Fp3Model) : Prop :=
  ∀ y : Fp3Model, ∃ a : Fin W → GoldilocksF, ∑ i : Fin W, Fp3Model.embed (a i) * v i = y

private theorem goldilocks_homogeneous_cubic_ne_zero {b c : GoldilocksF}
    (hbc : b ≠ 0 ∨ c ≠ 0) : b ^ 3 - b * c ^ 2 - c ^ 3 ≠ 0 := by
  have : Fact (Nat.Prime goldilocksP) := ⟨Aiur.Library.U32.Goldilocks.modulus_prime⟩
  by_cases hc : c = 0
  · subst hc
    have hb : b ≠ 0 := hbc.resolve_right (by simp)
    simpa using pow_ne_zero 3 hb
  · intro h0
    have hroot : (b * c⁻¹) ^ 3 - (b * c⁻¹) - 1 = 0 := by
      have hc3 : c ^ 3 ≠ 0 := pow_ne_zero 3 hc
      apply mul_right_cancel₀ hc3
      have h1 : ((b * c⁻¹) ^ 3 - (b * c⁻¹) - 1) * c ^ 3 = b ^ 3 - b * c ^ 2 - c ^ 3 := by
        field_simp [hc]
      rw [h1, h0, zero_mul]
    exact Fp3Model.cubicTrinomial_no_root (b * c⁻¹) hroot

private theorem fp3_span_of_det_ne_zero (u v : Fp3Model)
    (hdet : u.c1 * v.c2 - u.c2 * v.c1 ≠ 0) (y : Fp3Model) :
    ∃ a0 a1 a2 : GoldilocksF,
      Fp3Model.embed a0 * 1 + Fp3Model.embed a1 * u + Fp3Model.embed a2 * v = y := by
  have : Fact (Nat.Prime goldilocksP) := ⟨Aiur.Library.U32.Goldilocks.modulus_prime⟩
  let Δ := u.c1 * v.c2 - u.c2 * v.c1
  let a1 := (y.c1 * v.c2 - y.c2 * v.c1) * Δ⁻¹
  let a2 := (u.c1 * y.c2 - u.c2 * y.c1) * Δ⁻¹
  let a0 := y.c0 - a1 * u.c0 - a2 * v.c0
  have hinv : Δ⁻¹ * Δ = 1 := inv_mul_cancel₀ hdet
  refine ⟨a0, a1, a2, ?_⟩
  ext
  · simp [a0]; ring
  · simp only [Fp3Model.add_c1, Fp3Model.mul_c1, Fp3Model.embed_c0, Fp3Model.embed_c1,
      Fp3Model.embed_c2, Fp3Model.one_c1, mul_zero, zero_mul, add_zero, zero_add]
    apply mul_right_cancel₀ hdet
    calc (a1 * u.c1 + a2 * v.c1) * Δ
        = ((y.c1 * v.c2 - y.c2 * v.c1) * u.c1 + (u.c1 * y.c2 - u.c2 * y.c1) * v.c1) *
            (Δ⁻¹ * Δ) := by dsimp only [a1, a2]; ring
      _ = y.c1 * Δ := by rw [hinv, mul_one]; dsimp only [Δ]; ring
  · simp only [Fp3Model.add_c2, Fp3Model.mul_c2, Fp3Model.embed_c0, Fp3Model.embed_c1,
      Fp3Model.embed_c2, Fp3Model.one_c2, mul_zero, zero_mul, add_zero, zero_add]
    apply mul_right_cancel₀ hdet
    calc (a1 * u.c2 + a2 * v.c2) * Δ
        = ((y.c1 * v.c2 - y.c2 * v.c1) * u.c2 + (u.c1 * y.c2 - u.c2 * y.c1) * v.c2) *
            (Δ⁻¹ * Δ) := by dsimp only [a1, a2]; ring
      _ = y.c2 * Δ := by rw [hinv, mul_one]; dsimp only [Δ]; ring

/-- **Exact `W_R = 4` Tensor-Weight Span Theorem over `Fp3Model`:**
whenever `r₀ ∉ GF(p)` and `r₁ ∉ GF(p)`, the 4-element `FriBatching::Tensor`
weight tuple `![1, r₀, r₁, r₀ * r₁]` spans the full cubic extension `Fp3Model` over `GF(p)`. -/
theorem fp3_tensor4_spans_of_not_base {r₀ r₁ : Fp3Model}
    (hr₀ : r₀.c1 ≠ 0 ∨ r₀.c2 ≠ 0) (hr₁ : r₁.c1 ≠ 0 ∨ r₁.c2 ≠ 0) :
    FpSpan3 (![1, r₀, r₁, r₀ * r₁] : Fin 4 → Fp3Model) := by
  have : Fact (Nat.Prime goldilocksP) := ⟨Aiur.Library.U32.Goldilocks.modulus_prime⟩
  intro y
  have hembed0 : Fp3Model.embed 0 = 0 := rfl
  by_cases hdet1 : r₀.c1 * r₁.c2 - r₀.c2 * r₁.c1 ≠ 0
  · obtain ⟨a0, a1, a2, h⟩ := fp3_span_of_det_ne_zero r₀ r₁ hdet1 y
    refine ⟨![a0, a1, a2, 0], ?_⟩
    rw [Fin.sum_univ_four]
    simpa [hembed0] using h
  · push Not at hdet1
    have hlam : ∃ lam : GoldilocksF, lam ≠ 0 ∧ r₁.c1 = lam * r₀.c1 ∧ r₁.c2 = lam * r₀.c2 := by
      rcases hr₀ with hb0 | hc0
      · refine ⟨r₁.c1 * r₀.c1⁻¹, ?_, ?_, ?_⟩
        · intro h0
          have h1 : r₁.c1 = 0 := by
            have := congrArg (· * r₀.c1) h0
            simpa [mul_assoc, inv_mul_cancel₀ hb0] using this
          have h2 : r₁.c2 = 0 := by
            have : r₀.c1 * r₁.c2 = 0 := by linear_combination hdet1 + r₀.c2 * h1
            exact (mul_eq_zero.mp this).resolve_left hb0
          exact hr₁.elim (fun h => h h1) (fun h => h h2)
        · field_simp [hb0]
        · have : r₀.c1 * r₁.c2 = r₀.c2 * r₁.c1 := sub_eq_zero.mp hdet1
          field_simp [hb0]
          linear_combination this
      · refine ⟨r₁.c2 * r₀.c2⁻¹, ?_, ?_, ?_⟩
        · intro h0
          have h2 : r₁.c2 = 0 := by
            have := congrArg (· * r₀.c2) h0
            simpa [mul_assoc, inv_mul_cancel₀ hc0] using this
          have h1 : r₁.c1 = 0 := by
            have : r₀.c2 * r₁.c1 = 0 := by linear_combination -hdet1 + r₀.c1 * h2
            exact (mul_eq_zero.mp this).resolve_left hc0
          exact hr₁.elim (fun h => h h1) (fun h => h h2)
        · have : r₀.c1 * r₁.c2 = r₀.c2 * r₁.c1 := sub_eq_zero.mp hdet1
          field_simp [hc0]
          linear_combination -this
        · field_simp [hc0]
    obtain ⟨lam, hlam_ne, hrc1, hrc2⟩ := hlam
    have hdet2 : r₀.c1 * (r₀ * r₁).c2 - r₀.c2 * (r₀ * r₁).c1 ≠ 0 := by
      have hid : r₀.c1 * (r₀ * r₁).c2 - r₀.c2 * (r₀ * r₁).c1 =
          lam * (r₀.c1 ^ 3 - r₀.c1 * r₀.c2 ^ 2 - r₀.c2 ^ 3) := by
        simp only [Fp3Model.mul_c1, Fp3Model.mul_c2, hrc1, hrc2]
        ring
      rw [hid]
      exact mul_ne_zero hlam_ne (goldilocks_homogeneous_cubic_ne_zero hr₀)
    obtain ⟨a0, a1, a3, h⟩ := fp3_span_of_det_ne_zero r₀ (r₀ * r₁) hdet2 y
    refine ⟨![a0, a1, 0, a3], ?_⟩
    rw [Fin.sum_univ_four]
    simpa [hembed0] using h

private theorem natCard_goldilocksF : Nat.card GoldilocksF = CertiFri.P3.Goldilocks.order :=
  Nat.card_zmod _

private theorem natCard_fp3Model : Nat.card Fp3Model = CertiFri.P3.Goldilocks.order ^ 3 := by
  rw [Nat.card_eq_fintype_card, Fp3Model.card_fp3Model]

/-- **Exact `W_R = 4` Tensor-Randomizer Span-Failure Probability (`≤ 2 / p^2 < 1 / 2^126`):** -/
theorem fp3_tensor4_span_failure_prob_le :
    (Nat.card {p : Fp3Model × Fp3Model //
        ¬ FpSpan3 (![1, p.1, p.2, p.1 * p.2] : Fin 4 → Fp3Model)} : ℝ) /
      (Nat.card (Fp3Model × Fp3Model) : ℝ) ≤
      2 / (CertiFri.P3.Goldilocks.order : ℝ) ^ 2 := by
  let Bad := {p : Fp3Model × Fp3Model // ¬ FpSpan3 (![1, p.1, p.2, p.1 * p.2] : Fin 4 → Fp3Model)}
  have hbase : ∀ x : Bad, (x.1.1.c1 = 0 ∧ x.1.1.c2 = 0) ∨ (x.1.2.c1 = 0 ∧ x.1.2.c2 = 0) := by
    intro ⟨⟨r₀, r₁⟩, hbad⟩
    by_contra hnot
    push Not at hnot
    have hr₀ : r₀.c1 ≠ 0 ∨ r₀.c2 ≠ 0 := by
      by_cases h1 : r₀.c1 = 0
      · exact Or.inr (hnot.1 h1)
      · exact Or.inl h1
    have hr₁ : r₁.c1 ≠ 0 ∨ r₁.c2 ≠ 0 := by
      by_cases h1 : r₁.c1 = 0
      · exact Or.inr (hnot.2 h1)
      · exact Or.inl h1
    exact hbad (fp3_tensor4_spans_of_not_base hr₀ hr₁)
  let enc : Bad → (GoldilocksF × Fp3Model) ⊕ (Fp3Model × GoldilocksF) :=
    fun x =>
      @ite _ (x.1.1.c1 = 0 ∧ x.1.1.c2 = 0) (Classical.propDecidable _)
        (Sum.inl (x.1.1.c0, x.1.2))
        (Sum.inr (x.1.1, x.1.2.c0))
  have henc_inj : Function.Injective enc := by
    intro x y hxy
    have hx := hbase x
    have hy := hbase y
    dsimp only [enc] at hxy
    split_ifs at hxy with hx1 hy1 hy1
    · have hpair := Sum.inl.inj hxy
      have hc0 : x.1.1.c0 = y.1.1.c0 := congrArg (@Prod.fst GoldilocksF Fp3Model) hpair
      have hr2 : x.1.2 = y.1.2 := congrArg (@Prod.snd GoldilocksF Fp3Model) hpair
      apply Subtype.ext
      apply Prod.ext _ hr2
      ext
      · exact hc0
      · rw [hx1.1, hy1.1]
      · rw [hx1.2, hy1.2]
    · have hx2 : x.1.2.c1 = 0 ∧ x.1.2.c2 = 0 := hx.resolve_left hx1
      have hy2 : y.1.2.c1 = 0 ∧ y.1.2.c2 = 0 := hy.resolve_left hy1
      have hpair := Sum.inr.inj hxy
      have hr1 : x.1.1 = y.1.1 := congrArg (@Prod.fst Fp3Model GoldilocksF) hpair
      have hc0 : x.1.2.c0 = y.1.2.c0 := congrArg (@Prod.snd Fp3Model GoldilocksF) hpair
      apply Subtype.ext
      apply Prod.ext hr1
      ext
      · exact hc0
      · rw [hx2.1, hy2.1]
      · rw [hx2.2, hy2.2]
  have hcard_le : Nat.card Bad ≤ 2 * CertiFri.P3.Goldilocks.order ^ 4 := by
    have hle := Nat.card_le_card_of_injective enc henc_inj
    rw [Nat.card_sum, Nat.card_prod, Nat.card_prod, natCard_fp3Model, natCard_goldilocksF] at hle
    calc Nat.card Bad ≤ CertiFri.P3.Goldilocks.order * CertiFri.P3.Goldilocks.order ^ 3 +
          CertiFri.P3.Goldilocks.order ^ 3 * CertiFri.P3.Goldilocks.order := hle
      _ = 2 * CertiFri.P3.Goldilocks.order ^ 4 := by ring
  have hden : (Nat.card (Fp3Model × Fp3Model) : ℝ) = (CertiFri.P3.Goldilocks.order : ℝ) ^ 6 := by
    rw [Nat.card_prod, natCard_fp3Model]
    push_cast; ring
  have hp_pos : (0 : ℝ) < (CertiFri.P3.Goldilocks.order : ℝ) := by
    exact_mod_cast (by decide : 0 < CertiFri.P3.Goldilocks.order)
  have hcast : (Nat.card Bad : ℝ) ≤ 2 * (CertiFri.P3.Goldilocks.order : ℝ) ^ 4 := by
    exact_mod_cast hcard_le
  have hp6 : (0 : ℝ) ≤ (CertiFri.P3.Goldilocks.order : ℝ) ^ 6 := pow_nonneg hp_pos.le 6
  rw [hden]
  calc (Nat.card Bad : ℝ) / (CertiFri.P3.Goldilocks.order : ℝ) ^ 6
      ≤ (2 * (CertiFri.P3.Goldilocks.order : ℝ) ^ 4) / (CertiFri.P3.Goldilocks.order : ℝ) ^ 6 :=
        div_le_div_of_nonneg_right hcast hp6
    _ = 2 / (CertiFri.P3.Goldilocks.order : ℝ) ^ 2 := by field_simp [hp_pos.ne']

/-- Concrete numerical corollary: `2 / Goldilocks.order ^ 2 < 1 / 2 ^ 126`. -/
theorem fp3_tensor4_span_failure_lt_two_neg_126 :
    (2 : ℝ) / (CertiFri.P3.Goldilocks.order : ℝ) ^ 2 < 1 / (2 : ℝ) ^ 126 := by
  have hp_nat : 2 ^ 127 < CertiFri.P3.Goldilocks.order ^ 2 := by
    have h1 : 2 ^ 63 + 2 ^ 62 < CertiFri.P3.Goldilocks.order := by decide
    have h2 : (2 ^ 63 + 2 ^ 62) ^ 2 < CertiFri.P3.Goldilocks.order ^ 2 :=
      Nat.pow_lt_pow_left h1 (by decide)
    have h3 : (2 : ℕ) ^ 127 ≤ (2 ^ 63 + 2 ^ 62) ^ 2 := by
      have h3a : (2 ^ 63 + 2 ^ 62) ^ 2 = 9 * 2 ^ 124 := by ring
      have h3b : (2 : ℕ) ^ 127 = 8 * 2 ^ 124 := by
        rw [show (8 : ℕ) = 2 ^ 3 by decide, ← pow_add]
      omega
    exact lt_of_le_of_lt h3 h2
  have hp : (2 : ℝ) ^ 127 < (CertiFri.P3.Goldilocks.order : ℝ) ^ 2 := by exact_mod_cast hp_nat
  have hp_pos : (0 : ℝ) < (CertiFri.P3.Goldilocks.order : ℝ) := by
    exact_mod_cast (by decide : 0 < CertiFri.P3.Goldilocks.order)
  rw [div_lt_div_iff₀ (pow_pos hp_pos 2) (pow_pos (by norm_num) 126)]
  have h127 : (2 : ℝ) * (2 : ℝ) ^ 126 = (2 : ℝ) ^ 127 := by
    rw [mul_comm, ← pow_succ]
  linarith

/-- **Constructive Negative Control for `W_R = 3` (`≥ 1 / p > 1 / 2^64` tensor collision pitfall):**
with only `W_R = 3` randomizer columns (`![1, r₀, r₁]`), whenever `r₁ ∈ GF(p) + GF(p) * r₀`
(at least `p^5` pairs out of `p^6`), `![1, r₀, r₁]` fails to span `Fp3Model` over `GF(p)`,
giving failure probability `≥ 1 / p > 1 / 2^64`. -/
theorem negControl_fp3_tensor3_span_failure_ge :
    (1 : ℝ) / (CertiFri.P3.Goldilocks.order : ℝ) ≤
      (Nat.card {p : Fp3Model × Fp3Model // ¬ FpSpan3 (![1, p.1, p.2] : Fin 3 → Fp3Model)} : ℝ) /
      (Nat.card (Fp3Model × Fp3Model) : ℝ) ∧
    (1 : ℝ) / (2 : ℝ) ^ 64 < 1 / (CertiFri.P3.Goldilocks.order : ℝ) := by
  have : Fact (Nat.Prime goldilocksP) := ⟨Aiur.Library.U32.Goldilocks.modulus_prime⟩
  have hnotspan : ∀ (r₀ r₁ : Fp3Model), r₀.c1 * r₁.c2 = r₀.c2 * r₁.c1 →
      ¬ FpSpan3 (![1, r₀, r₁] : Fin 3 → Fp3Model) := by
    intro r₀ r₁ hdep hspan
    have hvec2 : (![1, r₀, r₁] : Fin 3 → Fp3Model) 2 = r₁ := rfl
    by_cases h0 : r₀.c1 = 0 ∧ r₀.c2 = 0
    · let y : Fp3Model := if r₁.c1 = 0 then ⟨0, 1, 0⟩ else ⟨0, 0, 1⟩
      obtain ⟨a, ha⟩ := hspan y
      rw [Fin.sum_univ_three] at ha
      have h1 := congrArg Fp3Model.c1 ha
      have h2 := congrArg Fp3Model.c2 ha
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hvec2,
        Fp3Model.add_c1, Fp3Model.add_c2, Fp3Model.mul_c1, Fp3Model.mul_c2,
        Fp3Model.embed_c0, Fp3Model.embed_c1, Fp3Model.embed_c2,
        Fp3Model.one_c1, Fp3Model.one_c2, h0.1, h0.2,
        mul_zero, zero_mul, add_zero, zero_add] at h1 h2
      dsimp only [y] at h1 h2
      split_ifs at h1 h2 with hr1
      · simp [hr1] at h1
      · have ha2 : a 2 = 0 := (mul_eq_zero.mp h1).resolve_right hr1
        simp [ha2] at h2
    · let y : Fp3Model := if r₀.c1 = 0 then ⟨0, 1, 0⟩ else ⟨0, 0, 1⟩
      obtain ⟨a, ha⟩ := hspan y
      rw [Fin.sum_univ_three] at ha
      have h1 := congrArg Fp3Model.c1 ha
      have h2 := congrArg Fp3Model.c2 ha
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hvec2,
        Fp3Model.add_c1, Fp3Model.add_c2, Fp3Model.mul_c1, Fp3Model.mul_c2,
        Fp3Model.embed_c0, Fp3Model.embed_c1, Fp3Model.embed_c2,
        Fp3Model.one_c1, Fp3Model.one_c2,
        mul_zero, zero_mul, add_zero, zero_add] at h1 h2
      have hcomb : r₀.c1 * y.c2 - r₀.c2 * y.c1 = 0 := by
        rw [← h1, ← h2]
        linear_combination (a 2) * hdep
      dsimp only [y] at hcomb
      split_ifs at hcomb with hc1
      · have hc2 : r₀.c2 ≠ 0 := fun h2 => h0 ⟨hc1, h2⟩
        simp [hc1] at hcomb
        exact hc2 hcomb
      · simp at hcomb
        exact hc1 hcomb
  let Bad := {p : Fp3Model × Fp3Model // ¬ FpSpan3 (![1, p.1, p.2] : Fin 3 → Fp3Model)}
  let f : Fp3Model × GoldilocksF × GoldilocksF → Fp3Model × Fp3Model :=
    fun x =>
      @ite _ (x.1.c1 = 0 ∧ x.1.c2 = 0) (Classical.propDecidable _)
        (x.1, ⟨x.2.1, x.2.2, 0⟩)
        (x.1, ⟨x.2.1, x.2.2 * x.1.c1, x.2.2 * x.1.c2⟩)
  have hf_inj : Function.Injective f := by
    intro ⟨r₀, u₁, v₁⟩ ⟨r₀', u₂, v₂⟩ heq
    have hr : r₀ = r₀' := by
      dsimp only [f] at heq
      split_ifs at heq <;> exact congrArg Prod.fst heq
    subst hr
    dsimp only [f] at heq
    split_ifs at heq with h0
    · have h2 := congrArg Prod.snd heq
      have hu : u₁ = u₂ := congrArg Fp3Model.c0 h2
      have hv : v₁ = v₂ := congrArg Fp3Model.c1 h2
      rw [hu, hv]
    · have h2 := congrArg Prod.snd heq
      have hu : u₁ = u₂ := congrArg Fp3Model.c0 h2
      have hvc1 : v₁ * r₀.c1 = v₂ * r₀.c1 := congrArg Fp3Model.c1 h2
      have hvc2 : v₁ * r₀.c2 = v₂ * r₀.c2 := congrArg Fp3Model.c2 h2
      have hv : v₁ = v₂ := by
        by_cases hc1 : r₀.c1 = 0
        · have hc2 : r₀.c2 ≠ 0 := fun hc2 => h0 ⟨hc1, hc2⟩
          exact mul_right_cancel₀ hc2 hvc2
        · exact mul_right_cancel₀ hc1 hvc1
      rw [hu, hv]
  have hf_mem : ∀ x, ¬ FpSpan3 (![1, (f x).1, (f x).2] : Fin 3 → Fp3Model) := by
    intro ⟨r₀, u, v⟩
    dsimp only [f]
    split_ifs with h0
    · exact hnotspan r₀ ⟨u, v, 0⟩ (by simp [h0.1, h0.2])
    · exact hnotspan r₀ ⟨u, v * r₀.c1, v * r₀.c2⟩ (by ring)
  let g : Fp3Model × GoldilocksF × GoldilocksF → Bad := fun x => ⟨f x, hf_mem x⟩
  have hg_inj : Function.Injective g := fun _ _ h => hf_inj (congrArg Subtype.val h)
  have hcard_ge : CertiFri.P3.Goldilocks.order ^ 5 ≤ Nat.card Bad := by
    have hle := Nat.card_le_card_of_injective g hg_inj
    rw [Nat.card_prod, Nat.card_prod, natCard_fp3Model, natCard_goldilocksF] at hle
    calc CertiFri.P3.Goldilocks.order ^ 5
        = CertiFri.P3.Goldilocks.order ^ 3 *
            (CertiFri.P3.Goldilocks.order * CertiFri.P3.Goldilocks.order) := by ring
      _ ≤ Nat.card Bad := hle
  have hden : (Nat.card (Fp3Model × Fp3Model) : ℝ) = (CertiFri.P3.Goldilocks.order : ℝ) ^ 6 := by
    rw [Nat.card_prod, natCard_fp3Model]; push_cast; ring
  have hp_pos : (0 : ℝ) < (CertiFri.P3.Goldilocks.order : ℝ) := by
    exact_mod_cast (by decide : 0 < CertiFri.P3.Goldilocks.order)
  have hp6 : (0 : ℝ) ≤ (CertiFri.P3.Goldilocks.order : ℝ) ^ 6 := pow_nonneg hp_pos.le 6
  constructor
  · rw [hden]
    have hcast : (CertiFri.P3.Goldilocks.order : ℝ) ^ 5 ≤ (Nat.card Bad : ℝ) := by
      exact_mod_cast hcard_ge
    calc (1 : ℝ) / (CertiFri.P3.Goldilocks.order : ℝ)
        = (CertiFri.P3.Goldilocks.order : ℝ) ^ 5 / (CertiFri.P3.Goldilocks.order : ℝ) ^ 6 := by
          field_simp [hp_pos.ne']
      _ ≤ (Nat.card Bad : ℝ) / (CertiFri.P3.Goldilocks.order : ℝ) ^ 6 :=
            div_le_div_of_nonneg_right hcast hp6
  · have hp_lt : (CertiFri.P3.Goldilocks.order : ℝ) < (2 : ℝ) ^ 64 := by
      exact_mod_cast (by decide : CertiFri.P3.Goldilocks.order < 2 ^ 64)
    rw [div_lt_div_iff₀ (pow_pos (by norm_num) 64) hp_pos]
    linarith

/-! ## 4. Endpoint 1b (`v6-zk`) STARK Shrinker Configuration & All 4 ZK Guardrails -/

/-- Configuration record for the 1-circuit fixed-layout Native `Fp^3` `v6-zk` hiding STARK Shrinker. -/
structure StarkShrinkerZkConfig where
  version                     : ProtocolVersion
  extDegree                   : ℕ
  digestBytes                 : ℕ
  batching                    : FriBatchingMode
  regime                      : SoundnessRegime
  logTraceHeight              : ℕ
  logBlowup                   : ℕ
  numQueries                  : ℕ
  queryPowBits                : ℕ
  randomizerWidth             : ℕ
  maxConstraintDegree         : ℕ
  leafSaltBytes               : ℕ
  oddCosetBlinding            : Bool
  interiorAccumulatorsBlinded : Bool
  numCircuits                 : ℕ
  leafDomain                  : Blake3Domain
  compressDomain              : Blake3Domain
  transcriptDomain            : Blake3Domain
  vkDomain                    : Blake3Domain
  pinnedVkDigest              : List UInt8
  deriving DecidableEq, Repr

/-- **All 4 `v6-zk` Hiding STARK Shrinker Guardrails + Zero-Leakage Profile (`StarkShrinkerZkGuardrailsOk`):**
1. **Guardrail 1 (Trace Height & Goldilocks Two-Adicity):**
   `minZkLogDegree numQueries extDegree ≤ logTraceHeight` (so `N ≥ next_pow2(2Q + 2D)`)
   AND `logTraceHeight + 1 + logBlowup ≤ 32`.
2. **Guardrail 2 (Randomizer Width):** `W_R ≥ 4` (`ZK_RANDOMIZER_WIDTH`).
3. **Guardrail 3 (Quotient Degree vs `log_blowup`):**
   `1 ≤ logBlowup` AND `zkQuotientDegree maxConstraintDegree ≤ 2 ^ logBlowup` (which also
   enforces `maxConstraintDegree ≤ 2 ^ logBlowup`).
4. **Guardrail 4 (Zero-Leakage Blinded Interior Accumulators, 1-Circuit Fixed Layout,
   16B BLAKE3-CTR Leaf Salting, 2× Odd-Coset Blinding, & Strict `v6-zk` Domain Separation):**
   `version = .v6Zk`, `extDegree = 3`, `digestBytes = 48`, `pinnedVkDigest.length = 48`,
   `batching = .tensor`, `v6QueryFloorOk`, `leafSaltBytes = 16`, `oddCosetBlinding = true`,
   `interiorAccumulatorsBlinded = true`, `numCircuits = 1`, and all 4 BLAKE3 `derive_key`
   domains strictly in `v6-zk`. -/
def StarkShrinkerZkGuardrailsOk (cfg : StarkShrinkerZkConfig) : Prop :=
  -- Guardrail 1: N ≥ next_pow2(2Q + 2D) and 2× LDE fits in 2^32
  minZkLogDegree cfg.numQueries cfg.extDegree ≤ cfg.logTraceHeight ∧
  cfg.logTraceHeight + 1 + cfg.logBlowup ≤ GOLDILOCKS_TWO_ADICITY ∧
  -- Guardrail 2: W_R ≥ 4
  ZK_RANDOMIZER_WIDTH ≤ cfg.randomizerWidth ∧
  -- Guardrail 3: 1 ≤ lb and zkQuotientDegree d ≤ 2^lb
  1 ≤ cfg.logBlowup ∧
  zkQuotientDegree cfg.maxConstraintDegree ≤ 2 ^ cfg.logBlowup ∧
  -- Guardrail 4: zero-leakage blinded interior accumulators, 1-circuit, 16B salt, 2× odd-coset, v6-zk domains
  cfg.version = .v6Zk ∧
  cfg.extDegree = 3 ∧
  cfg.digestBytes = 48 ∧
  cfg.pinnedVkDigest.length = 48 ∧
  cfg.batching = .tensor ∧
  v6QueryFloorOk cfg.regime cfg.logBlowup cfg.numQueries cfg.queryPowBits ∧
  cfg.leafSaltBytes = ZK_LEAF_SALT_BYTES ∧
  cfg.oddCosetBlinding = true ∧
  cfg.interiorAccumulatorsBlinded = true ∧
  cfg.numCircuits = 1 ∧
  cfg.leafDomain = .zkMerkleLeaf ∧
  cfg.compressDomain = .zkMerkleCompress ∧
  (cfg.transcriptDomain = .zkTranscriptSingle ∨ cfg.transcriptDomain = .zkTranscriptBatch) ∧
  cfg.vkDomain = .zkVerifyingKey

/-- Under `StarkShrinkerZkGuardrailsOk`, the unblinded trace height `2^logTraceHeight`
strictly satisfies `2 * Q + 2 * D ≤ 2 ^ logTraceHeight`. -/
theorem zkShrinkerGuardrails_trace_height_ge {cfg : StarkShrinkerZkConfig}
    (h : StarkShrinkerZkGuardrailsOk cfg) :
    2 * cfg.numQueries + 2 * cfg.extDegree ≤ 2 ^ cfg.logTraceHeight :=
  (le_two_pow_nextPow2Log _).trans (Nat.pow_le_pow_right two_pos h.1)

/-- Under `StarkShrinkerZkGuardrailsOk`, `maxConstraintDegree ≤ 2 ^ logBlowup`. -/
theorem zkShrinkerGuardrails_constraintDegree_le_blowup {cfg : StarkShrinkerZkConfig}
    (h : StarkShrinkerZkGuardrailsOk cfg) :
    cfg.maxConstraintDegree ≤ 2 ^ cfg.logBlowup := by
  have hd : cfg.maxConstraintDegree ≤ zkQuotientDegree cfg.maxConstraintDegree := by
    unfold zkQuotientDegree
    exact (Nat.le_max_left _ 1).trans (le_two_pow_nextPow2Log _)
  exact hd.trans h.2.2.2.2.1

/-- Under `StarkShrinkerZkGuardrailsOk`, all four active BLAKE3 `derive_key` domains are
strictly disjoint from every non-ZK (`v6` or `plain`) domain. -/
theorem zkShrinkerGuardrails_domains_disjoint_from_nonZk {cfg : StarkShrinkerZkConfig}
    (h : StarkShrinkerZkGuardrailsOk cfg) {dNonZk : Blake3Domain} (hn : dNonZk.isZk = false) :
    cfg.leafDomain.keyWords ≠ dNonZk.keyWords ∧
    cfg.compressDomain.keyWords ≠ dNonZk.keyWords ∧
    cfg.transcriptDomain.keyWords ≠ dNonZk.keyWords ∧
    cfg.vkDomain.keyWords ≠ dNonZk.keyWords := by
  have hL := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hC := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hT := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hV := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Blake3Domain.v6Zk_keyWords_ne_nonZk (by rw [hL]; rfl) hn
  · exact Blake3Domain.v6Zk_keyWords_ne_nonZk (by rw [hC]; rfl) hn
  · rcases hT with hT | hT
    · exact Blake3Domain.v6Zk_keyWords_ne_nonZk (by rw [hT]; rfl) hn
    · exact Blake3Domain.v6Zk_keyWords_ne_nonZk (by rw [hT]; rfl) hn
  · exact Blake3Domain.v6Zk_keyWords_ne_nonZk (by rw [hV]; rfl) hn

/-! ### Canonical Endpoint 1b (`v6-zk`) Shrinker Profiles (Positive Certificates) -/

def canonicalV6ZkVkDigest : List UInt8 := List.replicate 48 0x7B

def zkShrinkerUd128 : StarkShrinkerZkConfig where
  version                     := .v6Zk
  extDegree                   := 3
  digestBytes                 := 48
  batching                    := .tensor
  regime                      := .uniqueDecoding
  logTraceHeight              := 9
  logBlowup                   := 2
  numQueries                  := 160
  queryPowBits                := 20
  randomizerWidth             := 4
  maxConstraintDegree         := 3
  leafSaltBytes               := 16
  oddCosetBlinding            := true
  interiorAccumulatorsBlinded := true
  numCircuits                 := 1
  leafDomain                  := .zkMerkleLeaf
  compressDomain              := .zkMerkleCompress
  transcriptDomain            := .zkTranscriptSingle
  vkDomain                    := .zkVerifyingKey
  pinnedVkDigest              := canonicalV6ZkVkDigest

def zkShrinkerJohnsonLb2 : StarkShrinkerZkConfig :=
  { zkShrinkerUd128 with regime := .johnson, logTraceHeight := 8, logBlowup := 2, numQueries := 118 }

def zkShrinkerJohnsonLb3 : StarkShrinkerZkConfig :=
  { zkShrinkerUd128 with
    regime := .johnson, logTraceHeight := 8, logBlowup := 3, numQueries := 78,
    maxConstraintDegree := 5 }

def zkShrinkerJohnsonLb4 : StarkShrinkerZkConfig :=
  { zkShrinkerUd128 with
    regime := .johnson, logTraceHeight := 7, logBlowup := 4, numQueries := 58,
    maxConstraintDegree := 9 }

theorem zkShrinkerUd128_ok : StarkShrinkerZkGuardrailsOk zkShrinkerUd128 :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   rfl, rfl, rfl, by decide, rfl, ⟨by decide, rfl, by decide⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, rfl⟩

theorem zkShrinkerJohnsonLb2_ok : StarkShrinkerZkGuardrailsOk zkShrinkerJohnsonLb2 :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   rfl, rfl, rfl, by decide, rfl, ⟨by decide, Or.inl ⟨rfl, by decide⟩⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, rfl⟩

theorem zkShrinkerJohnsonLb3_ok : StarkShrinkerZkGuardrailsOk zkShrinkerJohnsonLb3 :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   rfl, rfl, rfl, by decide, rfl, ⟨by decide, Or.inr (Or.inl ⟨rfl, by decide⟩)⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, rfl⟩

theorem zkShrinkerJohnsonLb4_ok : StarkShrinkerZkGuardrailsOk zkShrinkerJohnsonLb4 :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   rfl, rfl, rfl, by decide, rfl, ⟨by decide, Or.inr (Or.inr ⟨rfl, by decide⟩)⟩,
   rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl, rfl⟩

/-! ## 5. Endpoint 1b (`v6-zk`) Public-Input Binding & Pure-ROM 128-Bit Soundness -/

/-- Public-input binding for the `v6-zk` hiding STARK Shrinker:
binds the pinned 48-byte `zkVerifyingKey` digest and 8-word Goldilocks claim digest while
enforcing that interior `intermediate_accumulators` are blinded (`interiorAccumulatorsBlinded = true`,
1-circuit fixed layout with zero unblinded public leakage). -/
structure StarkShrinkerZkPublicBinding (cfg : StarkShrinkerZkConfig)
    (stmt : StarkShrinkerPublicStatement)
    (friPub : List GoldilocksF)
    (outClaimDig : Fin 8 → Ix.Cert.MultiStark.Fp) : Prop where
  vkPinned            : stmt.vkDigest = cfg.pinnedVkDigest
  friBindsClaim       : ∀ i : Fin 8, friPub[i.val]? = some (stmt.claimDigest i)
  aggrBindsClaim      : ∀ i : Fin 8, GoldilocksF.ofNat (ZMod.val (outClaimDig i)) = stmt.claimDigest i
  accumulatorsBlinded : cfg.interiorAccumulatorsBlinded = true

/-- **Endpoint 1b Pure-ROM 128-Bit Soundness (`starkShrinker_v6zk_sound_128`):**
Composes:
- All 4 `v6-zk` guardrails + blinded interior `intermediate_accumulators` (`StarkShrinkerZkGuardrailsOk`),
- Monolithic single-oracle pure-ROM extraction (`monolithic_multiNode_rom_sound`) over ALL
  `1 + t.verificationCount` verifications (outer `v6-zk` shrinker + inner `v6` aggregation root)
  with 16-byte salted Merkle leaves, 48-byte BLAKE3 XOF (`|D| = 2^384`), and `c = 3/2`,
- 2× odd-coset randomizer `W_R ≥ 4` tensor span failure bound `≤ 2 / p^2 < 1 / 2^126`,
- In-circuit Goldilocks FRI verifier (`FriVerifier.friVerifierCircuit_sound`),
- 19-shape inner aggregation tree (`AcceptedAggrTree` → `AggrNodeHolds sem rootStmt`),
- Explicit zero-leakage public-input binding (`StarkShrinkerZkPublicBinding`).

**ZERO elliptic curves, ZERO SRS, ZERO `gnark` assumptions!** -/
theorem starkShrinker_v6zk_sound_128
    (cfg : StarkShrinkerZkConfig) (hCfg : StarkShrinkerZkGuardrailsOk cfg)
    -- Pure-ROM monolithic multi-node experiment (outer v6-zk shrinker + inner v6 aggr root)
    {Inst Msg : Type} {Chal : ℕ → Type} {X' : Type} {Y' : X' → Type}
    [DecidableEq Inst] [DecidableEq Msg] [∀ i, DecidableEq (Chal i)] [DecidableEq X']
    [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
    [∀ x, Fintype (Y' x)] [∀ x, Nonempty (Y' x)]
    {D : Type} [Fintype D] [Nonempty D]
    (hDigestCard : Fintype.card D = 2 ^ (8 * cfg.digestBytes))
    {r : Inst → ℕ} {doomed : Inst → ∀ i, Transcript Msg Chal i → Prop}
    {ε : Inst → ℕ → ℝ} {εmax : ℝ}
    (hsound : MultiRbrSound r doomed ε)
    (hε : ∀ inst, ∀ i < r inst, ε inst i ≤ εmax)
    (h0 : 0 ≤ εmax)
    (hε128 : εmax ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ 128)
    (hashBad : Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') →
      (x : MultiQuery Inst Msg Chal X') → MultiAnswer Chal Y' x → Prop)
    (hHashBad : ∀ l x, l.dlookup x = none →
      FractionLE (hashBad l x) ((2 * (3 / 2 : ℝ)) * (l.length : ℝ) / (Fintype.card D : ℝ)))
    -- Inner FRI verifier + 19-shape aggregation tree + zero-leakage public binding
    (friBase : Circuit GoldilocksF) (friLayout : FriVerifierLayout)
    (hMerkleLen : ∀ s ∈ friLayout.merkleSteps, s.2.1.length = s.2.2.1.length)
    (friPub : List GoldilocksF) (wFri : Wire → GoldilocksF)
    (hFri : (buildFriVerifierCircuit friBase friLayout).Satisfies friPub wFri)
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {rootStmt : _root_.Aggr.AggrNodeStmt _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    (t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim rootStmt)
    (stmt : StarkShrinkerPublicStatement) (outClaimDig : Fin 8 → Ix.Cert.MultiStark.Fp)
    (hBind : StarkShrinkerZkPublicBinding cfg stmt friPub outClaimDig)
    -- Shared single-oracle adversary + verifier over all `1 + t.verificationCount` nodes
    {A B : Type}
    (adv : OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') A)
    {Q M_verif : ℕ} (hadv : adv.QueryBound Q)
    (verifyAll : A → OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') B)
    (hver : ∀ a, (verifyAll a).QueryBound M_verif)
    (hM20 : M_verif ≤ 2 ^ 20)
    (hN128 : Q + M_verif ≤ 2 ^ 128)
    (NodeForges : B → Fin (1 + t.verificationCount) →
      Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') → Prop)
    (hExtract : ∀ b l', Outcome (adv.bind verifyAll) [] b l' →
      (∃ k : Fin (1 + t.verificationCount), NodeForges b k l') →
      ¬ HasBad hashBad l' →
      ∃ (inst : Inst) (tr : Transcript Msg Chal (r inst)),
        doomed inst 0 .nil ∧ MultiSupports inst tr l' ∧ ¬ doomed inst (r inst) tr) :
    prob (fun b l' => ∃ k : Fin (1 + t.verificationCount), NodeForges b k l')
        (adv.bind verifyAll) [] ≤ ((Q + M_verif : ℕ) : ℝ) / (2 : ℝ) ^ 128 ∧
    (shrinkerProximityTheta cfg.regime cfg.logBlowup) ^ cfg.numQueries /
        (2 : ℝ) ^ cfg.queryPowBits ≤ 1 / (2 : ℝ) ^ 128 ∧
    (Nat.card {p : Fp3Model × Fp3Model //
        ¬ FpSpan3 (![1, p.1, p.2, p.1 * p.2] : Fin 4 → Fp3Model)} : ℝ) /
      (Nat.card (Fp3Model × Fp3Model) : ℝ) < 1 / (2 : ℝ) ^ 126 ∧
    2 * cfg.numQueries + 2 * cfg.extDegree ≤ 2 ^ cfg.logTraceHeight ∧
    cfg.maxConstraintDegree ≤ 2 ^ cfg.logBlowup ∧
    (2 : ℕ) ^ 191 ≤ CertiFri.P3.Goldilocks.order ^ cfg.extDegree ∧
    FriVerifierSatisfied friBase friLayout friPub wFri ∧
    _root_.Aggr.AggrNodeHolds sem rootStmt ∧
    stmt.vkDigest = cfg.pinnedVkDigest ∧
    (∀ i : Fin 8, GoldilocksF.ofNat (ZMod.val (outClaimDig i)) = stmt.claimDigest i) ∧
    cfg.interiorAccumulatorsBlinded = true ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) := by
  have hProbRaw := monolithic_multiNode_rom_sound (D := D) (c := 3 / 2)
    hsound hε h0 (by norm_num) hashBad hHashBad adv hadv verifyAll hver NodeForges hExtract
  have hDigest48 : cfg.digestBytes = 48 := hCfg.2.2.2.2.2.2.2.1
  have hD384 : (Fintype.card D : ℝ) = (2 : ℝ) ^ 384 := by
    rw [hDigestCard, hDigest48, show 8 * 48 = 384 by decide, Nat.cast_pow, Nat.cast_ofNat]
  rw [hD384] at hProbRaw
  have hRate := monolithic_goldilocksExt3_xof48_rate_128 Q M_verif hM20 hN128 hε128
  unfold monolithicRomBound at hRate
  have hProb := hProbRaw.trans hRate
  have hQuery := starkShrinker_query_soundness_128 hCfg.2.2.2.2.2.2.2.2.2.2.1
  have hSpan : (Nat.card {p : Fp3Model × Fp3Model //
      ¬ FpSpan3 (![1, p.1, p.2, p.1 * p.2] : Fin 4 → Fp3Model)} : ℝ) /
      (Nat.card (Fp3Model × Fp3Model) : ℝ) < 1 / (2 : ℝ) ^ 126 :=
    lt_of_le_of_lt fp3_tensor4_span_failure_prob_le fp3_tensor4_span_failure_lt_two_neg_126
  have hExt : (2 : ℕ) ^ 191 ≤ CertiFri.P3.Goldilocks.order ^ cfg.extDegree := by
    rw [hCfg.2.2.2.2.2.2.1]
    exact goldilocksExt3_card_ge_two_pow_191
  have hFriSat := friVerifierCircuit_sound friBase friLayout hMerkleLen friPub wFri hFri
  obtain ⟨hDeriv, hChildOk⟩ := Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19 t
  exact ⟨hProb, hQuery, hSpan,
    zkShrinkerGuardrails_trace_height_ge hCfg,
    zkShrinkerGuardrails_constraintDegree_le_blowup hCfg,
    hExt, hFriSat, _root_.Aggr.aggrDerivation19_invariant hDeriv,
    hBind.vkPinned, hBind.aggrBindsClaim, hBind.accumulatorsBlinded, hChildOk⟩

/-- **Endpoint 1b Concrete `≤ 1 / 2^128` Probability Corollary (`starkShrinker_v6zk_concrete_prob_128`):**
Under `Q + M_verif ≤ 2^127` and `((Q + M_verif : ℕ) : ℝ) * εmax ≤ (1 / 2) / 2^128` (ZERO
curve/SRS/`gnark` assumptions), global pure-ROM forgery probability is literally `≤ 1 / 2^128`! -/
theorem starkShrinker_v6zk_concrete_prob_128
    (cfg : StarkShrinkerZkConfig) (hCfg : StarkShrinkerZkGuardrailsOk cfg)
    {Inst Msg : Type} {Chal : ℕ → Type} {X' : Type} {Y' : X' → Type}
    [DecidableEq Inst] [DecidableEq Msg] [∀ i, DecidableEq (Chal i)] [DecidableEq X']
    [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
    [∀ x, Fintype (Y' x)] [∀ x, Nonempty (Y' x)]
    {D : Type} [Fintype D] [Nonempty D]
    (hDigestCard : Fintype.card D = 2 ^ (8 * cfg.digestBytes))
    {r : Inst → ℕ} {doomed : Inst → ∀ i, Transcript Msg Chal i → Prop}
    {ε : Inst → ℕ → ℝ} {εmax : ℝ}
    (hsound : MultiRbrSound r doomed ε)
    (hε : ∀ inst, ∀ i < r inst, ε inst i ≤ εmax)
    (h0 : 0 ≤ εmax)
    (hashBad : Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') →
      (x : MultiQuery Inst Msg Chal X') → MultiAnswer Chal Y' x → Prop)
    (hHashBad : ∀ l x, l.dlookup x = none →
      FractionLE (hashBad l x) ((2 * (3 / 2 : ℝ)) * (l.length : ℝ) / (Fintype.card D : ℝ)))
    {A B : Type} {M : ℕ}
    (adv : OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') A)
    {Q M_verif : ℕ} (hadv : adv.QueryBound Q)
    (verifyAll : A → OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') B)
    (hver : ∀ a, (verifyAll a).QueryBound M_verif)
    (hM20 : M_verif ≤ 2 ^ 20)
    (hN127 : Q + M_verif ≤ 2 ^ 127)
    (hBudget : ((Q + M_verif : ℕ) : ℝ) * εmax ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ 128)
    (NodeForges : B → Fin M → Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') → Prop)
    (hExtract : ∀ b l', Outcome (adv.bind verifyAll) [] b l' →
      (∃ k : Fin M, NodeForges b k l') →
      ¬ HasBad hashBad l' →
      ∃ (inst : Inst) (tr : Transcript Msg Chal (r inst)),
        doomed inst 0 .nil ∧ MultiSupports inst tr l' ∧ ¬ doomed inst (r inst) tr) :
    prob (fun b l' => ∃ k : Fin M, NodeForges b k l') (adv.bind verifyAll) [] ≤
      1 / (2 : ℝ) ^ 128 := by
  have hProbRaw := monolithic_multiNode_rom_sound (D := D) (c := 3 / 2)
    hsound hε h0 (by norm_num) hashBad hHashBad adv hadv verifyAll hver NodeForges hExtract
  have hD384 : (Fintype.card D : ℝ) = (2 : ℝ) ^ 384 := by
    rw [hDigestCard, hCfg.2.2.2.2.2.2.2.1, show 8 * 48 = 384 by decide, Nat.cast_pow, Nat.cast_ofNat]
  rw [hD384] at hProbRaw
  exact hProbRaw.trans (monolithic_goldilocksExt3_xof48_concrete_prob_128 Q M_verif hM20 hN127 hBudget)

/-! ## 6. Constructive Negative Controls (All 4 ZK Guardrails + Zero-Leakage) -/

/-- **Negative Control 1 (`W_R = 3` tensor collision pitfall):**
Rejects `randomizerWidth = 3` AND proves that `W_R = 3` has `Fp3Model` tensor span failure
probability `≥ 1 / p > 1 / 2^64`. -/
theorem negControl_zkShrinker_rejects_wr3 :
    ¬ StarkShrinkerZkGuardrailsOk { zkShrinkerUd128 with randomizerWidth := 3 } ∧
    (1 : ℝ) / (CertiFri.P3.Goldilocks.order : ℝ) ≤
      (Nat.card {p : Fp3Model × Fp3Model // ¬ FpSpan3 (![1, p.1, p.2] : Fin 3 → Fp3Model)} : ℝ) /
      (Nat.card (Fp3Model × Fp3Model) : ℝ) ∧
    (1 : ℝ) / (2 : ℝ) ^ 64 < 1 / (CertiFri.P3.Goldilocks.order : ℝ) :=
  ⟨fun h => by have := h.2.2.1; simp [ZK_RANDOMIZER_WIDTH] at this,
   negControl_fp3_tensor3_span_failure_ge.1,
   negControl_fp3_tensor3_span_failure_ge.2⟩

/-- **Negative Control 2 (Undersized trace height `N < 2Q + 2D`):**
At `Q = 160, D = 3`, `2Q + 2D = 326 > 256 = 2^8`, so `logTraceHeight = 8` is rejected! -/
theorem negControl_zkShrinker_rejects_small_trace :
    ¬ StarkShrinkerZkGuardrailsOk { zkShrinkerUd128 with logTraceHeight := 8 } ∧
    2 ^ 8 < 2 * zkShrinkerUd128.numQueries + 2 * zkShrinkerUd128.extDegree := by
  refine ⟨fun h => ?_, by decide⟩
  have hge := zkShrinkerGuardrails_trace_height_ge h
  simp [zkShrinkerUd128] at hge

/-- **Negative Control 3 (Incompatible degree vs blowup: `d = 5, lb = 2`):**
In `v6-zk`, `zkQuotientDegree 5 = 8 > 4 = 2^2` (whereas non-ZK `v6` had `nonZkQuotientDegree 5 = 4`),
so `d = 5, lb = 2` is strictly rejected! -/
theorem negControl_zkShrinker_rejects_degree5_lb2 :
    ¬ StarkShrinkerZkGuardrailsOk
        { zkShrinkerUd128 with maxConstraintDegree := 5, logBlowup := 2 } ∧
    nonZkQuotientDegree 5 = 4 ∧
    zkQuotientDegree 5 = 8 := by
  refine ⟨fun h => ?_, by decide, by decide⟩
  have hq := h.2.2.2.2.1
  have h8 : zkQuotientDegree 5 = 8 := by decide
  simp [h8] at hq

/-- **Negative Control 4 (Cross-mode replay `v6` ↔ `v6-zk`):**
- Feeding non-ZK `v6` version or any `v6` domain into `StarkShrinkerZkGuardrailsOk` is rejected,
- Feeding `v6-zk` version or any `v6-zk` domain into `StarkShrinkerV6ProfileOk` is rejected,
- Every `v6` vs `v6-zk` BLAKE3 `derive_key` pair has strictly distinct 8-word `keyWords`! -/
theorem negControl_zkShrinker_rejects_cross_mode_replay :
    ¬ StarkShrinkerZkGuardrailsOk { zkShrinkerUd128 with version := .v6 } ∧
    ¬ StarkShrinkerZkGuardrailsOk { zkShrinkerUd128 with leafDomain := .merkleLeaf } ∧
    ¬ StarkShrinkerZkGuardrailsOk { zkShrinkerUd128 with compressDomain := .merkleCompress } ∧
    ¬ StarkShrinkerZkGuardrailsOk { zkShrinkerUd128 with transcriptDomain := .transcriptSingle } ∧
    ¬ StarkShrinkerZkGuardrailsOk { zkShrinkerUd128 with vkDomain := .verifyingKey } ∧
    ¬ StarkShrinkerV6ProfileOk { v6ShrinkerUd128 with version := .v6Zk } ∧
    ¬ StarkShrinkerV6ProfileOk { v6ShrinkerUd128 with leafDomain := .zkMerkleLeaf } ∧
    (∀ dV6 dZk : Blake3Domain, dV6.isV6 = true → dZk.isZk = true →
      dV6.keyWords ≠ dZk.keyWords) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; cases h.2.2.2.2.2.1
  · intro h; cases h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · intro h; cases h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · intro h; rcases h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hT | hT <;> cases hT
  · intro h; cases h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · intro h; cases h.1
  · intro h; cases h.2.2.2.2.2.2.2.1
  · intro dV6 dZk hV6 hZk heq
    have h := Blake3Domain.keyWords_injective heq
    subst h
    cases dV6 <;> simp [Blake3Domain.isV6, Blake3Domain.isZk] at hV6 hZk

/-- **Negative Control 5 (Unblinded interior accumulators / missing salting / missing odd-coset / multi-circuit leak):** -/
theorem negControl_zkShrinker_rejects_unblinded_accumulators :
    ¬ StarkShrinkerZkGuardrailsOk { zkShrinkerUd128 with interiorAccumulatorsBlinded := false } ∧
    ¬ StarkShrinkerZkGuardrailsOk { zkShrinkerUd128 with oddCosetBlinding := false } ∧
    ¬ StarkShrinkerZkGuardrailsOk { zkShrinkerUd128 with leafSaltBytes := 0 } ∧
    ¬ StarkShrinkerZkGuardrailsOk { zkShrinkerUd128 with numCircuits := 2 } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; cases h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · intro h; cases h.2.2.2.2.2.2.2.2.2.2.2.2.1
  · intro h; have := h.2.2.2.2.2.2.2.2.2.2.2.1; simp [ZK_LEAF_SALT_BYTES] at this
  · intro h; have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; simp at this

end Ix.Cert.Compression.StarkShrinkerZk
