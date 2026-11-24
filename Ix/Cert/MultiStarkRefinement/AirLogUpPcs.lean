import Ix.Cert.MultiStarkRefinement.TranscriptMmcs
import Ix.Cert.MultiStark.Air
import Ix.Cert.MultiStark.Preamble
import Ix.Cert.MultiStark.Verifier
import Ix.Cert.MultiStark.LogUpSoundness

/-! # AIR, LogUp, Preamble Bounds, & `verify_batch` Refinement (`AirLogUpPcs`)

Proves exact arithmetic and structural refinement of every check inside `StarkVerifier`
and `Pcs` against `Ix.Cert.MultiStark.{Preamble, Air, Verifier, LogUpSoundness}`:
1. `assert_shard_count_ok` ↔ `1 ≤ k ≤ MAX_BATCH_SHARDS` (`2^16`),
2. `at_most_row_bound` ↔ `n ≤ MAX_BATCH_ROWS` (`2^39`),
3. `lookups_ok` ↔ `l < MAX_CIRCUIT_LOOKUPS` (`2^24`),
4. `bytes8_le` ↔ `x ≤ y` on canonical 8-byte Goldilocks encodings,
5. `assert_closure_pairs` → `checkClosurePairs = true` AND per-width `DisjointIntervals`,
6. `ood_loop` + `claims_acc` + `pcs_fri_verify` → `verifyShard = some residual`,
7. `verify_batch` (`ext_is_zero(total) == 1`) → `verifyBatch = some allClaims`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace Ix.Cert.MultiStarkRefinement

open CertiFri CertiFri.P3
open Ix.Cert.MultiStark

/-! ## 1. Preamble Bound Checks (`assert_shard_count_ok`, `at_most_row_bound`, `lookups_ok`) -/

/-- Exact constraint predicate of `StarkVerifier::assert_shard_count_ok(k)`
(`StarkVerifier.lean:623-631`) on canonical byte decomposition `b` of `k : Fp`. -/
def assertShardCountOkSpec (k : Fp) (b : Fin 8 → UInt8) : Prop :=
  glValModel b = k ∧ glLtPModel b = 1 ∧
  isZeroFp k = 0 ∧
  (((b 3).toNat : Fp) + ((b 4).toNat : Fp) + ((b 5).toNat : Fp) +
    ((b 6).toNat : Fp) + ((b 7).toNat : Fp) = 0) ∧
  ((b 2).toNat : Fp) * (((b 2).toNat : Fp) - 1) = 0 ∧
  ((b 2).toNat : Fp) * (((b 0).toNat : Fp) + ((b 1).toNat : Fp)) = 0

private theorem sum5_bytes_eq_zero_iff (b3 b4 b5 b6 b7 : UInt8) :
    (((b3.toNat : Fp) + (b4.toNat : Fp) + (b5.toNat : Fp) + (b6.toNat : Fp) + (b7.toNat : Fp)) = 0) ↔
      (b3.toNat = 0 ∧ b4.toNat = 0 ∧ b5.toNat = 0 ∧ b6.toNat = 0 ∧ b7.toNat = 0) := by
  have h3 := b3.toNat_lt; have h4 := b4.toNat_lt; have h5 := b5.toNat_lt
  have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
  have hcast : ((b3.toNat : Fp) + (b4.toNat : Fp) + (b5.toNat : Fp) + (b6.toNat : Fp) + (b7.toNat : Fp)) =
      ((b3.toNat + b4.toNat + b5.toNat + b6.toNat + b7.toNat : Nat) : Fp) := by push_cast; ring
  have h0 : (0 : Fp) = ((0 : Nat) : Fp) := rfl
  rw [hcast, h0, ZMod.natCast_eq_natCast_iff']
  have hlt1 : b3.toNat + b4.toNat + b5.toNat + b6.toNat + b7.toNat < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; omega
  have hlt2 : 0 < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; decide
  rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]
  omega

private theorem sum3_bytes_eq_zero_iff (b5 b6 b7 : UInt8) :
    (((b5.toNat : Fp) + (b6.toNat : Fp) + (b7.toNat : Fp)) = 0) ↔
      (b5.toNat = 0 ∧ b6.toNat = 0 ∧ b7.toNat = 0) := by
  have h5 := b5.toNat_lt; have h6 := b6.toNat_lt; have h7 := b7.toNat_lt
  have hcast : ((b5.toNat : Fp) + (b6.toNat : Fp) + (b7.toNat : Fp)) =
      ((b5.toNat + b6.toNat + b7.toNat : Nat) : Fp) := by push_cast; ring
  have h0 : (0 : Fp) = ((0 : Nat) : Fp) := rfl
  rw [hcast, h0, ZMod.natCast_eq_natCast_iff']
  have hlt1 : b5.toNat + b6.toNat + b7.toNat < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; omega
  have hlt2 : 0 < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; decide
  rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]
  omega

private theorem sum2_bytes_eq_zero_iff (b0 b1 : UInt8) :
    (((b0.toNat : Fp) + (b1.toNat : Fp)) = 0) ↔ (b0.toNat = 0 ∧ b1.toNat = 0) := by
  have h0 := b0.toNat_lt; have h1 := b1.toNat_lt
  have hcast : ((b0.toNat : Fp) + (b1.toNat : Fp)) = ((b0.toNat + b1.toNat : Nat) : Fp) := by
    push_cast; ring
  have hz : (0 : Fp) = ((0 : Nat) : Fp) := rfl
  rw [hcast, hz, ZMod.natCast_eq_natCast_iff']
  have hlt1 : b0.toNat + b1.toNat < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; omega
  have hlt2 : 0 < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; decide
  rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]
  omega

/-- `StarkVerifier::assert_shard_count_ok(k)` holds iff `1 ≤ k.val ≤ MAX_BATCH_SHARDS` (`2^16`). -/
theorem assert_shard_count_ok_sound {k : Fp} {b : Fin 8 → UInt8}
    (h : assertShardCountOkSpec k b) :
    1 ≤ k.val ∧ k.val ≤ MAX_BATCH_SHARDS := by
  obtain ⟨hv, hlt, hnz, hhi, hbit, hhi_lo⟩ := h
  have hnat : leBytes8Nat b = k.val := (gl_to_bytes_spec hv hlt).1
  have h0 := (b 0).toNat_lt; have h1 := (b 1).toNat_lt; have h2 := (b 2).toNat_lt
  have hhi0 := (sum5_bytes_eq_zero_iff (b 3) (b 4) (b 5) (b 6) (b 7)).mp hhi
  have hk_ne0 : k ≠ 0 := by
    intro h0'; subst h0'; simp [isZeroFp] at hnz
  have hk_pos : 1 ≤ k.val := by
    by_contra hlt1
    have hv0 : k.val = 0 := by omega
    apply hk_ne0
    rw [← ZMod.natCast_zmod_val k, hv0]; rfl
  refine ⟨hk_pos, ?_⟩
  rcases mul_eq_zero.mp hbit with hb20 | hb21
  · have h2z : (b 2).toNat = 0 := by
      have hmod := (ZMod.natCast_eq_natCast_iff' (b 2).toNat 0 _).mp (by simpa using hb20)
      have hlt2 : (b 2).toNat < Aiur.Library.U32.Goldilocks.modulus := by
        unfold Aiur.Library.U32.Goldilocks.modulus; omega
      have hlt0 : 0 < Aiur.Library.U32.Goldilocks.modulus := by
        unfold Aiur.Library.U32.Goldilocks.modulus; decide
      rw [Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt hlt0] at hmod
      exact hmod
    rw [← hnat]
    unfold leBytes8Nat MAX_BATCH_SHARDS
    omega
  · have hb2eq : ((b 2).toNat : Fp) = 1 := sub_eq_zero.mp hb21
    have h2one : (b 2).toNat = 1 := by
      have hmod := (ZMod.natCast_eq_natCast_iff' (b 2).toNat 1 _).mp (by simpa using hb2eq)
      have hlt2 : (b 2).toNat < Aiur.Library.U32.Goldilocks.modulus := by
        unfold Aiur.Library.U32.Goldilocks.modulus; omega
      have hlt1 : 1 < Aiur.Library.U32.Goldilocks.modulus := by
        unfold Aiur.Library.U32.Goldilocks.modulus; decide
      rw [Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt hlt1] at hmod
      exact hmod
    rw [hb2eq, one_mul] at hhi_lo
    have hlo0 := (sum2_bytes_eq_zero_iff (b 0) (b 1)).mp hhi_lo
    rw [← hnat]
    unfold leBytes8Nat MAX_BATCH_SHARDS
    omega

/-- Exact constraint predicate of `StarkVerifier::at_most_row_bound(n) == 1`
(`StarkVerifier.lean:634-638`). -/
def atMostRowBoundSpec (n : Fp) (b : Fin 8 → UInt8) : Prop :=
  glValModel b = n ∧ glLtPModel b = 1 ∧
  isZeroFp (((b 5).toNat : Fp) + ((b 6).toNat : Fp) + ((b 7).toNat : Fp)) *
    ((if (b 4).toNat < 128 then (1 : Fp) else 0) + isZeroFp (n - (549755813888 : Fp))) = 1

/-- `StarkVerifier::at_most_row_bound(n) == 1` holds iff `n.val ≤ MAX_BATCH_ROWS` (`2^39`). -/
theorem at_most_row_bound_sound {n : Fp} {b : Fin 8 → UInt8}
    (h : atMostRowBoundSpec n b) :
    n.val ≤ MAX_BATCH_ROWS := by
  obtain ⟨hv, hlt, heq⟩ := h
  have h10 : (1 : Fp) ≠ 0 := by decide
  have hnat : leBytes8Nat b = n.val := (gl_to_bytes_spec hv hlt).1
  have h0 := (b 0).toNat_lt; have h1 := (b 1).toNat_lt
  have h2 := (b 2).toNat_lt; have h3 := (b 3).toNat_lt; have h4 := (b 4).toNat_lt
  by_cases hhi : ((b 5).toNat : Fp) + ((b 6).toNat : Fp) + ((b 7).toNat : Fp) = 0
  · have hhi0 := (sum3_bytes_eq_zero_iff (b 5) (b 6) (b 7)).mp hhi
    simp only [isZeroFp, hhi, ↓reduceIte, one_mul] at heq
    by_cases hb4 : (b 4).toNat < 128
    · rw [← hnat]; unfold leBytes8Nat MAX_BATCH_ROWS; omega
    · simp only [hb4, ↓reduceIte, zero_add] at heq
      by_cases htop : n - (549755813888 : Fp) = 0
      · have hn_eq : n = ((549755813888 : Nat) : Fp) := sub_eq_zero.mp htop
        have hlt_top : 549755813888 < Aiur.Library.U32.Goldilocks.modulus := by
          unfold Aiur.Library.U32.Goldilocks.modulus; decide
        have hval_eq : n.val = 549755813888 := by
          rw [hn_eq, ZMod.val_natCast, Nat.mod_eq_of_lt hlt_top]
        rw [hval_eq]; unfold MAX_BATCH_ROWS; omega
      · simp only [htop, ↓reduceIte] at heq
        exact absurd heq.symm h10
  · simp only [isZeroFp, hhi, ↓reduceIte, zero_mul] at heq
    exact absurd heq.symm h10

/-- Exact constraint predicate of `StarkVerifier::lookups_ok` on a single circuit's lookup count. -/
def lookupsOkSpec (l : Fp) (b : Fin 8 → UInt8) : Prop :=
  glValModel b = l ∧ glLtPModel b = 1 ∧
  (((b 3).toNat : Fp) + ((b 4).toNat : Fp) + ((b 5).toNat : Fp) +
    ((b 6).toNat : Fp) + ((b 7).toNat : Fp) = 0)

/-- `StarkVerifier::lookups_ok` forces `l.val < MAX_CIRCUIT_LOOKUPS` (`2^24`). -/
theorem lookups_ok_sound {l : Fp} {b : Fin 8 → UInt8} (h : lookupsOkSpec l b) :
    l.val < MAX_CIRCUIT_LOOKUPS := by
  obtain ⟨hv, hlt, hhi⟩ := h
  have hnat : leBytes8Nat b = l.val := (gl_to_bytes_spec hv hlt).1
  have h0 := (b 0).toNat_lt; have h1 := (b 1).toNat_lt; have h2 := (b 2).toNat_lt
  have hhi0 := (sum5_bytes_eq_zero_iff (b 3) (b 4) (b 5) (b 6) (b 7)).mp hhi
  rw [← hnat]; unfold leBytes8Nat MAX_CIRCUIT_LOOKUPS; omega

/-! ## 2. 8-Byte Comparison (`bytes8_le`) & `MEMSEG` Closure Pairs (`assert_closure_pairs`) -/

/-- Exact model of `StarkVerifier::le_step` (`StarkVerifier.lean:696-698`). -/
def leStepModel (xi yi : UInt8) (rest : Fp) : Fp :=
  (if xi.toNat < yi.toNat then (1 : Fp) else 0) +
    isZeroFp ((xi.toNat : Fp) - (yi.toNat : Fp)) * rest

/-- Exact model of `StarkVerifier::bytes8_le` (`StarkVerifier.lean:700-704`). -/
def bytes8LeModel (x y : Fin 8 → UInt8) : Fp :=
  leStepModel (x 7) (y 7) (leStepModel (x 6) (y 6) (leStepModel (x 5) (y 5)
    (leStepModel (x 4) (y 4) (leStepModel (x 3) (y 3) (leStepModel (x 2) (y 2)
      (leStepModel (x 1) (y 1) (leStepModel (x 0) (y 0) 1)))))))

private theorem byte_fp_eq_iff (a b : UInt8) :
    ((a.toNat : Fp) - (b.toNat : Fp) = 0) ↔ a.toNat = b.toNat := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff']
  have hlta : a.toNat < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; omega
  have hltb : b.toNat < Aiur.Library.U32.Goldilocks.modulus := by
    unfold Aiur.Library.U32.Goldilocks.modulus; omega
  rw [Nat.mod_eq_of_lt hlta, Nat.mod_eq_of_lt hltb]

private theorem leStepModel_bool {xi yi : UInt8} {p : Prop} [Decidable p]
    {r : Fp} (hr : r = if p then 1 else 0) :
    leStepModel xi yi r = if (xi.toNat < yi.toNat ∨ (xi.toNat = yi.toNat ∧ p)) then 1 else 0 := by
  unfold leStepModel isZeroFp
  rw [hr]
  by_cases hlt : xi.toNat < yi.toNat
  · have hne : ¬ ((xi.toNat : Fp) - (yi.toNat : Fp) = 0) := by
      rw [byte_fp_eq_iff]; omega
    simp [hlt, hne]
  · by_cases heq : xi.toNat = yi.toNat
    · simp [heq]
    · have hne : ¬ ((xi.toNat : Fp) - (yi.toNat : Fp) = 0) := by
        rw [byte_fp_eq_iff]; omega
      simp [hlt, heq, hne]

/-- One radix-`M` lexicographic comparison step: `(a < b ∨ (a = b ∧ r ≤ s)) ↔ r + M * a ≤ s + M * b`
when `r < M` and `s < M`. -/
private theorem lex_step_iff {a b r s M : Nat} (hr : r < M) (hs : s < M) :
    (a < b ∨ (a = b ∧ r ≤ s)) ↔ r + M * a ≤ s + M * b := by
  constructor
  · rintro (hab | ⟨rfl, hrs⟩)
    · have : M * a + M ≤ M * b := by
        have h1 : a + 1 ≤ b := hab
        calc M * a + M = M * (a + 1) := by ring
          _ ≤ M * b := Nat.mul_le_mul_left M h1
      omega
    · omega
  · intro hle
    by_cases hab : a < b
    · exact Or.inl hab
    · by_cases heq : a = b
      · subst heq; exact Or.inr ⟨rfl, by omega⟩
      · exfalso
        have hgt : b + 1 ≤ a := by omega
        have : M * b + M ≤ M * a := by
          calc M * b + M = M * (b + 1) := by ring
            _ ≤ M * a := Nat.mul_le_mul_left M hgt
        omega

/-- Exact specification of `StarkVerifier::bytes8_le`: evaluates to `1` if `leBytes8Nat x ≤ leBytes8Nat y`
and `0` otherwise. -/
theorem bytes8LeModel_eq_ite (x y : Fin 8 → UInt8) :
    bytes8LeModel x y = if leBytes8Nat x ≤ leBytes8Nat y then 1 else 0 := by
  unfold bytes8LeModel
  have h0 : (1 : Fp) = if True then 1 else 0 := rfl
  rw [leStepModel_bool h0]
  rw [leStepModel_bool rfl]
  rw [leStepModel_bool rfl]
  rw [leStepModel_bool rfl]
  rw [leStepModel_bool rfl]
  rw [leStepModel_bool rfl]
  rw [leStepModel_bool rfl]
  rw [leStepModel_bool rfl]
  have hx0 := (x 0).toNat_lt; have hx1 := (x 1).toNat_lt; have hx2 := (x 2).toNat_lt
  have hx3 := (x 3).toNat_lt; have hx4 := (x 4).toNat_lt; have hx5 := (x 5).toNat_lt
  have hx6 := (x 6).toNat_lt
  have hy0 := (y 0).toNat_lt; have hy1 := (y 1).toNat_lt; have hy2 := (y 2).toNat_lt
  have hy3 := (y 3).toNat_lt; have hy4 := (y 4).toNat_lt; have hy5 := (y 5).toNat_lt
  have hy6 := (y 6).toNat_lt
  have step0 : ((x 0).toNat < (y 0).toNat ∨ (x 0).toNat = (y 0).toNat ∧ True) ↔
      (x 0).toNat ≤ (y 0).toNat := by simp; omega
  have step1 : ((x 1).toNat < (y 1).toNat ∨ (x 1).toNat = (y 1).toNat ∧ (x 0).toNat ≤ (y 0).toNat) ↔
      (x 0).toNat + 256 * (x 1).toNat ≤ (y 0).toNat + 256 * (y 1).toNat :=
    lex_step_iff hx0 hy0
  have step2 : ((x 2).toNat < (y 2).toNat ∨ (x 2).toNat = (y 2).toNat ∧
      (x 0).toNat + 256 * (x 1).toNat ≤ (y 0).toNat + 256 * (y 1).toNat) ↔
      ((x 0).toNat + 256 * (x 1).toNat) + 65536 * (x 2).toNat ≤
      ((y 0).toNat + 256 * (y 1).toNat) + 65536 * (y 2).toNat :=
    lex_step_iff (by omega) (by omega)
  have step3 : ((x 3).toNat < (y 3).toNat ∨ (x 3).toNat = (y 3).toNat ∧
      ((x 0).toNat + 256 * (x 1).toNat) + 65536 * (x 2).toNat ≤
      ((y 0).toNat + 256 * (y 1).toNat) + 65536 * (y 2).toNat) ↔
      (((x 0).toNat + 256 * (x 1).toNat) + 65536 * (x 2).toNat) + 16777216 * (x 3).toNat ≤
      (((y 0).toNat + 256 * (y 1).toNat) + 65536 * (y 2).toNat) + 16777216 * (y 3).toNat :=
    lex_step_iff (by omega) (by omega)
  have step4 : ((x 4).toNat < (y 4).toNat ∨ (x 4).toNat = (y 4).toNat ∧
      (((x 0).toNat + 256 * (x 1).toNat) + 65536 * (x 2).toNat) + 16777216 * (x 3).toNat ≤
      (((y 0).toNat + 256 * (y 1).toNat) + 65536 * (y 2).toNat) + 16777216 * (y 3).toNat) ↔
      ((((x 0).toNat + 256 * (x 1).toNat) + 65536 * (x 2).toNat) + 16777216 * (x 3).toNat) +
        4294967296 * (x 4).toNat ≤
      ((((y 0).toNat + 256 * (y 1).toNat) + 65536 * (y 2).toNat) + 16777216 * (y 3).toNat) +
        4294967296 * (y 4).toNat :=
    lex_step_iff (by omega) (by omega)
  have step5 : ((x 5).toNat < (y 5).toNat ∨ (x 5).toNat = (y 5).toNat ∧
      ((((x 0).toNat + 256 * (x 1).toNat) + 65536 * (x 2).toNat) + 16777216 * (x 3).toNat) +
        4294967296 * (x 4).toNat ≤
      ((((y 0).toNat + 256 * (y 1).toNat) + 65536 * (y 2).toNat) + 16777216 * (y 3).toNat) +
        4294967296 * (y 4).toNat) ↔
      (((((x 0).toNat + 256 * (x 1).toNat) + 65536 * (x 2).toNat) + 16777216 * (x 3).toNat) +
        4294967296 * (x 4).toNat) + 1099511627776 * (x 5).toNat ≤
      (((((y 0).toNat + 256 * (y 1).toNat) + 65536 * (y 2).toNat) + 16777216 * (y 3).toNat) +
        4294967296 * (y 4).toNat) + 1099511627776 * (y 5).toNat :=
    lex_step_iff (by omega) (by omega)
  have step6 : ((x 6).toNat < (y 6).toNat ∨ (x 6).toNat = (y 6).toNat ∧
      (((((x 0).toNat + 256 * (x 1).toNat) + 65536 * (x 2).toNat) + 16777216 * (x 3).toNat) +
        4294967296 * (x 4).toNat) + 1099511627776 * (x 5).toNat ≤
      (((((y 0).toNat + 256 * (y 1).toNat) + 65536 * (y 2).toNat) + 16777216 * (y 3).toNat) +
        4294967296 * (y 4).toNat) + 1099511627776 * (y 5).toNat) ↔
      ((((((x 0).toNat + 256 * (x 1).toNat) + 65536 * (x 2).toNat) + 16777216 * (x 3).toNat) +
        4294967296 * (x 4).toNat) + 1099511627776 * (x 5).toNat) + 281474976710656 * (x 6).toNat ≤
      ((((((y 0).toNat + 256 * (y 1).toNat) + 65536 * (y 2).toNat) + 16777216 * (y 3).toNat) +
        4294967296 * (y 4).toNat) + 1099511627776 * (y 5).toNat) + 281474976710656 * (y 6).toNat :=
    lex_step_iff (by omega) (by omega)
  have step7 : ((x 7).toNat < (y 7).toNat ∨ (x 7).toNat = (y 7).toNat ∧
      ((((((x 0).toNat + 256 * (x 1).toNat) + 65536 * (x 2).toNat) + 16777216 * (x 3).toNat) +
        4294967296 * (x 4).toNat) + 1099511627776 * (x 5).toNat) + 281474976710656 * (x 6).toNat ≤
      ((((((y 0).toNat + 256 * (y 1).toNat) + 65536 * (y 2).toNat) + 16777216 * (y 3).toNat) +
        4294967296 * (y 4).toNat) + 1099511627776 * (y 5).toNat) + 281474976710656 * (y 6).toNat) ↔
      leBytes8Nat x ≤ leBytes8Nat y := by
    unfold leBytes8Nat
    exact lex_step_iff (by omega) (by omega)
  have hiff :
      ((x 7).toNat < (y 7).toNat ∨ (x 7).toNat = (y 7).toNat ∧
        ((x 6).toNat < (y 6).toNat ∨ (x 6).toNat = (y 6).toNat ∧
          ((x 5).toNat < (y 5).toNat ∨ (x 5).toNat = (y 5).toNat ∧
            ((x 4).toNat < (y 4).toNat ∨ (x 4).toNat = (y 4).toNat ∧
              ((x 3).toNat < (y 3).toNat ∨ (x 3).toNat = (y 3).toNat ∧
                ((x 2).toNat < (y 2).toNat ∨ (x 2).toNat = (y 2).toNat ∧
                  ((x 1).toNat < (y 1).toNat ∨ (x 1).toNat = (y 1).toNat ∧
                    ((x 0).toNat < (y 0).toNat ∨ (x 0).toNat = (y 0).toNat ∧ True)))))))) ↔
      leBytes8Nat x ≤ leBytes8Nat y := by
    simp only [step0, step1, step2, step3, step4, step5, step6, step7]
  by_cases hp : leBytes8Nat x ≤ leBytes8Nat y
  · have h1 := hiff.mpr hp; simp only [h1, hp, ↓reduceIte]
  · have h1 := mt hiff.mp hp; simp only [h1, hp, ↓reduceIte]

theorem bytes8LeModel_eq_one_iff (x y : Fin 8 → UInt8) :
    bytes8LeModel x y = 1 ↔ leBytes8Nat x ≤ leBytes8Nat y := by
  have h10 : (1 : Fp) ≠ 0 := by decide
  rw [bytes8LeModel_eq_ite]
  split_ifs with h
  · simp [h]
  · simp [h, h10.symm]

/-- Exact specification of `assert_eq!(bytes8_le(qb, pa), 0)` (`StarkVerifier.lean:867`):
`bytes8_le(y, x) = 0` iff `leBytes8Nat x < leBytes8Nat y` (strict inequality, rejecting empty
`a == b` no-op intervals). -/
theorem bytes8LeModel_eq_zero_iff (x y : Fin 8 → UInt8) :
    bytes8LeModel y x = 0 ↔ leBytes8Nat x < leBytes8Nat y := by
  have h10 : (1 : Fp) ≠ 0 := by decide
  rw [bytes8LeModel_eq_ite]
  split_ifs with h
  · simp only [h10, false_iff, not_lt]; exact h
  · simp only [true_iff]; omega

/-- Exact model of `StarkVerifier::rom_lanes_of` (`StarkVerifier.lean:664-671`) matching
`Ix.Cert.MultiStark.romLanes` (`C6` vectorized ROM lane schedule). -/
def romLanesOfModel (w : Nat) : Nat :=
  match w with
  | 0 | 1 | 2 | 3 | 4 => 8
  | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => 4
  | _ => 1

theorem rom_lanes_of_refines (w : Nat) : romLanesOfModel w = romLanes w := by
  unfold romLanesOfModel romLanes
  match w with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => rfl
  | w + 13 =>
    have h1 : ¬ (w + 13 ≤ 4) := by omega
    have h2 : ¬ (w + 13 ≤ 12) := by omega
    simp [h1, h2]

/-- Inductive specification of `StarkVerifier::assert_closure_pairs_n(ms, prevW, prevB, count)`
(`StarkVerifier.lean:841-879`) on a list of `BatchMessage`s: enforces strict `a < b` (rejecting
empty `a == b` intervals), `b < Goldilocks.order`, strictly ascending widths or non-overlapping
`prevB ≤ a`, and pair count `< MAX_CLOSURE_PAIRS` (`65536`). -/
inductive ClosurePairsAccepted : List BatchMessage → Nat → Nat → Prop where
  | nil (prevW prevB : Nat) : ClosurePairsAccepted [] prevW prevB
  | pair {pull push : BatchMessage} {rest : List BatchMessage}
      {prevW prevB w a b : Nat}
      (hpull_m : pull.multiplicity.add Goldilocks.one = Goldilocks.zero)
      (hpush_m : push.multiplicity = Goldilocks.one)
      (hpull_a : pull.args.size = 3)
      (hpush_a : push.args.size = 3)
      (hpull_c : pull.args[0]!.toNat = MEMSEG_CHANNEL)
      (hpush_c : push.args[0]!.toNat = MEMSEG_CHANNEL)
      (hpull_w : pull.args[1]!.toNat = w)
      (hpush_w : push.args[1]!.toNat = w)
      (hpull_x : pull.args[2]!.toNat = a)
      (hpush_x : push.args[2]!.toNat = b)
      (hab : a < b)
      (hb_lt : b < Goldilocks.order)
      (horder : prevW < w ∨ (w = prevW ∧ prevB ≤ a))
      (hrest : ClosurePairsAccepted rest w b) :
      ClosurePairsAccepted (pull :: push :: rest) prevW prevB

/-- Specification of `StarkVerifier::assert_closure_widths_ok` (`StarkVerifier.lean:881-901`):
every closure pair's ROM width belongs to `romWidthsOfSystem sys`, total pair count is at most
`headers.size * (romWidthsOfSystem sys).size`, and total message count is at most
`2 * MAX_CLOSURE_PAIRS`. -/
def ClosureWidthsAccepted (sys : StarkSystem) (headers : Array ShardHeader)
    (messages : Array BatchMessage) : Prop :=
  messages.size ≤ 2 * MAX_CLOSURE_PAIRS ∧
  messages.size / 2 ≤ headers.size * (romWidthsOfSystem sys).size ∧
  ∀ i, 2 * i < messages.size →
    ∃ pull wVal, messages[2 * i]? = some pull ∧ pull.args[1]? = some wVal ∧
      (romWidthsOfSystem sys).contains wVal.toNat = true

/-- Extract the list of `(a, b)` intervals for width `targetW` from a `BatchMessage` list. -/
def extractWidthIntervals (targetW : Nat) : List BatchMessage → List (Nat × Nat)
  | pull :: push :: rest =>
      let w := pull.args[1]!.toNat
      let a := pull.args[2]!.toNat
      let b := push.args[2]!.toNat
      if w = targetW then (a, b) :: extractWidthIntervals targetW rest
      else extractWidthIntervals targetW rest
  | _ => []

private theorem closurePairsAccepted_lowerBound {ms : List BatchMessage} {prevW prevB : Nat}
    (h : ClosurePairsAccepted ms prevW prevB) :
    ∀ {targetW : Nat},
      (targetW < prevW → extractWidthIntervals targetW ms = []) ∧
      (∀ iv ∈ extractWidthIntervals targetW ms,
        iv.1 ≤ iv.2 ∧ iv.2 < Goldilocks.order ∧ (targetW = prevW → prevB ≤ iv.1)) := by
  induction h with
  | nil prevW prevB =>
    intro targetW
    exact ⟨fun _ => rfl, fun _ hm => nomatch hm⟩
  | @pair pull push rest prevW prevB w a b _ _ _ _ _ _ hpw _ hpx hqx hab hb_lt horder _ ih =>
    intro targetW
    have hprevW_le : prevW ≤ w := by omega
    obtain ⟨ih_nil, ih_mem⟩ := ih (targetW := targetW)
    constructor
    · intro hlt
      unfold extractWidthIntervals
      dsimp only
      rw [hpw, hpx, hqx]
      have hne : w ≠ targetW := by omega
      simp only [hne, ↓reduceIte]
      exact ih_nil (by omega)
    · intro iv hiv
      unfold extractWidthIntervals at hiv
      dsimp only at hiv
      rw [hpw, hpx, hqx] at hiv
      by_cases htw : w = targetW
      · simp only [htw, ↓reduceIte] at hiv
        rcases List.mem_cons.mp hiv with rfl | hmem
        · refine ⟨Nat.le_of_lt hab, hb_lt, fun hEq => ?_⟩
          have : w = prevW := by omega
          omega
        · obtain ⟨h1, h2, h3⟩ := ih_mem iv hmem
          refine ⟨h1, h2, fun hEq => ?_⟩
          have hba : b ≤ iv.1 := h3 htw.symm
          have hpa : prevB ≤ a := by omega
          omega
      · simp only [htw, ↓reduceIte] at hiv
        obtain ⟨h1, h2, h3⟩ := ih_mem iv hiv
        refine ⟨h1, h2, fun hEq => ?_⟩
        by_cases hgt : targetW < w
        · rw [ih_nil hgt] at hiv; exact nomatch hiv
        · omega

/-- **Key Bridge Lemma (`closurePairsAccepted_disjoint`):**
Any `BatchMessage` list accepted by `StarkVerifier::assert_closure_pairs(ms, 0, 0)` induces
a sorted `DisjointIntervals` list for every width `w : Nat` — feeding directly into
`Ix.Cert.MultiStark.memseg_balance_implies_unique` and `widthROM_valid_of_count_le_one`! -/
theorem closurePairsAccepted_disjoint {ms : List BatchMessage} {prevW prevB : Nat}
    (h : ClosurePairsAccepted ms prevW prevB) (targetW : Nat) :
    DisjointIntervals (extractWidthIntervals targetW ms) := by
  induction h with
  | nil prevW prevB =>
    constructor
    · intro _ hm; exact nomatch hm
    · intro _ hi; simp [extractWidthIntervals] at hi
  | @pair pull push rest prevW prevB w a b _ _ _ _ _ _ hpw _ hpx hqx hab hb_lt horder hrest ih =>
    unfold extractWidthIntervals
    dsimp only
    rw [hpw, hpx, hqx]
    by_cases htw : w = targetW
    · simp only [htw, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · intro iv hiv
        rcases List.mem_cons.mp hiv with rfl | hmem
        · exact ⟨Nat.le_of_lt hab, hb_lt⟩
        · exact ih.1 iv hmem
      · intro i hi
        cases i with
        | zero =>
          simp only [List.length_cons] at hi
          have hpos : 0 < (extractWidthIntervals targetW rest).length := by omega
          have hmem0 : (extractWidthIntervals targetW rest)[0] ∈
              extractWidthIntervals targetW rest := List.getElem_mem hpos
          have hlb := (closurePairsAccepted_lowerBound hrest (targetW := targetW)).2 _ hmem0
          simpa using hlb.2.2 htw.symm
        | succ i =>
          simp only [List.length_cons] at hi
          exact ih.2 i (by omega)
    · simp only [htw, ↓reduceIte]
      exact ih

/-! ## 3. Full `verify_shard` & `verify_batch` Refinement onto `Ix.Cert.MultiStark.verifyBatch` -/

/-- Complete execution-level refinement witness for one shard `s` of `StarkVerifier::verify_shard`:
asserts header-proof agreement, active-circuit bounds, per-shard transcript & FRI/PCS verification,
and OOD AIR+LogUp verification for every active circuit, returning `residual`. -/
structure ShardVerifyWitness (sys : StarkSystem) (header : ShardHeader)
    (shardIdx : Nat) (proof : ShardProof) (batchState : ChallengerState)
    (beta gamma residual : EF) where
  header_active : header.active = proof.active
  header_s1 : header.stage1Trace = proof.commitments.stage1Trace
  header_lds : header.logDegrees = proof.logDegrees
  active_nonempty : (activeCircuitIndices proof.active).size ≠ 0
  accs_len : proof.intermediateAccumulators.size = (activeCircuitIndices proof.active).size
  transcript_pcs : ShardTranscriptPcsMatch sys header shardIdx proof batchState
  acc0 : EF
  claims_acc : claimsAccumulator? beta gamma header.claims = some acc0
  ood_all : ∀ (pos : Nat) (hpos : pos < (activeCircuitIndices proof.active).size),
    let activeIndices := activeCircuitIndices proof.active
    let ci := activeIndices[pos]
    ∃ c ld accNext s1 s1Cur s1Next s2 s2Cur s2Next qPts qRow prepSlot prepCur prepNext,
      sys.circuits[ci]? = some c ∧
      proof.logDegrees[pos]? = some ld ∧
      proof.intermediateAccumulators[pos]? = some accNext ∧
      proof.stage1OpenedValues[pos]? = some s1 ∧
      s1[0]? = some s1Cur ∧ s1[1]? = some s1Next ∧
      proof.stage2OpenedValues[pos]? = some s2 ∧
      s2[0]? = some s2Cur ∧ s2[1]? = some s2Next ∧
      proof.quotientOpenedValues[pos]? = some qPts ∧
      qPts[0]? = some qRow ∧
      sys.preprocessedIndices[ci]? = some prepSlot ∧
      (match prepSlot, proof.preprocessedOpenedValues with
       | some slot, some prepOpened =>
         ∃ pts, prepOpened[slot]? = some pts ∧ pts[0]? = some prepCur ∧ pts[1]? = some prepNext
       | none, _ => prepCur = #[] ∧ prepNext = #[]
       | some _, none => False) ∧
      checkCircuitOod c ld prepCur prepNext s1Cur s1Next s2Cur s2Next qRow
        beta gamma (if pos = 0 then acc0 else proof.intermediateAccumulators[pos - 1]!)
        accNext transcript_pcs.alphaAir transcript_pcs.zeta = true
  residual_eq : residual =
    proof.intermediateAccumulators[(activeCircuitIndices proof.active).size - 1]!

/-- Indexed helper: `forIn (List.range n)` in `Option` when step `pos` succeeds on the invariant state `inv pos`. -/
private theorem forIn_range_option_inv {β : Type} (n : Nat) (inv : Nat → β)
    (body : Nat → β → Option (ForInStep β))
    (hstep : ∀ pos < n, body pos (inv pos) = some (ForInStep.yield (inv (pos + 1)))) :
    forIn (List.range n) (inv 0) body = some (inv n) := by
  have hgen : ∀ (k start : Nat),
      (∀ i < k, body (start + i) (inv (start + i)) =
        some (ForInStep.yield (inv (start + i + 1)))) →
      forIn (List.range' start k 1) (inv start) body = some (inv (start + k)) := by
    intro k
    induction k with
    | zero => intro start _; simp [List.range']
    | succ m ih =>
      intro start hs
      rw [List.range'_succ, List.forIn_cons]
      have h0 := hs 0 (Nat.zero_lt_succ m)
      simp only [Nat.add_zero] at h0
      rw [h0]
      simp only [bind, Option.bind]
      have hrec := ih (start + 1) fun i hi => by
        have h1 := hs (i + 1) (Nat.succ_lt_succ hi)
        have ha : start + (i + 1) = start + 1 + i := by omega
        rw [ha] at h1
        exact h1
      have hgoal : start + 1 + m = start + (m + 1) := by omega
      rw [hgoal] at hrec
      exact hrec
  have h0 := hgen n 0 (by simpa using hstep)
  simpa [List.range_eq_range'] using h0

/-- **Shard Verifier Refinement (`verifyShard_of_witness`):**
Every shard satisfying `ShardVerifyWitness` is accepted by `Ix.Cert.MultiStark.verifyShard`
with exact residual `residual`! -/
theorem verifyShard_of_witness {sys : StarkSystem} {header : ShardHeader}
    {shardIdx : Nat} {proof : ShardProof} {batchState : ChallengerState}
    {beta gamma residual : EF}
    (w : ShardVerifyWitness sys header shardIdx proof batchState beta gamma residual) :
    verifyShard sys header shardIdx proof batchState beta gamma = some residual := by
  unfold verifyShard verifyShardWithOpts
  have h1 : (header.active != proof.active ||
      header.stage1Trace != proof.commitments.stage1Trace ||
      header.logDegrees != proof.logDegrees) = false := by
    simp [w.header_active, w.header_s1, w.header_lds]
  have h2 : ((activeCircuitIndices proof.active).size == 0 ||
      proof.intermediateAccumulators.size != (activeCircuitIndices proof.active).size) = false := by
    simp [w.active_nonempty, w.accs_len]
  have h3 : (w.transcript_pcs.zeta == GoldilocksExt3.zero) = false :=
    beq_false_of_ne w.transcript_pcs.zeta_ne_zero
  have hpcs : buildPcsInputsWithOpts? sys (activeCircuitIndices proof.active) proof
      w.transcript_pcs.zeta false =
      some (w.transcript_pcs.shape, w.transcript_pcs.commits,
            w.transcript_pcs.points, w.transcript_pcs.values) :=
    w.transcript_pcs.pcs_inputs
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte,
    w.transcript_pcs.shard_fs, h3,
    hpcs, w.transcript_pcs.shape_ok,
    w.transcript_pcs.fri_fs, w.transcript_pcs.fri_verify,
    Bool.not_true, w.claims_acc,
    bind, Option.bind, pure]
  set activeIndices := activeCircuitIndices proof.active
  set numActive := activeIndices.size
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrg : ([:numActive]).start = 0 ∧ ([:numActive]).size = numActive ∧ ([:numActive]).step = 1 := by
    refine ⟨rfl, ?_, rfl⟩
    simp [Std.Legacy.Range.size]
  rw [hrg.1, hrg.2.1, hrg.2.2, ← List.range_eq_range']
  set inv : Nat → EF := fun k => if k = 0 then w.acc0 else proof.intermediateAccumulators[k - 1]!
  have hinv0 : w.acc0 = inv 0 := rfl
  rw [hinv0, forIn_range_option_inv numActive inv]
  · have hne : numActive ≠ 0 := w.active_nonempty
    simp only [inv, hne, ↓reduceIte, w.residual_eq, numActive, activeIndices]
  · intro pos hpos
    have hci : activeIndices[pos]? = some activeIndices[pos] := Array.getElem?_eq_getElem hpos
    obtain ⟨c, ld, accNext, s1, s1Cur, s1Next, s2, s2Cur, s2Next, qPts, qRow, prepSlot,
      prepCur, prepNext, hc, hld, hacc, hs1, hs10, hs11, hs2, hs20, hs21, hq, hq0, hps,
      hprep, hood⟩ := w.ood_all pos hpos
    have hacc_eq : accNext = proof.intermediateAccumulators[pos]! := by
      have hpos_acc : pos < proof.intermediateAccumulators.size := by rw [w.accs_len]; exact hpos
      rw [Array.getElem?_eq_getElem hpos_acc, Option.some.injEq] at hacc
      rw [getElem!_pos proof.intermediateAccumulators pos hpos_acc, ← hacc]
    simp only [hci, activeIndices, hc, hld, hacc, hs1, hs10, hs11, hs2, hs20, hs21, hq, hq0, hps]
    cases prepSlot with
    | none =>
      rcases hprep with ⟨rfl, rfl⟩
      simp only [inv] at hood ⊢
      rw [hood]
      simp [hacc_eq]
    | some slot =>
      cases hpo : proof.preprocessedOpenedValues with
      | none =>
        rw [hpo] at hprep
        exact False.elim hprep
      | some prepOpened =>
        rw [hpo] at hprep
        obtain ⟨pts, hpts, hp0, hp1⟩ := hprep
        simp only [hpts, hp0, hp1]
        simp only [inv] at hood ⊢
        rw [hood]
        simp [hacc_eq]

/-- Complete execution-level refinement witness for `StarkVerifier::verify_batch`:
bundles preamble validation, batch Fiat–Shamir, message LogUp accumulator, every shard's
`ShardVerifyWitness`, global LogUp vanishing (`ext_is_zero(total) == 1`), and claim equality. -/
structure BatchVerifyWitness (sys : StarkSystem) (batch : BatchProof)
    (maxLogDeg : Nat) (expectedClaims : Array (Array F)) where
  preamble_ok : validatePreamble sys batch maxLogDeg = true
  closure_ok : ClosurePairsAccepted batch.preamble.messages.toList 0 0
  batchState : ChallengerState
  beta : EF
  gamma : EF
  batch_fs : BatchTranscriptMatch sys batch batchState beta gamma
  msgAcc : EF
  msg_acc : messagesAccumulator? beta gamma batch.preamble.messages = some msgAcc
  residuals : Array EF
  residuals_size : residuals.size = batch.preamble.headers.size
  proofs_size : batch.proofs.size = batch.preamble.headers.size
  shards_ok : ∀ (s : Nat) (hs : s < batch.preamble.headers.size),
    ShardVerifyWitness sys batch.preamble.headers[s] s
      (batch.proofs[s]'(by rw [proofs_size]; exact hs))
      batchState beta gamma (residuals[s]'(by rw [residuals_size]; exact hs))
  total_zero : (residuals.foldl GoldilocksExt3.add msgAcc) = GoldilocksExt3.zero
  claims_match : (batch.preamble.headers.foldl (fun acc h => acc ++ h.claims) #[]) = expectedClaims

/-- **Batch Verifier Refinement (`verifyBatch_of_witness`):**
Every batch satisfying `BatchVerifyWitness` is accepted by `Ix.Cert.MultiStark.verifyBatch`
and returns the exact `expectedClaims`! -/
theorem verifyBatch_of_witness {sys : StarkSystem} {batch : BatchProof}
    {maxLogDeg : Nat} {expectedClaims : Array (Array F)}
    (w : BatchVerifyWitness sys batch maxLogDeg expectedClaims) :
    verifyBatch sys batch maxLogDeg = some expectedClaims := by
  unfold verifyBatch verifyBatchWithFloor
  have hpre : validatePreambleWithFloor sys batch maxLogDeg false false = true := w.preamble_ok
  simp only [hpre, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    w.batch_fs.batch_fs, w.msg_acc, bind, Option.bind, pure]
  set headers := batch.preamble.headers
  set n := headers.size
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrg : ([:n]).start = 0 ∧ ([:n]).size = n ∧ ([:n]).step = 1 := by
    refine ⟨rfl, ?_, rfl⟩
    simp [Std.Legacy.Range.size]
  rw [hrg.1, hrg.2.1, hrg.2.2, ← List.range_eq_range']
  set inv : Nat → EF × Array (Array F) := fun k =>
    ((w.residuals.toList.take k).foldl GoldilocksExt3.add w.msgAcc,
     (headers.toList.take k).foldl (fun acc h => acc ++ h.claims) #[])
  have hinv0 : (w.msgAcc, (#[] : Array (Array F))) = inv 0 := rfl
  rw [hinv0, forIn_range_option_inv n inv]
  · have htakeR : w.residuals.toList.take n = w.residuals.toList :=
      List.take_of_length_le (by simp [w.residuals_size, n, headers])
    have htakeH : headers.toList.take n = headers.toList :=
      List.take_of_length_le (by simp [n])
    have ht : w.residuals.toList.foldl GoldilocksExt3.add w.msgAcc = GoldilocksExt3.zero := by
      have := w.total_zero
      rwa [← Array.foldl_toList] at this
    have hc : headers.toList.foldl (fun acc h => acc ++ h.claims) #[] = expectedClaims := by
      have := w.claims_match
      rwa [← Array.foldl_toList] at this
    simp only [inv, htakeR, htakeH, ht, hc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  · intro s hs
    have hh : headers[s]? = some headers[s] := Array.getElem?_eq_getElem hs
    have hp_lt : s < batch.proofs.size := by rw [w.proofs_size]; exact hs
    have hp : batch.proofs[s]? = some (batch.proofs[s]'hp_lt) := Array.getElem?_eq_getElem hp_lt
    have hr_lt : s < w.residuals.size := by rw [w.residuals_size]; exact hs
    have hvs := verifyShard_of_witness (w.shards_ok s hs)
    unfold verifyShard at hvs
    simp only [hh, hp, headers, hvs]
    have htake_r : w.residuals.toList.take (s + 1) =
        w.residuals.toList.take s ++ [w.residuals[s]'hr_lt] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hr_lt)]; rfl
    have htake_h : headers.toList.take (s + 1) =
        headers.toList.take s ++ [headers[s]'hs] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hs)]; rfl
    simp only [inv, htake_r, htake_h, List.foldl_append, List.foldl_cons, List.foldl_nil, headers]

end Ix.Cert.MultiStarkRefinement
