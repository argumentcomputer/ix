import Ix.Cert.Aggr.EndToEnd
import Ix.Cert.Aggr.MonolithicRom
import Ix.Cert.MultiStark.Security128Audit

/-! # 128-Bit Certified Aggregation Security Audit (`Ix.Cert.Aggr.Security128Audit`)

Mechanically pins (via `#guard_msgs` on `#check` and `#print axioms`) the 128-bit
Shape 17 security envelope predicate (`SecurityEnvelope128Ok`), its monotonic
upgrade over the `v5` envelope (`SecurityEnvelopeOk`), its exact equivalence with
`Ix.Cert.MultiStark.Security128.Security128Profile` / `Aiur.meetsSecurityFloor128*`,
the shared-log monolithic ROM aggregation bound (`Q + M`, no `M * Q` blowup), the
`M ≤ 16384` naive union-bound headroom theorem at `(2, 128, 0, 20)`, and
constructive negative controls rejecting `Fp^2`, `v5` protocol, 32B digests,
weak external VKs, `(2, 100, 0, 20)`, and `(4, 55, 0, 0)`.

Every theorem pinned here depends strictly on standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) — zero `sorry`, zero custom
axioms, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.Aggr.Security128

open Ix.Cert.MultiStark
open Ix.Cert.MultiStark.Security128
open Ix.Cert.Aggr

/-! ## 1. 128-Bit Shape 17 Security Envelope Predicate -/

/-- Target 128-bit Shape 17 security envelope in millibits (`128.000` bits). -/
def minSecurity128Millibits : Nat := Aiur.minProvableSecurityBits128 * 1000

/-- 128-bit `v6` Shape 17 security envelope predicate:
* Extension degree `≥ 3` (`Fp^3`, `p^3 > 2^191`);
* Protocol version `≥ 6` (`multi-stark` `v6` BLAKE3 `derive_key`);
* Digest width `≥ 48` bytes (384-bit BLAKE3 XOF);
* Strictly implies the existing `v5` Shape 17 envelope (`SecurityEnvelopeOk p`);
* Meets the 128-bit UD floor (`udQueryMillibits ≥ 128000`) when `requireUd = true`,
  or the 128-bit finite-`m` (`m = 16`) Johnson floor (`johnsonMillibits ≥ 128000`)
  when `requireUd = false`. -/
def SecurityEnvelope128Ok (extensionDegree protocolVersion digestBytes : Nat)
    (p : StarkParams) (requireUd : Bool) : Prop :=
  Aiur.extensionDegreeV6 ≤ extensionDegree ∧
  Aiur.protocolVersionV6 ≤ protocolVersion ∧
  Aiur.digestBytesXof48 ≤ digestBytes ∧
  SecurityEnvelopeOk p ∧
  (if requireUd then
    minSecurity128Millibits ≤ udQueryMillibits p.logBlowup p.numQueries p.queryPowBits
  else
    minSecurity128Millibits ≤ Aiur.johnsonMillibits (toAiurParams p).1 (toAiurParams p).2)

/-- Monotonic upgrade: every 128-bit `v6` Shape 17 envelope strictly satisfies the
`v5` Shape 17 envelope (`SecurityEnvelopeOk`). -/
theorem securityEnvelope128Ok_implies_v5 {ext ver dig : Nat} {p : StarkParams} {reqUd : Bool}
    (h : SecurityEnvelope128Ok ext ver dig p reqUd) :
    SecurityEnvelopeOk p :=
  h.2.2.2.1

private lemma provableUdMillibits_eq_some {p : StarkParams}
    (h1 : 1 ≤ p.logBlowup) (h4 : p.logBlowup ≤ 4) :
    Aiur.provableUdMillibits (toAiurParams p).1 (toAiurParams p).2 =
      some (udQueryMillibits p.logBlowup p.numQueries p.queryPowBits) := by
  unfold Aiur.provableUdMillibits toAiurParams udQueryMillibits
  dsimp only
  have hcases : p.logBlowup = 1 ∨ p.logBlowup = 2 ∨ p.logBlowup = 3 ∨ p.logBlowup = 4 := by omega
  rcases hcases with h | h | h | h <;>
    (rw [h]; simp only [Aiur.udMillibitsPerQuery, udMillibitsPerQuery, Option.map_some];
     congr 1; omega)

/-- Exact equivalence between the 128-bit Shape 17 envelope (`SecurityEnvelope128Ok`)
and the cross-language 128-bit Multi-STARK / Aiur profile (`Security128Profile`). -/
theorem securityEnvelope128Ok_iff_profile (ext ver dig : Nat) (p : StarkParams) (reqUd : Bool) :
    SecurityEnvelope128Ok ext ver dig p reqUd ↔ Security128Profile ext ver dig p reqUd := by
  constructor
  · rintro ⟨hext, hver, hdig, hv5, h128⟩
    refine ⟨hext, hver, hdig, ?_⟩
    have hv5' := (securityEnvelopeOk_iff p).mp hv5
    have hfloor : Aiur.meetsSecurityFloor ⟨p.logBlowup, p.capHeight⟩
        ⟨p.logFinalPolyLen, p.maxLogArity, p.numQueries, p.commitPowBits, p.queryPowBits⟩ = true :=
      hv5'.2.1
    have hlb1 : 1 ≤ p.logBlowup := hv5.2.2.2.1
    have hlb4 : p.logBlowup ≤ 4 := hv5.2.2.2.2.1
    have hqp : p.queryPowBits ≤ 32 := hv5.2.2.2.2.2.2.2.1
    have hlbCases : p.logBlowup = 1 ∨ p.logBlowup = 2 ∨ p.logBlowup = 3 ∨ p.logBlowup = 4 := by
      omega
    cases reqUd
    · simp only [Bool.false_eq_true, ite_false] at h128 ⊢
      unfold Aiur.meetsSecurityFloor128Johnson
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨hext, hver⟩, hfloor⟩, ?_⟩, ?_⟩
      · unfold minSecurity128Millibits Aiur.minProvableSecurityBits128 Aiur.johnsonMillibits
          Aiur.johnsonSlackMillibitsPerQuery toAiurParams at h128
        dsimp only at h128
        have hud := hv5.2.2.2.2.2.2.2.2.2.1
        unfold minProvableUdMillibits udQueryMillibits at hud
        rcases hlbCases with hlb | hlb | hlb | hlb <;>
          (rw [hlb] at h128 hud ⊢;
           simp [Aiur.minQueriesForLogBlowup128Johnson, udMillibitsPerQuery] at hud ⊢;
           omega)
      · exact h128
    · simp only [ite_true] at h128 ⊢
      unfold Aiur.meetsSecurityFloor128Ud
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨hext, hver⟩, hfloor⟩, ?_⟩, ?_⟩
      · unfold minSecurity128Millibits Aiur.minProvableSecurityBits128 udQueryMillibits at h128
        rcases hlbCases with hlb | hlb | hlb | hlb <;>
          (rw [hlb] at h128 ⊢;
           simp [Aiur.minQueriesForLogBlowup128Ud, udMillibitsPerQuery] at h128 ⊢;
           omega)
      · have hEq : Aiur.provableUdMillibits ⟨p.logBlowup, p.capHeight⟩
            ⟨p.logFinalPolyLen, p.maxLogArity, p.numQueries, p.commitPowBits, p.queryPowBits⟩ =
            some (udQueryMillibits p.logBlowup p.numQueries p.queryPowBits) :=
          provableUdMillibits_eq_some hlb1 hlb4
        rw [hEq]
        simp only [decide_eq_true_eq]
        exact h128
  · rintro ⟨hext, hver, hdig, hprof⟩
    refine ⟨hext, hver, hdig, ?_, ?_⟩
    · have hfloor : Aiur.meetsSecurityFloor (toAiurParams p).1 (toAiurParams p).2 = true := by
        cases reqUd
        · simp only [Bool.false_eq_true, ite_false] at hprof
          unfold Aiur.meetsSecurityFloor128Johnson at hprof
          simp only [Bool.and_eq_true] at hprof
          exact hprof.1.1.2
        · simp only [ite_true] at hprof
          unfold Aiur.meetsSecurityFloor128Ud at hprof
          simp only [Bool.and_eq_true] at hprof
          exact hprof.1.1.2
      unfold Aiur.meetsSecurityFloor Aiur.conjecturedSecurityBits Aiur.minProvableUdBits
        Aiur.minJohnsonBits Aiur.johnsonMillibits Aiur.johnsonSlackMillibitsPerQuery at hfloor
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hfloor
      rcases hfloor with ⟨hc, hfl, hma, hlb1, hlb4, hnq, hcp, hqp, _, hconj, hud, hj⟩
      unfold toAiurParams at hc hfl hma hlb1 hlb4 hnq hcp hqp hconj hj
      dsimp only at hc hfl hma hlb1 hlb4 hnq hcp hqp hconj hj
      rw [provableUdMillibits_eq_some hlb1 hlb4] at hud
      simp only [decide_eq_true_eq] at hud
      have hj' : minJohnson128Millibits ≤ johnsonQueryMillibits p.logBlowup p.numQueries p.queryPowBits := by
        unfold minJohnson128Millibits johnsonQueryMillibits
        have hlbCases : p.logBlowup = 1 ∨ p.logBlowup = 2 ∨ p.logBlowup = 3 ∨ p.logBlowup = 4 := by
          omega
        rcases hlbCases with hlb | hlb | hlb | hlb <;>
          (rw [hlb] at hj ⊢; omega)
      exact ⟨hc, hfl, hma, hlb1, hlb4, hnq, hcp, hqp, hconj, hud, hj'⟩
    · cases reqUd
      · simp only [Bool.false_eq_true, ite_false] at hprof ⊢
        unfold Aiur.meetsSecurityFloor128Johnson at hprof
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hprof
        exact hprof.2
      · simp only [ite_true] at hprof ⊢
        unfold Aiur.meetsSecurityFloor128Ud at hprof
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hprof
        have hfloor := hprof.1.1.2
        have hud := hprof.2
        unfold Aiur.meetsSecurityFloor at hfloor
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hfloor
        have hlb1 : 1 ≤ p.logBlowup := hfloor.2.2.2.1
        have hlb4 : p.logBlowup ≤ 4 := hfloor.2.2.2.2.1
        have hEq : Aiur.provableUdMillibits ⟨p.logBlowup, p.capHeight⟩
            ⟨p.logFinalPolyLen, p.maxLogArity, p.numQueries, p.commitPowBits, p.queryPowBits⟩ =
            some (udQueryMillibits p.logBlowup p.numQueries p.queryPowBits) :=
          provableUdMillibits_eq_some hlb1 hlb4
        rw [hEq] at hud
        simp only [decide_eq_true_eq] at hud
        exact hud

/-- Positive Shape 17 envelope certificates for `v6` `Fp^3` + 48B XOF at
UD `(2, 160, 0, 20)` and Johnson `(2, 118, 0, 20)` / `(2, 128, 0, 20)`. -/
theorem v6_shape17_envelopes_ok :
    SecurityEnvelope128Ok 3 6 48 v6Ud160Params true ∧
    SecurityEnvelope128Ok 3 6 48 v6Johnson118Params false ∧
    SecurityEnvelope128Ok 3 6 48 v6Johnson128Params false := by
  obtain ⟨h1, h2, h3⟩ := v6_positive_128_profiles
  exact ⟨(securityEnvelope128Ok_iff_profile ..).mpr h1,
         (securityEnvelope128Ok_iff_profile ..).mpr h2,
         (securityEnvelope128Ok_iff_profile ..).mpr h3⟩

/-! ## 2. Monolithic Shared-Log ROM & Tree Union-Bound Headroom Theorems -/

/-- **Monolithic Shared-Log Aggregation ROM Bound (`aggr_shared_log_rom_bound_128`):**
Under straight-line extraction from a single shared random-oracle log across `M`
verification nodes and `Q` adversary queries (`Q + M ≤ 2^128`), when per-round
soundness satisfies `εmax ≤ (3 / 4) / 2^128`, the global 48-byte BLAKE3 XOF
forgery probability satisfies literally `≤ (Q + M) / 2^128` (eliminating any
multiplicative `M * Q` blowup). -/
theorem aggr_shared_log_rom_bound_128 {Q M : ℕ} (hQM : Q + M ≤ 2 ^ 128)
    {εmax : ℝ} (hε : εmax ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128) :
    ((Q + M : ℕ) : ℝ) * εmax + (3 : ℝ) * ((Q + M : ℕ) : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 384) ≤
      ((Q + M : ℕ) : ℝ) / (2 : ℝ) ^ 128 :=
  fp3_xof48_total_budget_le_128 hQM hε

/-- **Belt-and-Suspenders Tree Union-Bound Headroom (`aggr_johnson_128_union_headroom`):**
Even under the naive `M`-node union bound (`tree_rom_error_bound`), the recommended
`v6` Johnson parameters `(2, 128, 0, 20)` (`142.3b` at `m = 16`) clear literally
`≤ 1 / 2^128` across any aggregation tree of up to `M ≤ 16384 = 2^14` nodes. -/
theorem aggr_johnson_128_union_headroom (probs : List ℝ)
    (hM : probs.length ≤ 16384)
    (hbound : ∀ p ∈ probs, p ≤ ((33 / 64 : ℝ) ^ 128) / (2 : ℝ) ^ 20) :
    probs.sum ≤ (1 : ℝ) / (2 : ℝ) ^ 128 := by
  have hsum := tree_rom_error_bound probs hbound
  have hq0 : (0 : ℝ) ≤ ((33 / 64 : ℝ) ^ 128) / (2 : ℝ) ^ 20 := by positivity
  have hMr : (probs.length : ℝ) ≤ (16384 : ℝ) := by exact_mod_cast hM
  have hle : (probs.length : ℝ) * (((33 / 64 : ℝ) ^ 128) / (2 : ℝ) ^ 20) ≤
      (16384 : ℝ) * (((33 / 64 : ℝ) ^ 128) / (2 : ℝ) ^ 20) :=
    mul_le_mul_of_nonneg_right hMr hq0
  refine le_trans (le_trans hsum hle) ?_
  have h32 : 25 * (33 : ℕ) ^ 32 ≤ 34 * (2 : ℕ) ^ 161 := by norm_num
  have hpow4 : (25 * (33 : ℕ) ^ 32) ^ 4 ≤ (34 * (2 : ℕ) ^ 161) ^ 4 :=
    Nat.pow_le_pow_left h32 4
  have hnat : (33 : ℕ) ^ 128 ≤ (2 : ℕ) ^ 646 := by
    have h25 : 25 ^ 4 * (33 : ℕ) ^ 128 ≤ 25 ^ 4 * (2 : ℕ) ^ 646 := by
      have h128 : (33 : ℕ) ^ 128 = ((33 : ℕ) ^ 32) ^ 4 := by rw [← pow_mul]
      have h646 : (2 : ℕ) ^ 646 = 4 * ((2 : ℕ) ^ 161) ^ 4 := by
        calc (2 : ℕ) ^ 646 = (2 : ℕ) ^ 2 * (2 : ℕ) ^ (161 * 4) := by rw [← pow_add]
          _ = 4 * ((2 : ℕ) ^ 161) ^ 4 := by rw [pow_mul]; rfl
      have hc : 34 ^ 4 ≤ 4 * 25 ^ 4 := by decide
      calc 25 ^ 4 * (33 : ℕ) ^ 128
          = (25 * (33 : ℕ) ^ 32) ^ 4 := by rw [h128, mul_pow]
        _ ≤ (34 * (2 : ℕ) ^ 161) ^ 4 := hpow4
        _ = 34 ^ 4 * ((2 : ℕ) ^ 161) ^ 4 := by rw [mul_pow]
        _ ≤ (4 * 25 ^ 4) * ((2 : ℕ) ^ 161) ^ 4 := Nat.mul_le_mul_right _ hc
        _ = 25 ^ 4 * (4 * ((2 : ℕ) ^ 161) ^ 4) := by ring
        _ = 25 ^ 4 * (2 : ℕ) ^ 646 := by rw [h646]
    exact Nat.le_of_mul_le_mul_left h25 (by decide)
  have hreal : (33 : ℝ) ^ 128 ≤ (2 : ℝ) ^ 646 := by exact_mod_cast hnat
  have h64 : (64 : ℝ) ^ 128 = (2 : ℝ) ^ 768 := by
    have h64e : (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
    rw [h64e, ← pow_mul]
  have h16384 : (16384 : ℝ) = (2 : ℝ) ^ 14 := by norm_num
  have h788 : (2 : ℝ) ^ 768 * (2 : ℝ) ^ 20 = (2 : ℝ) ^ 788 := by rw [← pow_add]
  have h788' : (2 : ℝ) ^ 788 = (2 : ℝ) ^ 14 * ((2 : ℝ) ^ 128 * (2 : ℝ) ^ 646) := by
    rw [← pow_add, ← pow_add]
  have hpos788 : (0 : ℝ) < (2 : ℝ) ^ 788 := pow_pos (by norm_num) 788
  have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
  rw [div_pow, h64, div_div, h788, ← mul_div_assoc, div_le_div_iff₀ hpos788 hpos128,
      one_mul, h16384, h788']
  calc (2 : ℝ) ^ 14 * (33 : ℝ) ^ 128 * (2 : ℝ) ^ 128
      = (2 : ℝ) ^ 14 * ((2 : ℝ) ^ 128 * (33 : ℝ) ^ 128) := by
        rw [mul_assoc, mul_comm ((33 : ℝ) ^ 128) ((2 : ℝ) ^ 128)]
    _ ≤ (2 : ℝ) ^ 14 * ((2 : ℝ) ^ 128 * (2 : ℝ) ^ 646) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) 14))
        exact mul_le_mul_of_nonneg_left hreal (le_of_lt hpos128)

/-! ## 3. Constructive Negative Controls (Shape 17 128-Bit Envelope) -/

/-- Negative control 1: `Fp^2` external VKs are rejected on the 128-bit Shape 17 envelope. -/
theorem negControl_aggr128_rejects_fp2 (reqUd : Bool) :
    ¬ SecurityEnvelope128Ok 2 6 48 v6Ud160Params reqUd := by
  intro h; exact absurd h.1 (by decide)

/-- Negative control 2: `v5` protocol external VKs are rejected on the 128-bit Shape 17 envelope. -/
theorem negControl_aggr128_rejects_v5_protocol (reqUd : Bool) :
    ¬ SecurityEnvelope128Ok 3 5 48 v6Ud160Params reqUd := by
  intro h; exact absurd h.2.1 (by decide)

/-- Negative control 3: 32-byte digest external VKs are rejected on the 128-bit XOF Shape 17 envelope. -/
theorem negControl_aggr128_rejects_32b_digest (reqUd : Bool) :
    ¬ SecurityEnvelope128Ok 3 6 32 v6Ud160Params reqUd := by
  intro h; exact absurd h.2.2.1 (by decide)

/-- Negative control 4: Weak Shape 17 external VK (`weakExternalStarkParams`, 60 conj. bits)
is rejected on the 128-bit Shape 17 envelope. -/
theorem negControl_aggr128_rejects_weak_envelope (reqUd : Bool) :
    ¬ SecurityEnvelope128Ok 3 6 48 weakExternalStarkParams reqUd := by
  intro h; exact negative_control_weak_security_envelope h.2.2.2.1

/-- Negative control 5: Legacy `v5` default `(2, 100, 0, 20)` is rejected on the 128-bit
Shape 17 envelope in BOTH UD and Johnson modes. -/
theorem negControl_aggr128_rejects_v5_default_100_20 (reqUd : Bool) :
    ¬ SecurityEnvelope128Ok 3 6 48 v5Default100Params reqUd := by
  intro h
  have hprof := (securityEnvelope128Ok_iff_profile ..).mp h
  cases reqUd
  · exact negControl_v5_default_100_20_rejected_128.2.2 hprof
  · exact negControl_v5_default_100_20_rejected_128.2.1 hprof

/-- Negative control 6: Deceptive high-blowup `(4, 55, 0, 0)` is rejected on the 128-bit
Shape 17 envelope in BOTH UD and Johnson modes. -/
theorem negControl_aggr128_rejects_deceptive_4_55_0 (reqUd : Bool) :
    ¬ SecurityEnvelope128Ok 3 6 48 deceptiveHighBlowupParams reqUd := by
  intro h; exact negative_control_deceptive_high_blowup_envelope h.2.2.2.1

end Ix.Cert.Aggr.Security128

/-! ## 4. Mechanical `#guard_msgs` Statement & Axiom Pins -/

/-- info: @Ix.Cert.Aggr.Security128.securityEnvelope128Ok_implies_v5 : ∀ {ext ver dig : ℕ} {p : Ix.Cert.MultiStark.StarkParams} {reqUd : Bool}, Ix.Cert.Aggr.Security128.SecurityEnvelope128Ok ext ver dig p reqUd → Ix.Cert.Aggr.SecurityEnvelopeOk p -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.Security128.securityEnvelope128Ok_implies_v5

/-- info: Ix.Cert.Aggr.Security128.securityEnvelope128Ok_iff_profile : ∀ (ext ver dig : ℕ) (p : Ix.Cert.MultiStark.StarkParams) (reqUd : Bool), Ix.Cert.Aggr.Security128.SecurityEnvelope128Ok ext ver dig p reqUd ↔ Ix.Cert.MultiStark.Security128.Security128Profile ext ver dig p reqUd -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.Security128.securityEnvelope128Ok_iff_profile

/-- info: Ix.Cert.Aggr.Security128.v6_shape17_envelopes_ok : Ix.Cert.Aggr.Security128.SecurityEnvelope128Ok 3 6 48 Ix.Cert.MultiStark.Security128.v6Ud160Params true ∧ Ix.Cert.Aggr.Security128.SecurityEnvelope128Ok 3 6 48 Ix.Cert.MultiStark.Security128.v6Johnson118Params false ∧ Ix.Cert.Aggr.Security128.SecurityEnvelope128Ok 3 6 48 Ix.Cert.MultiStark.Security128.v6Johnson128Params false -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.Security128.v6_shape17_envelopes_ok

/-- info: @Ix.Cert.Aggr.Security128.aggr_shared_log_rom_bound_128 : ∀ {Q M : ℕ}, Q + M ≤ 2 ^ 128 → ∀ {εmax : ℝ}, εmax ≤ 3 / 4 / 2 ^ 128 → ↑(Q + M) * εmax + 3 * ↑(Q + M) ^ 2 / (2 * 2 ^ 384) ≤ ↑(Q + M) / 2 ^ 128 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.Security128.aggr_shared_log_rom_bound_128

/-- info: Ix.Cert.Aggr.Security128.aggr_johnson_128_union_headroom : ∀ (probs : List ℝ), probs.length ≤ 16384 → (∀ p ∈ probs, p ≤ (33 / 64) ^ 128 / 2 ^ 20) → probs.sum ≤ 1 / 2 ^ 128 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.Security128.aggr_johnson_128_union_headroom

/-- info: Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_fp2 : ∀ (reqUd : Bool), ¬Ix.Cert.Aggr.Security128.SecurityEnvelope128Ok 2 6 48 Ix.Cert.MultiStark.Security128.v6Ud160Params reqUd -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_fp2

/-- info: Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_v5_protocol : ∀ (reqUd : Bool), ¬Ix.Cert.Aggr.Security128.SecurityEnvelope128Ok 3 5 48 Ix.Cert.MultiStark.Security128.v6Ud160Params reqUd -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_v5_protocol

/-- info: Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_32b_digest : ∀ (reqUd : Bool), ¬Ix.Cert.Aggr.Security128.SecurityEnvelope128Ok 3 6 32 Ix.Cert.MultiStark.Security128.v6Ud160Params reqUd -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_32b_digest

/-- info: Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_weak_envelope : ∀ (reqUd : Bool), ¬Ix.Cert.Aggr.Security128.SecurityEnvelope128Ok 3 6 48 Ix.Cert.Aggr.weakExternalStarkParams reqUd -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_weak_envelope

/-- info: Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_v5_default_100_20 : ∀ (reqUd : Bool), ¬Ix.Cert.Aggr.Security128.SecurityEnvelope128Ok 3 6 48 Ix.Cert.MultiStark.Security128.v5Default100Params reqUd -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_v5_default_100_20

/-- info: Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_deceptive_4_55_0 : ∀ (reqUd : Bool), ¬Ix.Cert.Aggr.Security128.SecurityEnvelope128Ok 3 6 48 Ix.Cert.Aggr.deceptiveHighBlowupParams reqUd -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_deceptive_4_55_0

/-- info: 'Ix.Cert.Aggr.Security128.securityEnvelope128Ok_implies_v5' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.Security128.securityEnvelope128Ok_implies_v5

/-- info: 'Ix.Cert.Aggr.Security128.securityEnvelope128Ok_iff_profile' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.Security128.securityEnvelope128Ok_iff_profile

/-- info: 'Ix.Cert.Aggr.Security128.v6_shape17_envelopes_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.Security128.v6_shape17_envelopes_ok

/-- info: 'Ix.Cert.Aggr.Security128.aggr_shared_log_rom_bound_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.Security128.aggr_shared_log_rom_bound_128

/-- info: 'Ix.Cert.Aggr.Security128.aggr_johnson_128_union_headroom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.Security128.aggr_johnson_128_union_headroom

/-- info: 'Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_fp2' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_fp2

/-- info: 'Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_v5_protocol' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_v5_protocol

/-- info: 'Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_32b_digest' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_32b_digest

/-- info: 'Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_weak_envelope' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_weak_envelope

/-- info: 'Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_v5_default_100_20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_v5_default_100_20

/-- info: 'Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_deceptive_4_55_0' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.Security128.negControl_aggr128_rejects_deceptive_4_55_0

/-! ## 5. Direct Monolithic Single-Oracle Multi-Node ROM Extraction Wiring (`Ix.Cert.Aggr.MonolithicRom`) -/

/-- info: Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_xof48_rate_128 : ∀ (Q M_verif : ℕ), M_verif ≤ 2 ^ 20 → Q + M_verif ≤ 2 ^ 128 → ∀ {εmax : ℝ}, εmax ≤ 1 / 2 / 2 ^ 128 → Ix.Cert.Aggr.MonolithicRom.monolithicRomBound Q M_verif εmax (3 / 2) (2 ^ 384) ≤ ↑(Q + M_verif) / 2 ^ 128 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_xof48_rate_128

/-- info: Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_xof48_concrete_prob_128 : ∀ (Q M_verif : ℕ), M_verif ≤ 2 ^ 20 → Q + M_verif ≤ 2 ^ 127 → ∀ {εmax : ℝ}, ↑(Q + M_verif) * εmax ≤ 1 / 2 / 2 ^ 128 → Ix.Cert.Aggr.MonolithicRom.monolithicRomBound Q M_verif εmax (3 / 2) (2 ^ 384) ≤ 1 / 2 ^ 128 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_xof48_concrete_prob_128

/-- info: Ix.Cert.Aggr.MonolithicRom.monolithic_beats_union_bound_2_pow_20 : ↑(2 ^ 20) * ↑(2 ^ 108) * (1 / 2 ^ 128) = 1 ∧ Ix.Cert.Aggr.MonolithicRom.monolithicRomBound (2 ^ 108) (2 ^ 20) (1 / 2 ^ 128) (3 / 2) (2 ^ 384) < 1 / 2 ^ 19 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.Aggr.MonolithicRom.monolithic_beats_union_bound_2_pow_20

/-- info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_multiNode_rom_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_multiNode_rom_sound

/-- info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_aggrTree_rom_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_aggrTree_rom_sound

/-- info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_xof48_rate_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_xof48_rate_128

/-- info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_xof48_concrete_prob_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_goldilocksExt3_xof48_concrete_prob_128

/-- info: 'Ix.Cert.Aggr.MonolithicRom.monolithic_beats_union_bound_2_pow_20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.Aggr.MonolithicRom.monolithic_beats_union_bound_2_pow_20
