import Ix.Cert.MultiStark.EndToEnd
import Ix.Cert.MultiStark.Verifier
import Ix.Aiur.Parameters
import CertiFriProofs.Audit128
import CertiFriProofs.Exec.SoundnessTensorSponge

/-! # 128-Bit Multi-STARK & FRI Security Audit Surface (`Ix.Cert.MultiStark.Security128Audit`)

Mechanically pins (via `#guard_msgs` on `#check` and `#print axioms`) the 128-bit
security floor, algebraic field entropy, incremental-sponge 64-byte RFC 7693
`BLAKE2b-512` collision bounds (classical BCS `255.71b`, BHT quantum `170.7b`,
CNS quantum `204.8b`, Grover preimage `256b`), and literal `≤ N / 2 ^ 128` FRI
soundness budgets for the Goldilocks cubic-extension (`Fp^3`, `multi-stark` `v6`)
profile, together with constructive negative controls rejecting `Fp^2`,
`(2, 100, 0, 20)`, `(4, 55, 0, 0)`, 32-byte digests at `N = 2 ^ 128` / BHT quantum
`Q = 2 ^ 86`, and legacy 48-byte `BLAKE3-XOF48` for concrete 128-bit PQ.

### Classical vs. Post-Quantum Hash Separation
- **Production 128-bit classical:** 32-byte `BLAKE3-256` (`digestBytesBlake3_256 = 32`,
  `127.71b` classical BCS / `85.3b` BHT quantum) with native BLAKE3 `derive_key`
  domain separation (`CertiFri.P3.Blake3Domain`).
- **64-byte profile (no prover or verifier uses it; every theorem is classical-ROM, and the
  BHT/CNS/Grover figures are inequalities about `2 ^ 512`, not quantum theorems):**
  64-byte RFC 7693 `BLAKE2b-512`
  (`digestBytesBlake2b512 = 64`, true 512-bit internal state, 128-byte block =
  single-block 2-to-1 Merkle compression, RFC 7693 `personal` domain separation via
  `CertiFri.P3.Blake2b512Domain`). `BLAKE3-XOF48`/`BLAKE3-XOF64` are excluded from
  concrete 128-bit PQ because BLAKE3's 256-bit internal `cv` caps concrete BHT
  collision resistance at `85.3b` on every `> 64`-byte input.

### Direct Unconditional `CertiFRI` Wiring (pinned `CertiFRI` `e815d47`)
Imports `CertiFriProofs.Audit128` and `CertiFriProofs.Exec.SoundnessTensorSponge` directly
and locks:
- RFC 7693 `BLAKE2b-512` kernel-checked KATs, `Blake2b512Domain` / `Blake3Domain` injectivity,
  `card_digest64` (`2 ^ 512`), and BHT/CNS/Grover arithmetic bounds;
- Unconditional `GoldilocksExt3` + incremental sponge (`c = 3 / 2`) executable FRI soundness
  theorems for Horner-batched `Fri.verify`, binary tensor-batched `Fri.verifyTensor`, and
  multi-arity (`2^a`, `logArity ∈ {1, 2, 3}`, fold factors `2, 4, 8`) tensor-batched FRI
  including `FriParams.compact400KBBalanced` (`lb = 4, maxLogArity = 3, q = 58, pow = 28`)
  and `FriParams.ultraCompact400KBZk` (`lb = 4, maxLogArity = 3, q = 55, pow = 30`), across
  both unique-decoding and unconditional Johnson (`lb = 2, 3, 4`, zero `CurveListCA`
  hypothesis) regimes over 32-byte `BLAKE3` (`Digest`) and 64-byte `BLAKE2b-512` (`Digest64`);
- Cubic-extension (`Fp3Model`) `GoldilocksExt3.starkModel`, concrete `DynamicRom`
  instantiations (`soundness_dynamic_rom_starkTensor_fp3_ud`,
  `soundness_dynamic_rom_starkTensorMulti_fp3_ud`), and unpruned & pruned-MMCS
  (`CertiFri.P3.prunedMmcs`) binary and multi-arity tensor-batched STARK + LogUp soundness;
- Protocol `v6-zk` formal Honest-Verifier Zero-Knowledge (`v6Zk_alg_perfect_hvzk`,
  `v6Zk_hvzk`, `goldilocksExt3_v6Zk_hvzk`, `goldilocksExt3_v6Zk_hvzk_salt32`,
  `goldilocksExt3_ultraCompact400KBZk_hvzk`, `goldilocksExt3_ultraCompact400KBZk_hvzk_salt32`,
  `goldilocksExt3_v6Zk_hvzk_with_tensor4_span`) covering polynomial blinding, masked-LogUp
  boundary hiding, multi-arity FRI randomizer uniformity, and salted-Merkle leaf hiding
  for both 16-byte (`2^128`) and 32-byte (`2^256`) salts —
together with their strict `[propext, Classical.choice, Quot.sound]` axiom footprints.

What these theorems are about: the executable soundness and HVZK theorems concern
`CertiFRI`'s Lean verifiers and `v6-zk` ROM model (binary and multi-arity `2^a` / 8-ary
tensor-batched FRI, unpruned and pruned-MMCS `GoldilocksExt3` STARKs, and salted-Merkle
`v6-zk` transcripts) under the idealized classical ROM (`c = 3 / 2` incremental sponge),
not the compiled Rust `multi-stark` binary directly. None considers a quantum adversary.

Every theorem pinned here depends strictly on standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) — zero `sorry`, zero custom
axioms, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.MultiStark.Security128

open CertiFri CertiFri.P3

/-! ## 1. `v6` 128-Bit Multi-STARK Security Profile Predicate -/

/-- Production 128-bit classical digest width in bytes (`BLAKE3-256`: 32 bytes = 256 bits,
`127.71b` classical BCS / `85.3b` BHT quantum). -/
def digestBytesBlake3_256 : Nat := 32

/-- Certified 128-bit post-quantum digest width in bytes (RFC 7693 `BLAKE2b-512`:
64 bytes = 512 bits, true 512-bit internal state, 128-byte block = single-block 2-to-1
Merkle compression; `255.71b` classical BCS / `170.7b` BHT / `204.8b` CNS / `256b` Grover). -/
def digestBytesBlake2b512 : Nat := 64

/-- Formal 128-bit post-quantum `v6` Multi-STARK parameter profile:
* Cubic Goldilocks extension (`extensionDegree ≥ 3`, `p^3 ≥ 2^191`);
* Protocol version `≥ 6` (domain-separated commitments and transcripts);
* 64-byte (512-bit) RFC 7693 `BLAKE2b-512` digest (`digestBytes ≥ 64`, true 512-bit
  internal state giving `255.71b` classical BCS, `170.7b` BHT quantum, `204.8b` CNS
  quantum, and `256b` Grover preimage resistance — rejecting both 32-byte `BLAKE3-256`
  and retired 48-byte `BLAKE3-XOF48` for concrete 128-bit PQ);
* FRI parameters meeting `Aiur.meetsSecurityFloor128Ud` (when `requireUd = true`)
  or `Aiur.meetsSecurityFloor128Johnson` (when `requireUd = false`). -/
def Security128Profile (extensionDegree protocolVersion digestBytes : Nat)
    (p : StarkParams) (requireUd : Bool) : Prop :=
  Aiur.extensionDegreeV6 ≤ extensionDegree ∧
  Aiur.protocolVersionV6 ≤ protocolVersion ∧
  digestBytesBlake2b512 ≤ digestBytes ∧
  (if requireUd then
    Aiur.meetsSecurityFloor128Ud extensionDegree protocolVersion
      ⟨p.logBlowup, p.capHeight⟩
      ⟨p.logFinalPolyLen, p.maxLogArity, p.numQueries, p.commitPowBits, p.queryPowBits⟩ = true
  else
    Aiur.meetsSecurityFloor128Johnson extensionDegree protocolVersion
      ⟨p.logBlowup, p.capHeight⟩
      ⟨p.logFinalPolyLen, p.maxLogArity, p.numQueries, p.commitPowBits, p.queryPowBits⟩ = true)

/-- Canonical `v6` unconditional 128-bit unique-decoding parameters `(2, 160, 0, 20)`. -/
def v6Ud160Params : StarkParams :=
  { logBlowup := 2
    capHeight := 0
    logFinalPolyLen := 0
    maxLogArity := 1
    numQueries := 160
    commitPowBits := 0
    queryPowBits := 20 }

/-- Lower-edge `v6` 128-bit Johnson parameters `(2, 118, 0, 20)`. -/
def v6Johnson118Params : StarkParams :=
  { logBlowup := 2
    capHeight := 0
    logFinalPolyLen := 0
    maxLogArity := 1
    numQueries := 118
    commitPowBits := 0
    queryPowBits := 20 }

/-- Recommended `v6` 128-bit Johnson parameters `(2, 128, 0, 20)` (`142.24b` finite-`m` Johnson). -/
def v6Johnson128Params : StarkParams :=
  { logBlowup := 2
    capHeight := 0
    logFinalPolyLen := 0
    maxLogArity := 1
    numQueries := 128
    commitPowBits := 0
    queryPowBits := 20 }

/-- Legacy `v5` default parameters `(2, 100, 0, 20)`. -/
def v5Default100Params : StarkParams :=
  { logBlowup := 2
    capHeight := 0
    logFinalPolyLen := 0
    maxLogArity := 1
    numQueries := 100
    commitPowBits := 0
    queryPowBits := 20 }

/-- Deceptive high-blowup / low-query parameters `(4, 55, 0, 0)`. -/
def deceptive455Params : StarkParams :=
  { logBlowup := 4
    capHeight := 0
    logFinalPolyLen := 0
    maxLogArity := 1
    numQueries := 55
    commitPowBits := 0
    queryPowBits := 0 }

/-! ## 2. Field Entropy, Query Soundness & 64-Byte RFC 7693 `BLAKE2b-512` Theorems -/

/-- Goldilocks cubic extension `Fp^3` has strictly more than `2^191` elements
(`p = 2^64 - 2^32 + 1`, `p^3 > 2^191`), clearing 128-bit field entropy with `> 63` bits of headroom. -/
theorem goldilocks_fp3_card_ge_2_pow_191 :
    2 ^ 191 ≤ Goldilocks.order ^ 3 := by
  unfold Goldilocks.order
  norm_num

/-- Unconditional unique-decoding query soundness at `(logBlowup = 2, numQueries = 160, queryPow = 20)`:
`(5 / 8)^160 / 2^20 ≤ (3 / 4) / 2^128` (`128.49` bits). -/
theorem ud_160_pow20_query_error_le_128 :
    ((5 / 8 : ℝ) ^ 160) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have h80 : 7 * (5 : ℕ) ^ 80 ≤ 6 * (2 : ℕ) ^ 186 := by norm_num
  have hsq : (7 * (5 : ℕ) ^ 80) ^ 2 ≤ (6 * (2 : ℕ) ^ 186) ^ 2 :=
    Nat.pow_le_pow_left h80 2
  have hnat : 4 * (5 : ℕ) ^ 160 ≤ 3 * (2 : ℕ) ^ 372 := by
    have h49 : 49 * (4 * (5 : ℕ) ^ 160) ≤ 49 * (3 * (2 : ℕ) ^ 372) := by
      have hL : 49 * (4 * (5 : ℕ) ^ 160) = 4 * (7 * (5 : ℕ) ^ 80) ^ 2 := by
        have h160 : (5 : ℕ) ^ 160 = ((5 : ℕ) ^ 80) ^ 2 := by rw [← pow_mul]
        rw [h160, mul_pow]
        ring
      have hR : 4 * (6 * (2 : ℕ) ^ 186) ^ 2 ≤ 49 * (3 * (2 : ℕ) ^ 372) := by
        have h372 : (2 : ℕ) ^ 372 = ((2 : ℕ) ^ 186) ^ 2 := by rw [← pow_mul]
        rw [h372, mul_pow]
        have hc : 4 * 6 ^ 2 ≤ 49 * 3 := by decide
        calc 4 * (6 ^ 2 * ((2 : ℕ) ^ 186) ^ 2)
            = (4 * 6 ^ 2) * ((2 : ℕ) ^ 186) ^ 2 := by ring
          _ ≤ (49 * 3) * ((2 : ℕ) ^ 186) ^ 2 := Nat.mul_le_mul_right _ hc
          _ = 49 * (3 * ((2 : ℕ) ^ 186) ^ 2) := by ring
      calc 49 * (4 * (5 : ℕ) ^ 160)
          = 4 * (7 * (5 : ℕ) ^ 80) ^ 2 := hL
        _ ≤ 4 * (6 * (2 : ℕ) ^ 186) ^ 2 := Nat.mul_le_mul_left 4 hsq
        _ ≤ 49 * (3 * (2 : ℕ) ^ 372) := hR
    exact Nat.le_of_mul_le_mul_left h49 (by decide)
  have hreal : (4 : ℝ) * (5 : ℝ) ^ 160 ≤ (3 : ℝ) * (2 : ℝ) ^ 372 := by
    exact_mod_cast hnat
  have h8 : (8 : ℝ) ^ 160 = (2 : ℝ) ^ 480 := by
    have h8e : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
    rw [h8e, ← pow_mul]
  have h500 : (2 : ℝ) ^ 480 * (2 : ℝ) ^ 20 = (2 : ℝ) ^ 500 := by rw [← pow_add]
  have h500' : (2 : ℝ) ^ 500 = (2 : ℝ) ^ 128 * (2 : ℝ) ^ 372 := by rw [← pow_add]
  have hpos500 : (0 : ℝ) < (2 : ℝ) ^ 500 := pow_pos (by norm_num) 500
  have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
  rw [div_pow, h8, div_div, h500, div_le_div_iff₀ hpos500 hpos128]
  have hmul : (4 : ℝ) * ((5 : ℝ) ^ 160 * (2 : ℝ) ^ 128) ≤ (4 : ℝ) * ((3 / 4 : ℝ) * (2 : ℝ) ^ 500) := by
    calc (4 : ℝ) * ((5 : ℝ) ^ 160 * (2 : ℝ) ^ 128)
        = ((4 : ℝ) * (5 : ℝ) ^ 160) * (2 : ℝ) ^ 128 := by rw [mul_assoc]
      _ ≤ ((3 : ℝ) * (2 : ℝ) ^ 372) * (2 : ℝ) ^ 128 :=
          mul_le_mul_of_nonneg_right hreal (le_of_lt hpos128)
      _ = (3 : ℝ) * ((2 : ℝ) ^ 128 * (2 : ℝ) ^ 372) := by
          rw [mul_assoc, mul_comm ((2 : ℝ) ^ 372) ((2 : ℝ) ^ 128)]
      _ = (3 : ℝ) * (2 : ℝ) ^ 500 := by rw [h500']
      _ = (4 : ℝ) * ((3 / 4 : ℝ) * (2 : ℝ) ^ 500) := by
          rw [← mul_assoc]; norm_num
  exact le_of_mul_le_mul_left hmul (by norm_num)

/-- Finite-`m` (`m = 16`, per-query factor `(1 + 1/32) · √(1/4) = 33 / 64`) Johnson-regime
query soundness at `logBlowup = 2, queryPow = 20` for EVERY `q ≥ 118` (covering `q = 118..128`):
`(33 / 64)^q / 2^20 ≤ (3 / 4) / 2^128` (`≥ 132.7` bits). -/
theorem johnson_118_pow20_query_error_le_128 {q : ℕ} (hq : 118 ≤ q) :
    ((33 / 64 : ℝ) ^ q) / (2 : ℝ) ^ 20 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have hmono : (33 / 64 : ℝ) ^ q ≤ (33 / 64 : ℝ) ^ 118 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have hdiv : ((33 / 64 : ℝ) ^ q) / (2 : ℝ) ^ 20 ≤ ((33 / 64 : ℝ) ^ 118) / (2 : ℝ) ^ 20 :=
    div_le_div_of_nonneg_right hmono (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) 20))
  refine le_trans hdiv ?_
  have h29 : (33 : ℕ) ^ 29 ≤ (2 : ℕ) ^ 147 := by norm_num
  have hpow4 : ((33 : ℕ) ^ 29) ^ 4 ≤ ((2 : ℕ) ^ 147) ^ 4 := Nat.pow_le_pow_left h29 4
  have hnat : 4 * (33 : ℕ) ^ 118 ≤ 3 * (2 : ℕ) ^ 600 := by
    have h118 : (33 : ℕ) ^ 118 = 33 ^ 2 * ((33 : ℕ) ^ 29) ^ 4 := by
      rw [← pow_mul, ← pow_add]
    have h600 : (2 : ℕ) ^ 600 = 2 ^ 12 * ((2 : ℕ) ^ 147) ^ 4 := by
      rw [← pow_mul, ← pow_add]
    have hc : 4 * 33 ^ 2 ≤ 3 * 2 ^ 12 := by decide
    rw [h118, h600]
    calc 4 * (33 ^ 2 * ((33 : ℕ) ^ 29) ^ 4)
        = (4 * 33 ^ 2) * ((33 : ℕ) ^ 29) ^ 4 := by ring
      _ ≤ (3 * 2 ^ 12) * ((2 : ℕ) ^ 147) ^ 4 := Nat.mul_le_mul hc hpow4
      _ = 3 * (2 ^ 12 * ((2 : ℕ) ^ 147) ^ 4) := by ring
  have hreal : (4 : ℝ) * (33 : ℝ) ^ 118 ≤ (3 : ℝ) * (2 : ℝ) ^ 600 := by
    exact_mod_cast hnat
  have h64 : (64 : ℝ) ^ 118 = (2 : ℝ) ^ 708 := by
    have h64e : (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
    rw [h64e, ← pow_mul]
  have h728 : (2 : ℝ) ^ 708 * (2 : ℝ) ^ 20 = (2 : ℝ) ^ 728 := by rw [← pow_add]
  have h728' : (2 : ℝ) ^ 728 = (2 : ℝ) ^ 128 * (2 : ℝ) ^ 600 := by rw [← pow_add]
  have hpos728 : (0 : ℝ) < (2 : ℝ) ^ 728 := pow_pos (by norm_num) 728
  have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
  rw [div_pow, h64, div_div, h728, div_le_div_iff₀ hpos728 hpos128]
  have hmul : (4 : ℝ) * ((33 : ℝ) ^ 118 * (2 : ℝ) ^ 128) ≤ (4 : ℝ) * ((3 / 4 : ℝ) * (2 : ℝ) ^ 728) := by
    calc (4 : ℝ) * ((33 : ℝ) ^ 118 * (2 : ℝ) ^ 128)
        = ((4 : ℝ) * (33 : ℝ) ^ 118) * (2 : ℝ) ^ 128 := by rw [mul_assoc]
      _ ≤ ((3 : ℝ) * (2 : ℝ) ^ 600) * (2 : ℝ) ^ 128 :=
          mul_le_mul_of_nonneg_right hreal (le_of_lt hpos128)
      _ = (3 : ℝ) * ((2 : ℝ) ^ 128 * (2 : ℝ) ^ 600) := by
          rw [mul_assoc, mul_comm ((2 : ℝ) ^ 600) ((2 : ℝ) ^ 128)]
      _ = (3 : ℝ) * (2 : ℝ) ^ 728 := by rw [h728']
      _ = (4 : ℝ) * ((3 / 4 : ℝ) * (2 : ℝ) ^ 728) := by
          rw [← mul_assoc]; norm_num
  exact le_of_mul_le_mul_left hmul (by norm_num)

/-- Tight incremental-sponge BCS collision bound (`entryCap = 1`, `c = 3 / 2`) over 64-byte
(512-bit) RFC 7693 `BLAKE2b-512` digests (true 512-bit internal state): for every query budget
`N ≤ 2^128`, `3 * N^2 / (2 * 2^512) ≤ N / (4 * 2^128)` (`255.71b` classical threshold). -/
theorem sponge_blake2b512_classical_collision_le_128 {N : ℕ} (hN : N ≤ 2 ^ 128) :
    (3 : ℝ) * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 512) ≤ (N : ℝ) / (4 * (2 : ℝ) ^ 128) := by
  have h := CertiFri.P3.digest64_sponge_collision_le_quarter_128 hN
  rw [CertiFri.P3.card_digest64, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- Brassard–Høyer–Tapp (BHT) / Zhandry QROM quantum collision bound at `Q ≤ 2^128` for 64-byte
(512-bit) RFC 7693 `BLAKE2b-512`: `Q^3 / 2^512 ≤ 1 / 2^128` (`+42.7b` headroom above 128-bit PQ!). -/
theorem sponge_blake2b512_bht_quantum_128 {Q : ℕ} (hQ : Q ≤ 2 ^ 128) :
    (Q : ℝ) ^ 3 / (2 : ℝ) ^ 512 ≤ 1 / (2 : ℝ) ^ 128 := by
  have h := CertiFri.P3.digest64_bht_quantum_collision_at_128 hQ
  rw [CertiFri.P3.card_digest64, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- BHT / Zhandry QROM quantum collision threshold (`170.7b`) for 64-byte RFC 7693 `BLAKE2b-512`:
for all `Q ≤ 2^170`, `Q^3 / 2^512 ≤ 1 / 4 < 1`. -/
theorem sponge_blake2b512_bht_quantum_170 {Q : ℕ} (hQ : Q ≤ 2 ^ 170) :
    (Q : ℝ) ^ 3 / (2 : ℝ) ^ 512 ≤ 1 / 4 := by
  have h := CertiFri.P3.digest64_bht_quantum_collision_at_170 hQ
  rw [CertiFri.P3.card_digest64, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- CNS (non-qRAM) quantum collision threshold (`204.8b`) for 64-byte RFC 7693 `BLAKE2b-512`:
for all `Q ≤ 2^204`, `Q^5 / (2^512)^2 ≤ 1 / 16 < 1`. -/
theorem sponge_blake2b512_cns_quantum_204 {Q : ℕ} (hQ : Q ≤ 2 ^ 204) :
    (Q : ℝ) ^ 5 / ((2 : ℝ) ^ 512) ^ 2 ≤ 1 / 16 := by
  have h := CertiFri.P3.digest64_cns_quantum_collision_at_204 hQ
  rw [CertiFri.P3.card_digest64, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- Grover quantum preimage bound (`256b`) for 64-byte RFC 7693 `BLAKE2b-512`:
`Q^2 / 2^512 = (Q / 2^256)^2`. -/
theorem sponge_blake2b512_grover_preimage_256 (Q : ℕ) :
    (Q : ℝ) ^ 2 / (2 : ℝ) ^ 512 = ((Q : ℝ) / (2 : ℝ) ^ 256) ^ 2 := by
  have h := CertiFri.P3.digest64_grover_preimage Q
  rw [CertiFri.P3.card_digest64, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- Composite literal `≤ N / 2^128` 128-bit ROM soundness budget combining round error
`εmax ≤ (3 / 4) / 2^128` with incremental-sponge 64-byte RFC 7693 `BLAKE2b-512` collision error
for any query budget `N ≤ 2^128`. -/
theorem fp3_blake2b512_total_budget_le_128 {N : ℕ} (hN : N ≤ 2 ^ 128)
    {εmax : ℝ} (hε : εmax ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128) :
    (N : ℝ) * εmax + (3 : ℝ) * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 512) ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : (N : ℝ) * εmax ≤ (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) :=
    mul_le_mul_of_nonneg_left hε hN0
  have h2 := sponge_blake2b512_classical_collision_le_128 hN
  calc (N : ℝ) * εmax + (3 : ℝ) * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 512)
      ≤ (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + (N : ℝ) / (4 * (2 : ℝ) ^ 128) :=
        add_le_add h1 h2
    _ = (N : ℝ) / (2 : ℝ) ^ 128 := by ring

/-- Positive profile certificates: `v6` `Fp^3` + 64B RFC 7693 `BLAKE2b-512` passes at
UD `(2, 160, 0, 20)` and Johnson `(2, 118, 0, 20)` / `(2, 128, 0, 20)`. -/
theorem v6_positive_128_profiles :
    Security128Profile 3 6 64 v6Ud160Params true ∧
    Security128Profile 3 6 64 v6Johnson118Params false ∧
    Security128Profile 3 6 64 v6Johnson128Params false := by
  refine ⟨⟨by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide⟩⟩

/-! ## 3. Constructive Negative Controls (Boundary Tightness) -/

/-- Negative control 1: Goldilocks `Fp^2` (`p^2 < 2^128`) has strictly fewer than 128 bits
of field entropy and is rejected by `Security128Profile` in BOTH UD and Johnson modes. -/
theorem negControl_fp2_rejected_128 :
    Goldilocks.order ^ 2 < 2 ^ 128 ∧
    ¬ Security128Profile 2 6 64 v6Ud160Params true ∧
    ¬ Security128Profile 2 6 64 v6Johnson128Params false := by
  refine ⟨by unfold Goldilocks.order; norm_num, ?_, ?_⟩
  · intro h; exact absurd h.1 (by decide)
  · intro h; exact absurd h.1 (by decide)

/-- Negative control 2: Legacy `v5` default `(2, 100, 0, 20)` strictly fails `1 / 2^128`
unique-decoding soundness and is rejected by `Security128Profile` in BOTH UD and Johnson modes. -/
theorem negControl_v5_default_100_20_rejected_128 :
    (1 : ℝ) / (2 : ℝ) ^ 128 < ((5 / 8 : ℝ) ^ 100) / (2 : ℝ) ^ 20 ∧
    ¬ Security128Profile 3 6 64 v5Default100Params true ∧
    ¬ Security128Profile 3 6 64 v5Default100Params false := by
  refine ⟨?_, ?_, ?_⟩
  · have h5 : (2 : ℕ) ^ 192 < (5 : ℕ) ^ 100 := by norm_num
    have h5r : (2 : ℝ) ^ 192 < (5 : ℝ) ^ 100 := by exact_mod_cast h5
    have h8 : (8 : ℝ) ^ 100 = (2 : ℝ) ^ 300 := by
      have h8e : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      rw [h8e, ← pow_mul]
    have h320 : (2 : ℝ) ^ 300 * (2 : ℝ) ^ 20 = (2 : ℝ) ^ 320 := by rw [← pow_add]
    have h320' : (2 : ℝ) ^ 320 = (2 : ℝ) ^ 128 * (2 : ℝ) ^ 192 := by rw [← pow_add]
    have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
    have hpos320 : (0 : ℝ) < (2 : ℝ) ^ 320 := pow_pos (by norm_num) 320
    rw [div_pow, h8, div_div, h320, div_lt_div_iff₀ hpos128 hpos320, one_mul, h320']
    rw [mul_comm ((5 : ℝ) ^ 100) ((2 : ℝ) ^ 128)]
    exact mul_lt_mul_of_pos_left h5r hpos128
  · intro h
    have hok := h.2.2.2
    simp only [ite_true] at hok
    exact absurd hok (by decide)
  · intro h
    have hok := h.2.2.2
    simp only [Bool.false_eq_true, ite_false] at hok
    exact absurd hok (by decide)

/-- Negative control 3: Deceptive high-blowup `(4, 55, 0, 0)` strictly fails `1 / 2^128`
unique-decoding soundness and is rejected by `Security128Profile` in BOTH UD and Johnson modes. -/
theorem negControl_deceptive_4_55_0_rejected_128 :
    (1 : ℝ) / (2 : ℝ) ^ 128 < (17 / 32 : ℝ) ^ 55 ∧
    ¬ Security128Profile 3 6 64 deceptive455Params true ∧
    ¬ Security128Profile 3 6 64 deceptive455Params false := by
  refine ⟨?_, ?_, ?_⟩
  · have h17 : (2 : ℕ) ^ 147 < (17 : ℕ) ^ 55 := by norm_num
    have h17r : (2 : ℝ) ^ 147 < (17 : ℝ) ^ 55 := by exact_mod_cast h17
    have h32 : (32 : ℝ) ^ 55 = (2 : ℝ) ^ 275 := by
      have h32e : (32 : ℝ) = (2 : ℝ) ^ 5 := by norm_num
      rw [h32e, ← pow_mul]
    have h275 : (2 : ℝ) ^ 275 = (2 : ℝ) ^ 128 * (2 : ℝ) ^ 147 := by rw [← pow_add]
    have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
    have hpos275 : (0 : ℝ) < (2 : ℝ) ^ 275 := pow_pos (by norm_num) 275
    rw [div_pow, h32, div_lt_div_iff₀ hpos128 hpos275, one_mul, h275]
    rw [mul_comm ((17 : ℝ) ^ 55) ((2 : ℝ) ^ 128)]
    exact mul_lt_mul_of_pos_left h17r hpos128
  · intro h
    have hok := h.2.2.2
    simp only [ite_true] at hok
    exact absurd hok (by decide)
  · intro h
    have hok := h.2.2.2
    simp only [Bool.false_eq_true, ite_false] at hok
    exact absurd hok (by decide)

/-- Negative control 4: 32-byte (256-bit) `BLAKE3-256` digests (production 128-bit classical)
fail BOTH classical BCS at the exact `N = 2^128` boundary (`3/2 > 1`) AND BHT quantum
collision resistance at `Q = 2^86` (`2^258 / 2^256 = 4 > 1`, i.e., `85.3b`), and are rejected
by the 128-bit PQ `Security128Profile`. -/
theorem negControl_digest32_rejected_128 :
    (1 : ℝ) < (3 : ℝ) * ((2 ^ 128 : ℕ) : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 256) ∧
    (1 : ℝ) < ((2 ^ 86 : ℕ) : ℝ) ^ 3 / (2 : ℝ) ^ 256 ∧
    ¬ Security128Profile 3 6 32 v6Ud160Params true := by
  refine ⟨?_, ?_, ?_⟩
  · have h256 : ((2 ^ 128 : ℕ) : ℝ) ^ 2 = (2 : ℝ) ^ 256 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    rw [h256]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ 256 := pow_pos (by norm_num) 256
    rw [one_lt_div (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ 256)]
    linarith
  · have h258 : ((2 ^ 86 : ℕ) : ℝ) ^ 3 = (4 : ℝ) * (2 : ℝ) ^ 256 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
      have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [h4, ← pow_add]
    rw [h258]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ 256 := pow_pos (by norm_num) 256
    rw [one_lt_div hpos]
    linarith
  · intro h; exact absurd h.2.2.1 (by decide)

/-- Negative control 5: Legacy 48-byte `BLAKE3-XOF48` digests are rejected by the 128-bit PQ
`Security128Profile` in BOTH UD and Johnson modes (BLAKE3's 256-bit internal `cv` caps
concrete collision resistance at `128b` classical / `85.3b` BHT quantum on every `> 64`-byte
input; 64-byte RFC 7693 `BLAKE2b-512` with a true 512-bit internal state is required). -/
theorem negControl_digest48_xof_rejected_128 :
    ¬ Security128Profile 3 6 48 v6Ud160Params true ∧
    ¬ Security128Profile 3 6 48 v6Johnson128Params false := by
  refine ⟨?_, ?_⟩
  · intro h; exact absurd h.2.2.1 (by decide)
  · intro h; exact absurd h.2.2.1 (by decide)

end Ix.Cert.MultiStark.Security128

/-! ## 4. Mechanical `#guard_msgs` Statement & Axiom Pins -/

/-- info: Ix.Cert.MultiStark.Security128.goldilocks_fp3_card_ge_2_pow_191 : 2 ^ 191 ≤ CertiFri.P3.Goldilocks.order ^ 3 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.goldilocks_fp3_card_ge_2_pow_191

/-- info: Ix.Cert.MultiStark.Security128.ud_160_pow20_query_error_le_128 : (5 / 8) ^ 160 / 2 ^ 20 ≤ 3 / 4 / 2 ^ 128 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.ud_160_pow20_query_error_le_128

/-- info: @Ix.Cert.MultiStark.Security128.johnson_118_pow20_query_error_le_128 : ∀ {q : ℕ}, 118 ≤ q → (33 / 64) ^ q / 2 ^ 20 ≤ 3 / 4 / 2 ^ 128 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.johnson_118_pow20_query_error_le_128

/-- info: @Ix.Cert.MultiStark.Security128.sponge_blake2b512_classical_collision_le_128 : ∀ {N : ℕ}, N ≤ 2 ^ 128 → 3 * ↑N ^ 2 / (2 * 2 ^ 512) ≤ ↑N / (4 * 2 ^ 128) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.sponge_blake2b512_classical_collision_le_128

/-- info: @Ix.Cert.MultiStark.Security128.sponge_blake2b512_bht_quantum_128 : ∀ {Q : ℕ}, Q ≤ 2 ^ 128 → ↑Q ^ 3 / 2 ^ 512 ≤ 1 / 2 ^ 128 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.sponge_blake2b512_bht_quantum_128

/-- info: @Ix.Cert.MultiStark.Security128.sponge_blake2b512_bht_quantum_170 : ∀ {Q : ℕ}, Q ≤ 2 ^ 170 → ↑Q ^ 3 / 2 ^ 512 ≤ 1 / 4 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.sponge_blake2b512_bht_quantum_170

/-- info: @Ix.Cert.MultiStark.Security128.sponge_blake2b512_cns_quantum_204 : ∀ {Q : ℕ}, Q ≤ 2 ^ 204 → ↑Q ^ 5 / (2 ^ 512) ^ 2 ≤ 1 / 16 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.sponge_blake2b512_cns_quantum_204

/-- info: Ix.Cert.MultiStark.Security128.sponge_blake2b512_grover_preimage_256 : ∀ (Q : ℕ), ↑Q ^ 2 / 2 ^ 512 = (↑Q / 2 ^ 256) ^ 2 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.sponge_blake2b512_grover_preimage_256

/-- info: @Ix.Cert.MultiStark.Security128.fp3_blake2b512_total_budget_le_128 : ∀ {N : ℕ}, N ≤ 2 ^ 128 → ∀ {εmax : ℝ}, εmax ≤ 3 / 4 / 2 ^ 128 → ↑N * εmax + 3 * ↑N ^ 2 / (2 * 2 ^ 512) ≤ ↑N / 2 ^ 128 -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.fp3_blake2b512_total_budget_le_128

/-- info: Ix.Cert.MultiStark.Security128.v6_positive_128_profiles : Ix.Cert.MultiStark.Security128.Security128Profile 3 6 64 Ix.Cert.MultiStark.Security128.v6Ud160Params true ∧ Ix.Cert.MultiStark.Security128.Security128Profile 3 6 64 Ix.Cert.MultiStark.Security128.v6Johnson118Params false ∧ Ix.Cert.MultiStark.Security128.Security128Profile 3 6 64 Ix.Cert.MultiStark.Security128.v6Johnson128Params false -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.v6_positive_128_profiles

/-- info: Ix.Cert.MultiStark.Security128.negControl_fp2_rejected_128 : CertiFri.P3.Goldilocks.order ^ 2 < 2 ^ 128 ∧ ¬Ix.Cert.MultiStark.Security128.Security128Profile 2 6 64 Ix.Cert.MultiStark.Security128.v6Ud160Params true ∧ ¬Ix.Cert.MultiStark.Security128.Security128Profile 2 6 64 Ix.Cert.MultiStark.Security128.v6Johnson128Params false -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.negControl_fp2_rejected_128

/-- info: Ix.Cert.MultiStark.Security128.negControl_v5_default_100_20_rejected_128 : 1 / 2 ^ 128 < (5 / 8) ^ 100 / 2 ^ 20 ∧ ¬Ix.Cert.MultiStark.Security128.Security128Profile 3 6 64 Ix.Cert.MultiStark.Security128.v5Default100Params true ∧ ¬Ix.Cert.MultiStark.Security128.Security128Profile 3 6 64 Ix.Cert.MultiStark.Security128.v5Default100Params false -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.negControl_v5_default_100_20_rejected_128

/-- info: Ix.Cert.MultiStark.Security128.negControl_deceptive_4_55_0_rejected_128 : 1 / 2 ^ 128 < (17 / 32) ^ 55 ∧ ¬Ix.Cert.MultiStark.Security128.Security128Profile 3 6 64 Ix.Cert.MultiStark.Security128.deceptive455Params true ∧ ¬Ix.Cert.MultiStark.Security128.Security128Profile 3 6 64 Ix.Cert.MultiStark.Security128.deceptive455Params false -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.negControl_deceptive_4_55_0_rejected_128

/-- info: Ix.Cert.MultiStark.Security128.negControl_digest32_rejected_128 : 1 < 3 * ↑(2 ^ 128) ^ 2 / (2 * 2 ^ 256) ∧ 1 < ↑(2 ^ 86) ^ 3 / 2 ^ 256 ∧ ¬Ix.Cert.MultiStark.Security128.Security128Profile 3 6 32 Ix.Cert.MultiStark.Security128.v6Ud160Params true -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.negControl_digest32_rejected_128

/-- info: Ix.Cert.MultiStark.Security128.negControl_digest48_xof_rejected_128 : ¬Ix.Cert.MultiStark.Security128.Security128Profile 3 6 48 Ix.Cert.MultiStark.Security128.v6Ud160Params true ∧ ¬Ix.Cert.MultiStark.Security128.Security128Profile 3 6 48 Ix.Cert.MultiStark.Security128.v6Johnson128Params false -/
#guard_msgs (whitespace := lax) in
#check @Ix.Cert.MultiStark.Security128.negControl_digest48_xof_rejected_128

/-- info: 'Ix.Cert.MultiStark.Security128.goldilocks_fp3_card_ge_2_pow_191' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.goldilocks_fp3_card_ge_2_pow_191

/-- info: 'Ix.Cert.MultiStark.Security128.ud_160_pow20_query_error_le_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.ud_160_pow20_query_error_le_128

/-- info: 'Ix.Cert.MultiStark.Security128.johnson_118_pow20_query_error_le_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.johnson_118_pow20_query_error_le_128

/-- info: 'Ix.Cert.MultiStark.Security128.sponge_blake2b512_classical_collision_le_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.sponge_blake2b512_classical_collision_le_128

/-- info: 'Ix.Cert.MultiStark.Security128.sponge_blake2b512_bht_quantum_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.sponge_blake2b512_bht_quantum_128

/-- info: 'Ix.Cert.MultiStark.Security128.sponge_blake2b512_bht_quantum_170' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.sponge_blake2b512_bht_quantum_170

/-- info: 'Ix.Cert.MultiStark.Security128.sponge_blake2b512_cns_quantum_204' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.sponge_blake2b512_cns_quantum_204

/-- info: 'Ix.Cert.MultiStark.Security128.sponge_blake2b512_grover_preimage_256' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.sponge_blake2b512_grover_preimage_256

/-- info: 'Ix.Cert.MultiStark.Security128.fp3_blake2b512_total_budget_le_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.fp3_blake2b512_total_budget_le_128

/-- info: 'Ix.Cert.MultiStark.Security128.v6_positive_128_profiles' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.v6_positive_128_profiles

/-- info: 'Ix.Cert.MultiStark.Security128.negControl_fp2_rejected_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.negControl_fp2_rejected_128

/-- info: 'Ix.Cert.MultiStark.Security128.negControl_v5_default_100_20_rejected_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.negControl_v5_default_100_20_rejected_128

/-- info: 'Ix.Cert.MultiStark.Security128.negControl_deceptive_4_55_0_rejected_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.negControl_deceptive_4_55_0_rejected_128

/-- info: 'Ix.Cert.MultiStark.Security128.negControl_digest32_rejected_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.negControl_digest32_rejected_128

/-- info: 'Ix.Cert.MultiStark.Security128.negControl_digest48_xof_rejected_128' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.Security128.negControl_digest48_xof_rejected_128

/-- info: 'Ix.Cert.MultiStark.goldilocks_pruned_fri_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.goldilocks_pruned_fri_soundness

/-! ## 5. Direct Upstream `CertiFRI` (`e815d47`) Unconditional 128-Bit Theorem & Axiom Locks -/

/-- info: CertiFri.P3.Exec.curveListCA_fp3 : CertiFri.CurveListCA CertiFri.P3.Fp3Model CertiFri.CurveListCAProof.curveListThreshold -/
#guard_msgs (whitespace := lax) in
#check @CertiFri.P3.Exec.curveListCA_fp3

/-- info: @CertiFri.P3.Blake3Domain.mode_injective : ∀ {d₁ d₂ : CertiFri.P3.Blake3Domain}, (d₁.keyWords, d₁.domainFlags) = (d₂.keyWords, d₂.domainFlags) → d₁ = d₂ -/
#guard_msgs (whitespace := lax) in
#check @CertiFri.P3.Blake3Domain.mode_injective

/-- info: @CertiFri.P3.Blake3Domain.v6Zk_keyWords_ne_nonZk : ∀ {d₁ d₂ : CertiFri.P3.Blake3Domain}, d₁.isZk = true → d₂.isZk = false → d₁.keyWords ≠ d₂.keyWords -/
#guard_msgs (whitespace := lax) in
#check @CertiFri.P3.Blake3Domain.v6Zk_keyWords_ne_nonZk

/-- info: @CertiFri.P3.Blake2b512Domain.initState_injective : ∀ {d₁ d₂ : CertiFri.P3.Blake2b512Domain}, d₁.initState = d₂.initState → d₁ = d₂ -/
#guard_msgs (whitespace := lax) in
#check @CertiFri.P3.Blake2b512Domain.initState_injective

/-- info: @CertiFri.P3.Blake2b512Domain.v6Zk_initState_ne_nonZk : ∀ {d₁ d₂ : CertiFri.P3.Blake2b512Domain}, d₁.isZk = true → d₂.isZk = false → d₁.initState ≠ d₂.initState -/
#guard_msgs (whitespace := lax) in
#check @CertiFri.P3.Blake2b512Domain.v6Zk_initState_ne_nonZk

/-- info: CertiFri.P3.card_digest64 : Fintype.card CertiFri.P3.Digest64 = 2 ^ 512 -/
#guard_msgs (whitespace := lax) in
#check @CertiFri.P3.card_digest64

/-- info: CertiFri.P3.Exec.goldilocksExt3_tensor2DMCA_ud_128 : ∀ (D : Finset CertiFri.P3.Fp3Model) (d W M : ℕ), D.card ≤ 2 ^ 32 → W ≤ 2 ^ 16 → M ≤ 2 ^ 16 → 2 * (3 / 8 * ↑D.card) + ↑d ≤ ↑D.card → CertiFri.Tensor2DMCA D d W M (5 / 8) (3 / 4 / 2 ^ 128) -/
#guard_msgs (whitespace := lax) in
#check @CertiFri.P3.Exec.goldilocksExt3_tensor2DMCA_ud_128

/-- info: CertiFri.P3.Exec.goldilocksExt3_zk_tensor2DMCA_ud_128 : ∀ (D : Finset CertiFri.P3.Fp3Model) (d W_orig W_R M : ℕ), D.card ≤ 2 ^ 32 → W_orig + W_R ≤ 2 ^ 16 → M ≤ 2 ^ 16 → 2 * (3 / 8 * ↑D.card) + ↑d ≤ ↑D.card → CertiFri.Tensor2DMCA D d (W_orig + W_R) M (5 / 8) (3 / 4 / 2 ^ 128) -/
#guard_msgs (whitespace := lax) in
#check @CertiFri.P3.Exec.goldilocksExt3_zk_tensor2DMCA_ud_128

/-- info: 'CertiFri.P3.Blake3Domain.mode_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Blake3Domain.mode_injective

/-- info: 'CertiFri.P3.Blake3Domain.v6Zk_keyWords_ne_nonZk' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Blake3Domain.v6Zk_keyWords_ne_nonZk

/-- info: 'CertiFri.P3.Blake2b512Domain.initState_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Blake2b512Domain.initState_injective

/-- info: 'CertiFri.P3.Blake2b512Domain.v6Zk_initState_ne_nonZk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Blake2b512Domain.v6Zk_initState_ne_nonZk

/-- info: 'CertiFri.P3.Blake2b.kat_empty_hex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Blake2b.kat_empty_hex

/-- info: 'CertiFri.P3.Blake2b.kat_abc_hex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Blake2b.kat_abc_hex

/-- info: 'CertiFri.P3.Blake2b.kat_exact128_hex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Blake2b.kat_exact128_hex

/-- info: 'CertiFri.P3.Blake2b.kat_hashPair64_exact128' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Blake2b.kat_hashPair64_exact128

/-- info: 'CertiFri.P3.Blake2b.kat_multi129_hex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Blake2b.kat_multi129_hex

/-- info: 'CertiFri.P3.Blake2b.kat_personal_abc_hex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Blake2b.kat_personal_abc_hex

/-- info: 'CertiFri.P3.card_digest64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.card_digest64

/-- info: 'CertiFri.P3.Exec.curveListCA_fp3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.curveListCA_fp3

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding_128

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_128_unconditional

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_118_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_118_128_unconditional

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_lb3_78_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_lb3_78_128_unconditional

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_lb4_58_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_lb4_58_128_unconditional

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_soundness_blake2b512_johnson_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_v6Zk_soundness_blake2b512_johnson_128_unconditional

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_tensor2DMCA_ud_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_tensor2DMCA_ud_128

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_zk_tensor2DMCA_ud_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_zk_tensor2DMCA_ud_128

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_uniqueDecoding_128_blake3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_uniqueDecoding_128_blake3

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_blake2b512_uniqueDecoding_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_blake2b512_uniqueDecoding_128

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_johnson_128_blake3_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_johnson_128_blake3_unconditional

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_128_unconditional

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_118_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_118_128_unconditional

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_lb3_78_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_lb3_78_128_unconditional

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_lb4_58_128_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_lb4_58_128_unconditional

/-! ## 6. `Fp^3` `StarkModel`, Concrete `DynamicRom`, Multi-Arity 8-ary FRI & `v6-zk` HVZK Locks -/

/-- info: CertiFri.P3.GoldilocksExt3.starkModel : CertiFri.Exec.Stark.StarkModel CertiFri.P3.Goldilocks CertiFri.P3.GoldilocksExt3 CertiFri.P3.Fp3Model -/
#guard_msgs (whitespace := lax) in
#check @CertiFri.P3.GoldilocksExt3.starkModel

/-- info: CertiFri.FriParams.compact400KBBalanced : CertiFri.FriParams -/
#guard_msgs (whitespace := lax) in
#check @CertiFri.FriParams.compact400KBBalanced

/-- info: CertiFri.FriParams.ultraCompact400KBZk : CertiFri.FriParams -/
#guard_msgs (whitespace := lax) in
#check @CertiFri.FriParams.ultraCompact400KBZk

/-- info: 'Ix.Cert.MultiStark.soundness_dynamic_rom_starkTensor_fp3_ud' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.soundness_dynamic_rom_starkTensor_fp3_ud

/-- info: 'Ix.Cert.MultiStark.soundness_dynamic_rom_starkTensorMulti_fp3_ud' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ix.Cert.MultiStark.soundness_dynamic_rom_starkTensorMulti_fp3_ud

/-- info: 'CertiFri.P3.GoldilocksExt3.starkModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.starkModel

/-- info: 'CertiFri.P3.GoldilocksExt3.rbrSound_starkTensor_ud' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.rbrSound_starkTensor_ud

/-- info: 'CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensor_johnson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensor_johnson

/-- info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_digest32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_digest32

/-- info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_digest64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_digest64

/-- info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest32

/-- info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest64

/-- info: 'CertiFri.P3.GoldilocksExt3.rbrSound_starkTensorMulti_ud' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.rbrSound_starkTensorMulti_ud

/-- info: 'CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_compact400KBBalanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_compact400KBBalanced

/-- info: 'CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_ultraCompact400KBZk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_ultraCompact400KBZk

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_compact400KBBalanced_sponge_blake3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_compact400KBBalanced_sponge_blake3

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_compact400KBBalanced_sponge_blake2b512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_compact400KBBalanced_sponge_blake2b512

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_sponge_blake3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_sponge_blake3

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_sponge_blake2b512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_sponge_blake2b512

/-- info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest32

/-- info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest64

/-- info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest32

/-- info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest64

/-- info: 'CertiFri.P3.Exec.v6Zk_alg_perfect_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.v6Zk_alg_perfect_hvzk

/-- info: 'CertiFri.P3.Exec.v6Zk_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.v6Zk_hvzk

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk_salt32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk_salt32

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_hvzk

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_hvzk_salt32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_hvzk_salt32

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk_with_tensor4_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk_with_tensor4_span
