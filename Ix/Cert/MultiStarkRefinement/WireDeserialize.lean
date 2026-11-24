import Ix.Cert.MultiStarkRefinement.ProgramPin
import Ix.Cert.MultiStarkRefinement.FieldBridge
import Ix.Cert.MultiStark.Wire
import Ix.Cert.MultiStark.Blake3Parity
import Aiur.Library.Blake3.Correctness

/-! # Wire Deserialization & BLAKE3 Digest Refinement (`WireDeserialize`)

Refines the wire decoders and digest checks in `MultiStark.recursionProgram`:
- `SystemDeserialize::lookup_groups_count` → `SysCircuit.logupGroupCount`, `stage2Width`, `constraintCount`,
- `Blake3::pack_digest (Blake3::hash bytes)` → `packDigest8 (Address.blake3Pure bytes)` and `CertiFri.P3.blake3`,
- `SystemDeserialize::read_system` → `Ix.Cert.MultiStark.StarkSystem.fromBytes`,
- `StarkVerifier::read_claims` → `Ix.Cert.MultiStark.decodeClaims`,
- `ProofDeserialize::read_batch` → `Ix.Cert.MultiStark.BatchProof.fromBytes`,
- Digest verification soundness (`verify_vk_and_claims_digests`): any accepted run either matches
  the exact expected `(vkBytes, claimsBytes)` or exhibits a concrete BLAKE3 collision in `calls`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace Ix.Cert.MultiStarkRefinement

open CertiFri CertiFri.P3
open Ix.Cert.MultiStark

/-! ## 1. `SystemDeserialize::lookup_groups_count` & Circuit Width/Constraint Counts -/

/-- Exact natural-number model of `SystemDeserialize::lookup_groups_count(n, rem, k)`
(`SystemDeserialize.lean:221-229`). -/
def lookupGroupsCountModel : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, 0, k => 1 + lookupGroupsCountModel n (k - 1) k
  | n + 1, rem + 1, k => lookupGroupsCountModel n rem k

/-- General recurrence for `lookupGroupsCountModel` when `1 ≤ k` and `rem < k`:
`lookupGroupsCountModel n rem k = if n ≤ rem then 0 else 1 + (n - rem - 1) / k`. -/
theorem lookupGroupsCountModel_eq :
    ∀ (n rem k : Nat), 1 ≤ k → rem < k →
      lookupGroupsCountModel n rem k = if n ≤ rem then 0 else 1 + (n - rem - 1) / k := by
  intro n
  induction n with
  | zero =>
    intro rem k _ _
    simp [lookupGroupsCountModel]
  | succ n ih =>
    intro rem k hk hlt
    cases rem with
    | zero =>
      simp only [lookupGroupsCountModel]
      rw [ih (k - 1) k hk (by omega)]
      have hnotle : ¬ (n + 1 ≤ 0) := by omega
      simp only [hnotle, ↓reduceIte, Nat.sub_zero, Nat.add_sub_cancel]
      by_cases hnk : n ≤ k - 1
      · simp only [hnk, ↓reduceIte]
        have hdiv : n / k = 0 := Nat.div_eq_of_lt (by omega)
        omega
      · simp only [hnk, ↓reduceIte]
        have hsub : n = (n - k) + k := by omega
        have hsub2 : n - (k - 1) - 1 = n - k := by omega
        rw [hsub2]
        conv_rhs => rw [hsub, Nat.add_div_right _ (by omega)]
        omega
    | succ r =>
      simp only [lookupGroupsCountModel]
      rw [ih r k hk (by omega)]
      by_cases hnr : n ≤ r
      · have hnr2 : n + 1 ≤ r + 1 := by omega
        simp [hnr, hnr2]
      · have hnr2 : ¬ (n + 1 ≤ r + 1) := by omega
        simp [hnr, hnr2]

/-- `SystemDeserialize::lookup_groups_count(lcount, 0, max(1, k))` equals
`SysCircuit.logupGroupCount` identically! -/
theorem lookup_groups_count_refines (c : SysCircuit) :
    lookupGroupsCountModel c.lookups.size 0 (max 1 c.lookupGroupSize) = c.logupGroupCount := by
  have hk : 1 ≤ max 1 c.lookupGroupSize := le_max_left 1 _
  rw [lookupGroupsCountModel_eq c.lookups.size 0 (max 1 c.lookupGroupSize) hk (by omega)]
  unfold SysCircuit.logupGroupCount
  cases h : c.lookups.size with
  | zero =>
    simp only [Nat.le_refl, ↓reduceIte, zero_add]
    exact (Nat.div_eq_of_lt (by omega)).symm
  | succ m =>
    have hnot : ¬ (m + 1 ≤ 0) := by omega
    simp only [hnot, ↓reduceIte, Nat.sub_zero, Nat.add_sub_cancel]
    have hEq : m + 1 + max 1 c.lookupGroupSize - 1 = m + max 1 c.lookupGroupSize := by omega
    rw [hEq, Nat.add_div_right _ (by omega)]
    omega

/-- `SystemDeserialize::read_sys_circuit`'s `s2w` formula matches `SysCircuit.stage2Width`. -/
theorem stage2_width_refines (c : SysCircuit) :
    (let g := lookupGroupsCountModel c.lookups.size 0 (max 1 c.lookupGroupSize)
     (if g == 0 then 1 else g) * 3) = c.stage2Width := by
  rw [lookup_groups_count_refines]
  unfold SysCircuit.stage2Width
  cases hg : c.logupGroupCount with
  | zero => rfl
  | succ m => simp

/-- `SystemDeserialize::read_sys_circuit`'s `zcount + s2w` shape limb matches `SysCircuit.constraintCount`. -/
theorem constraint_count_refines (c : SysCircuit) :
    c.zeros.size + c.stage2Width = c.constraintCount := rfl

/-! ## 2. BLAKE3 Hash & Digest Packing Parity (`Blake3::hash` ↔ `CertiFri.P3.blake3` ↔ `Address.blake3Pure`) -/

/-- `CertiFri.P3.blake3` agrees byte-for-byte with `Address.blake3Pure`. -/
theorem certifri_blake3_eq_address_blake3Pure (bytes : ByteArray) :
    CertiFri.P3.blake3 bytes = (Address.blake3Pure bytes).hash := by
  rw [Ix.Cert.MultiStark.blake3_eq_pure]
  rfl

/-- `Blake3::pack_digest` on the 8 `UInt32` words of `Blake3.Pure.digest` equals
`packDigest8 (Address.blake3Pure bytes)`. -/
theorem blake3_pack_digest_eq_packDigest8 (bytes : ByteArray) (i : Fin 8) :
    let d := Blake3.Pure.digest bytes.data.toList
    let w := Aiur.Library.Blake3.wordOfBytes
      (d.toArray.getD (4 * i.val) 0)
      (d.toArray.getD (4 * i.val + 1) 0)
      (d.toArray.getD (4 * i.val + 2) 0)
      (d.toArray.getD (4 * i.val + 3) 0)
    (w.toNat : Fp) = packDigest8 (Address.blake3Pure bytes) i := by
  dsimp only
  rw [Aiur.Library.Blake3.wordOfBytes_toNat]
  unfold Aiur.Library.U32.pack packDigest8 Address.blake3Pure
  rfl

/-! ## 3. Wire Decoder Refinement Specifications (`read_system`, `read_claims`, `read_batch`) -/

/-- Wire-decoding agreement between `MultiStark::verify_multi_stark_proof`'s deserialized streams
and `Ix.Cert.MultiStark.{StarkSystem.fromBytes, decodeClaims, BatchProof.fromBytes}`:
- `sbytes` was hashed by `Blake3::hash` in `calls`, its packed digest equals `systemDigest`,
  and `SystemDeserialize::read_system(sbytes)` succeeded with `Nil` remainder, matching
  `StarkSystem.fromBytes sbytes = .ok sys`.
- `cbytes` was hashed by `Blake3::hash` in `calls`, its packed digest equals `claimsDigest`,
  and `StarkVerifier::read_claims(cbytes)` succeeded with `Nil` remainder, matching
  `decodeClaims cbytes = .ok expectedClaims`.
- `proofBytes` of length `len` was decoded by `ProofDeserialize::read_batch` consuming exactly
  `len` bytes, matching `BatchProof.fromBytes proofBytes = .ok batch`. -/
structure WireDecodingWitness
    (calls : List (Aiur.Generic.SourceSemantics.Call Fp))
    (systemDigest claimsDigest : Fin 8 → Fp)
    (sbytes cbytes proofBytes : ByteArray)
    (sys : StarkSystem) (expectedClaims : Array (Array F)) (batch : BatchProof) : Prop where
  sbytes_hashed : HashedInMultiStark calls sbytes
  sbytes_digest : packDigest8 (Address.blake3Pure sbytes) = systemDigest
  sys_decoded : StarkSystem.fromBytes sbytes = .ok sys
  cbytes_hashed : HashedInMultiStark calls cbytes
  cbytes_digest : packDigest8 (Address.blake3Pure cbytes) = claimsDigest
  claims_decoded : decodeClaims cbytes = .ok expectedClaims
  batch_decoded : BatchProof.fromBytes proofBytes = .ok batch

/-- **Digest Authenticity for `verify_multi_stark_proof`:**
Given expected `(vkBytes, claimsBytes)` whose packed BLAKE3 digests are passed as public inputs
`(systemDigest, claimsDigest)`, any `WireDecodingWitness` either:
- decoded the exact `(vkBytes, claimsBytes)` bytes (`sbytes = vkBytes ∧ cbytes = claimsBytes`,
  hence `StarkSystem.fromBytes vkBytes = .ok sys` and `decodeClaims claimsBytes = .ok expectedClaims`), OR
- exhibited a concrete BLAKE3 collision in `calls` against `[vkBytes, claimsBytes]`! -/
theorem wire_decoding_authentic_or_collision
    {calls : List (Aiur.Generic.SourceSemantics.Call Fp)}
    {vkBytes claimsBytes sbytes cbytes proofBytes : ByteArray}
    {sys : StarkSystem} {expectedClaims : Array (Array F)} {batch : BatchProof}
    (w : WireDecodingWitness calls
      (packDigest8 (Address.blake3Pure vkBytes))
      (packDigest8 (Address.blake3Pure claimsBytes))
      sbytes cbytes proofBytes sys expectedClaims batch) :
    MultiStarkCollision [vkBytes, claimsBytes] calls ∨
      (sbytes = vkBytes ∧ cbytes = claimsBytes ∧
       StarkSystem.fromBytes vkBytes = .ok sys ∧
       decodeClaims claimsBytes = .ok expectedClaims ∧
       BatchProof.fromBytes proofBytes = .ok batch) := by
  rcases hashed_eq_or_collision (anchors := [vkBytes, claimsBytes]) (a := vkBytes) (b := sbytes)
      (by simp) w.sbytes_hashed w.sbytes_digest with hsEq | hcol
  · rcases hashed_eq_or_collision (anchors := [vkBytes, claimsBytes]) (a := claimsBytes) (b := cbytes)
        (by simp) w.cbytes_hashed w.cbytes_digest with hcEq | hcol
    · refine Or.inr ⟨hsEq, hcEq, ?_, ?_, w.batch_decoded⟩
      · rw [← hsEq]; exact w.sys_decoded
      · rw [← hcEq]; exact w.claims_decoded
    · exact Or.inl hcol
  · exact Or.inl hcol

end Ix.Cert.MultiStarkRefinement
