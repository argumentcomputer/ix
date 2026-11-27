import CertiFriP3.Blake3
import CertiFriP3.Hashers
import Aiur.Library.Blake3.PureTree
import Mathlib.Tactic.IntervalCases

/-! # BLAKE3 Parity: `CertiFri.P3.blake3` = `Blake3.Pure.digest` (Gap 1b)

Proves exact byte-for-byte equality between CertiFRI's Plonky3 BLAKE3 implementation
(`CertiFri.P3.blake3`, `CertiFri.P3.baseHasher`, `CertiFri.P3.extHasher`,
`CertiFri.P3.Blake3.hashPair`) and Ix's pure mathematical specification
`Blake3.Pure.digest` (the same specification audited in `Aiur.Audit` and `IxVM.Refinement`).
Zero `sorry`, standard axioms only.
-/

namespace Ix.Cert.MultiStark

open CertiFri.P3

/-! ## 1. Type Conversions between `CertiFri.P3.Blake3` and `Blake3.Pure` -/

def digestToCV (d : Digest) : Blake3.Pure.CV :=
  #v[d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7]

def blockToPure (b : Blake3.Block) : Blake3.Pure.Block :=
  #v[b.m0, b.m1, b.m2, b.m3, b.m4, b.m5, b.m6, b.m7,
     b.m8, b.m9, b.m10, b.m11, b.m12, b.m13, b.m14, b.m15]

def stateToPure (s : Blake3.State) : Blake3.Pure.Block :=
  #v[s.v0, s.v1, s.v2, s.v3, s.v4, s.v5, s.v6, s.v7,
     s.v8, s.v9, s.v10, s.v11, s.v12, s.v13, s.v14, s.v15]

def nodeToOutput (n : Blake3.Node) : Blake3.Pure.Output :=
  ⟨digestToCV n.cv, blockToPure n.block, n.blockLen, n.counter, n.flags⟩

/-! ## 2. Compression Function Equivalence -/

private lemma quarter_eq_mix (a b c d x y : UInt32) :
    Blake3.Pure.mix a b c d x y =
      #v[(Blake3.quarter a b c d x y).1, (Blake3.quarter a b c d x y).2.1,
         (Blake3.quarter a b c d x y).2.2.1, (Blake3.quarter a b c d x y).2.2.2] := rfl

private lemma g_col0 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 0 4 8 12 x y =
      let q := Blake3.quarter v0 v4 v8 v12 x y
      #v[q.1, v1, v2, v3, q.2.1, v5, v6, v7, q.2.2.1, v9, v10, v11, q.2.2.2, v13, v14, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v0 v4 v8 v12 x y; _ = _
  rw [quarter_eq_mix]
  rfl

private lemma g_col1 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 1 5 9 13 x y =
      let q := Blake3.quarter v1 v5 v9 v13 x y
      #v[v0, q.1, v2, v3, v4, q.2.1, v6, v7, v8, q.2.2.1, v10, v11, v12, q.2.2.2, v14, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v1 v5 v9 v13 x y; _ = _
  rw [quarter_eq_mix]
  rfl

private lemma g_col2 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 2 6 10 14 x y =
      let q := Blake3.quarter v2 v6 v10 v14 x y
      #v[v0, v1, q.1, v3, v4, v5, q.2.1, v7, v8, v9, q.2.2.1, v11, v12, v13, q.2.2.2, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v2 v6 v10 v14 x y; _ = _
  rw [quarter_eq_mix]
  rfl

private lemma g_col3 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 3 7 11 15 x y =
      let q := Blake3.quarter v3 v7 v11 v15 x y
      #v[v0, v1, v2, q.1, v4, v5, v6, q.2.1, v8, v9, v10, q.2.2.1, v12, v13, v14, q.2.2.2] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v3 v7 v11 v15 x y; _ = _
  rw [quarter_eq_mix]
  rfl

private lemma g_diag0 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 0 5 10 15 x y =
      let q := Blake3.quarter v0 v5 v10 v15 x y
      #v[q.1, v1, v2, v3, v4, q.2.1, v6, v7, v8, v9, q.2.2.1, v11, v12, v13, v14, q.2.2.2] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v0 v5 v10 v15 x y; _ = _
  rw [quarter_eq_mix]
  rfl

private lemma g_diag1 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 1 6 11 12 x y =
      let q := Blake3.quarter v1 v6 v11 v12 x y
      #v[v0, q.1, v2, v3, v4, v5, q.2.1, v7, v8, v9, v10, q.2.2.1, q.2.2.2, v13, v14, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v1 v6 v11 v12 x y; _ = _
  rw [quarter_eq_mix]
  rfl

private lemma g_diag2 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 2 7 8 13 x y =
      let q := Blake3.quarter v2 v7 v8 v13 x y
      #v[v0, v1, q.1, v3, v4, v5, v6, q.2.1, q.2.2.1, v9, v10, v11, v12, q.2.2.2, v14, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v2 v7 v8 v13 x y; _ = _
  rw [quarter_eq_mix]
  rfl

private lemma g_diag3 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : UInt32) :
    Blake3.Pure.g #v[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 3 4 9 14 x y =
      let q := Blake3.quarter v3 v4 v9 v14 x y
      #v[v0, v1, v2, q.1, q.2.1, v5, v6, v7, v8, q.2.2.1, v10, v11, v12, v13, q.2.2.2, v15] := by
  unfold Blake3.Pure.g
  change let words := Blake3.Pure.mix v3 v4 v9 v14 x y; _ = _
  rw [quarter_eq_mix]
  rfl

private lemma round_eq (s : Blake3.State) (m : Blake3.Block)
    (msg : Blake3.Pure.Block) (sched : Vector (Fin 16) 16)
    (h0 : m.m0 = msg[sched[0]]) (h1 : m.m1 = msg[sched[1]])
    (h2 : m.m2 = msg[sched[2]]) (h3 : m.m3 = msg[sched[3]])
    (h4 : m.m4 = msg[sched[4]]) (h5 : m.m5 = msg[sched[5]])
    (h6 : m.m6 = msg[sched[6]]) (h7 : m.m7 = msg[sched[7]])
    (h8 : m.m8 = msg[sched[8]]) (h9 : m.m9 = msg[sched[9]])
    (h10 : m.m10 = msg[sched[10]]) (h11 : m.m11 = msg[sched[11]])
    (h12 : m.m12 = msg[sched[12]]) (h13 : m.m13 = msg[sched[13]])
    (h14 : m.m14 = msg[sched[14]]) (h15 : m.m15 = msg[sched[15]]) :
    stateToPure (Blake3.round s m) = Blake3.Pure.round (stateToPure s) msg sched := by
  unfold Blake3.round Blake3.Pure.round stateToPure
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7,
      ← h8, ← h9, ← h10, ← h11, ← h12, ← h13, ← h14, ← h15]
  simp only [g_col0, g_col1, g_col2, g_col3, g_diag0, g_diag1, g_diag2, g_diag3]

theorem compress_eq (cv : Digest) (m : Blake3.Block) (counter : UInt64) (blockLen flags : UInt32) :
    digestToCV (Blake3.compress cv m counter blockLen flags) =
      Blake3.Pure.compress (digestToCV cv) (blockToPure m) counter blockLen flags := by
  unfold Blake3.compress Blake3.Pure.compress
  -- Unfold the 7 rounds on both sides step by step using `round_eq`
  set s0 : Blake3.State :=
    ⟨cv.w0, cv.w1, cv.w2, cv.w3, cv.w4, cv.w5, cv.w6, cv.w7,
     Blake3.iv.w0, Blake3.iv.w1, Blake3.iv.w2, Blake3.iv.w3,
     counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags⟩
  have hfold :
      Blake3.Pure.schedules.foldl (fun state schedule => Blake3.Pure.round state (blockToPure m) schedule)
        (Blake3.Pure.initialWords (digestToCV cv) counter blockLen flags) =
      stateToPure (Blake3.rounds 7 s0 m) := by
    have hinit : Blake3.Pure.initialWords (digestToCV cv) counter blockLen flags = stateToPure s0 := rfl
    rw [hinit]
    change
      Blake3.Pure.round (Blake3.Pure.round (Blake3.Pure.round (Blake3.Pure.round
        (Blake3.Pure.round (Blake3.Pure.round (Blake3.Pure.round (stateToPure s0)
          (blockToPure m) Blake3.Pure.schedules[0])
          (blockToPure m) Blake3.Pure.schedules[1])
          (blockToPure m) Blake3.Pure.schedules[2])
          (blockToPure m) Blake3.Pure.schedules[3])
          (blockToPure m) Blake3.Pure.schedules[4])
          (blockToPure m) Blake3.Pure.schedules[5])
          (blockToPure m) Blake3.Pure.schedules[6] =
      stateToPure (Blake3.round (Blake3.round (Blake3.round (Blake3.round
        (Blake3.round (Blake3.round (Blake3.round s0 m)
          (Blake3.permute m))
          (Blake3.permute (Blake3.permute m)))
          (Blake3.permute (Blake3.permute (Blake3.permute m))))
          (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute m)))))
          (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute m))))))
          (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute m)))))))
    rw [← round_eq s0 m (blockToPure m) Blake3.Pure.schedules[0]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← round_eq _ (Blake3.permute m) (blockToPure m) Blake3.Pure.schedules[1]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← round_eq _ (Blake3.permute (Blake3.permute m)) (blockToPure m) Blake3.Pure.schedules[2]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← round_eq _ (Blake3.permute (Blake3.permute (Blake3.permute m)))
      (blockToPure m) Blake3.Pure.schedules[3]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← round_eq _ (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute m))))
      (blockToPure m) Blake3.Pure.schedules[4]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← round_eq _ (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute m)))))
      (blockToPure m) Blake3.Pure.schedules[5]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
    rw [← round_eq _ (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute (Blake3.permute m))))))
      (blockToPure m) Blake3.Pure.schedules[6]
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl]
  rw [hfold]
  cases Blake3.rounds 7 s0 m
  rfl

lemma node_chainingValue_eq (n : Blake3.Node) :
    digestToCV n.chainingValue = (nodeToOutput n).chainingValue :=
  compress_eq n.cv n.block n.counter n.blockLen n.flags

lemma parentNode_eq (a b : Digest) :
    nodeToOutput (Blake3.parentNode a b) = Blake3.Pure.parentOutput (digestToCV a) (digestToCV b) := by
  rfl

/-! ## 3. Little-Endian Word and Byte Packing Equivalence -/

private lemma uint8_toUInt32_toNat (b : UInt8) : b.toUInt32.toNat = b.toNat :=
  UInt8.toNat_toUInt32 b

private lemma uint32_shr_toUInt8_eq (w : UInt32) (k : Nat) (hk : k < 4) :
    (w >>> (8 * k).toUInt32).toUInt8 = (w.toNat / 256 ^ k).toUInt8 := by
  have hk32 : (8 * k).toUInt32.toNat % 32 = 8 * k := by
    have : 8 * k < 32 := by omega
    simp [UInt32.toNat_ofNat, Nat.mod_eq_of_lt this]
  have hpow : 2 ^ (8 * k) = 256 ^ k := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, hk32, Nat.shiftRight_eq_div_pow, hpow]
  rfl

private lemma pack_le_u32 (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)) =
      UInt32.ofNat (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))) := by
  have h0 : b0.toNat < 2 ^ 8 := b0.toNat_lt
  have h1 : b1.toNat < 2 ^ 8 := b1.toNat_lt
  have h2 : b2.toNat < 2 ^ 8 := b2.toNat_lt
  have h3 : b3.toNat < 2 ^ 8 := b3.toNat_lt
  have hsum : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) < 2 ^ 32 := by omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hsum]
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or]
  have hs1 : (b1.toUInt32 <<< 8).toNat = b1.toNat * 2 ^ 8 := by
    rw [UInt32.toNat_shiftLeft, uint8_toUInt32_toNat]
    have : (8 : UInt32).toNat % 32 = 8 := rfl
    rw [this, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hs2 : (b2.toUInt32 <<< 16).toNat = b2.toNat * 2 ^ 16 := by
    rw [UInt32.toNat_shiftLeft, uint8_toUInt32_toNat]
    have : (16 : UInt32).toNat % 32 = 16 := rfl
    rw [this, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hs3 : (b3.toUInt32 <<< 24).toNat = b3.toNat * 2 ^ 24 := by
    rw [UInt32.toNat_shiftLeft, uint8_toUInt32_toNat]
    have : (24 : UInt32).toNat % 32 = 24 := rfl
    rw [this, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  rw [uint8_toUInt32_toNat, hs1, hs2, hs3]
  -- Bitwise OR of non-overlapping byte lanes equals arithmetic sum
  have lor_mul_pow : ∀ (a b k : Nat), a < 2 ^ k → (a ||| (b * 2 ^ k)) = a + b * 2 ^ k := by
    intro a b k ha
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_or, Nat.testBit_mul_two_pow]
    have hbit : (a + b * 2 ^ k).testBit i = if i < k then a.testBit i else b.testBit (i - k) := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      split_ifs with hi
      · have hpow : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
          rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
        have hstep : 2 ^ (k - i) = 2 ^ (k - i - 1) * 2 := by
          conv => lhs; rw [show k - i = (k - i - 1) + 1 by omega, Nat.pow_succ]
        rw [hpow, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i), hstep,
            ← Nat.mul_assoc, Nat.and_comm 1, Nat.and_comm 1, Nat.and_one_is_mod, Nat.and_one_is_mod]
        have hmod : (a / 2 ^ i + b * 2 ^ (k - i - 1) * 2) % 2 = (a / 2 ^ i) % 2 := by omega
        rw [hmod]
      · have hpow : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
          rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
        rw [hpow, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k),
            Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [hbit]
    by_cases hi : i < k
    · have : ¬ k ≤ i := by omega
      simp [hi, this]
    · have ha_lt : a < 2 ^ i :=
        lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
      have : a.testBit i = false := by
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt ha_lt]; rfl
      have hge : k ≤ i := by omega
      simp [hi, hge, this]
  rw [lor_mul_pow b0.toNat b1.toNat 8 h0]
  rw [lor_mul_pow (b0.toNat + b1.toNat * 2 ^ 8) b2.toNat 16 (by omega)]
  rw [lor_mul_pow (b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16) b3.toNat 24 (by omega)]
  omega

private lemma pushWord32_toList (b : ByteArray) (w : UInt32) :
    (LittleEndian.pushWord32 b w).data.toList =
      b.data.toList ++ [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8] := by
  unfold LittleEndian.pushWord32
  change ((((b.data.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8).toList = _
  simp only [Array.toList_push, List.append_assoc, List.cons_append, List.nil_append]

private lemma digest_toBytes_toList (d : Digest) :
    d.toBytes.data.toList =
      [d.w0.toUInt8, (d.w0 >>> 8).toUInt8, (d.w0 >>> 16).toUInt8, (d.w0 >>> 24).toUInt8,
       d.w1.toUInt8, (d.w1 >>> 8).toUInt8, (d.w1 >>> 16).toUInt8, (d.w1 >>> 24).toUInt8,
       d.w2.toUInt8, (d.w2 >>> 8).toUInt8, (d.w2 >>> 16).toUInt8, (d.w2 >>> 24).toUInt8,
       d.w3.toUInt8, (d.w3 >>> 8).toUInt8, (d.w3 >>> 16).toUInt8, (d.w3 >>> 24).toUInt8,
       d.w4.toUInt8, (d.w4 >>> 8).toUInt8, (d.w4 >>> 16).toUInt8, (d.w4 >>> 24).toUInt8,
       d.w5.toUInt8, (d.w5 >>> 8).toUInt8, (d.w5 >>> 16).toUInt8, (d.w5 >>> 24).toUInt8,
       d.w6.toUInt8, (d.w6 >>> 8).toUInt8, (d.w6 >>> 16).toUInt8, (d.w6 >>> 24).toUInt8,
       d.w7.toUInt8, (d.w7 >>> 8).toUInt8, (d.w7 >>> 16).toUInt8, (d.w7 >>> 24).toUInt8] := by
  unfold Digest.toBytes
  have hempty : (ByteArray.emptyWithCapacity 32).data.toList = [] := rfl
  simp only [List.foldl_cons, List.foldl_nil, pushWord32_toList, hempty,
    List.nil_append, List.cons_append]

private def word4 (w : UInt32) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

private lemma word4_length (w : UInt32) : (word4 w).length = 4 := rfl

private lemma word4_getElem (w : UInt32) (r : Nat) (hr : r < 4) :
    (word4 w)[r]'hr = (Blake3.Pure.wordBytes w)[r]'hr := by
  unfold Blake3.Pure.wordBytes
  simp only [Vector.getElem_ofFn]
  have h := uint32_shr_toUInt8_eq w r hr
  interval_cases r
  · have h0 : w.toUInt8 = (w.toNat / 256 ^ 0).toUInt8 := by
      apply UInt8.toNat_inj.mp; simp [UInt32.toNat_toUInt8]
    exact h0
  · exact h
  · exact h
  · exact h

private lemma flatMap_word4_getElem : ∀ (l : List UInt32) (i : Nat) (hi : i < (l.flatMap word4).length),
    (l.flatMap word4)[i]'hi =
      (word4 (l[i / 4]'(by
        have hlen : (l.flatMap word4).length = 4 * l.length := by
          clear hi
          induction l with
          | nil => rfl
          | cons _ _ ih => simp [List.flatMap_cons, word4_length, ih]; omega
        omega)))[i % 4]'(Nat.mod_lt _ (by omega))
  | [], i, hi => by simp at hi
  | w :: ws, i, hi => by
    simp only [List.flatMap_cons]
    by_cases h4 : i < 4
    · rw [List.getElem_append_left (by simpa [word4_length] using h4)]
      have hq : i / 4 = 0 := by omega
      have hr : i % 4 = i := by omega
      simp only [hq, hr, List.getElem_cons_zero]
    · rw [List.getElem_append_right (by simp [word4_length]; omega)]
      simp only [word4_length]
      have hih := flatMap_word4_getElem ws (i - 4) (by
        simp only [List.flatMap_cons, List.length_append, word4_length] at hi; omega)
      rw [hih]
      have hq : i / 4 = (i - 4) / 4 + 1 := by omega
      have hr : (i - 4) % 4 = i % 4 := by omega
      simp only [hq, hr, List.getElem_cons_succ]

theorem digest_toBytes_eq_cvBytes (d : Digest) :
    d.toBytes.data = (Blake3.Pure.cvBytes (digestToCV d)).toArray := by
  have hfold : ∀ (l : List UInt32) (acc : ByteArray),
      (l.foldl LittleEndian.pushWord32 acc).data.toList = acc.data.toList ++ l.flatMap word4 := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons w ws ih =>
      intro acc
      rw [List.foldl_cons, ih, pushWord32_toList, List.flatMap_cons, List.append_assoc]
      rfl
  have hlist : d.toBytes.data.toList = [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7].flatMap word4 := by
    unfold Digest.toBytes
    rw [hfold]
    have hempty : (ByteArray.emptyWithCapacity 32).data.toList = [] := rfl
    rw [hempty, List.nil_append]
  have hsz : d.toBytes.data.size = 32 := by
    have : d.toBytes.data.toList.length = 32 := by rw [hlist]; rfl
    simpa only [Array.length_toList] using this
  generalize hxs : d.toBytes.data = xs at hlist hsz ⊢
  generalize hys : Blake3.Pure.cvBytes (digestToCV d) = ys
  apply Array.ext
  · rw [hsz]; simp
  · intro i hi1 hi2
    have hi : i < 32 := by omega
    rw [← Array.getElem_toList (xs := xs) (i := i), Vector.getElem_toArray]
    simp only [hlist, ← hys]
    rw [flatMap_word4_getElem, word4_getElem]
    unfold Blake3.Pure.cvBytes digestToCV
    simp only [Vector.getElem_ofFn]
    rfl

private lemma byteOrZero_eq_list_getD (bytes : ByteArray) (i : Nat) :
    LittleEndian.byteOrZero bytes i = bytes.data.toList[i]?.getD 0 := by
  unfold LittleEndian.byteOrZero
  by_cases h : i < bytes.size
  · have hl : i < bytes.data.toList.length := by simpa only [ByteArray.size, Array.length_toList] using h
    simp only [h, ↓reduceDIte, List.getElem?_eq_getElem hl, Option.getD_some]
    rfl
  · have hl : ¬ i < bytes.data.toList.length := by simpa only [ByteArray.size, Array.length_toList] using h
    simp only [h, ↓reduceDIte, List.getElem?_eq_none (Nat.le_of_not_lt hl), Option.getD_none]

private lemma word32_eq_bytesWord (bytes : ByteArray) (off : Nat) :
    LittleEndian.word32 bytes off =
      Blake3.Pure.bytesWord (Vector.ofFn fun b : Fin 4 => bytes.data.toList[off + b.val]?.getD 0) := by
  unfold LittleEndian.word32 Blake3.Pure.bytesWord Blake3.Pure.littleEndian
  simp only [byteOrZero_eq_list_getD]
  rw [pack_le_u32]
  simp [Vector.toList_ofFn, List.ofFn_succ]

private lemma blockToPure_bytesBlock (bytes : ByteArray) (i : Nat) :
    blockToPure (Blake3.bytesBlock bytes i) =
      Blake3.Pure.blockWords ((bytes.data.toList.drop (64 * i)).take 64) := by
  apply Vector.ext
  intro k hk
  have hbyte (w : Fin 16) (b : Fin 4) :
      ((bytes.data.toList.drop (64 * i)).take 64).toArray[w.val * 4 + b.val]?.getD 0 =
        bytes.data.toList[64 * i + 4 * w.val + b.val]?.getD 0 := by
    rw [Array.getElem?_toList.symm]
    have hlt64 : w.val * 4 + b.val < 64 := by omega
    simp only [List.getElem?_take_of_lt hlt64, List.getElem?_drop]
    congr 2; omega
  have hw (w : Fin 16) :
      LittleEndian.word32 bytes (64 * i + 4 * w.val) =
        (Blake3.Pure.blockWords ((bytes.data.toList.drop (64 * i)).take 64))[w.val] := by
    rw [word32_eq_bytesWord]
    unfold Blake3.Pure.blockWords
    simp only [Vector.getElem_ofFn]
    congr 1
    apply Vector.ext
    intro b hb
    simp only [Vector.getElem_ofFn]
    exact (hbyte w ⟨b, hb⟩).symm
  interval_cases k
  · exact hw ⟨0, by omega⟩
  · exact hw ⟨1, by omega⟩
  · exact hw ⟨2, by omega⟩
  · exact hw ⟨3, by omega⟩
  · exact hw ⟨4, by omega⟩
  · exact hw ⟨5, by omega⟩
  · exact hw ⟨6, by omega⟩
  · exact hw ⟨7, by omega⟩
  · exact hw ⟨8, by omega⟩
  · exact hw ⟨9, by omega⟩
  · exact hw ⟨10, by omega⟩
  · exact hw ⟨11, by omega⟩
  · exact hw ⟨12, by omega⟩
  · exact hw ⟨13, by omega⟩
  · exact hw ⟨14, by omega⟩
  · exact hw ⟨15, by omega⟩

/-! ## 4. Chunk Compression Equivalence -/

private lemma chainBlocks_chunkLoop_eq (block : Nat → Blake3.Block) (first : Nat) (counter : UInt64)
    (chunkBytes : List UInt8) (hlen : chunkBytes.length ≤ 1024)
    (hblk : ∀ j, j < max 1 ((chunkBytes.length + 63) / 64) →
      blockToPure (block (first + j)) = Blake3.Pure.blockWords ((chunkBytes.drop (64 * j)).take 64)) :
    ∀ (count j : Nat) (cv : Digest),
      let blocks := max 1 ((chunkBytes.length + 63) / 64)
      count + j + 1 = blocks →
      nodeToOutput
        { cv := Blake3.chainBlocks block first counter count j cv
          block := block (first + (blocks - 1))
          counter := counter
          blockLen := (chunkBytes.length - 64 * (blocks - 1)).toUInt32
          flags := if blocks = 1 then Blake3.flagChunkStart ||| Blake3.flagChunkEnd
                   else Blake3.flagChunkEnd } =
        Blake3.Pure.chunkLoop counter (digestToCV cv) (j = 0) (chunkBytes.drop (64 * j)) := by
  intro count
  induction count with
  | zero =>
    intro j cv blocks hsum
    have hj : j = blocks - 1 := by omega
    have hrem_len : (chunkBytes.drop (64 * j)).length = chunkBytes.length - 64 * (blocks - 1) := by
      rw [List.length_drop, hj]
    have hrem_le : (chunkBytes.drop (64 * j)).length ≤ 64 := by
      rw [hrem_len]
      dsimp only [blocks] at *
      omega
    rw [Blake3.Pure.chunkLoop_of_le counter (digestToCV cv) (decide (j = 0)) _ hrem_le]
    unfold Blake3.chainBlocks nodeToOutput
    have htake : (chunkBytes.drop (64 * (blocks - 1))).take 64 = chunkBytes.drop (64 * j) := by
      rw [← hj, List.take_of_length_le hrem_le]
    have hb := hblk (blocks - 1) (by dsimp only [blocks]; omega)
    rw [htake] at hb
    rw [hb, hrem_len]
    have hflags :
        (if blocks = 1 then Blake3.flagChunkStart ||| Blake3.flagChunkEnd else Blake3.flagChunkEnd) =
        ((if decide (j = 0) = true then (1 : UInt32) else 0) ||| 2) := by
      by_cases h1 : blocks = 1
      · have hj0 : j = 0 := by omega
        simp [h1, hj0, Blake3.flagChunkStart, Blake3.flagChunkEnd]
      · have hjne : j ≠ 0 := by omega
        simp [h1, hjne, Blake3.flagChunkEnd]
    rw [hflags]
  | succ count ih =>
    intro j cv blocks hsum
    have hblocks_gt1 : 1 < blocks := by omega
    have hrem_gt : 64 < (chunkBytes.drop (64 * j)).length := by
      rw [List.length_drop]
      dsimp only [blocks] at *
      omega
    rw [Blake3.Pure.chunkLoop_of_gt counter (digestToCV cv) (decide (j = 0)) _ hrem_gt]
    unfold Blake3.chainBlocks
    have hdrop : (chunkBytes.drop (64 * j)).drop 64 = chunkBytes.drop (64 * (j + 1)) := by
      rw [List.drop_drop, show 64 * j + 64 = 64 * (j + 1) by omega]
    rw [hdrop]
    have hnext_cv :
        digestToCV (Blake3.compress cv (block (first + j)) counter 64
          (if j = 0 then Blake3.flagChunkStart else 0)) =
        Blake3.Pure.compress (digestToCV cv) (Blake3.Pure.blockWords ((chunkBytes.drop (64 * j)).take 64))
          counter 64 (if decide (j = 0) = true then 1 else 0) := by
      rw [compress_eq, hblk j (by omega)]
      by_cases hj0 : j = 0 <;> simp [hj0, Blake3.flagChunkStart]
    have hstep := ih (j + 1)
      (Blake3.compress cv (block (first + j)) counter 64 (if j = 0 then Blake3.flagChunkStart else 0))
      (by omega)
    rw [hnext_cv] at hstep
    dsimp only [blocks]
    simpa [Nat.succ_ne_zero] using hstep

theorem chunkNode_eq_chunkOutput (bytes : ByteArray) (chunk : Nat)
    (_hchunk : chunk < max 1 ((bytes.size + 1023) / 1024)) :
    nodeToOutput (Blake3.chunkNode bytes.size (Blake3.bytesBlock bytes) chunk) =
      Blake3.Pure.chunkOutput chunk.toUInt64 ((bytes.data.toList.drop (1024 * chunk)).take 1024) := by
  set chunkBytes := (bytes.data.toList.drop (1024 * chunk)).take 1024
  have hlen : chunkBytes.length = min 1024 (bytes.size - 1024 * chunk) := by
    simp only [chunkBytes, List.length_take, List.length_drop, Array.length_toList]
    rfl
  have hlen_le : chunkBytes.length ≤ 1024 := by omega
  have hblk : ∀ j, j < max 1 ((chunkBytes.length + 63) / 64) →
      blockToPure (Blake3.bytesBlock bytes (16 * chunk + j)) =
        Blake3.Pure.blockWords ((chunkBytes.drop (64 * j)).take 64) := by
    intro j hj
    rw [blockToPure_bytesBlock]
    congr 1
    have h64 : 64 * (16 * chunk + j) = 1024 * chunk + 64 * j := by omega
    rw [h64]
    have hj_lt16 : j < 16 := by omega
    -- Both are `64`-byte slices starting at `1024 * chunk + 64 * j`
    apply List.ext_getElem?
    intro idx
    by_cases hidx : idx < 64
    · simp only [chunkBytes, List.getElem?_take_of_lt hidx, List.getElem?_drop,
        List.getElem?_take_of_lt (show 64 * j + idx < 1024 by omega)]
      congr 1; omega
    · simp only [List.getElem?_take_eq_none (Nat.le_of_not_lt hidx)]
  have hmain := chainBlocks_chunkLoop_eq (Blake3.bytesBlock bytes) (16 * chunk) chunk.toUInt64
    chunkBytes hlen_le hblk (max 1 ((chunkBytes.length + 63) / 64) - 1) 0 Blake3.iv (by omega)
  simpa [Blake3.chunkNode, Blake3.Pure.chunkOutput, hlen, Blake3.iv, digestToCV, Blake3.Pure.iv] using hmain

/-! ## 5. Tree Stack Invariant (`pushChunk` / `pushChunks` / `finish`) -/

/-- Exponents of the 1-bits of `n` (shifted up by `shift`), in strictly increasing order. -/
private def bitExps (shift : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 =>
    if (n + 1) % 2 = 1 then shift :: bitExps (shift + 1) ((n + 1) / 2)
    else bitExps (shift + 1) ((n + 1) / 2)
termination_by n => n

private lemma bitExps_zero (shift : Nat) : bitExps shift 0 = [] := by
  unfold bitExps; rfl

private lemma bitExps_odd (shift n : Nat) (h : n % 2 = 1) :
    bitExps shift n = shift :: bitExps (shift + 1) (n / 2) := by
  cases n with
  | zero => simp at h
  | succ k => simp [bitExps, h]

private lemma bitExps_even_pos (shift n : Nat) (hpos : 0 < n) (heven : n % 2 = 0) :
    bitExps shift n = bitExps (shift + 1) (n / 2) := by
  cases n with
  | zero => omega
  | succ k =>
    have hne : (k + 1) % 2 ≠ 1 := by omega
    simp [bitExps, hne]

private lemma bitExps_ge (shift n : Nat) : ∀ e ∈ bitExps shift n, shift ≤ e := by
  induction n using Nat.strong_induction_on generalizing shift with
  | h n ih =>
    cases n with
    | zero => intro e he; simp [bitExps] at he
    | succ k =>
      unfold bitExps
      split_ifs with h
      · intro e he
        rcases List.mem_cons.mp he with rfl | he'
        · exact le_rfl
        · exact Nat.le_of_succ_le (ih ((k + 1) / 2) (by omega) (shift + 1) e he')
      · intro e he
        exact Nat.le_of_succ_le (ih ((k + 1) / 2) (by omega) (shift + 1) e he)

private lemma bitExps_strict (shift n : Nat) : (bitExps shift n).Pairwise (· < ·) := by
  induction n using Nat.strong_induction_on generalizing shift with
  | h n ih =>
    cases n with
    | zero => simp [bitExps]
    | succ k =>
      unfold bitExps
      split_ifs with h
      · refine List.pairwise_cons.mpr ⟨fun e he => ?_, ih ((k + 1) / 2) (by omega) (shift + 1)⟩
        have := bitExps_ge (shift + 1) ((k + 1) / 2) e he
        omega
      · exact ih ((k + 1) / 2) (by omega) (shift + 1)

/-- Stack invariant: `st` holds the chaining values of power-of-two subtrees whose sizes
match `exps` (head = rightmost / smallest subtree), concatenating left-to-right to `outs`. -/
private def StackInv (exps : List Nat) (st : List Digest) (outs : List Blake3.Pure.Output) : Prop :=
  ∃ (segs : List (List Blake3.Pure.Output)) (hsegs : segs.length = exps.length)
    (hst : st.length = exps.length),
    segs.reverse.flatten = outs ∧
    (∀ (k : Nat) (hk : k < exps.length),
      (segs[k]'(by omega)).length = 2 ^ exps[k] ∧
      digestToCV (st[k]'(by omega)) = (Blake3.Pure.mergeLevels (segs[k]'(by omega))).chainingValue)

private lemma stackInv_nil : StackInv [] [] [] :=
  ⟨[], rfl, rfl, rfl, fun k hk => by simp at hk⟩

private lemma pushChunk_inv (shift : Nat) (q : Nat) (st : List Digest)
    (outs cur : List Blake3.Pure.Output) (cv : Digest)
    (hst : StackInv (bitExps shift q) st outs)
    (hcur_len : cur.length = 2 ^ shift)
    (hcv : digestToCV cv = (Blake3.Pure.mergeLevels cur).chainingValue) :
    StackInv (bitExps shift (q + 1)) (Blake3.pushChunk st cv (q + 1)) (outs ++ cur) := by
  induction q using Nat.strong_induction_on generalizing shift st outs cur cv with
  | h q ih =>
    by_cases hodd : q % 2 = 1
    · -- `q + 1` is even: pop top `2^shift` subtree, merge with `cur`, recurse at `shift + 1`
      have hexp_q := bitExps_odd shift q hodd
      have hexp_q1 : bitExps shift (q + 1) = bitExps (shift + 1) ((q + 1) / 2) :=
        bitExps_even_pos shift (q + 1) (by omega) (by omega)
      rw [hexp_q] at hst
      obtain ⟨segs, hsegs_len, hst_len, hflat, hspec⟩ := hst
      cases st with
      | nil => simp at hst_len
      | cons top rest =>
        cases segs with
        | nil => simp at hsegs_len
        | cons s0 srest =>
          have hs0 := hspec 0 (by simp)
          simp only [List.getElem_cons_zero] at hs0
          have hmerged_len : (s0 ++ cur).length = 2 ^ (shift + 1) := by
            rw [List.length_append, hs0.1, hcur_len, Nat.pow_succ]; omega
          have hmerged_cv :
              digestToCV (Blake3.parentNode top cv).chainingValue =
                (Blake3.Pure.mergeLevels (s0 ++ cur)).chainingValue := by
            rw [node_chainingValue_eq, parentNode_eq, hs0.2, hcv,
              Blake3.Pure.mergeLevels_append shift s0 cur hs0.1
                (by rw [hcur_len]; exact Nat.two_pow_pos shift) (by rw [hcur_len])]
          have hrest_inv : StackInv (bitExps (shift + 1) (q / 2)) rest srest.reverse.flatten := by
            refine ⟨srest, by simpa using hsegs_len, by simpa using hst_len, rfl, ?_⟩
            intro k hk
            have hk' := hspec (k + 1) (by simp; omega)
            simp only [List.getElem_cons_succ] at hk'
            exact hk'
          have hstep : Blake3.pushChunk (top :: rest) cv (q + 1) =
              Blake3.pushChunk rest (Blake3.parentNode top cv).chainingValue ((q + 1) / 2) := by
            simp [Blake3.pushChunk, show (q + 1) % 2 = 0 by omega]
          have hdiv : (q + 1) / 2 = q / 2 + 1 := by omega
          rw [hexp_q1, hstep, hdiv]
          have hrec := ih (q / 2) (by omega) (shift + 1) rest srest.reverse.flatten (s0 ++ cur)
            (Blake3.parentNode top cv).chainingValue hrest_inv hmerged_len hmerged_cv
          have hflat' : srest.reverse.flatten ++ (s0 ++ cur) = outs ++ cur := by
            rw [← hflat, List.reverse_cons, List.flatten_append, List.flatten_singleton, List.append_assoc]
          rwa [hflat'] at hrec
    · -- `q` is even, `q + 1` is odd: push `cv` onto the stack without merging
      have heven : q % 2 = 0 := by omega
      have hexp_q1 : bitExps shift (q + 1) = shift :: bitExps (shift + 1) ((q + 1) / 2) :=
        bitExps_odd shift (q + 1) (by omega)
      have hexp_q : bitExps shift q = bitExps (shift + 1) ((q + 1) / 2) := by
        cases q with
        | zero => simp [bitExps]
        | succ k =>
          have hdiv : (k + 1 + 1) / 2 = (k + 1) / 2 := by omega
          rw [hdiv]
          exact bitExps_even_pos shift (k + 1) (by omega) heven
      have hpush_eq : Blake3.pushChunk st cv (q + 1) = cv :: st := by
        cases st with
        | nil => rfl
        | cons top rest => simp [Blake3.pushChunk, show (q + 1) % 2 ≠ 0 by omega]
      rw [hexp_q1, hpush_eq]
      rw [hexp_q] at hst
      obtain ⟨segs, hsegs_len, hst_len, hflat, hspec⟩ := hst
      refine ⟨cur :: segs, by simp [hsegs_len], by simp [hst_len], ?_, ?_⟩
      · rw [List.reverse_cons, List.flatten_append, List.flatten_singleton, hflat]
      · intro k hk
        cases k with
        | zero => exact ⟨hcur_len, hcv⟩
        | succ k => simpa only [List.getElem_cons_succ] using hspec k (by simp at hk; omega)

private lemma pushChunks_inv (len : Nat) (block : Nat → Blake3.Block)
    (outs : Nat → Blake3.Pure.Output) :
    ∀ (count start : Nat) (st : List Digest) (prefixOuts : List Blake3.Pure.Output),
      StackInv (bitExps 0 start) st prefixOuts →
      (∀ c, start ≤ c → c < start + count →
        nodeToOutput (Blake3.chunkNode len block c) = outs c) →
      StackInv (bitExps 0 (start + count))
        (Blake3.pushChunks len block count start st)
        (prefixOuts ++ (List.range count).map (fun i => outs (start + i))) := by
  intro count
  induction count with
  | zero =>
    intro start st prefixOuts hst _
    simpa [Blake3.pushChunks] using hst
  | succ count ih =>
    intro start st prefixOuts hst hmatch
    unfold Blake3.pushChunks
    have h0 := hmatch start (le_refl _) (by omega)
    have hcv0 : digestToCV (Blake3.chunkNode len block start).chainingValue =
        (Blake3.Pure.mergeLevels [outs start]).chainingValue := by
      rw [node_chainingValue_eq, h0, Blake3.Pure.mergeLevels_singleton]
    have hst1 := pushChunk_inv 0 start st prefixOuts [outs start]
      (Blake3.chunkNode len block start).chainingValue hst rfl hcv0
    have hrec := ih (start + 1)
      (Blake3.pushChunk st (Blake3.chunkNode len block start).chainingValue (start + 1))
      (prefixOuts ++ [outs start]) hst1
      (fun c hc1 hc2 => hmatch c (by omega) (by omega))
    have hsum : start + 1 + count = start + (count + 1) := by omega
    rw [hsum] at hrec
    have hlist :
        (prefixOuts ++ [outs start]) ++ (List.range count).map (fun i => outs (start + 1 + i)) =
        prefixOuts ++ (List.range (count + 1)).map (fun i => outs (start + i)) := by
      rw [List.append_assoc, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, Function.comp_def, List.singleton_append]
      congr 2
      apply List.map_congr_left
      intro i _
      congr 1; omega
    rwa [hlist] at hrec

private lemma finish_spec :
    ∀ (exps : List Nat) (st : List Digest) (prefixOuts tailOuts : List Blake3.Pure.Output)
      (lastNode : Blake3.Node),
      exps.Pairwise (· < ·) →
      StackInv exps st prefixOuts →
      0 < tailOuts.length →
      (∀ e ∈ exps, tailOuts.length ≤ 2 ^ e) →
      nodeToOutput lastNode = Blake3.Pure.mergeLevels tailOuts →
      (exps = [] → lastNode.counter = 0) →
      digestToCV (Blake3.finish st lastNode) =
        let out := Blake3.Pure.mergeLevels (prefixOuts ++ tailOuts)
        Blake3.Pure.compress out.cv out.block 0 out.blockLen (out.flags ||| 8) := by
  intro exps
  induction exps with
  | nil =>
    intro st prefixOuts tailOuts lastNode _ hst _ _ hlast hcnt
    obtain ⟨segs, hsegs_len, hst_len, hflat, _⟩ := hst
    cases st with
    | cons _ _ => simp at hst_len
    | nil =>
      cases segs with
      | cons _ _ => simp at hsegs_len
      | nil =>
        have hp : prefixOuts = [] := by simpa using hflat.symm
        subst hp
        simp only [Blake3.finish, Blake3.Node.rootDigest, List.nil_append]
        rw [compress_eq, ← hlast]
        have hc0 := hcnt rfl
        simp [nodeToOutput, hc0, Blake3.flagRoot]
  | cons e0 erest ih =>
    intro st prefixOuts tailOuts lastNode hpair hst htail_pos htail_le hlast _
    obtain ⟨segs, hsegs_len, hst_len, hflat, hspec⟩ := hst
    cases st with
    | nil => simp at hst_len
    | cons top rest =>
      cases segs with
      | nil => simp at hsegs_len
      | cons s0 srest =>
        have hs0 := hspec 0 (by simp)
        simp only [List.getElem_cons_zero] at hs0
        have he0_le : tailOuts.length ≤ 2 ^ e0 := htail_le e0 (by simp)
        have hparent_out :
            nodeToOutput (Blake3.parentNode top lastNode.chainingValue) =
              Blake3.Pure.mergeLevels (s0 ++ tailOuts) := by
          rw [parentNode_eq, hs0.2, node_chainingValue_eq, hlast,
            Blake3.Pure.mergeLevels_append e0 s0 tailOuts hs0.1 htail_pos he0_le]
        have hrest_inv : StackInv erest rest srest.reverse.flatten := by
          refine ⟨srest, by simpa using hsegs_len, by simpa using hst_len, rfl, ?_⟩
          intro k hk
          have hk' := hspec (k + 1) (by simp; omega)
          simp only [List.getElem_cons_succ] at hk'
          exact hk'
        have hpair' := List.pairwise_cons.mp hpair
        have hnew_le : ∀ e ∈ erest, (s0 ++ tailOuts).length ≤ 2 ^ e := by
          intro e he
          have hlt : e0 < e := hpair'.1 e he
          rw [List.length_append, hs0.1]
          have hpow : 2 ^ (e0 + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by omega) (by omega)
          rw [Nat.pow_succ] at hpow
          omega
        unfold Blake3.finish
        have hrec := ih rest srest.reverse.flatten (s0 ++ tailOuts)
          (Blake3.parentNode top lastNode.chainingValue) hpair'.2 hrest_inv
          (by rw [List.length_append]; omega) hnew_le hparent_out (fun _ => rfl)
        have hconcat : srest.reverse.flatten ++ (s0 ++ tailOuts) = prefixOuts ++ tailOuts := by
          rw [← hflat, List.reverse_cons, List.flatten_append, List.flatten_singleton, List.append_assoc]
        rwa [hconcat] at hrec

/-! ## 6. Chunk Output Indexing and Top-Level `blake3` Parity -/

private lemma chunkOutputs_eq_range (input : List UInt8) :
    ∀ (counter : Nat),
      Blake3.Pure.chunkOutputs counter input =
        (List.range (max 1 ((input.length + 1023) / 1024))).map fun i =>
          Blake3.Pure.chunkOutput (counter + i).toUInt64 ((input.drop (1024 * i)).take 1024) := by
  induction hlen : input.length using Nat.strong_induction_on generalizing input with
  | h n ih =>
    intro counter
    by_cases hsmall : input.length ≤ 1024
    · have hc : max 1 ((n + 1023) / 1024) = 1 := by omega
      rw [Blake3.Pure.chunkOutputs_small counter input hsmall, hc, List.range_one, List.map_singleton]
      simp [List.take_of_length_le hsmall]
    · have hlarge : 1024 < input.length := by omega
      rw [Blake3.Pure.chunkOutputs_large counter input hlarge]
      have hdrop_len : (input.drop 1024).length < n := by rw [List.length_drop]; omega
      have hrec := ih (input.drop 1024).length hdrop_len (input.drop 1024) rfl (counter + 1)
      have hc : max 1 ((n + 1023) / 1024) =
          max 1 (((input.drop 1024).length + 1023) / 1024) + 1 := by
        rw [List.length_drop]; omega
      rw [hc, List.range_succ_eq_map, List.map_cons, List.map_map, hrec]
      simp only [Nat.add_zero, Nat.mul_zero, List.drop_zero, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_def, List.drop_drop, Nat.succ_eq_add_one]
      rw [show counter + 1 + i = counter + (i + 1) by omega,
          show 1024 + 1024 * i = 1024 * (i + 1) by omega]

/-- **BLAKE3 Parity (plain mode):** `CertiFri.P3.blake3` (unkeyed BLAKE3) produces the
exact same 32 bytes as `Blake3.Pure.digest` for every `ByteArray`. The keyed `derive_key` hashers
that every v6 verifier uses (`baseHasherSep`, `ext3HasherSep`, the in-circuit `b3_dk_*`) are not
covered. -/
theorem blake3_eq_pure (bytes : ByteArray) :
    CertiFri.P3.blake3 bytes = ByteArray.mk (Blake3.Pure.digest bytes.data.toList).toArray := by
  unfold CertiFri.P3.blake3 Blake3.hash Blake3.hashBlocks
  set chunks := max 1 ((bytes.size + 1023) / 1024)
  set f : Nat → Blake3.Pure.Output := fun i =>
    Blake3.Pure.chunkOutput i.toUInt64 ((bytes.data.toList.drop (1024 * i)).take 1024)
  have hchunks_pos : 0 < chunks := by dsimp [chunks]; omega
  have hpush := pushChunks_inv bytes.size (Blake3.bytesBlock bytes) f
    (chunks - 1) 0 [] [] (by rw [bitExps_zero]; exact stackInv_nil)
    (fun c _ hc => chunkNode_eq_chunkOutput bytes c (by omega))
  simp only [Nat.zero_add, List.nil_append] at hpush
  have hlast : nodeToOutput (Blake3.chunkNode bytes.size (Blake3.bytesBlock bytes) (chunks - 1)) =
      Blake3.Pure.mergeLevels [f (chunks - 1)] := by
    rw [Blake3.Pure.mergeLevels_singleton]
    exact chunkNode_eq_chunkOutput bytes (chunks - 1) (by omega)
  have hcnt : bitExps 0 (chunks - 1) = [] →
      (Blake3.chunkNode bytes.size (Blake3.bytesBlock bytes) (chunks - 1)).counter = 0 := by
    intro hnil
    have h0 : chunks - 1 = 0 := by
      by_contra hne
      have hpos : 0 < chunks - 1 := by omega
      have hne_nil : bitExps 0 (chunks - 1) ≠ [] := by
        clear hnil
        generalize hm : chunks - 1 = m at hpos
        clear hm
        generalize hs : 0 = s
        clear hs
        induction m using Nat.strong_induction_on generalizing s with
        | h m ihm =>
          cases m with
          | zero => omega
          | succ k =>
            by_cases ho : (k + 1) % 2 = 1
            · rw [bitExps_odd s (k + 1) ho]; exact List.cons_ne_nil _ _
            · rw [bitExps_even_pos s (k + 1) (by omega) (by omega)]
              exact ihm ((k + 1) / 2) (by omega) (by omega) (s + 1)
      exact hne_nil hnil
    simp [Blake3.chunkNode, h0]
  have hfin := finish_spec (bitExps 0 (chunks - 1))
    (Blake3.pushChunks bytes.size (Blake3.bytesBlock bytes) (chunks - 1) 0 [])
    ((List.range (chunks - 1)).map f) [f (chunks - 1)]
    (Blake3.chunkNode bytes.size (Blake3.bytesBlock bytes) (chunks - 1))
    (bitExps_strict 0 (chunks - 1)) hpush (by simp)
    (fun e _ => by simp [Nat.one_le_two_pow]) hlast hcnt
  have hall_chunks :
      (List.range (chunks - 1)).map f ++ [f (chunks - 1)] =
        Blake3.Pure.chunkOutputs 0 bytes.data.toList := by
    rw [chunkOutputs_eq_range bytes.data.toList 0]
    have hsz : bytes.data.toList.length = bytes.size := rfl
    rw [hsz]
    have hrange : List.range chunks = List.range (chunks - 1) ++ [chunks - 1] := by
      conv => lhs; rw [show chunks = (chunks - 1) + 1 by omega, List.range_succ]
    rw [hrange, List.map_append, List.map_singleton]
    simp [f]
  rw [hall_chunks] at hfin
  apply ByteArray.ext
  rw [digest_toBytes_eq_cvBytes, hfin, Blake3.Pure.digest_eq_mergeLevels]
  rfl

/-! ## 7. `baseHasher`, `extHasher`, and `hashPair` Byte-Stream Parity -/

private lemma hashBlocks_congr (len : Nat) (b1 b2 : Nat → Blake3.Block)
    (h : ∀ i, i < 16 * max 1 ((len + 1023) / 1024) → b1 i = b2 i) :
    Blake3.hashBlocks len b1 = Blake3.hashBlocks len b2 := by
  have hchain : ∀ first counter count j cv,
      (∀ k, k < count → b1 (first + (j + k)) = b2 (first + (j + k))) →
      Blake3.chainBlocks b1 first counter count j cv =
        Blake3.chainBlocks b2 first counter count j cv := by
    intro first counter count
    induction count with
    | zero => intro j cv _; rfl
    | succ count ih =>
      intro j cv hb
      unfold Blake3.chainBlocks
      have h0 : b1 (first + j) = b2 (first + j) := by simpa using hb 0 (by omega)
      rw [h0]
      exact ih (j + 1) _ (fun k hk => by
        have := hb (k + 1) (by omega)
        rwa [show j + (k + 1) = j + 1 + k by omega] at this)
  have hchunk : ∀ c, c < max 1 ((len + 1023) / 1024) →
      Blake3.chunkNode len b1 c = Blake3.chunkNode len b2 c := by
    intro c hc
    unfold Blake3.chunkNode
    dsimp only
    have hblks_le : max 1 ((min 1024 (len - 1024 * c) + 63) / 64) ≤ 16 := by omega
    have hch := hchain (16 * c) c.toUInt64 (max 1 ((min 1024 (len - 1024 * c) + 63) / 64) - 1) 0
      Blake3.iv (fun k hk => h (16 * c + (0 + k)) (by omega))
    have hlast := h (16 * c + (max 1 ((min 1024 (len - 1024 * c) + 63) / 64) - 1)) (by omega)
    rw [hch, hlast]
  have hpush : ∀ count c st, c + count ≤ max 1 ((len + 1023) / 1024) →
      Blake3.pushChunks len b1 count c st = Blake3.pushChunks len b2 count c st := by
    intro count
    induction count with
    | zero => intro c st _; rfl
    | succ count ih =>
      intro c st hle
      unfold Blake3.pushChunks
      rw [hchunk c (by omega)]
      exact ih (c + 1) _ (by omega)
  unfold Blake3.hashBlocks
  dsimp only
  rw [hpush (max 1 ((len + 1023) / 1024) - 1) 0 [] (by omega),
      hchunk (max 1 ((len + 1023) / 1024) - 1) (by omega)]

/-- `Blake3.hashPair a b` is the BLAKE3 hash of the 64-byte concatenation `a.toBytes ++ b.toBytes`. -/
theorem hashPair_eq_blake3 (a b : Digest) :
    (Blake3.hashPair a b).toBytes = CertiFri.P3.blake3 (a.toBytes ++ b.toBytes) := by
  have hlist : (a.toBytes ++ b.toBytes).data.toList =
      [a.w0.toUInt8, (a.w0 >>> 8).toUInt8, (a.w0 >>> 16).toUInt8, (a.w0 >>> 24).toUInt8,
       a.w1.toUInt8, (a.w1 >>> 8).toUInt8, (a.w1 >>> 16).toUInt8, (a.w1 >>> 24).toUInt8,
       a.w2.toUInt8, (a.w2 >>> 8).toUInt8, (a.w2 >>> 16).toUInt8, (a.w2 >>> 24).toUInt8,
       a.w3.toUInt8, (a.w3 >>> 8).toUInt8, (a.w3 >>> 16).toUInt8, (a.w3 >>> 24).toUInt8,
       a.w4.toUInt8, (a.w4 >>> 8).toUInt8, (a.w4 >>> 16).toUInt8, (a.w4 >>> 24).toUInt8,
       a.w5.toUInt8, (a.w5 >>> 8).toUInt8, (a.w5 >>> 16).toUInt8, (a.w5 >>> 24).toUInt8,
       a.w6.toUInt8, (a.w6 >>> 8).toUInt8, (a.w6 >>> 16).toUInt8, (a.w6 >>> 24).toUInt8,
       a.w7.toUInt8, (a.w7 >>> 8).toUInt8, (a.w7 >>> 16).toUInt8, (a.w7 >>> 24).toUInt8,
       b.w0.toUInt8, (b.w0 >>> 8).toUInt8, (b.w0 >>> 16).toUInt8, (b.w0 >>> 24).toUInt8,
       b.w1.toUInt8, (b.w1 >>> 8).toUInt8, (b.w1 >>> 16).toUInt8, (b.w1 >>> 24).toUInt8,
       b.w2.toUInt8, (b.w2 >>> 8).toUInt8, (b.w2 >>> 16).toUInt8, (b.w2 >>> 24).toUInt8,
       b.w3.toUInt8, (b.w3 >>> 8).toUInt8, (b.w3 >>> 16).toUInt8, (b.w3 >>> 24).toUInt8,
       b.w4.toUInt8, (b.w4 >>> 8).toUInt8, (b.w4 >>> 16).toUInt8, (b.w4 >>> 24).toUInt8,
       b.w5.toUInt8, (b.w5 >>> 8).toUInt8, (b.w5 >>> 16).toUInt8, (b.w5 >>> 24).toUInt8,
       b.w6.toUInt8, (b.w6 >>> 8).toUInt8, (b.w6 >>> 16).toUInt8, (b.w6 >>> 24).toUInt8,
       b.w7.toUInt8, (b.w7 >>> 8).toUInt8, (b.w7 >>> 16).toUInt8, (b.w7 >>> 24).toUInt8] := by
    have happ : (a.toBytes ++ b.toBytes).data.toList =
        a.toBytes.data.toList ++ b.toBytes.data.toList := by
      simp [Array.toList_append]
    rw [happ, digest_toBytes_toList a, digest_toBytes_toList b]
    rfl
  have hsz : (a.toBytes ++ b.toBytes).size = 64 := by
    have : (a.toBytes ++ b.toBytes).data.toList.length = 64 := by rw [hlist]; rfl
    simpa only [ByteArray.size, Array.length_toList] using this
  have hblk : Blake3.bytesBlock (a.toBytes ++ b.toBytes) 0 = Blake3.pairBlock a b := by
    have hrepack (w : UInt32) :
        w.toUInt8.toUInt32 ||| ((w >>> 8).toUInt8.toUInt32 <<< 8) |||
        ((w >>> 16).toUInt8.toUInt32 <<< 16) ||| ((w >>> 24).toUInt8.toUInt32 <<< 24) = w := by
      rw [pack_le_u32]
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_ofNat']
      have h0 : w.toUInt8.toNat = w.toNat % 256 := rfl
      have h1 : (w >>> 8).toUInt8.toNat = (w.toNat / 256) % 256 := by
        have h := uint32_shr_toUInt8_eq w 1 (by omega)
        change (w >>> 8).toUInt8 = _ at h
        rw [h]; rfl
      have h2 : (w >>> 16).toUInt8.toNat = (w.toNat / 65536) % 256 := by
        have h := uint32_shr_toUInt8_eq w 2 (by omega)
        change (w >>> 16).toUInt8 = _ at h
        rw [h]; rfl
      have h3 : (w >>> 24).toUInt8.toNat = (w.toNat / 16777216) % 256 := by
        have h := uint32_shr_toUInt8_eq w 3 (by omega)
        change (w >>> 24).toUInt8 = _ at h
        rw [h]; rfl
      have hwlt : w.toNat < 2 ^ 32 := w.toNat_lt
      rw [h0, h1, h2, h3, Nat.mod_eq_of_lt (by omega)]
      omega
    unfold Blake3.bytesBlock Blake3.pairBlock LittleEndian.word32
    simp only [byteOrZero_eq_list_getD, hlist, Nat.mul_zero, Nat.zero_add]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, hrepack]
  unfold CertiFri.P3.blake3 Blake3.hash Blake3.hashBlocks Blake3.hashPair
  rw [hsz]
  change (Blake3.compress Blake3.iv (Blake3.pairBlock a b) 0 64
      (Blake3.flagChunkStart ||| Blake3.flagChunkEnd ||| Blake3.flagRoot)).toBytes =
    (Blake3.compress Blake3.iv (Blake3.bytesBlock (a.toBytes ++ b.toBytes) 0) 0 64
      (Blake3.flagChunkStart ||| Blake3.flagChunkEnd ||| Blake3.flagRoot)).toBytes
  rw [hblk]

/-- `Blake3.hashPair a b` equals `Blake3.Pure.digest` of the 64 concatenated digest bytes. -/
theorem hashPair_eq_pure (a b : Digest) :
    (Blake3.hashPair a b).toBytes =
      ByteArray.mk (Blake3.Pure.digest (a.toBytes ++ b.toBytes).data.toList).toArray := by
  rw [hashPair_eq_blake3, blake3_eq_pure]

private lemma byteArray_size_emptyWithCapacity (n : Nat) :
    (ByteArray.emptyWithCapacity n).size = 0 := rfl

private lemma byteArray_getElem_push_lt (b : ByteArray) (x : UInt8) (i : Nat)
    (hi : i < b.size) (hi' : i < (b.push x).size) :
    (b.push x)[i]'hi' = b[i]'hi := by
  exact Array.getElem_push_lt hi

private lemma pushBytes_toList (acc : ByteArray) (x : Goldilocks) :
    (Goldilocks.pushBytes acc x).data.toList =
      acc.data.toList ++
        [x.val.toUInt8, (x.val >>> 8).toUInt8, (x.val >>> 16).toUInt8, (x.val >>> 24).toUInt8,
         (x.val >>> 32).toUInt8, (x.val >>> 40).toUInt8, (x.val >>> 48).toUInt8, (x.val >>> 56).toUInt8] := by
  unfold Goldilocks.pushBytes
  simp only [ByteArray.push, Array.toList_push, List.append_assoc, List.cons_append, List.nil_append]

private lemma pushBytes_getElem_add (acc : ByteArray) (x : Goldilocks) (r : Nat) (hr : r < 8)
    (hlt : acc.size + r < (Goldilocks.pushBytes acc x).size) :
    (Goldilocks.pushBytes acc x)[acc.size + r]'hlt = (x.val >>> (8 * r).toUInt64).toUInt8 := by
  have hlen : acc.data.toList.length = acc.size := Array.length_toList
  have hlt_list : acc.size + r < (Goldilocks.pushBytes acc x).data.toList.length := by
    rwa [Array.length_toList]
  have hget : (Goldilocks.pushBytes acc x)[acc.size + r]'hlt =
      (Goldilocks.pushBytes acc x).data.toList[acc.size + r]'hlt_list := rfl
  rw [hget]
  simp only [pushBytes_toList]
  have hle : acc.data.toList.length ≤ acc.size + r := by omega
  rw [List.getElem_append_right hle]
  have hsub : acc.size + r - acc.data.toList.length = r := by omega
  simp only [hsub]
  interval_cases r <;> rfl

private lemma rowBytes_size (row : Array Goldilocks) :
    (Hashers.rowBytes row).size = 8 * row.size := by
  unfold Hashers.rowBytes
  have hfold : ∀ (l : List Goldilocks) (acc : ByteArray),
      (l.foldl Goldilocks.pushBytes acc).size = acc.size + 8 * l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, List.length_cons, ih]
      have hpush : (Goldilocks.pushBytes acc x).size = acc.size + 8 := by
        simp [Goldilocks.pushBytes, ByteArray.size_push]
      rw [hpush]; omega
  rw [← Array.foldl_toList, hfold, byteArray_size_emptyWithCapacity]
  simp

private lemma rowBytes_get (row : Array Goldilocks) (i : Nat) (k : Nat) (hk : k < 8) :
    LittleEndian.byteOrZero (Hashers.rowBytes row) (8 * i + k) =
      ((Hashers.wordOrZero row i) >>> (8 * k).toUInt64).toUInt8 := by
  unfold Hashers.rowBytes
  have hfold : ∀ (l : List Goldilocks) (acc : ByteArray) (idx : Nat),
      LittleEndian.byteOrZero (l.foldl Goldilocks.pushBytes acc) idx =
        if idx < acc.size then LittleEndian.byteOrZero acc idx
        else
          let rel := idx - acc.size
          let elemIdx := rel / 8
          let byteIdx := rel % 8
          if h : elemIdx < l.length then
            (l[elemIdx].val >>> (8 * byteIdx).toUInt64).toUInt8
          else 0 := by
    intro l
    induction l with
    | nil =>
      intro acc idx
      simp only [List.foldl_nil, List.length_nil, Nat.not_lt_zero, ↓reduceDIte]
      by_cases h1 : idx < acc.size
      · simp only [h1, ↓reduceIte]
      · simp only [h1, ↓reduceIte, LittleEndian.byteOrZero, ↓reduceDIte]
    | cons x xs ih =>
      intro acc idx
      rw [List.foldl_cons, ih]
      have hsz : (Goldilocks.pushBytes acc x).size = acc.size + 8 := by
        simp [Goldilocks.pushBytes, ByteArray.size_push]
      by_cases hlt : idx < acc.size
      · have hlt2 : idx < (Goldilocks.pushBytes acc x).size := by omega
        simp only [hlt2, hlt, ↓reduceIte, LittleEndian.byteOrZero, ↓reduceDIte]
        unfold Goldilocks.pushBytes
        repeat rw [byteArray_getElem_push_lt (hi := by simp [ByteArray.size_push]; omega)]
        exact byteArray_getElem_push_lt acc x.val.toUInt8 idx hlt _
      · by_cases hmid : idx < acc.size + 8
        · have hlt2 : idx < (Goldilocks.pushBytes acc x).size := by omega
          simp only [hlt2, hlt, ↓reduceIte]
          have hdiv : (idx - acc.size) / 8 = 0 := by omega
          have hmod : (idx - acc.size) % 8 = idx - acc.size := by omega
          simp only [hdiv, hmod, List.length_cons, Nat.zero_lt_succ, ↓reduceDIte, List.getElem_cons_zero]
          unfold LittleEndian.byteOrZero
          simp only [hlt2, ↓reduceDIte]
          have hr : idx - acc.size < 8 := by omega
          have hidx_eq : idx = acc.size + (idx - acc.size) := by omega
          generalize hrem : idx - acc.size = r at hr hidx_eq
          clear hrem hlt hmid
          revert hlt2
          rw [hidx_eq]
          intro hlt2
          exact pushBytes_getElem_add acc x r hr hlt2
        · simp only [hsz, hmid, hlt, ↓reduceIte]
          have hdiv : (idx - acc.size) / 8 = (idx - (acc.size + 8)) / 8 + 1 := by omega
          have hmod : (idx - acc.size) % 8 = (idx - (acc.size + 8)) % 8 := by omega
          simp only [hdiv, hmod, List.length_cons]
          by_cases hlen : (idx - (acc.size + 8)) / 8 < xs.length
          · have hlen' : (idx - (acc.size + 8)) / 8 + 1 < xs.length + 1 := by omega
            simp only [hlen, hlen', ↓reduceDIte, List.getElem_cons_succ]
          · have hlen' : ¬ (idx - (acc.size + 8)) / 8 + 1 < xs.length + 1 := by omega
            simp only [hlen, hlen', ↓reduceDIte]
  rw [← Array.foldl_toList, hfold, byteArray_size_emptyWithCapacity]
  simp only [Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero,
    show (8 * i + k) / 8 = i by omega, show (8 * i + k) % 8 = k by omega]
  unfold Hashers.wordOrZero
  by_cases hi : i < row.size
  · have hl : i < row.toList.length := by simpa using hi
    simp only [hl, hi, ↓reduceDIte]; rfl
  · have hl : ¬ i < row.toList.length := by simpa using hi
    simp only [hl, hi, ↓reduceDIte]
    simp

private lemma word32_rowBytes_lo (row : Array Goldilocks) (i : Nat) :
    LittleEndian.word32 (Hashers.rowBytes row) (8 * i) = (Hashers.wordOrZero row i).toUInt32 := by
  unfold LittleEndian.word32
  have h0 := rowBytes_get row i 0 (by omega)
  have h1 := rowBytes_get row i 1 (by omega)
  have h2 := rowBytes_get row i 2 (by omega)
  have h3 := rowBytes_get row i 3 (by omega)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3, pack_le_u32]
  set w := Hashers.wordOrZero row i
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', UInt64.toNat_toUInt32]
  have hw0 : (w >>> (8 * 0).toUInt64).toUInt8.toNat = w.toNat % 256 := by
    change (w >>> 0).toUInt8.toNat = _
    simp [UInt64.toNat_toUInt8]
  have hw1 : (w >>> (8 * 1).toUInt64).toUInt8.toNat = (w.toNat / 256) % 256 := by
    change (w >>> 8).toUInt8.toNat = _
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
    have : (8 : UInt64).toNat % 64 = 8 := rfl
    rw [this, Nat.shiftRight_eq_div_pow]
  have hw2 : (w >>> (8 * 2).toUInt64).toUInt8.toNat = (w.toNat / 65536) % 256 := by
    change (w >>> 16).toUInt8.toNat = _
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
    have : (16 : UInt64).toNat % 64 = 16 := rfl
    rw [this, Nat.shiftRight_eq_div_pow]
  have hw3 : (w >>> (8 * 3).toUInt64).toUInt8.toNat = (w.toNat / 16777216) % 256 := by
    change (w >>> 24).toUInt8.toNat = _
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
    have : (24 : UInt64).toNat % 64 = 24 := rfl
    rw [this, Nat.shiftRight_eq_div_pow]
  rw [hw0, hw1, hw2, hw3]
  omega

private lemma word32_rowBytes_hi (row : Array Goldilocks) (i : Nat) :
    LittleEndian.word32 (Hashers.rowBytes row) (8 * i + 4) =
      ((Hashers.wordOrZero row i) >>> 32).toUInt32 := by
  unfold LittleEndian.word32
  have h4 := rowBytes_get row i 4 (by omega)
  have h5 := rowBytes_get row i 5 (by omega)
  have h6 := rowBytes_get row i 6 (by omega)
  have h7 := rowBytes_get row i 7 (by omega)
  rw [show 8 * i + 4 + 1 = 8 * i + 5 by omega,
      show 8 * i + 4 + 2 = 8 * i + 6 by omega,
      show 8 * i + 4 + 3 = 8 * i + 7 by omega]
  rw [h4, h5, h6, h7, pack_le_u32]
  set w := Hashers.wordOrZero row i
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
  have hs32 : (32 : UInt64).toNat % 64 = 32 := rfl
  rw [hs32, Nat.shiftRight_eq_div_pow]
  have hw4 : (w >>> (8 * 4).toUInt64).toUInt8.toNat = (w.toNat / 2 ^ 32) % 256 := by
    change (w >>> 32).toUInt8.toNat = _
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, hs32, Nat.shiftRight_eq_div_pow]
  have hw5 : (w >>> (8 * 5).toUInt64).toUInt8.toNat = ((w.toNat / 2 ^ 32) / 256) % 256 := by
    change (w >>> 40).toUInt8.toNat = _
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
    have : (40 : UInt64).toNat % 64 = 40 := rfl
    rw [this, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]; rfl
  have hw6 : (w >>> (8 * 6).toUInt64).toUInt8.toNat = ((w.toNat / 2 ^ 32) / 65536) % 256 := by
    change (w >>> 48).toUInt8.toNat = _
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
    have : (48 : UInt64).toNat % 64 = 48 := rfl
    rw [this, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]; rfl
  have hw7 : (w >>> (8 * 7).toUInt64).toUInt8.toNat = ((w.toNat / 2 ^ 32) / 16777216) % 256 := by
    change (w >>> 56).toUInt8.toNat = _
    rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
    have : (56 : UInt64).toNat % 64 = 56 := rfl
    rw [this, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]; rfl
  have hwlt : w.toNat < 2 ^ 64 := w.toNat_lt
  rw [hw4, hw5, hw6, hw7]
  omega

/-- `baseHasher.hashRows row` equals `Blake3.Pure.digest` of `Hashers.rowBytes row`. -/
theorem baseHasher_hashRows_eq_pure (row : Array Goldilocks) :
    (CertiFri.P3.baseHasher.hashRows row).toBytes =
      ByteArray.mk (Blake3.Pure.digest (Hashers.rowBytes row).data.toList).toArray := by
  rw [← blake3_eq_pure]
  unfold CertiFri.P3.baseHasher CertiFri.P3.blake3 Blake3.hash
  rw [rowBytes_size]
  congr 1
  apply hashBlocks_congr
  intro i _
  unfold Hashers.rowBlock Hashers.wordsBlock Blake3.bytesBlock
  simp only [
    show 64 * i + 4 * 0 = 8 * (8 * i) by omega,
    show 64 * i + 4 * 1 = 8 * (8 * i) + 4 by omega,
    show 64 * i + 4 * 2 = 8 * (8 * i + 1) by omega,
    show 64 * i + 4 * 3 = 8 * (8 * i + 1) + 4 by omega,
    show 64 * i + 4 * 4 = 8 * (8 * i + 2) by omega,
    show 64 * i + 4 * 5 = 8 * (8 * i + 2) + 4 by omega,
    show 64 * i + 4 * 6 = 8 * (8 * i + 3) by omega,
    show 64 * i + 4 * 7 = 8 * (8 * i + 3) + 4 by omega,
    show 64 * i + 4 * 8 = 8 * (8 * i + 4) by omega,
    show 64 * i + 4 * 9 = 8 * (8 * i + 4) + 4 by omega,
    show 64 * i + 4 * 10 = 8 * (8 * i + 5) by omega,
    show 64 * i + 4 * 11 = 8 * (8 * i + 5) + 4 by omega,
    show 64 * i + 4 * 12 = 8 * (8 * i + 6) by omega,
    show 64 * i + 4 * 13 = 8 * (8 * i + 6) + 4 by omega,
    show 64 * i + 4 * 14 = 8 * (8 * i + 7) by omega,
    show 64 * i + 4 * 15 = 8 * (8 * i + 7) + 4 by omega,
    word32_rowBytes_lo, word32_rowBytes_hi]

/-- Flatten extension row into its `2 * row.size` base Goldilocks coordinates `(c0, c1)`. -/
def flattenExtRow (row : Array GoldilocksExt) : Array Goldilocks :=
  (row.toList.flatMap fun e => [e.c0, e.c1]).toArray

private lemma extRowBytes_eq_rowBytes_flatten (row : Array GoldilocksExt) :
    Hashers.extRowBytes row = Hashers.rowBytes (flattenExtRow row) := by
  unfold Hashers.extRowBytes Hashers.rowBytes flattenExtRow
  have hfold : ∀ (l : List GoldilocksExt) (acc : ByteArray),
      l.foldl (fun bytes e => Goldilocks.pushBytes (Goldilocks.pushBytes bytes e.c0) e.c1) acc =
        (l.flatMap fun e => [e.c0, e.c1]).foldl Goldilocks.pushBytes acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons e es ih =>
      intro acc
      simp [List.foldl_cons, List.flatMap_cons, ih]
  rw [← Array.foldl_toList, ← Array.foldl_toList, hfold]
  rfl

private lemma flattenExtRow_size (row : Array GoldilocksExt) :
    (flattenExtRow row).size = 2 * row.size := by
  unfold flattenExtRow
  have h : ∀ l : List GoldilocksExt, (l.flatMap fun e => [e.c0, e.c1]).length = 2 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => simp [List.flatMap_cons, ih]; omega
  simpa using h row.toList

private lemma wordOrZero_flattenExtRow_even (row : Array GoldilocksExt) (k : Nat) :
    Hashers.wordOrZero (flattenExtRow row) (2 * k) = (row[k]?.getD default).c0.val := by
  have hget : ∀ (l : List GoldilocksExt) (k : Nat),
      (l.flatMap fun e => [e.c0, e.c1])[2 * k]?.map (·.val) =
        if k < l.length then some (l[k]?.getD default).c0.val else none := by
    intro l
    induction l with
    | nil => intro k; simp
    | cons e es ih =>
      intro k
      cases k with
      | zero => simp [List.flatMap_cons]
      | succ k =>
        simp only [List.flatMap_cons, List.cons_append, List.nil_append,
          show 2 * (k + 1) = (2 * k) + 2 by omega, List.getElem?_cons_succ, List.length_cons]
        simpa using ih k
  unfold Hashers.wordOrZero
  by_cases hk : k < row.size
  · have h2k : 2 * k < (flattenExtRow row).size := by rw [flattenExtRow_size]; omega
    simp only [h2k, ↓reduceDIte]
    have hspec := hget row.toList k
    have hlt : k < row.toList.length := by simpa using hk
    simp only [hlt, ↓reduceIte] at hspec
    have hflat_lt : 2 * k < (row.toList.flatMap fun e => [e.c0, e.c1]).length := by
      simpa [flattenExtRow] using h2k
    have helem : (row.toList.flatMap fun e => [e.c0, e.c1])[2 * k]? =
        some (flattenExtRow row)[2 * k] := by
      rw [List.getElem?_eq_getElem hflat_lt]; rfl
    rw [helem] at hspec
    have hinj := Option.some.inj (by simpa using hspec)
    exact hinj
  · have h2k : ¬ 2 * k < (flattenExtRow row).size := by rw [flattenExtRow_size]; omega
    simp only [h2k, ↓reduceDIte, Array.getElem?_eq_none (Nat.le_of_not_lt hk)]
    rfl

private lemma wordOrZero_flattenExtRow_odd (row : Array GoldilocksExt) (k : Nat) :
    Hashers.wordOrZero (flattenExtRow row) (2 * k + 1) = (row[k]?.getD default).c1.val := by
  have hget : ∀ (l : List GoldilocksExt) (k : Nat),
      (l.flatMap fun e => [e.c0, e.c1])[2 * k + 1]?.map (·.val) =
        if k < l.length then some (l[k]?.getD default).c1.val else none := by
    intro l
    induction l with
    | nil => intro k; simp
    | cons e es ih =>
      intro k
      cases k with
      | zero => simp [List.flatMap_cons]
      | succ k =>
        simp only [List.flatMap_cons, List.cons_append, List.nil_append,
          show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, List.getElem?_cons_succ, List.length_cons]
        simpa using ih k
  unfold Hashers.wordOrZero
  by_cases hk : k < row.size
  · have h2k : 2 * k + 1 < (flattenExtRow row).size := by rw [flattenExtRow_size]; omega
    simp only [h2k, ↓reduceDIte]
    have hspec := hget row.toList k
    have hlt : k < row.toList.length := by simpa using hk
    simp only [hlt, ↓reduceIte] at hspec
    have hflat_lt : 2 * k + 1 < (row.toList.flatMap fun e => [e.c0, e.c1]).length := by
      simpa [flattenExtRow] using h2k
    have helem : (row.toList.flatMap fun e => [e.c0, e.c1])[2 * k + 1]? =
        some (flattenExtRow row)[2 * k + 1] := by
      rw [List.getElem?_eq_getElem hflat_lt]; rfl
    rw [helem] at hspec
    have hinj := Option.some.inj (by simpa using hspec)
    exact hinj
  · have h2k : ¬ 2 * k + 1 < (flattenExtRow row).size := by rw [flattenExtRow_size]; omega
    simp only [h2k, ↓reduceDIte, Array.getElem?_eq_none (Nat.le_of_not_lt hk)]
    rfl

/-- `extHasher.hashRows row` equals `Blake3.Pure.digest` of `Hashers.extRowBytes row`. -/
theorem extHasher_hashRows_eq_pure (row : Array GoldilocksExt) :
    (CertiFri.P3.extHasher.hashRows row).toBytes =
      ByteArray.mk (Blake3.Pure.digest (Hashers.extRowBytes row).data.toList).toArray := by
  rw [extRowBytes_eq_rowBytes_flatten, ← baseHasher_hashRows_eq_pure]
  unfold CertiFri.P3.extHasher CertiFri.P3.baseHasher
  dsimp only
  rw [flattenExtRow_size, show 8 * (2 * row.size) = 16 * row.size by omega]
  congr 1
  apply hashBlocks_congr
  intro i _
  unfold Hashers.extRowBlock Hashers.rowBlock
  dsimp only
  rw [show 8 * i = 2 * (4 * i) by omega,
      show 2 * (4 * i) + 2 = 2 * (4 * i + 1) by omega,
      show 2 * (4 * i) + 3 = 2 * (4 * i + 1) + 1 by omega,
      show 2 * (4 * i) + 4 = 2 * (4 * i + 2) by omega,
      show 2 * (4 * i) + 5 = 2 * (4 * i + 2) + 1 by omega,
      show 2 * (4 * i) + 6 = 2 * (4 * i + 3) by omega,
      show 2 * (4 * i) + 7 = 2 * (4 * i + 3) + 1 by omega,
      wordOrZero_flattenExtRow_even, wordOrZero_flattenExtRow_odd,
      wordOrZero_flattenExtRow_even, wordOrZero_flattenExtRow_odd,
      wordOrZero_flattenExtRow_even, wordOrZero_flattenExtRow_odd,
      wordOrZero_flattenExtRow_even, wordOrZero_flattenExtRow_odd]

private def flattenExt3Row (row : Array GoldilocksExt3) : Array Goldilocks :=
  (row.toList.flatMap fun e => [e.c0, e.c1, e.c2]).toArray

private lemma ext3RowBytes_eq_rowBytes_flatten (row : Array GoldilocksExt3) :
    Hashers.ext3RowBytes row = Hashers.rowBytes (flattenExt3Row row) := by
  unfold Hashers.ext3RowBytes Hashers.rowBytes flattenExt3Row
  have hfold : ∀ (l : List GoldilocksExt3) (acc : ByteArray),
      l.foldl GoldilocksExt3.pushBytes acc =
        (l.flatMap fun e => [e.c0, e.c1, e.c2]).foldl Goldilocks.pushBytes acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons e es ih =>
      intro acc
      simp [List.foldl_cons, List.flatMap_cons, GoldilocksExt3.pushBytes, ih]
  rw [← Array.foldl_toList, ← Array.foldl_toList, hfold]
  rfl

private lemma flattenExt3Row_size (row : Array GoldilocksExt3) :
    (flattenExt3Row row).size = 3 * row.size := by
  unfold flattenExt3Row
  have h : ∀ l : List GoldilocksExt3, (l.flatMap fun e => [e.c0, e.c1, e.c2]).length = 3 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => simp [List.flatMap_cons, ih]; omega
  simpa using h row.toList

private lemma wordOrZero_flattenExt3Row (row : Array GoldilocksExt3) (k : Nat) :
    Hashers.wordOrZero (flattenExt3Row row) k = Hashers.ext3WordOrZero row k := by
  have hget : ∀ (l : List GoldilocksExt3) (k : Nat),
      (l.flatMap fun e => [e.c0, e.c1, e.c2])[k]?.map (·.val) =
        if k / 3 < l.length then
          some (let e := l[k / 3]?.getD default
                match k % 3 with | 0 => e.c0.val | 1 => e.c1.val | _ => e.c2.val)
        else none := by
    intro l
    induction l with
    | nil => intro k; simp
    | cons e es ih =>
      intro k
      by_cases h3 : k < 3
      · have hq : k / 3 = 0 := by omega
        interval_cases k <;> simp [List.flatMap_cons, hq]
      · have hge : k ≥ 3 := by omega
        have hq : k / 3 = (k - 3) / 3 + 1 := by omega
        have hr : k % 3 = (k - 3) % 3 := by omega
        have hstep : (List.flatMap (fun e => [e.c0, e.c1, e.c2]) (e :: es))[k]? =
            (List.flatMap (fun e => [e.c0, e.c1, e.c2]) es)[k - 3]? := by
          simp only [List.flatMap_cons, List.cons_append, List.nil_append]
          cases k with
          | zero => omega
          | succ k1 =>
            cases k1 with
            | zero => omega
            | succ k2 =>
              cases k2 with
              | zero => omega
              | succ k3 => rfl
        rw [hstep, ih (k - 3)]
        simp only [hq, hr, List.length_cons, Nat.add_lt_add_iff_right, List.getElem?_cons_succ]
  unfold Hashers.wordOrZero Hashers.ext3WordOrZero
  by_cases hk : k < (flattenExt3Row row).size
  · have hq_lt : k / 3 < row.size := by rw [flattenExt3Row_size] at hk; omega
    simp only [hk, ↓reduceDIte]
    have hspec := hget row.toList k
    have hlt : k / 3 < row.toList.length := by simpa using hq_lt
    simp only [hlt, ↓reduceIte] at hspec
    have hflat_lt : k < (row.toList.flatMap fun e => [e.c0, e.c1, e.c2]).length := by
      simpa [flattenExt3Row] using hk
    have helem : (row.toList.flatMap fun e => [e.c0, e.c1, e.c2])[k]? =
        some (flattenExt3Row row)[k] := by
      rw [List.getElem?_eq_getElem hflat_lt]; rfl
    rw [helem] at hspec
    have hval := Option.some.inj hspec
    dsimp only at hval
    simp only [Array.getElem?_eq_getElem hq_lt, Option.getD_some]
    refine hval.trans ?_
    have hm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hm with h0 | h1 | h2
    · simp [h0, List.getElem?_eq_getElem hlt]
    · simp [h1, List.getElem?_eq_getElem hlt]
    · simp [h2, List.getElem?_eq_getElem hlt]
  · have hq_ge : row.size ≤ k / 3 := by rw [flattenExt3Row_size] at hk; omega
    simp only [hk, ↓reduceDIte, Array.getElem?_eq_none hq_ge, Option.getD_none]
    have hm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hm with h0 | h1 | h2
    · simp [h0]; rfl
    · simp [h1]; rfl
    · simp [h2]; rfl

/-- `ext3Hasher.hashRows row` equals `Blake3.Pure.digest` of `Hashers.ext3RowBytes row`. -/
theorem ext3Hasher_hashRows_eq_pure (row : Array GoldilocksExt3) :
    (CertiFri.P3.ext3Hasher.hashRows row).toBytes =
      ByteArray.mk (Blake3.Pure.digest (Hashers.ext3RowBytes row).data.toList).toArray := by
  rw [ext3RowBytes_eq_rowBytes_flatten, ← baseHasher_hashRows_eq_pure]
  unfold CertiFri.P3.ext3Hasher CertiFri.P3.baseHasher
  dsimp only
  rw [flattenExt3Row_size, show 8 * (3 * row.size) = 24 * row.size by omega]
  congr 1
  apply hashBlocks_congr
  intro i _
  unfold Hashers.ext3RowBlock Hashers.rowBlock
  dsimp only
  simp only [wordOrZero_flattenExt3Row]

end Ix.Cert.MultiStark
