import IxVMRefinement.L1.Stream

/-! # BLAKE3's block loop and byte loop at source level

* 64-bit chunk counters: `UInt64::is_zero`, `UInt64::wrapping_succ` (through the byte model
  `U64.wrappingSuccBytes` and its soundness).
* `Blake3::finish` (no generated path lemmas: its scrutinee is a pair of fields matched against
  literal pairs), inverted here against its elaborated body (`finish_body`).
* `Blake3::compress_chunks` on the bytes after the last full block (fewer than 64; the only way
  `Blake3::hash` reaches it), and `Blake3::hash_blocks`, against `Aiur.Library.Blake3.finish`,
  `compressChunks` and `hashBlocks`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

namespace IxVM.Refinement.L1

open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Refinement (byteStreamEnum)
open Aiur.Library.Blake3 (wordOfBytes wordOfBytes_toNat)

/-! ## 64-bit counters -/

theorem u64v_eq (c : UInt64) : (u64v c : SourceValue F) =
    .tuple [bv (u64b c 0), bv (u64b c 1), bv (u64b c 2), bv (u64b c 3), bv (u64b c 4),
      bv (u64b c 5), bv (u64b c 6), bv (u64b c 7)] := rfl

theorem u64b_0 (c : UInt64) : (u64b c 0).toNat = c.toNat % 256 := by simp [u64b_toNat]
theorem u64b_1 (c : UInt64) : (u64b c 1).toNat = c.toNat / 256 % 256 := by simp [u64b_toNat]
theorem u64b_2 (c : UInt64) : (u64b c 2).toNat = c.toNat / 65536 % 256 := by simp [u64b_toNat]
theorem u64b_3 (c : UInt64) : (u64b c 3).toNat = c.toNat / 16777216 % 256 := by simp [u64b_toNat]
theorem u64b_4 (c : UInt64) : (u64b c 4).toNat = c.toNat / 4294967296 % 256 := by
  simp [u64b_toNat]
theorem u64b_5 (c : UInt64) : (u64b c 5).toNat = c.toNat / 1099511627776 % 256 := by
  simp [u64b_toNat]
theorem u64b_6 (c : UInt64) : (u64b c 6).toNat = c.toNat / 281474976710656 % 256 := by
  simp [u64b_toNat]
theorem u64b_7 (c : UInt64) : (u64b c 7).toNat = c.toNat / 72057594037927936 % 256 := by
  simp [u64b_toNat]

theorem toNat_lt64 (c : UInt64) : c.toNat < 18446744073709551616 := by
  have := c.toNat_lt
  simpa using this

theorem pack_digits (n : Nat) (hn : n < 18446744073709551616) :
    Aiur.Library.U64.pack (n % 256) (n / 256 % 256) (n / 65536 % 256) (n / 16777216 % 256)
      (n / 4294967296 % 256) (n / 1099511627776 % 256) (n / 281474976710656 % 256)
      (n / 72057594037927936 % 256) = n := by
  unfold Aiur.Library.U64.pack
  first
  | omega
  | (have q1 : n / 256 / 256 = n / 65536 := by rw [Nat.div_div_eq_div_mul]
     have q2 : n / 65536 / 256 = n / 16777216 := by rw [Nat.div_div_eq_div_mul]
     have q3 : n / 16777216 / 256 = n / 4294967296 := by rw [Nat.div_div_eq_div_mul]
     have q4 : n / 4294967296 / 256 = n / 1099511627776 := by rw [Nat.div_div_eq_div_mul]
     have q5 : n / 1099511627776 / 256 = n / 281474976710656 := by rw [Nat.div_div_eq_div_mul]
     have q6 : n / 281474976710656 / 256 = n / 72057594037927936 := by rw [Nat.div_div_eq_div_mul]
     have e0 := Nat.div_add_mod n 256
     have e1 := Nat.div_add_mod (n / 256) 256
     have e2 := Nat.div_add_mod (n / 65536) 256
     have e3 := Nat.div_add_mod (n / 16777216) 256
     have e4 := Nat.div_add_mod (n / 4294967296) 256
     have e5 := Nat.div_add_mod (n / 1099511627776) 256
     have e6 := Nat.div_add_mod (n / 281474976710656) 256
     have e7 : n / 72057594037927936 < 256 := by omega
     omega)

theorem u64_pack (c : UInt64) :
    Aiur.Library.U64.pack (u64b c 0).toNat (u64b c 1).toNat (u64b c 2).toNat (u64b c 3).toNat
      (u64b c 4).toNat (u64b c 5).toNat (u64b c 6).toNat (u64b c 7).toNat = c.toNat := by
  rw [u64b_0, u64b_1, u64b_2, u64b_3, u64b_4, u64b_5, u64b_6, u64b_7]
  exact pack_digits _ (toNat_lt64 c)

theorem u64v_zero : (u64v 0 : SourceValue F) = .tuple (List.replicate 8 (.field 0)) := by
  rw [u64v_eq]
  first
  | (simp [u64b, bv]; done)
  | (simp [u64b_toNat, bv]; done)
  | rfl

theorem byte_zero_of {b : UInt8} (h : bv b = (.field 0 : SourceValue F)) : b.toNat = 0 :=
  natCast_byte_inj (byte_lt b) (by norm_num) (by simpa using Value.field.inj h)

theorem digit255 {b : UInt8} (h : (.field 255 : SourceValue F) = bv b) : b.toNat = 255 :=
  (natCast_byte_inj (by norm_num) (byte_lt b) (by simpa using Value.field.inj h)).symm

theorem digit_ne255 {b : UInt8} (h : bv b ≠ (.field 255 : SourceValue F)) : b.toNat ≠ 255 := by
  intro e
  apply h
  simp [bv, e]

/-- **`UInt64::is_zero`** tests the counter against 0. -/
theorem u64_isZero {c : UInt64} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt64::is_zero" [u64v c] h r h' cs) :
    r = .field (if c = 0 then 1 else 0) ∧ h' = h := by
  rcases «UInt64::is_zero».obs ev with ⟨hv, rfl, rfl, -⟩ | ⟨hne, rfl, rfl, -⟩
  · have hc : c = 0 := by
      rw [u64v_eq] at hv
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv
      obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := hv
      have d0 := byte_zero_of e0
      have d1 := byte_zero_of e1
      have d2 := byte_zero_of e2
      have d3 := byte_zero_of e3
      have d4 := byte_zero_of e4
      have d5 := byte_zero_of e5
      have d6 := byte_zero_of e6
      have d7 := byte_zero_of e7
      have hp := u64_pack c
      rw [d0, d1, d2, d3, d4, d5, d6, d7] at hp
      apply UInt64.toNat_inj.mp
      rw [← hp]
      rfl
    subst hc
    exact ⟨by simp, rfl⟩
  · have hc : c ≠ 0 := by
      rintro rfl
      exact hne (u64v_zero.trans rfl)
    exact ⟨by simp [hc], rfl⟩

/-- The counter after `wrapping_succ`, from the bytes the byte model computes. -/
theorem u64v_succ (c : UInt64) {r0 r1 r2 r3 r4 r5 r6 r7 : Nat}
    (hr : Aiur.Library.U64.wrappingSuccBytes (u64b c 0).toNat (u64b c 1).toNat (u64b c 2).toNat
      (u64b c 3).toNat (u64b c 4).toNat (u64b c 5).toNat (u64b c 6).toNat (u64b c 7).toNat =
      (r0, r1, r2, r3, r4, r5, r6, r7)) :
    (u64v (c + 1) : SourceValue F) = .tuple [.field (r0 : F), .field (r1 : F), .field (r2 : F),
      .field (r3 : F), .field (r4 : F), .field (r5 : F), .field (r6 : F), .field (r7 : F)] := by
  have sound := Aiur.Library.U64.wrapping_succ_sound (byte_lt (u64b c 0)) (byte_lt (u64b c 1))
    (byte_lt (u64b c 2)) (byte_lt (u64b c 3)) (byte_lt (u64b c 4)) (byte_lt (u64b c 5))
    (byte_lt (u64b c 6)) (byte_lt (u64b c 7))
  rw [hr] at sound
  simp only at sound
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hp⟩ := sound
  rw [u64_pack] at hp
  have hs : (c + 1).toNat = Aiur.Library.U64.pack r0 r1 r2 r3 r4 r5 r6 r7 := by
    rw [hp]
    simp [UInt64.toNat_add, Aiur.Library.U64.base]
  have d0 : (u64b (c + 1) 0).toNat = r0 := by
    rw [u64b_0, hs]; unfold Aiur.Library.U64.pack; omega
  have d1 : (u64b (c + 1) 1).toNat = r1 := by
    rw [u64b_1, hs]; unfold Aiur.Library.U64.pack; omega
  have d2 : (u64b (c + 1) 2).toNat = r2 := by
    rw [u64b_2, hs]; unfold Aiur.Library.U64.pack; omega
  have d3 : (u64b (c + 1) 3).toNat = r3 := by
    rw [u64b_3, hs]; unfold Aiur.Library.U64.pack; omega
  have d4 : (u64b (c + 1) 4).toNat = r4 := by
    rw [u64b_4, hs]; unfold Aiur.Library.U64.pack; omega
  have d5 : (u64b (c + 1) 5).toNat = r5 := by
    rw [u64b_5, hs]; unfold Aiur.Library.U64.pack; omega
  have d6 : (u64b (c + 1) 6).toNat = r6 := by
    rw [u64b_6, hs]; unfold Aiur.Library.U64.pack; omega
  have d7 : (u64b (c + 1) 7).toNat = r7 := by
    rw [u64b_7, hs]; unfold Aiur.Library.U64.pack; omega
  rw [u64v_eq]
  simp only [bv, d0, d1, d2, d3, d4, d5, d6, d7]

/-- **`UInt64::wrapping_succ`** adds one, modulo `2^64`. -/
theorem u64_wrappingSucc {c : UInt64} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt64::wrapping_succ" [u64v c] h r h' cs) : r = u64v (c + 1) ∧ h' = h := by
  rcases «UInt64::wrapping_succ».obs ev with
    ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, m54, cs65, m81, cs92, m108, cs119, m135, cs146, m162, cs173, m189, cs200, m216, cs227, m243, cs254, hv11, ev67, ev94, ev121, ev148, ev175, ev202, ev229, ev256, he279, he328, hc329⟩ |
    ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, m54, cs65, m81, cs92, m108, cs119, m135, cs146, m162, cs173, m189, cs200, m216, cs227, v242, m243, cs254, v343, m388, cs396, v399, x406, m408, cs417, hv11, ev67, ev94, ev121, ev148, ev175, ev202, ev229, ev256, hne330, he344, ev419, op413, ev398, he428, hc429⟩ |
    ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, m54, cs65, m81, cs92, m108, cs119, m135, cs146, m162, cs173, m189, cs200, v215, m216, cs227, v442, m482, cs490, v493, x500, m502, cs511, hv11, ev67, ev94, ev121, ev148, ev175, ev202, ev229, hne430, he444, ev513, op507, ev492, he529, hc530⟩ |
    ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, m54, cs65, m81, cs92, m108, cs119, m135, cs146, m162, cs173, v188, m189, cs200, v542, m577, cs585, v588, x595, m597, cs606, hv11, ev67, ev94, ev121, ev148, ev175, ev202, hne531, he545, ev608, op602, ev587, he631, hc632⟩ |
    ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, m54, cs65, m81, cs92, m108, cs119, m135, cs146, v161, m162, cs173, v643, m673, cs681, v684, x691, m693, cs702, hv11, ev67, ev94, ev121, ev148, ev175, hne633, he647, ev704, op698, ev683, he734, hc735⟩ |
    ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, m54, cs65, m81, cs92, m108, cs119, v134, m135, cs146, v745, m770, cs778, v781, x788, m790, cs799, hv11, ev67, ev94, ev121, ev148, hne736, he750, ev801, op795, ev780, he838, hc839⟩ |
    ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, m54, cs65, m81, cs92, v107, m108, cs119, v848, m868, cs876, v879, x886, m888, cs897, hv11, ev67, ev94, ev121, hne840, he854, ev899, op893, ev878, he943, hc944⟩ |
    ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, m54, cs65, v80, m81, cs92, v952, m967, cs975, v978, x985, m987, cs996, hv11, ev67, ev94, hne945, he959, ev998, op992, ev977, he1049, hc1050⟩ |
    ⟨x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, v53, m54, cs65, v1057, m1067, cs1075, v1078, x1085, m1087, cs1096, hv11, ev67, hne1051, he1065, ev1098, op1092, ev1077, he1156, hc1157⟩
  · -- n255_n255_n255_n255_n255_n255_n255_n255
    rw [u64v_eq] at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
    obtain ⟨e0, rfl⟩ := u8_toField ev67
    obtain ⟨e1, rfl⟩ := u8_toField ev94
    obtain ⟨e2, rfl⟩ := u8_toField ev121
    obtain ⟨e3, rfl⟩ := u8_toField ev148
    obtain ⟨e4, rfl⟩ := u8_toField ev175
    obtain ⟨e5, rfl⟩ := u8_toField ev202
    obtain ⟨e6, rfl⟩ := u8_toField ev229
    obtain ⟨e7, rfl⟩ := u8_toField ev256
    subst he279 he328
    refine ⟨?_, rfl⟩
    rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0) (r3 := 0) (r4 := 0) (r5 := 0) (r6 := 0) (r7 := 0) (by simp [Aiur.Library.U64.wrappingSuccBytes, digit255 e0, digit255 e1, digit255 e2, digit255 e3, digit255 e4, digit255 e5, digit255 e6, digit255 e7])]
    simp
  · -- n255_n255_n255_n255_n255_n255_n255_other
    rw [u64v_eq] at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
    obtain ⟨e0, rfl⟩ := u8_toField ev67
    obtain ⟨e1, rfl⟩ := u8_toField ev94
    obtain ⟨e2, rfl⟩ := u8_toField ev121
    obtain ⟨e3, rfl⟩ := u8_toField ev148
    obtain ⟨e4, rfl⟩ := u8_toField ev175
    obtain ⟨e5, rfl⟩ := u8_toField ev202
    obtain ⟨e6, rfl⟩ := u8_toField ev229
    obtain ⟨rfl, rfl⟩ := u8_toField ev256
    obtain ⟨rfl, rfl⟩ := u8_toField ev419
    obtain rfl := binop_add op413
    obtain ⟨bb, e7, rfl, rfl⟩ := u8_fromField ev398
    subst he344 he428
    refine ⟨?_, rfl⟩
    rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0) (r3 := 0) (r4 := 0) (r5 := 0) (r6 := 0) (r7 := (u64b c 7).toNat + 1) (by simp [Aiur.Library.U64.wrappingSuccBytes, digit255 e0, digit255 e1, digit255 e2, digit255 e3, digit255 e4, digit255 e5, digit255 e6, digit_ne255 hne330]), ← e7]
    simp [bv]
  · -- n255_n255_n255_n255_n255_n255_other
    rw [u64v_eq] at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
    obtain ⟨e0, rfl⟩ := u8_toField ev67
    obtain ⟨e1, rfl⟩ := u8_toField ev94
    obtain ⟨e2, rfl⟩ := u8_toField ev121
    obtain ⟨e3, rfl⟩ := u8_toField ev148
    obtain ⟨e4, rfl⟩ := u8_toField ev175
    obtain ⟨e5, rfl⟩ := u8_toField ev202
    obtain ⟨rfl, rfl⟩ := u8_toField ev229
    obtain ⟨rfl, rfl⟩ := u8_toField ev513
    obtain rfl := binop_add op507
    obtain ⟨bb, e6, rfl, rfl⟩ := u8_fromField ev492
    subst he444 he529
    refine ⟨?_, rfl⟩
    rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0) (r3 := 0) (r4 := 0) (r5 := 0) (r6 := (u64b c 6).toNat + 1) (r7 := (u64b c 7).toNat) (by simp [Aiur.Library.U64.wrappingSuccBytes, digit255 e0, digit255 e1, digit255 e2, digit255 e3, digit255 e4, digit255 e5, digit_ne255 hne430]), ← e6]
    simp [bv]
  · -- n255_n255_n255_n255_n255_other
    rw [u64v_eq] at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
    obtain ⟨e0, rfl⟩ := u8_toField ev67
    obtain ⟨e1, rfl⟩ := u8_toField ev94
    obtain ⟨e2, rfl⟩ := u8_toField ev121
    obtain ⟨e3, rfl⟩ := u8_toField ev148
    obtain ⟨e4, rfl⟩ := u8_toField ev175
    obtain ⟨rfl, rfl⟩ := u8_toField ev202
    obtain ⟨rfl, rfl⟩ := u8_toField ev608
    obtain rfl := binop_add op602
    obtain ⟨bb, e5, rfl, rfl⟩ := u8_fromField ev587
    subst he545 he631
    refine ⟨?_, rfl⟩
    rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0) (r3 := 0) (r4 := 0) (r5 := (u64b c 5).toNat + 1) (r6 := (u64b c 6).toNat) (r7 := (u64b c 7).toNat) (by simp [Aiur.Library.U64.wrappingSuccBytes, digit255 e0, digit255 e1, digit255 e2, digit255 e3, digit255 e4, digit_ne255 hne531]), ← e5]
    simp [bv]
  · -- n255_n255_n255_n255_other
    rw [u64v_eq] at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
    obtain ⟨e0, rfl⟩ := u8_toField ev67
    obtain ⟨e1, rfl⟩ := u8_toField ev94
    obtain ⟨e2, rfl⟩ := u8_toField ev121
    obtain ⟨e3, rfl⟩ := u8_toField ev148
    obtain ⟨rfl, rfl⟩ := u8_toField ev175
    obtain ⟨rfl, rfl⟩ := u8_toField ev704
    obtain rfl := binop_add op698
    obtain ⟨bb, e4, rfl, rfl⟩ := u8_fromField ev683
    subst he647 he734
    refine ⟨?_, rfl⟩
    rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0) (r3 := 0) (r4 := (u64b c 4).toNat + 1) (r5 := (u64b c 5).toNat) (r6 := (u64b c 6).toNat) (r7 := (u64b c 7).toNat) (by simp [Aiur.Library.U64.wrappingSuccBytes, digit255 e0, digit255 e1, digit255 e2, digit255 e3, digit_ne255 hne633]), ← e4]
    simp [bv]
  · -- n255_n255_n255_other
    rw [u64v_eq] at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
    obtain ⟨e0, rfl⟩ := u8_toField ev67
    obtain ⟨e1, rfl⟩ := u8_toField ev94
    obtain ⟨e2, rfl⟩ := u8_toField ev121
    obtain ⟨rfl, rfl⟩ := u8_toField ev148
    obtain ⟨rfl, rfl⟩ := u8_toField ev801
    obtain rfl := binop_add op795
    obtain ⟨bb, e3, rfl, rfl⟩ := u8_fromField ev780
    subst he750 he838
    refine ⟨?_, rfl⟩
    rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := 0) (r3 := (u64b c 3).toNat + 1) (r4 := (u64b c 4).toNat) (r5 := (u64b c 5).toNat) (r6 := (u64b c 6).toNat) (r7 := (u64b c 7).toNat) (by simp [Aiur.Library.U64.wrappingSuccBytes, digit255 e0, digit255 e1, digit255 e2, digit_ne255 hne736]), ← e3]
    simp [bv]
  · -- n255_n255_other
    rw [u64v_eq] at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
    obtain ⟨e0, rfl⟩ := u8_toField ev67
    obtain ⟨e1, rfl⟩ := u8_toField ev94
    obtain ⟨rfl, rfl⟩ := u8_toField ev121
    obtain ⟨rfl, rfl⟩ := u8_toField ev899
    obtain rfl := binop_add op893
    obtain ⟨bb, e2, rfl, rfl⟩ := u8_fromField ev878
    subst he854 he943
    refine ⟨?_, rfl⟩
    rw [u64v_succ c (r0 := 0) (r1 := 0) (r2 := (u64b c 2).toNat + 1) (r3 := (u64b c 3).toNat) (r4 := (u64b c 4).toNat) (r5 := (u64b c 5).toNat) (r6 := (u64b c 6).toNat) (r7 := (u64b c 7).toNat) (by simp [Aiur.Library.U64.wrappingSuccBytes, digit255 e0, digit255 e1, digit_ne255 hne840]), ← e2]
    simp [bv]
  · -- n255_other
    rw [u64v_eq] at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
    obtain ⟨e0, rfl⟩ := u8_toField ev67
    obtain ⟨rfl, rfl⟩ := u8_toField ev94
    obtain ⟨rfl, rfl⟩ := u8_toField ev998
    obtain rfl := binop_add op992
    obtain ⟨bb, e1, rfl, rfl⟩ := u8_fromField ev977
    subst he959 he1049
    refine ⟨?_, rfl⟩
    rw [u64v_succ c (r0 := 0) (r1 := (u64b c 1).toNat + 1) (r2 := (u64b c 2).toNat) (r3 := (u64b c 3).toNat) (r4 := (u64b c 4).toNat) (r5 := (u64b c 5).toNat) (r6 := (u64b c 6).toNat) (r7 := (u64b c 7).toNat) (by simp [Aiur.Library.U64.wrappingSuccBytes, digit255 e0, digit_ne255 hne945]), ← e1]
    simp [bv]
  · -- other
    rw [u64v_eq] at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hv11
    obtain ⟨rfl, rfl⟩ := u8_toField ev67
    obtain ⟨rfl, rfl⟩ := u8_toField ev1098
    obtain rfl := binop_add op1092
    obtain ⟨bb, e0, rfl, rfl⟩ := u8_fromField ev1077
    subst he1065 he1156
    refine ⟨?_, rfl⟩
    rw [u64v_succ c (r0 := (u64b c 0).toNat + 1) (r1 := (u64b c 1).toNat) (r2 := (u64b c 2).toNat) (r3 := (u64b c 3).toNat) (r4 := (u64b c 4).toNat) (r5 := (u64b c 5).toNat) (r6 := (u64b c 6).toNat) (r7 := (u64b c 7).toNat) (by simp [Aiur.Library.U64.wrappingSuccBytes, digit_ne255 hne1051]), ← e0]
    simp [bv]

/-! ## Expression-level helpers -/

theorem ObsExpr.global_inv' {types : List (String × Aiur.Generic.Ty)} {locals : Environment F Nat}
    {name : String} {t : Aiur.Generic.Ty} {before after : Heap F} {r : SourceValue F}
    {calls : List (Call F)}
    (h : ObsExpr W types locals (.global name (some t)) before r after calls) :
    ∃ pattern body, W.constant name (t.subst types) = .ok pattern ∧
      Consts.toExpr pattern = .ok body ∧ ObsExpr W [] [] body before r after calls := by
  cases h with | global lookup interpreted value => exact ⟨_, _, lookup, interpreted, value⟩

/-- `UInt32::ZERO`'s pattern, as a Boolean test. -/
def isZeroWord (e : Except EvalError (Aiur.Generic.Pattern F)) : Bool :=
  match e with
  | .ok (.repeat (.global "UInt8::BYTE_0" (some .field)) 4) => true
  | _ => false

theorem eq_of_isZeroWord {e : Except EvalError (Aiur.Generic.Pattern F)} (h : isZeroWord e = true) :
    e = .ok (.repeat (.global "UInt8::BYTE_0" (some .field)) 4) := by
  unfold isZeroWord at h
  split at h
  · rfl
  · cases h

theorem zero_word_const :
    W.constant "UInt32::ZERO" (Aiur.Generic.Ty.subst [] (.array .field 4)) =
      .ok (.repeat (.global "UInt8::BYTE_0" (some .field)) 4) :=
  eq_of_isZeroWord (by decide +kernel)

theorem zero_word_expr :
    Consts.toExpr (.repeat (.global "UInt8::BYTE_0" (some .field)) 4 : Aiur.Generic.Pattern F) =
      .ok (.repeat (.global "UInt8::BYTE_0" (some .field)) 4) := by
  first
  | rfl
  | (rw [Consts.toExpr, Consts.toExpr]; rfl)
  | (simp [Consts.toExpr]; done)

/-- **`[UInt32::ZERO; 16]`** is sixteen zero words. -/
theorem zero_block_inv {locals : Environment F Nat}
    {before after : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (h : ObsExpr W [] locals (.repeat (.global "UInt32::ZERO" (some (.array .field 4))) 16)
      before r after calls) :
    r = vecV (Vector.replicate 16 (0 : UInt32)) ∧ after = before := by
  obtain ⟨inp, dg, rfl⟩ := h.repeat_inv
  obtain ⟨pat, body, hc, he, db⟩ := ObsExpr.global_inv' dg
  rw [zero_word_const] at hc
  cases hc
  rw [zero_word_expr] at he
  cases he
  obtain ⟨w, dw, rfl⟩ := db.repeat_inv
  obtain ⟨rfl, rfl, rfl⟩ := dw.global_literal_inv Names.c9173999864893739538
  refine ⟨?_, rfl⟩
  rfl

theorem zero_word_wv : (wv (0 : UInt32) : SourceValue F) = .tuple (List.replicate 4 (.field 0)) := by
  first
  | rfl
  | (simp [wv, w4, bv, Blake3.Pure.wordBytes]; done)
  | (simp [wv, w4, bv, Blake3.Pure.wordBytes, List.replicate]; done)

/-! ## `Blake3::finish` -/

def finishArm1 : Aiur.Generic.Expr F :=
  .matchValue (.load (.var "chunk_count"))
    [(.array (List.replicate 8 (.global "UInt8::BYTE_0" (some .field))),
        .letValue (.bind "flags")
          (.binary .add (.binary .add (.var "ROOT") (.var "CHUNK_START")) (.var "CHUNK_END"))
          (.store (.construct "Blake3::LayerNode" (some []) "Push"
            [.var "layer", .call "Blake3::compress_init" (some [])
              [.load (.var "block_digest"), .repeat (.global "UInt32::ZERO" (some (.array .field 4))) 16,
                .load (.var "chunk_count"), .literal 0, .var "flags"]]))),
      (.wildcard, .var "layer")]

def finishArm2 : Aiur.Generic.Expr F :=
  .store (.construct "Blake3::LayerNode" (some []) "Push" [.var "layer", .load (.var "block_digest")])

def finishArm3 : Aiur.Generic.Expr F :=
  .letValue (.bind "flags")
    (.binary .add
      (.binary .add (.var "CHUNK_END")
        (.binary .mul (.call "UInt64::is_zero" (some []) [.load (.var "chunk_count")]) (.var "ROOT")))
      (.binary .mul
        (.call "Fields::is_zero" (some []) [.binary .sub (.var "chunk_index") (.var "block_index")])
        (.var "CHUNK_START")))
    (.letValue (.bind "block")
      (.call "Blake3::bytes_to_block" (some [])
        [.call "Blake3::pad_block" (some [])
          [.var "byte_acc", .binary .sub (.literal 64) (.var "block_index")]])
      (.store (.construct "Blake3::LayerNode" (some []) "Push"
        [.var "layer", .call "Blake3::compress_init" (some [])
          [.load (.var "block_digest"), .var "block", .load (.var "chunk_count"), .var "block_index",
            .var "flags"]])))

def finishExpr : Aiur.Generic.Expr F :=
  .letValue (.bind "CHUNK_START") (.literal 1)
    (.letValue (.bind "CHUNK_END") (.literal 2)
      (.letValue (.bind "ROOT") (.literal 8)
        (.matchValue (.tuple [.var "block_index", .var "chunk_index"])
          [(.tuple [.literal 0, .literal 0], finishArm1),
            (.tuple [.literal 0, .wildcard], finishArm2),
            (.tuple [.wildcard, .wildcard], finishArm3)])))

theorem finish_body : IxVM.Blake3.finish.body = finishExpr := rfl

theorem m_ll_00 (h : Heap F) :
    W.matchPattern [] h (.tuple [.literal 0, .literal 0]) (.tuple [.field 0, .field 0]) =
      .ok (some []) := by
  rw [matchPattern_tuple]
  simp [matchListWith, matchPattern_literal, bind, Except.bind, pure, Except.pure]

theorem m_ll_x (h : Heap F) {x : F} (y : F) (hx : (0 : F) ≠ x) :
    W.matchPattern [] h (.tuple [.literal 0, .literal 0]) (.tuple [.field x, .field y]) =
      .ok none := by
  rw [matchPattern_tuple]
  simp [matchListWith, matchPattern_literal, hx, bind, Except.bind, pure, Except.pure]

theorem m_ll_0y (h : Heap F) {y : F} (hy : (0 : F) ≠ y) :
    W.matchPattern [] h (.tuple [.literal 0, .literal 0]) (.tuple [.field 0, .field y]) =
      .ok none := by
  rw [matchPattern_tuple]
  simp [matchListWith, matchPattern_literal, hy, bind, Except.bind, pure, Except.pure]

theorem m_lw_0 (h : Heap F) (y : F) :
    W.matchPattern [] h (.tuple [.literal 0, .wildcard]) (.tuple [.field 0, .field y]) =
      .ok (some []) := by
  rw [matchPattern_tuple]
  simp [matchListWith, matchPattern_literal, matchPattern_wildcard, bind, Except.bind, pure,
    Except.pure]

theorem m_lw_x (h : Heap F) {x : F} (y : F) (hx : (0 : F) ≠ x) :
    W.matchPattern [] h (.tuple [.literal 0, .wildcard]) (.tuple [.field x, .field y]) =
      .ok none := by
  rw [matchPattern_tuple]
  simp [matchListWith, matchPattern_literal, hx, bind, Except.bind, pure, Except.pure]

theorem m_ww (h : Heap F) (u v : SourceValue F) :
    W.matchPattern [] h (.tuple [.wildcard, .wildcard]) (.tuple [u, v]) = .ok (some []) := by
  rw [matchPattern_tuple]
  simp [matchListWith, matchPattern_wildcard, bind, Except.bind, pure, Except.pure]

theorem zeros_matches :
    MatchesConst W [] (.array (List.replicate 8 (.global "UInt8::BYTE_0" (some .field))))
      (.tuple (List.replicate 8 (.field 0)) : SourceValue F) := by
  have g : MatchesConst W [] (.global "UInt8::BYTE_0" (some .field)) (.field (0 : F)) :=
    MatchesConst.global (s := IxVM.source) Names.c9173999864893739538
  exact MatchesConst.array (.cons g (.cons g (.cons g (.cons g (.cons g (.cons g (.cons g
    (.cons g .nil))))))))

theorem flags_nat (s e r : Bool) :
    (Aiur.Library.Blake3.blockFlags s e r).toNat =
      (if s then 1 else 0) + 2 * (if e then 1 else 0) + 8 * (if r then 1 else 0) := by
  cases s <;> cases e <;> cases r <;> decide

/-- The flags as a field element: `CHUNK_START * start + CHUNK_END * end + ROOT * root`. -/
theorem flags_general (s e r : Bool) :
    ((Aiur.Library.Blake3.blockFlags s e r).toNat : F) =
      (if s then 1 else 0) + 2 * (if e then 1 else 0) + 8 * (if r then 1 else 0) := by
  rw [flags_nat]
  cases s <;> cases e <;> cases r <;> norm_num

theorem flags_field (s r : Bool) :
    ((Aiur.Library.Blake3.blockFlags s true r).toNat : F) =
      (2 : F) + (if r then 1 else 0) * 8 + (if s then 1 else 0) * 1 := by
  rw [flags_general]
  cases s <;> cases r <;> norm_num

theorem toUInt32_toNat (x : UInt32) : Nat.toUInt32 x.toNat = x := UInt32.ofNat_toNat

theorem flags_lt (s e r : Bool) : (Aiur.Library.Blake3.blockFlags s e r).toNat < 256 := by
  cases s <;> cases e <;> cases r <;> decide

theorem natCast_ne_zero {k : Nat} (hk : k < 1024) (h0 : k ≠ 0) : (0 : F) ≠ (k : F) := by
  intro e
  apply h0
  exact (IxVM.natCast_inj hk (by omega) (by simpa using e.symm))

theorem padded_block (acc : List UInt8) (k : Nat) (hacc : acc.length = k) (hk : k ≤ 64) :
    Blake3.Pure.blockWords ((List.replicate (64 - k) 0 ++ acc).take 64).reverse =
      Blake3.Pure.blockWords acc.reverse := by
  have hlen : (List.replicate (64 - k) (0 : UInt8) ++ acc).length = 64 := by simp; omega
  rw [List.take_of_length_le (by omega), List.reverse_append, List.reverse_replicate]
  have := Aiur.Library.Blake3.bytes_to_block_spec acc.reverse (by simp; omega)
  rw [List.length_reverse, hacc] at this
  exact this

/-- **`Blake3::finish`**: the end of the byte loop, against the model's `finish`. `byte_acc`
holds the last block's `k` bytes, last first; `chunk_index` counts the chunk's bytes. -/
theorem finish_spec {acc : List UInt8} {k j : Nat} {c : UInt64} {cv : Blake3.Pure.CV}
    {layer : List Blake3.Pure.CV} {accp ccp cvp lp r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hk : k ≤ 63) (hj : j < 1024) (hkj : k ≤ j) (hacc : acc.length = k)
    (hs : Stream h acc accp) (hcc : loadValue h ccp = .ok (u64v c))
    (hcv : loadValue h cvp = .ok (vecV cv)) (hl : Stack h layer.reverse lp)
    (ev : ObsFn W "Blake3::finish" [accp, .field (k : F), .field (j : F), ccp, cvp, lp] h r h' cs) :
    Heap.Extends h h' ∧ Stack h' (Aiur.Library.Blake3.finish acc k j c cv layer).reverse r := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.Blake3.finish.lookup
    (by first | rfl | decide | simp [IxVM.Blake3.finish, ControlLower.hasControl]) ev
  rw [finish_body] at d0
  obtain ⟨v1, m1, bs1, c1, c2, dl1, mt1, d1, rfl⟩ := d0.letValue_inv
  obtain ⟨rfl, rfl, rfl⟩ := dl1.literal_inv
  rw [matchPattern_bind] at mt1
  cases mt1
  obtain ⟨v2, m2, bs2, c3, c4, dl2, mt2, d2, rfl⟩ := d1.letValue_inv
  obtain ⟨rfl, rfl, rfl⟩ := dl2.literal_inv
  rw [matchPattern_bind] at mt2
  cases mt2
  obtain ⟨v3, m3, bs3, c5, c6, dl3, mt3, d3, rfl⟩ := d2.letValue_inv
  obtain ⟨rfl, rfl, rfl⟩ := dl3.literal_inv
  rw [matchPattern_bind] at mt3
  cases mt3
  obtain ⟨sv, m4, bs4, body, c7, c8, dsc, sel, db, rfl⟩ := d3.matchValue_inv
  obtain ⟨vs, asc, rfl⟩ := dsc.tuple_inv
  obtain ⟨u1, us1, n1, e1, f1, rfl, du1, au1, rfl⟩ := asc.cons_inv
  obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) du1
  obtain ⟨u2, us2, n2, e2, f2, rfl, du2, au2, rfl⟩ := au1.cons_inv
  obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) du2
  obtain ⟨rfl, rfl, rfl⟩ := au2.nil_inv
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.cast_zero] at sel
    by_cases hj0 : j = 0
    · subst hj0
      simp only [Nat.cast_zero] at sel
      rcases selectArm_cons_inv sel with ⟨mt, rfl⟩ | ⟨nm, -⟩
      · rw [m_ll_00] at mt
        cases mt
        -- the first arm: the counter decides
        simp only [finishArm1] at db
        obtain ⟨cv0, m5, bs5, body5, c9, c10, dcc, sel5, db5, rfl⟩ := db.matchValue_inv
        obtain ⟨pc, dpc, ldc⟩ := dcc.load_inv
        obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dpc
        obtain rfl := ok_inj (hcc.symm.trans ldc)
        rcases selectArm_const_inv sel5 zeros_matches with ⟨hz, rfl, rfl⟩ | ⟨hnz, sel6⟩
        · -- a zero counter: the empty input's root block
          have hc0 : c = 0 := by
            rw [u64v_eq] at hz
            simp only [List.replicate, Value.tuple.injEq, List.cons.injEq, and_true] at hz
            obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := hz
            have hp := u64_pack c
            rw [byte_zero_of e0, byte_zero_of e1, byte_zero_of e2, byte_zero_of e3,
              byte_zero_of e4, byte_zero_of e5, byte_zero_of e6, byte_zero_of e7] at hp
            exact UInt64.toNat_inj.mp (by rw [← hp]; rfl)
          subst hc0
          obtain ⟨fv, m6, bs6, c11, c12, dfl, mt6, d6, rfl⟩ := db5.letValue_inv
          obtain ⟨x1, y1, m7, c13, c14, dfa, dfb, opf, rfl⟩ := dfl.binary_inv
          obtain ⟨x2, y2, m8, c15, c16, dr, dcs, op2, rfl⟩ := dfa.binary_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dr
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dcs
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dfb
          obtain rfl := binop_add op2
          obtain rfl := binop_add opf
          rw [matchPattern_bind] at mt6
          cases mt6
          obtain ⟨cell, m9, dc, rfl, rfl⟩ := d6.store_inv
          obtain ⟨vs9, a9, rfl⟩ := dc.construct_inv
          obtain ⟨w1, ws1, n9, c17, c18, rfl, dw1, aw1, rfl⟩ := a9.cons_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dw1
          obtain ⟨w2, ws2, n10, c19, c20, rfl, dw2, aw2, rfl⟩ := aw1.cons_inv
          obtain ⟨rfl, rfl, rfl⟩ := aw2.nil_inv
          obtain ⟨vci, mci, cc1, cc2, aci, evci, rfl⟩ := dw2.call_inv
          rw [instanceName_plain_some] at evci
          obtain ⟨g1, gs1, ng1, c21, c22, rfl, dg1, ag1, rfl⟩ := aci.cons_inv
          obtain ⟨pg1, dpg1, ldg1⟩ := dg1.load_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dpg1
          obtain rfl := ok_inj (hcv.symm.trans ldg1)
          obtain ⟨g2, gs2, ng2, c23, c24, rfl, dg2, ag2, rfl⟩ := ag1.cons_inv
          obtain ⟨rfl, rfl⟩ := zero_block_inv dg2
          obtain ⟨g3, gs3, ng3, c25, c26, rfl, dg3, ag3, rfl⟩ := ag2.cons_inv
          obtain ⟨pg3, dpg3, ldg3⟩ := dg3.load_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dpg3
          obtain rfl := ok_inj (hcc.symm.trans ldg3)
          obtain ⟨g4, gs4, ng4, c27, c28, rfl, dg4, ag4, rfl⟩ := ag3.cons_inv
          obtain ⟨rfl, rfl, rfl⟩ := dg4.literal_inv
          obtain ⟨g5, gs5, ng5, c29, c30, rfl, dg5, ag5, rfl⟩ := ag4.cons_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dg5
          obtain ⟨rfl, rfl, rfl⟩ := ag5.nil_inv
          have hfl : ((8 : F) + 1 + 2) = ((Aiur.Library.Blake3.blockFlags true true true).toNat : F) := by
            simp [Aiur.Library.Blake3.blockFlags]; norm_num
          rw [hfl, show (0 : F) = ((0 : Nat) : F) by simp] at evci
          obtain ⟨rfl, rfl⟩ := compress_init_spec (len := 0) (by norm_num) (flags_lt _ _ _) evci
          refine ⟨Heap.Extends.snoc _ _, ?_⟩
          try rw [instanceName_plain_some]
          try rw [type_construct]
          have hmodel : Aiur.Library.Blake3.finish acc 0 0 0 cv layer =
              layer ++ [Blake3.Pure.compress cv (Blake3.Pure.blockWords []) 0 0
                (Aiur.Library.Blake3.blockFlags true true true)] := by
            simp [Aiur.Library.Blake3.finish]
          rw [hmodel, List.reverse_append, List.reverse_singleton, List.singleton_append,
            Aiur.Library.Blake3.blockWords_nil, toUInt32_toNat]
          exact stack_push_snoc hl
        · -- a nonzero counter: nothing is pushed
          rcases selectArm_cons_inv sel6 with ⟨mt7, rfl⟩ | ⟨nm7, sel7⟩
          · rw [matchPattern_wildcard] at mt7
            cases mt7
            obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) db5
            have hc0 : c ≠ 0 := by
              rintro rfl
              exact hnz (u64v_zero.trans rfl)
            refine ⟨Heap.Extends.refl _, ?_⟩
            simpa [Aiur.Library.Blake3.finish, hc0] using hl
          · exact (selectArm_nil_inv sel7).elim
      · rw [m_ll_00] at nm
        cases nm
    · -- k = 0, j ≠ 0: the chunk's chaining value is the last block's
      have hj' := natCast_ne_zero hj hj0
      rcases selectArm_cons_inv sel with ⟨mt, rfl⟩ | ⟨nm, sel2⟩
      · rw [m_ll_0y _ hj'] at mt
        cases mt
      · rcases selectArm_cons_inv sel2 with ⟨mt2, rfl⟩ | ⟨nm2, -⟩
        · rw [m_lw_0] at mt2
          cases mt2
          simp only [finishArm2] at db
          obtain ⟨cell, m5, dc, rfl, rfl⟩ := db.store_inv
          obtain ⟨vs5, a5, rfl⟩ := dc.construct_inv
          obtain ⟨w1, ws1, n5, c9, c10, rfl, dw1, aw1, rfl⟩ := a5.cons_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dw1
          obtain ⟨w2, ws2, n6, c11, c12, rfl, dw2, aw2, rfl⟩ := aw1.cons_inv
          obtain ⟨p2, dp2, ld2⟩ := dw2.load_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dp2
          obtain rfl := ok_inj (hcv.symm.trans ld2)
          obtain ⟨rfl, rfl, rfl⟩ := aw2.nil_inv
          refine ⟨Heap.Extends.snoc _ _, ?_⟩
          try rw [instanceName_plain_some]
          try rw [type_construct]
          have hmodel : Aiur.Library.Blake3.finish acc 0 j c cv layer = layer ++ [cv] := by
            simp [Aiur.Library.Blake3.finish, hj0]
          rw [hmodel, List.reverse_append, List.reverse_singleton, List.singleton_append]
          exact stack_push_snoc hl
        · rw [m_lw_0] at nm2
          cases nm2
  · -- k ≠ 0: the last block, padded
    have hk' := natCast_ne_zero (by omega) hk0
    rcases selectArm_cons_inv sel with ⟨mt, rfl⟩ | ⟨nm, sel2⟩
    · rw [m_ll_x _ _ hk'] at mt
      cases mt
    · rcases selectArm_cons_inv sel2 with ⟨mt2, rfl⟩ | ⟨nm2, sel3⟩
      · rw [m_lw_x _ _ hk'] at mt2
        cases mt2
      · rcases selectArm_cons_inv sel3 with ⟨mt3, rfl⟩ | ⟨nm3, sel4⟩
        · rw [m_ww] at mt3
          cases mt3
          simp only [finishArm3] at db
          obtain ⟨fv, m5, bs5, c9, c10, dfl, mt5, d5, rfl⟩ := db.letValue_inv
          obtain ⟨x1, y1, m6, c11, c12, dfa, dfb, opf, rfl⟩ := dfl.binary_inv
          obtain ⟨x2, y2, m7, c13, c14, dce, dmul1, op2, rfl⟩ := dfa.binary_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dce
          obtain ⟨x3, y3, m8, c15, c16, diz, droot, op3, rfl⟩ := dmul1.binary_inv
          obtain ⟨vz, mz, cz1, cz2, az, evz, rfl⟩ := diz.call_inv
          rw [instanceName_plain_some] at evz
          obtain ⟨z1, zs1, nz, c17, c18, rfl, dz1, azz, rfl⟩ := az.cons_inv
          obtain ⟨pz, dpz, ldz⟩ := dz1.load_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dpz
          obtain rfl := ok_inj (hcc.symm.trans ldz)
          obtain ⟨rfl, rfl, rfl⟩ := azz.nil_inv
          obtain ⟨rfl, rfl⟩ := u64_isZero evz
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) droot
          obtain rfl := binop_mul op3
          obtain rfl := binop_add op2
          obtain ⟨x4, y4, m9, c19, c20, dfz, dcs, op4, rfl⟩ := dfb.binary_inv
          obtain ⟨vf, mf, cf1, cf2, af, evf, rfl⟩ := dfz.call_inv
          rw [instanceName_plain_some] at evf
          obtain ⟨f1, fs1, nf, c21, c22, rfl, dsub, afs, rfl⟩ := af.cons_inv
          obtain ⟨s1, s2, ms, c23, c24, dci, dbi, ops, rfl⟩ := dsub.binary_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dci
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dbi
          obtain rfl := binop_sub ops
          obtain ⟨rfl, rfl, rfl⟩ := afs.nil_inv
          rw [show ((j : F) - (k : F)) = ((j - k : Nat) : F) by push_cast [Nat.cast_sub hkj]; ring]
            at evf
          obtain ⟨rfl, rfl⟩ := fields_isZero (by omega) evf
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dcs
          obtain rfl := binop_mul op4
          obtain rfl := binop_add opf
          rw [matchPattern_bind] at mt5
          cases mt5
          obtain ⟨bv5, m10, bs6, c25, c26, dblk, mt6, d6, rfl⟩ := d5.letValue_inv
          obtain ⟨vb, mb, cb1, cb2, ab, evb, rfl⟩ := dblk.call_inv
          rw [instanceName_plain_some] at evb
          obtain ⟨pv, pvs, np, c27, c28, rfl, dpad, apad, rfl⟩ := ab.cons_inv
          obtain ⟨rfl, rfl, rfl⟩ := apad.nil_inv
          obtain ⟨vp, mp, cp1, cp2, ap, evp, rfl⟩ := dpad.call_inv
          rw [instanceName_plain_some] at evp
          obtain ⟨a1, as1, na, c29, c30, rfl, da1, aa1, rfl⟩ := ap.cons_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) da1
          obtain ⟨a2, as2, nb, c31, c32, rfl, da2, aa2, rfl⟩ := aa1.cons_inv
          obtain ⟨l64, sk, msub, c33, c34, d64, dbk, opsub, rfl⟩ := da2.binary_inv
          obtain ⟨rfl, rfl, rfl⟩ := d64.literal_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dbk
          obtain rfl := binop_sub opsub
          obtain ⟨rfl, rfl, rfl⟩ := aa2.nil_inv
          rw [show (64 : F) - (k : F) = ((64 - k : Nat) : F) by push_cast [Nat.cast_sub (by omega : k ≤ 64)]; ring]
            at evp
          obtain ⟨ext1, hpad⟩ := pad_block_spec (64 - k) (by omega) hs evp
          obtain ⟨rfl, hle, rfl⟩ := bytes_to_block_spec hpad evb
          rw [matchPattern_bind] at mt6
          cases mt6
          obtain ⟨cell, m11, dc, rfl, rfl⟩ := d6.store_inv
          obtain ⟨vs7, a7, rfl⟩ := dc.construct_inv
          obtain ⟨w1, ws1, n7, c35, c36, rfl, dw1, aw1, rfl⟩ := a7.cons_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dw1
          obtain ⟨w2, ws2, n8, c37, c38, rfl, dci2, aw2, rfl⟩ := aw1.cons_inv
          obtain ⟨rfl, rfl, rfl⟩ := aw2.nil_inv
          obtain ⟨vci, mci, cc1, cc2, aci, evci, rfl⟩ := dci2.call_inv
          rw [instanceName_plain_some] at evci
          obtain ⟨g1, gs1, ng1, c39, c40, rfl, dg1, ag1, rfl⟩ := aci.cons_inv
          obtain ⟨pg1, dpg1, ldg1⟩ := dg1.load_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dpg1
          obtain rfl := ok_inj ((loadValue_extend ext1 hcv).symm.trans ldg1)
          obtain ⟨g2, gs2, ng2, c41, c42, rfl, dg2, ag2, rfl⟩ := ag1.cons_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dg2
          obtain ⟨g3, gs3, ng3, c43, c44, rfl, dg3, ag3, rfl⟩ := ag2.cons_inv
          obtain ⟨pg3, dpg3, ldg3⟩ := dg3.load_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dpg3
          obtain rfl := ok_inj ((loadValue_extend ext1 hcc).symm.trans ldg3)
          obtain ⟨g4, gs4, ng4, c45, c46, rfl, dg4, ag4, rfl⟩ := ag3.cons_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dg4
          obtain ⟨g5, gs5, ng5, c47, c48, rfl, dg5, ag5, rfl⟩ := ag4.cons_inv
          obtain ⟨rfl, rfl⟩ := var_lookup (by rfl) dg5
          obtain ⟨rfl, rfl, rfl⟩ := ag5.nil_inv
          have hfl : ((2 : F) + (if c = 0 then 1 else 0) * 8 + (if j - k = 0 then 1 else 0) * 1) =
              ((Aiur.Library.Blake3.blockFlags (decide (j - k = 0)) true (decide (c = 0))).toNat : F) := by
            rw [flags_field]
            by_cases hc : c = 0 <;> by_cases hjk : j - k = 0 <;> simp [hc, hjk]
          rw [hfl] at evci
          obtain ⟨rfl, rfl⟩ := compress_init_spec (len := k) (by omega) (flags_lt _ _ _) evci
          refine ⟨ext1.trans (Heap.Extends.snoc _ _), ?_⟩
          try rw [instanceName_plain_some]
          try rw [type_construct]
          have hmodel : Aiur.Library.Blake3.finish acc k j c cv layer =
              layer ++ [Blake3.Pure.compress cv (Blake3.Pure.blockWords acc.reverse) c k.toUInt32
                (Aiur.Library.Blake3.blockFlags (decide (j - k = 0)) true (decide (c = 0)))] := by
            simp [Aiur.Library.Blake3.finish, hk0]
          rw [hmodel, List.reverse_append, List.reverse_singleton, List.singleton_append,
            ← padded_block acc k hacc (by omega), toUInt32_toNat]
          exact stack_push_snoc (hl.mono ext1)
        · exact (selectArm_nil_inv sel4).elim

/-! ## `Blake3::compress_chunks` on the last bytes -/

/-- **`Blake3::compress_chunks` on fewer bytes than are left in the block** (the only way
`Blake3::hash` calls it): the bytes accumulate, last first, and `finish` ends the block. -/
theorem compress_chunks_spec : ∀ (bytes acc : List UInt8) {k j : Nat} {c : UInt64}
    {cv : Blake3.Pure.CV} {layer : List Blake3.Pure.CV} {inp accp ccp cvp lp r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)},
    k + bytes.length ≤ 63 → j + bytes.length < 1024 → k ≤ j → acc.length = k →
    Stream h bytes inp → Stream h acc accp → loadValue h ccp = .ok (u64v c) →
    loadValue h cvp = .ok (vecV cv) → Stack h layer.reverse lp →
    ObsFn W "Blake3::compress_chunks" [inp, accp, .field (k : F), .field (j : F), ccp, cvp, lp]
      h r h' cs →
    Heap.Extends h h' ∧ Stack h' (Aiur.Library.Blake3.finish (bytes.reverse ++ acc)
      (k + bytes.length) (j + bytes.length) c cv layer).reverse r
  | [], acc, k, j, c, cv, layer, inp, accp, ccp, cvp, lp, r, h, h', cs, hk, hj, hkj, hacc, hs, hsa,
      hcc, hcv, hl, ev => by
    rcases «Blake3::compress_chunks».obs ev with ⟨cs23, ld12, ev25, -⟩ |
      ⟨x_head, x_input_82, m94, cs141, ld12, -⟩ | ⟨x_head, x_input_82, m94, cs200, v205, v206, ld12, -⟩
    · simpa using finish_spec (by simp at hk; omega) (by simp at hj; omega) hkj hacc hsa hcc hcv hl ev25
    · rcases stream_inv hs ld12 with ⟨-, hv⟩ | ⟨x, xs, tail, he, -⟩
      · simp at hv
      · cases he
    · rcases stream_inv hs ld12 with ⟨-, hv⟩ | ⟨x, xs, tail, he, -⟩
      · simp at hv
      · cases he
  | x :: xs, acc, k, j, c, cv, layer, inp, accp, ccp, cvp, lp, r, h, h', cs, hk, hj, hkj, hacc, hs,
      hsa, hcc, hcv, hl, ev => by
    rcases «Blake3::compress_chunks».obs ev with ⟨cs23, ld12, ev25, -⟩ |
      ⟨x_head, x_input_82, m94, cs141, ld12, hm104, hv137, ev143, -⟩ |
      ⟨x_head, x_input_82, m94, cs200, v205, v206, ld12, hm104, hne193, op237, op252, ev202, -⟩
    · rcases stream_inv hs ld12 with ⟨he, -⟩ | ⟨x', xs', tail, -, hv, -⟩
      · cases he
      · simp at hv
    · have e63 := IxVM.natCast_inj (a := k) (b := 63) (by simp at hk; omega) (by omega)
        (by simpa using Value.field.inj hv137)
      simp at hk
      exfalso
      omega
    · rcases stream_inv hs ld12 with ⟨he, -⟩ | ⟨x', xs', tail, he, hv, htail⟩
      · cases he
      · obtain ⟨rfl, rfl⟩ := List.cons.inj he
        obtain ⟨-, -, hargs⟩ := Value.construct.inj hv
        obtain ⟨rfl, hargs2⟩ := List.cons.inj hargs
        obtain ⟨rfl, -⟩ := List.cons.inj hargs2
        subst hm104
        obtain rfl := binop_add op237
        obtain rfl := binop_add op252
        rw [show (k : F) + 1 = ((k + 1 : Nat) : F) by push_cast; ring,
          show (j : F) + 1 = ((j + 1 : Nat) : F) by push_cast; ring] at ev202
        have ext := Heap.Extends.snoc h (.construct byteStreamEnum "Cons" [bv x, accp])
        obtain ⟨ext2, hst⟩ := compress_chunks_spec xs (x :: acc) (k := k + 1) (j := j + 1)
          (by simp at hk; omega) (by simp at hj; omega) (by omega) (by simp [hacc])
          (htail.mono ext) (stream_cons_snoc hsa) (loadValue_extend ext hcc)
          (loadValue_extend ext hcv) (hl.mono ext) ev202
        refine ⟨ext.trans ext2, ?_⟩
        have e1 : (x :: xs).reverse ++ acc = xs.reverse ++ x :: acc := by simp
        have e2 : k + (x :: xs).length = k + 1 + xs.length := by simp; omega
        have e3 : j + (x :: xs).length = j + 1 + xs.length := by simp; omega
        rw [e1, e2, e3]
        exact hst

/-! ## `Blake3::hash_blocks` -/

theorem none_lit1_wild {h : Heap F} {u v : SourceValue F}
    (nm : W.matchPattern [] h (.tuple [.literal 1, .wildcard]) (.tuple [u, v]) = .ok none) :
    u ≠ .field 1 := by
  intro hu
  subst hu
  rw [matchPattern_tuple] at nm
  simp [matchListWith, matchPattern_literal, matchPattern_wildcard, bind, Except.bind, pure,
    Except.pure] at nm

theorem none_wild_lit1 {h : Heap F} {u v : SourceValue F}
    (nm : W.matchPattern [] h (.tuple [.wildcard, .literal 1]) (.tuple [u, v]) = .ok none) :
    v ≠ .field 1 := by
  intro hv
  subst hv
  rw [matchPattern_tuple] at nm
  simp [matchListWith, matchPattern_literal, matchPattern_wildcard, bind, Except.bind, pure,
    Except.pure] at nm

/-- The evaluation paths of `Blake3::hash_blocks` (as the generated `Path`, with the arms of the
`(empty, at15)` match that were not taken recorded: `hne1`, `hne2`). -/
inductive HBPath (x_input x_block_no x_chunk_count x_cv x_layer : SourceValue F) (h : Heap F) (r : SourceValue F) (h' : Heap F)
    (calls : List (Call F)) : Prop where
  | Short
      (m2 : Heap F) (cs13 : List (Call F)) (cs33 : List (Call F)) (v39 : SourceValue F) (m51 : Heap F)
      (ev15 : ObsFn W "Blake3::take_block" [x_input] h (.construct "Blake3::BlockRead" "Short" []) m2 cs13)
      (hm59 : m51 = (m2 ++ [(.construct Names.«Lists::Node<Field>» "Nil" [])]))
      (op82 : evalBinOp .mul ((.field 64) : SourceValue F) (x_block_no : SourceValue F) = .ok v39)
      (ev35 : ObsFn W "Blake3::compress_chunks" [x_input, (.ptr (.enum Names.«Lists::Node<Field>») (m2).length), (.field 0), v39, x_chunk_count, x_cv, x_layer] m51 r h' cs33)
      (hc105 : calls = ((⟨"Blake3::take_block", [x_input], h⟩ : Call F) :: (cs13 ++ ((⟨"Blake3::compress_chunks", [x_input, (.ptr (.enum Names.«Lists::Node<Field>») (m2).length), (.field 0), v39, x_chunk_count, x_cv, x_layer], m51⟩ : Call F) :: cs33))))
  | Full_n1_other
      (m2 : Heap F) (cs13 : List (Call F)) (x_block : SourceValue F) (x_rest : SourceValue F) (m177 : Heap F) (cs179 : List (Call F)) (v185 : SourceValue F) (m186 : Heap F) (cs196 : List (Call F)) (v199 : SourceValue F) (v215 : SourceValue F) (m216 : Heap F) (cs226 : List (Call F)) (v237 : SourceValue F) (x245 : SourceValue F) (y246 : SourceValue F) (v273 : SourceValue F) (m274 : Heap F) (y282 : SourceValue F) (cs293 : List (Call F)) (v296 : SourceValue F) (v307 : SourceValue F) (x315 : SourceValue F) (y316 : SourceValue F) (x323 : SourceValue F) (y324 : SourceValue F) (v361 : SourceValue F) (m362 : Heap F) (cs372 : List (Call F)) (v375 : SourceValue F) (v377 : SourceValue F)
      (ev15 : ObsFn W "Blake3::take_block" [x_input] h (.construct "Blake3::BlockRead" "Full" [x_block, x_rest]) m2 cs13)
      (sg184 : «Blake3::hash_blocks».Seg1 (.field 8) (.field 2) (.field 1) x_block x_rest x_input x_block_no x_chunk_count x_cv x_layer m2 (.field 1) m177 cs179)
      (op213 : evalBinOp .sub (x_block_no : SourceValue F) ((.field 15) : SourceValue F) = .ok v199)
      (ev198 : ObsFn W "Fields::is_zero" [v199] m177 v185 m186 cs196)
      (ev228 : ObsFn W "Fields::is_zero" [x_block_no] m186 v215 m216 cs226)
      (op260 : evalBinOp .add ((.field 1) : SourceValue F) (v185 : SourceValue F) = .ok x245)
      (op270 : evalBinOp .mul ((.field 1) : SourceValue F) (v185 : SourceValue F) = .ok y246)
      (op252 : evalBinOp .sub (x245 : SourceValue F) (y246 : SourceValue F) = .ok v237)
      (ld305 : loadValue m216 x_chunk_count = .ok v296)
      (ev295 : ObsFn W "UInt64::is_zero" [v296] m216 y282 m274 cs293)
      (op288 : evalBinOp .mul ((.field 1) : SourceValue F) (y282 : SourceValue F) = .ok v273)
      (op338 : evalBinOp .mul ((.field 1) : SourceValue F) (v215 : SourceValue F) = .ok x323)
      (op348 : evalBinOp .mul ((.field 2) : SourceValue F) (v237 : SourceValue F) = .ok y324)
      (op330 : evalBinOp .add (x323 : SourceValue F) (y324 : SourceValue F) = .ok x315)
      (op358 : evalBinOp .mul ((.field 8) : SourceValue F) (v273 : SourceValue F) = .ok y316)
      (op322 : evalBinOp .add (x315 : SourceValue F) (y316 : SourceValue F) = .ok v307)
      (ld388 : loadValue m274 x_cv = .ok v375)
      (ld405 : loadValue m274 x_chunk_count = .ok v377)
      (ev374 : ObsFn W "Blake3::compress_init" [v375, x_block, v377, (.field 64), v307] m274 v361 m362 cs372)
      (he464 : r = (.ptr (.enum "Blake3::LayerNode") (m362).length))
      (hm463 : h' = (m362 ++ [(.construct "Blake3::LayerNode" "Push" [x_layer, v361])]))
      (hc484 : calls = ((⟨"Blake3::take_block", [x_input], h⟩ : Call F) :: (cs13 ++ (cs179 ++ ((⟨"Fields::is_zero", [v199], m177⟩ : Call F) :: (cs196 ++ ((⟨"Fields::is_zero", [x_block_no], m186⟩ : Call F) :: (cs226 ++ ((⟨"UInt64::is_zero", [v296], m216⟩ : Call F) :: (cs293 ++ ((⟨"Blake3::compress_init", [v375, x_block, v377, (.field 64), v307], m274⟩ : Call F) :: cs372)))))))))))
  | Full_other_n1
      (m2 : Heap F) (cs13 : List (Call F)) (x_block : SourceValue F) (x_rest : SourceValue F) (v176 : SourceValue F) (m177 : Heap F) (cs179 : List (Call F)) (m186 : Heap F) (cs196 : List (Call F)) (v199 : SourceValue F) (v215 : SourceValue F) (m216 : Heap F) (cs226 : List (Call F)) (v237 : SourceValue F) (x245 : SourceValue F) (y246 : SourceValue F) (v273 : SourceValue F) (m274 : Heap F) (y282 : SourceValue F) (cs293 : List (Call F)) (v296 : SourceValue F) (v307 : SourceValue F) (x315 : SourceValue F) (y316 : SourceValue F) (x323 : SourceValue F) (y324 : SourceValue F) (v361 : SourceValue F) (m362 : Heap F) (cs372 : List (Call F)) (v375 : SourceValue F) (v377 : SourceValue F) (v498 : SourceValue F) (m499 : Heap F) (cs509 : List (Call F)) (cs515 : List (Call F)) (m537 : Heap F) (v542 : SourceValue F) (m543 : Heap F) (cs549 : List (Call F)) (v552 : SourceValue F) (m564 : Heap F) (m575 : Heap F)
      (ev15 : ObsFn W "Blake3::take_block" [x_input] h (.construct "Blake3::BlockRead" "Full" [x_block, x_rest]) m2 cs13)
      (sg184 : «Blake3::hash_blocks».Seg1 (.field 8) (.field 2) (.field 1) x_block x_rest x_input x_block_no x_chunk_count x_cv x_layer m2 v176 m177 cs179)
      (op213 : evalBinOp .sub (x_block_no : SourceValue F) ((.field 15) : SourceValue F) = .ok v199)
      (ev198 : ObsFn W "Fields::is_zero" [v199] m177 (.field 1) m186 cs196)
      (ev228 : ObsFn W "Fields::is_zero" [x_block_no] m186 v215 m216 cs226)
      (op260 : evalBinOp .add (v176 : SourceValue F) ((.field 1) : SourceValue F) = .ok x245)
      (op270 : evalBinOp .mul (v176 : SourceValue F) ((.field 1) : SourceValue F) = .ok y246)
      (op252 : evalBinOp .sub (x245 : SourceValue F) (y246 : SourceValue F) = .ok v237)
      (ld305 : loadValue m216 x_chunk_count = .ok v296)
      (ev295 : ObsFn W "UInt64::is_zero" [v296] m216 y282 m274 cs293)
      (op288 : evalBinOp .mul (v176 : SourceValue F) (y282 : SourceValue F) = .ok v273)
      (op338 : evalBinOp .mul ((.field 1) : SourceValue F) (v215 : SourceValue F) = .ok x323)
      (op348 : evalBinOp .mul ((.field 2) : SourceValue F) (v237 : SourceValue F) = .ok y324)
      (op330 : evalBinOp .add (x323 : SourceValue F) (y324 : SourceValue F) = .ok x315)
      (op358 : evalBinOp .mul ((.field 8) : SourceValue F) (v273 : SourceValue F) = .ok y316)
      (op322 : evalBinOp .add (x315 : SourceValue F) (y316 : SourceValue F) = .ok v307)
      (ld388 : loadValue m274 x_cv = .ok v375)
      (ld405 : loadValue m274 x_chunk_count = .ok v377)
      (ev374 : ObsFn W "Blake3::compress_init" [v375, x_block, v377, (.field 64), v307] m274 v361 m362 cs372)
      (ev511 : ObsFn W "Blake3::iv" [] m362 v498 m499 cs509)
      (hm545 : m537 = (m543 ++ [v542]))
      (ld561 : loadValue m499 x_chunk_count = .ok v552)
      (ev551 : ObsFn W "UInt64::wrapping_succ" [v552] m499 v542 m543 cs549)
      (hm572 : m564 = (m537 ++ [v498]))
      (hm583 : m575 = (m564 ++ [(.construct "Blake3::LayerNode" "Push" [x_layer, v361])]))
      (ev517 : ObsFn W "Blake3::hash_blocks" [x_rest, (.field 0), (.ptr (Value.type (v542 : SourceValue F)) (m543).length), (.ptr (Value.type (v498 : SourceValue F)) (m537).length), (.ptr (.enum "Blake3::LayerNode") (m564).length)] m575 r h' cs515)
      (hc603 : calls = ((⟨"Blake3::take_block", [x_input], h⟩ : Call F) :: (cs13 ++ (cs179 ++ ((⟨"Fields::is_zero", [v199], m177⟩ : Call F) :: (cs196 ++ ((⟨"Fields::is_zero", [x_block_no], m186⟩ : Call F) :: (cs226 ++ ((⟨"UInt64::is_zero", [v296], m216⟩ : Call F) :: (cs293 ++ ((⟨"Blake3::compress_init", [v375, x_block, v377, (.field 64), v307], m274⟩ : Call F) :: (cs372 ++ ((⟨"Blake3::iv", [], m362⟩ : Call F) :: (cs509 ++ ((⟨"UInt64::wrapping_succ", [v552], m499⟩ : Call F) :: (cs549 ++ ((⟨"Blake3::hash_blocks", [x_rest, (.field 0), (.ptr (Value.type (v542 : SourceValue F)) (m543).length), (.ptr (Value.type (v498 : SourceValue F)) (m537).length), (.ptr (.enum "Blake3::LayerNode") (m564).length)], m575⟩ : Call F) :: cs515)))))))))))))))))
      (hne1 : (v176 : SourceValue F) ≠ .field 1)
  | Full_other_other
      (m2 : Heap F) (cs13 : List (Call F)) (x_block : SourceValue F) (x_rest : SourceValue F) (v176 : SourceValue F) (m177 : Heap F) (cs179 : List (Call F)) (v185 : SourceValue F) (m186 : Heap F) (cs196 : List (Call F)) (v199 : SourceValue F) (v215 : SourceValue F) (m216 : Heap F) (cs226 : List (Call F)) (v237 : SourceValue F) (x245 : SourceValue F) (y246 : SourceValue F) (v273 : SourceValue F) (m274 : Heap F) (y282 : SourceValue F) (cs293 : List (Call F)) (v296 : SourceValue F) (v307 : SourceValue F) (x315 : SourceValue F) (y316 : SourceValue F) (x323 : SourceValue F) (y324 : SourceValue F) (v361 : SourceValue F) (m362 : Heap F) (cs372 : List (Call F)) (v375 : SourceValue F) (v377 : SourceValue F) (cs619 : List (Call F)) (v623 : SourceValue F) (m657 : Heap F)
      (ev15 : ObsFn W "Blake3::take_block" [x_input] h (.construct "Blake3::BlockRead" "Full" [x_block, x_rest]) m2 cs13)
      (sg184 : «Blake3::hash_blocks».Seg1 (.field 8) (.field 2) (.field 1) x_block x_rest x_input x_block_no x_chunk_count x_cv x_layer m2 v176 m177 cs179)
      (op213 : evalBinOp .sub (x_block_no : SourceValue F) ((.field 15) : SourceValue F) = .ok v199)
      (ev198 : ObsFn W "Fields::is_zero" [v199] m177 v185 m186 cs196)
      (ev228 : ObsFn W "Fields::is_zero" [x_block_no] m186 v215 m216 cs226)
      (op260 : evalBinOp .add (v176 : SourceValue F) (v185 : SourceValue F) = .ok x245)
      (op270 : evalBinOp .mul (v176 : SourceValue F) (v185 : SourceValue F) = .ok y246)
      (op252 : evalBinOp .sub (x245 : SourceValue F) (y246 : SourceValue F) = .ok v237)
      (ld305 : loadValue m216 x_chunk_count = .ok v296)
      (ev295 : ObsFn W "UInt64::is_zero" [v296] m216 y282 m274 cs293)
      (op288 : evalBinOp .mul (v176 : SourceValue F) (y282 : SourceValue F) = .ok v273)
      (op338 : evalBinOp .mul ((.field 1) : SourceValue F) (v215 : SourceValue F) = .ok x323)
      (op348 : evalBinOp .mul ((.field 2) : SourceValue F) (v237 : SourceValue F) = .ok y324)
      (op330 : evalBinOp .add (x323 : SourceValue F) (y324 : SourceValue F) = .ok x315)
      (op358 : evalBinOp .mul ((.field 8) : SourceValue F) (v273 : SourceValue F) = .ok y316)
      (op322 : evalBinOp .add (x315 : SourceValue F) (y316 : SourceValue F) = .ok v307)
      (ld388 : loadValue m274 x_cv = .ok v375)
      (ld405 : loadValue m274 x_chunk_count = .ok v377)
      (ev374 : ObsFn W "Blake3::compress_init" [v375, x_block, v377, (.field 64), v307] m274 v361 m362 cs372)
      (op647 : evalBinOp .add (x_block_no : SourceValue F) ((.field 1) : SourceValue F) = .ok v623)
      (hm665 : m657 = (m362 ++ [v361]))
      (ev621 : ObsFn W "Blake3::hash_blocks" [x_rest, v623, x_chunk_count, (.ptr (Value.type (v361 : SourceValue F)) (m362).length), x_layer] m657 r h' cs619)
      (hc674 : calls = ((⟨"Blake3::take_block", [x_input], h⟩ : Call F) :: (cs13 ++ (cs179 ++ ((⟨"Fields::is_zero", [v199], m177⟩ : Call F) :: (cs196 ++ ((⟨"Fields::is_zero", [x_block_no], m186⟩ : Call F) :: (cs226 ++ ((⟨"UInt64::is_zero", [v296], m216⟩ : Call F) :: (cs293 ++ ((⟨"Blake3::compress_init", [v375, x_block, v377, (.field 64), v307], m274⟩ : Call F) :: (cs372 ++ ((⟨"Blake3::hash_blocks", [x_rest, v623, x_chunk_count, (.ptr (Value.type (v361 : SourceValue F)) (m362).length), x_layer], m657⟩ : Call F) :: cs619)))))))))))))
      (hne1 : (v176 : SourceValue F) ≠ .field 1)
      (hne2 : (v185 : SourceValue F) ≠ .field 1)

set_option maxHeartbeats 40000000 in
/-- **Every observed derivation of `Blake3::hash_blocks` takes one of its paths** (`HBPath`). -/
theorem hb_obs {x_input x_block_no x_chunk_count x_cv x_layer : SourceValue F} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn W "Blake3::hash_blocks" [x_input, x_block_no, x_chunk_count, x_cv, x_layer] h r h' calls) :
    HBPath x_input x_block_no x_chunk_count x_cv x_layer h r h' calls := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.Blake3.hash_blocks.lookup
    (by simp [IxVM.Blake3.hash_blocks, ControlLower.hasControl]) ev
  simp only [IxVM.Blake3.hash_blocks] at d0
  obtain ⟨v1, m2, bs3, body4, c5, c6, d7, sel8, d9, rfl⟩ := d0.matchValue_inv
  obtain ⟨vs10, m11, c12, cs13, a14, ev15, rfl⟩ := d7.call_inv
  rw [instanceName_plain_some] at ev15
  obtain ⟨v16, vs17, m18, c19, c20, rfl, d21, a22, rfl⟩ := a14.cons_inv
  obtain ⟨l23, rfl, rfl⟩ := d21.var_inv
  simp at l23
  subst l23
  obtain ⟨rfl, rfl, rfl⟩ := a22.nil_inv
  rcases selectArm_cons_inv sel8 with ⟨mt24, rfl⟩ | ⟨nm25, sel26⟩
  · obtain ⟨vs27, hv28, -, ml29⟩ := matchPattern_construct_inv mt24
    rw [Names.n2864496815413202991] at hv28
    subst hv28
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml29
    obtain ⟨vs30, m31, c32, cs33, a34, ev35, rfl⟩ := d9.call_inv
    rw [instanceName_plain_some] at ev35
    obtain ⟨v36, vs43, m44, c45, c46, rfl, d47, a48, rfl⟩ := a34.cons_inv
    obtain ⟨l49, rfl, rfl⟩ := d47.var_inv
    simp at l49
    subst l49
    obtain ⟨v37, vs50, m51, c52, c53, rfl, d54, a55, rfl⟩ := a48.cons_inv
    obtain ⟨v56, m57, d58, rfl, hm59⟩ := d54.store_inv
    obtain ⟨vs60, a61, hres62⟩ := d58.construct_inv
    rw [Names.n12516105052029042359] at hres62
    subst hres62
    obtain ⟨rfl, rfl, rfl⟩ := a61.nil_inv
    obtain ⟨v38, vs63, m64, c65, c66, rfl, d67, a68, rfl⟩ := a55.cons_inv
    obtain ⟨rfl, rfl, rfl⟩ := d67.literal_inv
    obtain ⟨v39, vs69, m70, c71, c72, rfl, d73, a74, rfl⟩ := a68.cons_inv
    obtain ⟨x75, y76, m77, c78, c79, d80, d81, op82, rfl⟩ := d73.binary_inv
    obtain ⟨rfl, rfl, rfl⟩ := d80.literal_inv
    obtain ⟨l83, rfl, rfl⟩ := d81.var_inv
    simp at l83
    subst l83
    obtain ⟨v40, vs84, m85, c86, c87, rfl, d88, a89, rfl⟩ := a74.cons_inv
    obtain ⟨l90, rfl, rfl⟩ := d88.var_inv
    simp at l90
    subst l90
    obtain ⟨v41, vs91, m92, c93, c94, rfl, d95, a96, rfl⟩ := a89.cons_inv
    obtain ⟨l97, rfl, rfl⟩ := d95.var_inv
    simp at l97
    subst l97
    obtain ⟨v42, vs98, m99, c100, c101, rfl, d102, a103, rfl⟩ := a96.cons_inv
    obtain ⟨l104, rfl, rfl⟩ := d102.var_inv
    simp at l104
    subst l104
    obtain ⟨rfl, rfl, rfl⟩ := a103.nil_inv
    try simp only [Value.type, List.map_cons, List.map_nil] at ev15 hm59 op82 ev35 ⊢
    exact HBPath.Short _ _ _ _ _ ev15 hm59 op82 ev35 (by first | rfl | simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil, instanceName_plain_none, instanceName_plain_some])
  · have hne106 := matchPattern_construct_none (by trivial) nm25
    simp only [Names.n2864496815413202991] at hne106
    rcases selectArm_cons_inv sel26 with ⟨mt107, rfl⟩ | ⟨nm108, sel109⟩
    · obtain ⟨vs110, hv111, -, ml112⟩ := matchPattern_construct_inv mt107
      rw [Names.n2864496815413202991] at hv111
      subst hv111
      obtain ⟨x_block, vs113, b114, b115, rfl, mt116, ml117, rfl⟩ := matchListWith_cons_inv ml112
      obtain rfl := matchPattern_bind_inv mt116
      obtain ⟨x_rest, vs118, b119, b120, rfl, mt121, ml122, rfl⟩ := matchListWith_cons_inv ml117
      obtain rfl := matchPattern_bind_inv mt121
      obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml122
      obtain ⟨v123, m124, bs125, c126, c127, d128, mt129, d130, rfl⟩ := d9.letValue_inv
      obtain ⟨rfl, rfl, rfl⟩ := d128.literal_inv
      obtain rfl := matchPattern_bind_inv mt129
      obtain ⟨v131, m132, bs133, c134, c135, d136, mt137, d138, rfl⟩ := d130.letValue_inv
      obtain ⟨rfl, rfl, rfl⟩ := d136.literal_inv
      obtain rfl := matchPattern_bind_inv mt137
      obtain ⟨v139, m140, bs141, c142, c143, d144, mt145, d146, rfl⟩ := d138.letValue_inv
      obtain ⟨rfl, rfl, rfl⟩ := d144.literal_inv
      obtain rfl := matchPattern_bind_inv mt145
      obtain ⟨v176, m177, bs178, cs179, c180, d181, mt182, d183, rfl⟩ := d146.letValue_inv
      have sg184 := «Blake3::hash_blocks».seg1 d181
      clear d181
      obtain rfl := matchPattern_bind_inv mt182
      obtain ⟨v185, m186, bs187, c188, c189, d190, mt191, d192, rfl⟩ := d183.letValue_inv
      obtain ⟨vs193, m194, c195, cs196, a197, ev198, rfl⟩ := d190.call_inv
      rw [instanceName_plain_some] at ev198
      obtain ⟨v199, vs200, m201, c202, c203, rfl, d204, a205, rfl⟩ := a197.cons_inv
      obtain ⟨x206, y207, m208, c209, c210, d211, d212, op213, rfl⟩ := d204.binary_inv
      obtain ⟨l214, rfl, rfl⟩ := d211.var_inv
      simp at l214
      subst l214
      obtain ⟨rfl, rfl, rfl⟩ := d212.literal_inv
      obtain ⟨rfl, rfl, rfl⟩ := a205.nil_inv
      obtain rfl := matchPattern_bind_inv mt191
      obtain ⟨v215, m216, bs217, c218, c219, d220, mt221, d222, rfl⟩ := d192.letValue_inv
      obtain ⟨vs223, m224, c225, cs226, a227, ev228, rfl⟩ := d220.call_inv
      rw [instanceName_plain_some] at ev228
      obtain ⟨v229, vs230, m231, c232, c233, rfl, d234, a235, rfl⟩ := a227.cons_inv
      obtain ⟨l236, rfl, rfl⟩ := d234.var_inv
      simp at l236
      subst l236
      obtain ⟨rfl, rfl, rfl⟩ := a235.nil_inv
      obtain rfl := matchPattern_bind_inv mt221
      obtain ⟨v237, m238, bs239, c240, c241, d242, mt243, d244, rfl⟩ := d222.letValue_inv
      obtain ⟨x245, y246, m247, c248, c249, d250, d251, op252, rfl⟩ := d242.binary_inv
      obtain ⟨x253, y254, m255, c256, c257, d258, d259, op260, rfl⟩ := d250.binary_inv
      obtain ⟨l261, rfl, rfl⟩ := d258.var_inv
      simp at l261
      subst l261
      obtain ⟨l262, rfl, rfl⟩ := d259.var_inv
      simp at l262
      subst l262
      obtain ⟨x263, y264, m265, c266, c267, d268, d269, op270, rfl⟩ := d251.binary_inv
      obtain ⟨l271, rfl, rfl⟩ := d268.var_inv
      simp at l271
      subst l271
      obtain ⟨l272, rfl, rfl⟩ := d269.var_inv
      simp at l272
      subst l272
      obtain rfl := matchPattern_bind_inv mt243
      obtain ⟨v273, m274, bs275, c276, c277, d278, mt279, d280, rfl⟩ := d244.letValue_inv
      obtain ⟨x281, y282, m283, c284, c285, d286, d287, op288, rfl⟩ := d278.binary_inv
      obtain ⟨l289, rfl, rfl⟩ := d286.var_inv
      simp at l289
      subst l289
      obtain ⟨vs290, m291, c292, cs293, a294, ev295, rfl⟩ := d287.call_inv
      rw [instanceName_plain_some] at ev295
      obtain ⟨v296, vs297, m298, c299, c300, rfl, d301, a302, rfl⟩ := a294.cons_inv
      obtain ⟨p303, d304, ld305⟩ := d301.load_inv
      obtain ⟨l306, rfl, rfl⟩ := d304.var_inv
      simp at l306
      subst l306
      obtain ⟨rfl, rfl, rfl⟩ := a302.nil_inv
      obtain rfl := matchPattern_bind_inv mt279
      obtain ⟨v307, m308, bs309, c310, c311, d312, mt313, d314, rfl⟩ := d280.letValue_inv
      obtain ⟨x315, y316, m317, c318, c319, d320, d321, op322, rfl⟩ := d312.binary_inv
      obtain ⟨x323, y324, m325, c326, c327, d328, d329, op330, rfl⟩ := d320.binary_inv
      obtain ⟨x331, y332, m333, c334, c335, d336, d337, op338, rfl⟩ := d328.binary_inv
      obtain ⟨l339, rfl, rfl⟩ := d336.var_inv
      simp at l339
      subst l339
      obtain ⟨l340, rfl, rfl⟩ := d337.var_inv
      simp at l340
      subst l340
      obtain ⟨x341, y342, m343, c344, c345, d346, d347, op348, rfl⟩ := d329.binary_inv
      obtain ⟨l349, rfl, rfl⟩ := d346.var_inv
      simp at l349
      subst l349
      obtain ⟨l350, rfl, rfl⟩ := d347.var_inv
      simp at l350
      subst l350
      obtain ⟨x351, y352, m353, c354, c355, d356, d357, op358, rfl⟩ := d321.binary_inv
      obtain ⟨l359, rfl, rfl⟩ := d356.var_inv
      simp at l359
      subst l359
      obtain ⟨l360, rfl, rfl⟩ := d357.var_inv
      simp at l360
      subst l360
      obtain rfl := matchPattern_bind_inv mt313
      obtain ⟨v361, m362, bs363, c364, c365, d366, mt367, d368, rfl⟩ := d314.letValue_inv
      obtain ⟨vs369, m370, c371, cs372, a373, ev374, rfl⟩ := d366.call_inv
      rw [instanceName_plain_some] at ev374
      obtain ⟨v375, vs380, m381, c382, c383, rfl, d384, a385, rfl⟩ := a373.cons_inv
      obtain ⟨p386, d387, ld388⟩ := d384.load_inv
      obtain ⟨l389, rfl, rfl⟩ := d387.var_inv
      simp at l389
      subst l389
      obtain ⟨v376, vs390, m391, c392, c393, rfl, d394, a395, rfl⟩ := a385.cons_inv
      obtain ⟨l396, rfl, rfl⟩ := d394.var_inv
      simp at l396
      subst l396
      obtain ⟨v377, vs397, m398, c399, c400, rfl, d401, a402, rfl⟩ := a395.cons_inv
      obtain ⟨p403, d404, ld405⟩ := d401.load_inv
      obtain ⟨l406, rfl, rfl⟩ := d404.var_inv
      simp at l406
      subst l406
      obtain ⟨v378, vs407, m408, c409, c410, rfl, d411, a412, rfl⟩ := a402.cons_inv
      obtain ⟨rfl, rfl, rfl⟩ := d411.literal_inv
      obtain ⟨v379, vs413, m414, c415, c416, rfl, d417, a418, rfl⟩ := a412.cons_inv
      obtain ⟨l419, rfl, rfl⟩ := d417.var_inv
      simp at l419
      subst l419
      obtain ⟨rfl, rfl, rfl⟩ := a418.nil_inv
      obtain rfl := matchPattern_bind_inv mt367
      obtain ⟨v420, m421, bs422, body423, c424, c425, d426, sel427, d428, rfl⟩ := d368.matchValue_inv
      obtain ⟨vs429, a430, rfl⟩ := d426.tuple_inv
      obtain ⟨v431, vs433, m434, c435, c436, rfl, d437, a438, rfl⟩ := a430.cons_inv
      obtain ⟨l439, rfl, rfl⟩ := d437.var_inv
      simp at l439
      subst l439
      obtain ⟨v432, vs440, m441, c442, c443, rfl, d444, a445, rfl⟩ := a438.cons_inv
      obtain ⟨l446, rfl, rfl⟩ := d444.var_inv
      simp at l446
      subst l446
      obtain ⟨rfl, rfl, rfl⟩ := a445.nil_inv
      rcases selectArm_cons_inv sel427 with ⟨mt447, rfl⟩ | ⟨nm448, sel449⟩
      · have ml450 := matchPattern_tuple_tuple_inv mt447
        obtain ⟨b451, b452, mt453, ml454, rfl⟩ := matchListWith_cons_cons_inv ml450
        obtain ⟨hv455, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 1) mt453
        subst hv455
        obtain ⟨b456, b457, mt458, ml459, rfl⟩ := matchListWith_cons_cons_inv ml454
        obtain rfl := matchPattern_wildcard_inv mt458
        obtain ⟨-, rfl⟩ := matchListWith_nil_inv ml459
        obtain ⟨v460, m461, d462, rfl, hm463⟩ := d428.store_inv
        obtain ⟨vs465, a466, hres467⟩ := d462.construct_inv
        rw [instanceName_plain_some] at hres467
        subst hres467
        obtain ⟨v468, vs470, m471, c472, c473, rfl, d474, a475, rfl⟩ := a466.cons_inv
        obtain ⟨l476, rfl, rfl⟩ := d474.var_inv
        simp at l476
        subst l476
        obtain ⟨v469, vs477, m478, c479, c480, rfl, d481, a482, rfl⟩ := a475.cons_inv
        obtain ⟨l483, rfl, rfl⟩ := d481.var_inv
        simp at l483
        subst l483
        obtain ⟨rfl, rfl, rfl⟩ := a482.nil_inv
        try simp only [Value.type, List.map_cons, List.map_nil] at ev15 hne106 sg184 op213 ev198 ev228 op260 op270 op252 ld305 ev295 op288 op338 op348 op330 op358 op322 ld388 ld405 ev374 hm463 ⊢
        exact HBPath.Full_n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev15 sg184 op213 ev198 ev228 op260 op270 op252 ld305 ev295 op288 op338 op348 op330 op358 op322 ld388 ld405 ev374 rfl hm463 (by first | rfl | simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil, instanceName_plain_none, instanceName_plain_some])
      · have hne_a := none_lit1_wild nm448
        rcases selectArm_cons_inv sel449 with ⟨mt485, rfl⟩ | ⟨nm486, sel487⟩
        · have ml488 := matchPattern_tuple_tuple_inv mt485
          obtain ⟨b489, b490, mt491, ml492, rfl⟩ := matchListWith_cons_cons_inv ml488
          obtain rfl := matchPattern_wildcard_inv mt491
          obtain ⟨b493, b494, mt495, ml496, rfl⟩ := matchListWith_cons_cons_inv ml492
          obtain ⟨hv497, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 1) mt495
          subst hv497
          obtain ⟨-, rfl⟩ := matchListWith_nil_inv ml496
          obtain ⟨v498, m499, bs500, c501, c502, d503, mt504, d505, rfl⟩ := d428.letValue_inv
          obtain ⟨vs506, m507, c508, cs509, a510, ev511, rfl⟩ := d503.call_inv
          rw [instanceName_plain_some] at ev511
          obtain ⟨rfl, rfl, rfl⟩ := a510.nil_inv
          obtain rfl := matchPattern_bind_inv mt504
          obtain ⟨vs512, m513, c514, cs515, a516, ev517, rfl⟩ := d505.call_inv
          rw [instanceName_plain_some] at ev517
          obtain ⟨v518, vs523, m524, c525, c526, rfl, d527, a528, rfl⟩ := a516.cons_inv
          obtain ⟨l529, rfl, rfl⟩ := d527.var_inv
          simp at l529
          subst l529
          obtain ⟨v519, vs530, m531, c532, c533, rfl, d534, a535, rfl⟩ := a528.cons_inv
          obtain ⟨rfl, rfl, rfl⟩ := d534.literal_inv
          obtain ⟨v520, vs536, m537, c538, c539, rfl, d540, a541, rfl⟩ := a535.cons_inv
          obtain ⟨v542, m543, d544, rfl, hm545⟩ := d540.store_inv
          obtain ⟨vs546, m547, c548, cs549, a550, ev551, rfl⟩ := d544.call_inv
          rw [instanceName_plain_some] at ev551
          obtain ⟨v552, vs553, m554, c555, c556, rfl, d557, a558, rfl⟩ := a550.cons_inv
          obtain ⟨p559, d560, ld561⟩ := d557.load_inv
          obtain ⟨l562, rfl, rfl⟩ := d560.var_inv
          simp at l562
          subst l562
          obtain ⟨rfl, rfl, rfl⟩ := a558.nil_inv
          obtain ⟨v521, vs563, m564, c565, c566, rfl, d567, a568, rfl⟩ := a541.cons_inv
          obtain ⟨v569, m570, d571, rfl, hm572⟩ := d567.store_inv
          obtain ⟨l573, rfl, rfl⟩ := d571.var_inv
          simp at l573
          subst l573
          obtain ⟨v522, vs574, m575, c576, c577, rfl, d578, a579, rfl⟩ := a568.cons_inv
          obtain ⟨v580, m581, d582, rfl, hm583⟩ := d578.store_inv
          obtain ⟨vs584, a585, hres586⟩ := d582.construct_inv
          rw [instanceName_plain_some] at hres586
          subst hres586
          obtain ⟨v587, vs589, m590, c591, c592, rfl, d593, a594, rfl⟩ := a585.cons_inv
          obtain ⟨l595, rfl, rfl⟩ := d593.var_inv
          simp at l595
          subst l595
          obtain ⟨v588, vs596, m597, c598, c599, rfl, d600, a601, rfl⟩ := a594.cons_inv
          obtain ⟨l602, rfl, rfl⟩ := d600.var_inv
          simp at l602
          subst l602
          obtain ⟨rfl, rfl, rfl⟩ := a601.nil_inv
          obtain ⟨rfl, rfl, rfl⟩ := a579.nil_inv
          try simp only [Value.type, List.map_cons, List.map_nil] at ev15 hne106 sg184 op213 ev198 ev228 op260 op270 op252 ld305 ev295 op288 op338 op348 op330 op358 op322 ld388 ld405 ev374 ev511 hm545 ld561 ev551 hm572 hm583 ev517 ⊢
          exact HBPath.Full_other_n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev15 sg184 op213 ev198 ev228 op260 op270 op252 ld305 ev295 op288 op338 op348 op330 op358 op322 ld388 ld405 ev374 ev511 hm545 ld561 ev551 hm572 hm583 ev517 (by first | rfl | simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil, instanceName_plain_none, instanceName_plain_some]) hne_a
        · have hne_b := none_wild_lit1 nm486
          rcases selectArm_cons_inv sel487 with ⟨mt604, rfl⟩ | ⟨nm605, sel606⟩
          · have ml607 := matchPattern_tuple_tuple_inv mt604
            obtain ⟨b608, b609, mt610, ml611, rfl⟩ := matchListWith_cons_cons_inv ml607
            obtain rfl := matchPattern_wildcard_inv mt610
            obtain ⟨b612, b613, mt614, ml615, rfl⟩ := matchListWith_cons_cons_inv ml611
            obtain rfl := matchPattern_wildcard_inv mt614
            obtain ⟨-, rfl⟩ := matchListWith_nil_inv ml615
            obtain ⟨vs616, m617, c618, cs619, a620, ev621, rfl⟩ := d428.call_inv
            rw [instanceName_plain_some] at ev621
            obtain ⟨v622, vs627, m628, c629, c630, rfl, d631, a632, rfl⟩ := a620.cons_inv
            obtain ⟨l633, rfl, rfl⟩ := d631.var_inv
            simp at l633
            subst l633
            obtain ⟨v623, vs634, m635, c636, c637, rfl, d638, a639, rfl⟩ := a632.cons_inv
            obtain ⟨x640, y641, m642, c643, c644, d645, d646, op647, rfl⟩ := d638.binary_inv
            obtain ⟨l648, rfl, rfl⟩ := d645.var_inv
            simp at l648
            subst l648
            obtain ⟨rfl, rfl, rfl⟩ := d646.literal_inv
            obtain ⟨v624, vs649, m650, c651, c652, rfl, d653, a654, rfl⟩ := a639.cons_inv
            obtain ⟨l655, rfl, rfl⟩ := d653.var_inv
            simp at l655
            subst l655
            obtain ⟨v625, vs656, m657, c658, c659, rfl, d660, a661, rfl⟩ := a654.cons_inv
            obtain ⟨v662, m663, d664, rfl, hm665⟩ := d660.store_inv
            obtain ⟨l666, rfl, rfl⟩ := d664.var_inv
            simp at l666
            subst l666
            obtain ⟨v626, vs667, m668, c669, c670, rfl, d671, a672, rfl⟩ := a661.cons_inv
            obtain ⟨l673, rfl, rfl⟩ := d671.var_inv
            simp at l673
            subst l673
            obtain ⟨rfl, rfl, rfl⟩ := a672.nil_inv
            try simp only [Value.type, List.map_cons, List.map_nil] at ev15 hne106 sg184 op213 ev198 ev228 op260 op270 op252 ld305 ev295 op288 op338 op348 op330 op358 op322 ld388 ld405 ev374 op647 hm665 ev621 ⊢
            exact HBPath.Full_other_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev15 sg184 op213 ev198 ev228 op260 op270 op252 ld305 ev295 op288 op338 op348 op330 op358 op322 ld388 ld405 ev374 op647 hm665 ev621 (by first | rfl | simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil, instanceName_plain_none, instanceName_plain_some]) hne_a hne_b
          · have hne675 := matchPattern_tuple_none (by trivial) nm605
            exact (selectArm_nil_inv sel606).elim
    · have hne676 := matchPattern_construct_none (by trivial) nm108
      simp only [Names.n2864496815413202991] at hne676
      exact (selectArm_nil_inv sel109).elim


theorem fields_isZero' {x : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "Fields::is_zero" [.field x] h r h' cs) :
    r = .field (if x = 0 then 1 else 0) ∧ h' = h := by
  rcases «Fields::is_zero».obs ev with ⟨hv, rfl, rfl, -⟩ | ⟨hne, rfl, rfl, -⟩
  · have hx : x = 0 := Value.field.inj hv
    exact ⟨by simp [hx], rfl⟩
  · have hx : x ≠ 0 := fun e => hne (by rw [e])
    exact ⟨by simp [hx], rfl⟩

theorem sub15_eq_zero {n : Nat} (hn : n < 1024) : ((n : F) - 15 = 0) ↔ n = 15 := by
  rw [sub_eq_zero]
  constructor
  · intro e
    exact IxVM.natCast_inj (b := 15) hn (by omega) (by simpa using e)
  · rintro rfl
    simp

theorem cast_eq_zero {n : Nat} (hn : n < 1024) : ((n : F) = 0) ↔ n = 0 := by
  constructor
  · intro e
    exact IxVM.natCast_inj (b := 0) hn (by omega) (by simpa using e)
  · rintro rfl
    simp

/-- `compress_init` with its flags given as a word. -/
theorem compress_init_spec' {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block} {c : UInt64}
    {len : Nat} {fl : UInt32} (hlen : len < 256) (hfl : fl.toNat < 256) {r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "Blake3::compress_init"
      [vecV cv, vecV m, u64v c, .field (len : F), .field (fl.toNat : F)] h r h' cs) :
    r = vecV (Blake3.Pure.compress cv m c len.toUInt32 fl) ∧ h' = h := by
  obtain ⟨rfl, rfl⟩ := compress_init_spec hlen hfl ev
  exact ⟨by rw [toUInt32_toNat], rfl⟩

/-- The short path of `hash_blocks`: fewer than 64 bytes left, so the byte loop finishes. -/
theorem hb_short {bytes : List UInt8} {n : Nat} {c : UInt64} {cv : Blake3.Pure.CV}
    {layer : List Blake3.Pure.CV} {inp ccp cvp lp r : SourceValue F} {h h' m2 m51 : Heap F}
    {cs13 cs33 : List (Call F)} {v39 : SourceValue F}
    (hn : n ≤ 15) (hs : Stream h bytes inp) (hcc : loadValue h ccp = .ok (u64v c))
    (hcv : loadValue h cvp = .ok (vecV cv)) (hl : Stack h layer.reverse lp)
    (ev15 : ObsFn W "Blake3::take_block" [inp] h (.construct "Blake3::BlockRead" "Short" []) m2 cs13)
    (hm59 : m51 = m2 ++ [.construct Names.«Lists::Node<Field>» "Nil" []])
    (op82 : evalBinOp .mul ((.field 64) : SourceValue F) (.field (n : F)) = .ok v39)
    (ev35 : ObsFn W "Blake3::compress_chunks" [inp, .ptr (.enum Names.«Lists::Node<Field>») m2.length,
      .field 0, v39, ccp, cvp, lp] m51 r h' cs33) :
    Heap.Extends h h' ∧ Stack h' (Aiur.Library.Blake3.hashBlocks bytes n c cv layer).reverse r := by
  obtain ⟨hm2, hsr⟩ := take_block_spec hs ev15
  subst m2
  rcases hsr with ⟨hlt, -⟩ | ⟨hle, tail, he, -⟩
  · subst hm59
    obtain rfl := binop_mul op82
    rw [show (64 : F) * (n : F) = ((64 * n : Nat) : F) by push_cast; ring,
      show (0 : F) = ((0 : Nat) : F) by simp] at ev35
    obtain ⟨ext2, hst⟩ := compress_chunks_spec bytes [] (k := 0) (j := 64 * n) (c := c) (cv := cv)
      (layer := layer) (by omega) (by omega) (by omega) rfl
      (by exact hs.mono (Heap.Extends.snoc _ _)) (by exact stream_nil_snoc h)
      (by exact loadValue_extend (Heap.Extends.snoc _ _) hcc)
      (by exact loadValue_extend (Heap.Extends.snoc _ _) hcv)
      (by exact hl.mono (Heap.Extends.snoc _ _)) ev35
    refine ⟨(Heap.Extends.snoc _ _).trans ext2, ?_⟩
    rw [Aiur.Library.Blake3.hashBlocks_short bytes n c cv layer hlt,
      Aiur.Library.Blake3.compressChunks_tail c cv layer bytes [] 0 (64 * n) (by omega)]
    exact hst
  · simp at he

theorem extends3 (h : Heap F) (a b d : SourceValue F) : Heap.Extends h (h ++ [a] ++ [b] ++ [d]) :=
  ⟨[a, b, d], by simp⟩

/-- The specification of `hash_blocks` on a byte list (see `hash_blocks_spec`). -/
def HBSpec (bytes : List UInt8) : Prop :=
  ∀ {n : Nat} {c : UInt64} {cv : Blake3.Pure.CV} {layer : List Blake3.Pure.CV}
    {inp ccp cvp lp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    n ≤ 15 → Stream h bytes inp → loadValue h ccp = .ok (u64v c) →
    loadValue h cvp = .ok (vecV cv) → Stack h layer.reverse lp →
    ObsFn W "Blake3::hash_blocks" [inp, .field (n : F), ccp, cvp, lp] h r h' cs →
    Heap.Extends h h' ∧ Stack h' (Aiur.Library.Blake3.hashBlocks bytes n c cv layer).reverse r

/-- One row of `hash_blocks`, given the specification on shorter inputs. -/
theorem hb_core (bytes : List UInt8)
    (ih : ∀ b : List UInt8, b.length < bytes.length → HBSpec b) : HBSpec bytes := by
  intro n c cv layer inp ccp cvp lp r h h' cs hn hs hcc hcv hl ev
  rcases hb_obs ev with
    ⟨m2, cs13, cs33, v39, m51, ev15, hm59, op82, ev35, -⟩ |
    ⟨m2, cs13, x_block, x_rest, m177, cs179, v185, m186, cs196, v199, v215, m216, cs226, v237,
      x245, y246, v273, m274, y282, cs293, v296, v307, x315, y316, x323, y324, v361, m362, cs372,
      v375, v377, ev15, sg184, op213, ev198, ev228, op260, op270, op252, ld305, ev295, op288,
      op338, op348, op330, op358, op322, ld388, ld405, ev374, he464, hm463, -⟩ |
    ⟨m2, cs13, x_block, x_rest, v176, m177, cs179, m186, cs196, v199, v215, m216, cs226, v237,
      x245, y246, v273, m274, y282, cs293, v296, v307, x315, y316, x323, y324, v361, m362, cs372,
      v375, v377, v498, m499, cs509, cs515, m537, v542, m543, cs549, v552, m564, m575, ev15,
      sg184, op213, ev198, ev228, op260, op270, op252, ld305, ev295, op288, op338, op348, op330,
      op358, op322, ld388, ld405, ev374, ev511, hm545, ld561, ev551, hm572, hm583, ev517, -, hne1⟩ |
    ⟨m2, cs13, x_block, x_rest, v176, m177, cs179, v185, m186, cs196, v199, v215, m216, cs226,
      v237, x245, y246, v273, m274, y282, cs293, v296, v307, x315, y316, x323, y324, v361, m362,
      cs372, v375, v377, cs619, v623, m657, ev15, sg184, op213, ev198, ev228, op260, op270, op252,
      ld305, ev295, op288, op338, op348, op330, op358, op322, ld388, ld405, ev374, op647, hm665,
      ev621, -, hne1, hne2⟩
  · exact hb_short hn hs hcc hcv hl ev15 hm59 op82 ev35
  · -- the last block of the input (64 bytes left)
    obtain ⟨hm2, hsr⟩ := take_block_spec hs ev15
    subst m2
    rcases hsr with ⟨-, he⟩ | ⟨hle, tail, he, htail⟩
    · simp at he
    obtain ⟨-, -, hargs⟩ := Value.construct.inj he
    obtain ⟨rfl, hargs2⟩ := List.cons.inj hargs
    obtain ⟨rfl, -⟩ := List.cons.inj hargs2
    have hempty : bytes.drop 64 = [] := by
      rcases sg184 with ⟨ld158, -, -, -⟩ | ⟨v147, ld158, hne169, he173, -, -⟩
      · rcases stream_inv htail ld158 with ⟨he0, -⟩ | ⟨x, xs, tl, -, hv, -⟩
        · exact he0
        · simp at hv
      · exact absurd (Value.field.inj he173) one_ne_zero
    have hm177 : m177 = h := by
      rcases sg184 with ⟨-, -, hm, -⟩ | ⟨-, -, -, -, hm, -⟩ <;> exact hm
    subst m177
    have hlen : bytes.length = 64 := by
      have := congrArg List.length hempty
      simp at this
      omega
    obtain rfl := binop_sub op213
    obtain ⟨rfl, hm186⟩ := fields_isZero' ev198
    subst m186
    obtain ⟨rfl, hm216⟩ := fields_isZero' ev228
    subst m216
    obtain rfl := binop_add op260
    obtain rfl := binop_mul op270
    obtain rfl := binop_sub op252
    obtain rfl := ok_inj (hcc.symm.trans ld305)
    obtain ⟨rfl, hm274⟩ := u64_isZero ev295
    subst m274
    obtain rfl := binop_mul op288
    obtain rfl := binop_mul op338
    obtain rfl := binop_mul op348
    obtain rfl := binop_add op330
    obtain rfl := binop_mul op358
    have hv307 := binop_add op322
    obtain rfl := ok_inj (hcv.symm.trans ld388)
    obtain rfl := ok_inj (hcc.symm.trans ld405)
    have hfl : v307 = .field (((Aiur.Library.Blake3.blockFlags (decide (n = 0)) true
        (decide (c = 0))).toNat : Nat) : F) := by
      rw [hv307, flags_general]
      congr 1
      simp only [cast_eq_zero (by omega : n < 1024)]
      by_cases hn0 : n = 0 <;> by_cases hc0 : c = 0 <;> simp [hn0, hc0] <;> ring
    subst hfl
    rw [show (64 : F) = ((64 : Nat) : F) by simp] at ev374
    obtain ⟨rfl, hm362⟩ := compress_init_spec' (len := 64) (by norm_num) (flags_lt _ _ _) ev374
    subst m362
    subst he464 hm463
    refine ⟨Heap.Extends.snoc _ _, ?_⟩
    rw [Aiur.Library.Blake3.hashBlocks_last_block bytes n c cv layer hlen, List.reverse_append,
      List.reverse_singleton, List.singleton_append,
      List.take_of_length_le (by omega : bytes.length ≤ 64)]
    exact stack_push_snoc hl
  · -- a chunk's last block, more input after it: push the chunk's value, start the next chunk
    obtain ⟨hm2, hsr⟩ := take_block_spec hs ev15
    subst m2
    rcases hsr with ⟨-, he⟩ | ⟨hle, tail, he, htail⟩
    · simp at he
    obtain ⟨-, -, hargs⟩ := Value.construct.inj he
    obtain ⟨rfl, hargs2⟩ := List.cons.inj hargs
    obtain ⟨rfl, -⟩ := List.cons.inj hargs2
    rcases sg184 with ⟨ld158, he166, hm177, -⟩ | ⟨v147, ld158, hne169, he173, hm177, -⟩
    · exact absurd he166 hne1
    subst he173 m177
    have hmore : bytes.drop 64 ≠ [] := by
      intro hnil
      rcases stream_inv htail ld158 with ⟨-, hv⟩ | ⟨x, xs, tl, hc, -, -⟩
      · exact hne169 [] rfl hv
      · rw [hnil] at hc
        cases hc
    have hlong : 64 < bytes.length := by
      by_contra hc
      apply hmore
      rw [List.drop_eq_nil_iff]
      omega
    obtain rfl := binop_sub op213
    obtain ⟨h15, hm186⟩ := fields_isZero' ev198
    subst m186
    have hn15 : n = 15 := by
      by_contra hne
      have hc15 : ¬ ((n : F) - 15 = 0) := by
        rw [sub15_eq_zero (by omega : n < 1024)]
        exact hne
      simp only [hc15, ↓reduceIte] at h15
      exact one_ne_zero (Value.field.inj h15)
    obtain ⟨rfl, hm216⟩ := fields_isZero' ev228
    subst m216
    obtain rfl := binop_add op260
    obtain rfl := binop_mul op270
    obtain rfl := binop_sub op252
    obtain rfl := ok_inj (hcc.symm.trans ld305)
    obtain ⟨rfl, hm274⟩ := u64_isZero ev295
    subst m274
    obtain rfl := binop_mul op288
    obtain rfl := binop_mul op338
    obtain rfl := binop_mul op348
    obtain rfl := binop_add op330
    obtain rfl := binop_mul op358
    have hv307 := binop_add op322
    obtain rfl := ok_inj (hcv.symm.trans ld388)
    obtain rfl := ok_inj (hcc.symm.trans ld405)
    have hfl : v307 = .field (((Aiur.Library.Blake3.blockFlags false true false).toNat : Nat) : F) := by
      have h0 : ¬ ((n : F) = 0) := by
        rw [cast_eq_zero (by omega : n < 1024)]
        omega
      rw [hv307, flags_general]
      congr 1
      simp only [h0, ↓reduceIte]
      norm_num
    subst hfl
    rw [show (64 : F) = ((64 : Nat) : F) by simp] at ev374
    obtain ⟨rfl, hm362⟩ := compress_init_spec' (len := 64) (by norm_num) (flags_lt _ _ _) ev374
    subst m362
    obtain ⟨rfl, hm499⟩ := iv_src ev511
    subst m499
    obtain rfl := ok_inj (hcc.symm.trans ld561)
    obtain ⟨rfl, hm543⟩ := u64_wrappingSucc ev551
    subst m543
    subst hm545 hm572 hm583
    rw [show (0 : F) = ((0 : Nat) : F) by simp] at ev517
    have IH := @ih (bytes.drop 64) (by rw [List.length_drop]; omega)
    unfold HBSpec at IH
    obtain ⟨ext2, hres⟩ := IH (n := 0) (c := c + 1) (cv := Blake3.Pure.iv)
      (layer := layer ++ [Blake3.Pure.compress cv (Blake3.Pure.blockWords (bytes.take 64)) c
        (Nat.toUInt32 64) (Aiur.Library.Blake3.blockFlags false true false)])
      (by omega)
      (by exact htail.mono (extends3 _ _ _ _))
      (by
        exact loadValue_extend ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _))
          (loadValue_snoc h _))
      (by exact loadValue_extend (Heap.Extends.snoc _ _) (loadValue_snoc _ _))
      (by
        rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
        exact stack_push_snoc (hl.mono ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _))))
      ev517
    refine ⟨(extends3 _ _ _ _).trans ext2, ?_⟩
    subst hn15
    rw [Aiur.Library.Blake3.hashBlocks_chunk_end bytes c cv layer hlong]
    exact hres
  · -- a block inside a chunk, more input after it
    obtain ⟨hm2, hsr⟩ := take_block_spec hs ev15
    subst m2
    rcases hsr with ⟨-, he⟩ | ⟨hle, tail, he, htail⟩
    · simp at he
    obtain ⟨-, -, hargs⟩ := Value.construct.inj he
    obtain ⟨rfl, hargs2⟩ := List.cons.inj hargs
    obtain ⟨rfl, -⟩ := List.cons.inj hargs2
    rcases sg184 with ⟨ld158, he166, hm177, -⟩ | ⟨v147, ld158, hne169, he173, hm177, -⟩
    · exact absurd he166 hne1
    subst he173 m177
    have hmore : bytes.drop 64 ≠ [] := by
      intro hnil
      rcases stream_inv htail ld158 with ⟨-, hv⟩ | ⟨x, xs, tl, hc, -, -⟩
      · exact hne169 [] rfl hv
      · rw [hnil] at hc
        cases hc
    have hlong : 64 < bytes.length := by
      by_contra hc
      apply hmore
      rw [List.drop_eq_nil_iff]
      omega
    obtain rfl := binop_sub op213
    obtain ⟨rfl, hm186⟩ := fields_isZero' ev198
    subst m186
    have hn15 : n ≠ 15 := by
      intro e
      apply hne2
      rw [e]
      simp
    obtain ⟨rfl, hm216⟩ := fields_isZero' ev228
    subst m216
    obtain rfl := binop_add op260
    obtain rfl := binop_mul op270
    obtain rfl := binop_sub op252
    obtain rfl := ok_inj (hcc.symm.trans ld305)
    obtain ⟨rfl, hm274⟩ := u64_isZero ev295
    subst m274
    obtain rfl := binop_mul op288
    obtain rfl := binop_mul op338
    obtain rfl := binop_mul op348
    obtain rfl := binop_add op330
    obtain rfl := binop_mul op358
    have hv307 := binop_add op322
    obtain rfl := ok_inj (hcv.symm.trans ld388)
    obtain rfl := ok_inj (hcc.symm.trans ld405)
    have hfl : v307 = .field (((Aiur.Library.Blake3.blockFlags (decide (n = 0)) false false).toNat :
        Nat) : F) := by
      rw [hv307, flags_general]
      congr 1
      simp only [cast_eq_zero (by omega : n < 1024), sub15_eq_zero (by omega : n < 1024), hn15]
      by_cases hn0 : n = 0 <;> simp [hn0]
    subst hfl
    rw [show (64 : F) = ((64 : Nat) : F) by simp] at ev374
    obtain ⟨rfl, hm362⟩ := compress_init_spec' (len := 64) (by norm_num) (flags_lt _ _ _) ev374
    subst m362
    obtain rfl := binop_add op647
    subst hm665
    rw [show (n : F) + 1 = ((n + 1 : Nat) : F) by push_cast; ring] at ev621
    have IH := @ih (bytes.drop 64) (by rw [List.length_drop]; omega)
    unfold HBSpec at IH
    obtain ⟨ext2, hres⟩ := IH (n := n + 1) (c := c)
      (cv := Blake3.Pure.compress cv (Blake3.Pure.blockWords (bytes.take 64)) c (Nat.toUInt32 64)
        (Aiur.Library.Blake3.blockFlags (decide (n = 0)) false false))
      (layer := layer) (by omega)
      (by exact htail.mono (Heap.Extends.snoc _ _))
      (by exact loadValue_extend (Heap.Extends.snoc _ _) hcc)
      (by exact loadValue_snoc _ _)
      (by exact hl.mono (Heap.Extends.snoc _ _))
      ev621
    refine ⟨(Heap.Extends.snoc _ _).trans ext2, ?_⟩
    rw [Aiur.Library.Blake3.hashBlocks_step bytes n c cv layer hlong hn15]
    exact hres

theorem hash_blocks_le (N : Nat) : ∀ bytes : List UInt8, bytes.length ≤ N → HBSpec bytes := by
  induction N with
  | zero =>
    intro bytes hb
    exact hb_core bytes (fun b hlt => absurd hlt (by omega))
  | succ N ih =>
    intro bytes hb
    exact hb_core bytes (fun b hlt => ih b (by omega))

/-- **`Blake3::hash_blocks`** computes `Aiur.Library.Blake3.hashBlocks`: a block per row while 64
bytes are left, then the byte loop, pushing every chunk's chaining value on the layer stack. -/
theorem hash_blocks_spec (bytes : List UInt8) {n : Nat} {c : UInt64} {cv : Blake3.Pure.CV}
    {layer : List Blake3.Pure.CV} {inp ccp cvp lp r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hn : n ≤ 15) (hs : Stream h bytes inp)
    (hcc : loadValue h ccp = .ok (u64v c)) (hcv : loadValue h cvp = .ok (vecV cv))
    (hl : Stack h layer.reverse lp)
    (ev : ObsFn W "Blake3::hash_blocks" [inp, .field (n : F), ccp, cvp, lp] h r h' cs) :
    Heap.Extends h h' ∧ Stack h' (Aiur.Library.Blake3.hashBlocks bytes n c cv layer).reverse r := by
  exact hash_blocks_le bytes.length bytes (Nat.le_refl _) hn hs hcc hcv hl ev

end IxVM.Refinement.L1
