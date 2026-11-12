import IxVMRefinement.Lib.WordSub

/-! # Word library functions that read a hint, over observed derivations

`UInt64::from_field` decomposes a field element into bytes from a hint (`bytes_le`) and
checks the decomposition: each pair of bytes is range-checked (`UInt8::from_fields`), and
the bytes must recompose to the value through `UInt64::to_field`, which also bounds it below
`2^56`. Whatever the hint, a derivation returns the bytes of the value. The generator emits
no path lemma for it (its first `let` destructures the hint's array); the inversion is
written out here, with each byte range read off `UInt8::from_fields`. -/

namespace IxVM.Refinement.Lib

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxVM.Refinement.Obs (W)
open IxVM (F)

set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

set_option maxHeartbeats 2000000 in
/-- **`UInt64::from_field(x)`**: a derivation exists only on a field element below `2^56`, and
returns its eight bytes; no allocation. -/
theorem u64_from_field_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt64::from_field" [x] h r h' cs) :
    ∃ n : Nat, n < 72057594037927936 ∧ x = .field (n : F) ∧ r = TagN.u64Value n ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.UInt64.from_field.lookup
    (by simp [IxVM.UInt64.from_field, ControlLower.hasControl]) ev
  simp only [IxVM.UInt64.from_field] at d0
  -- `let [h0, …, h7] = hint::<[Field; 8]>("bytes_le", value)`
  obtain ⟨v1, m2, bs3, c4, c5, d6, mt7, d8, rfl⟩ := d0.letValue_inv
  obtain ⟨x9, k10, d11, ty12, rfl⟩ := d6.hint_inv
  obtain ⟨l13, rfl, rfl⟩ := d11.var_inv
  simp at l13
  subst l13
  obtain ⟨vs14, hv15, -, ml16⟩ := matchPattern_array_inv mt7
  obtain ⟨y0, vs17, b18, b19, rfl, mt20, ml21, rfl⟩ := matchListWith_cons_inv ml16
  obtain rfl := matchPattern_bind_inv mt20
  obtain ⟨y1, vs22, b23, b24, rfl, mt25, ml26, rfl⟩ := matchListWith_cons_inv ml21
  obtain rfl := matchPattern_bind_inv mt25
  obtain ⟨y2, vs27, b28, b29, rfl, mt30, ml31, rfl⟩ := matchListWith_cons_inv ml26
  obtain rfl := matchPattern_bind_inv mt30
  obtain ⟨y3, vs32, b33, b34, rfl, mt35, ml36, rfl⟩ := matchListWith_cons_inv ml31
  obtain rfl := matchPattern_bind_inv mt35
  obtain ⟨y4, vs37, b38, b39, rfl, mt40, ml41, rfl⟩ := matchListWith_cons_inv ml36
  obtain rfl := matchPattern_bind_inv mt40
  obtain ⟨y5, vs42, b43, b44, rfl, mt45, ml46, rfl⟩ := matchListWith_cons_inv ml41
  obtain rfl := matchPattern_bind_inv mt45
  obtain ⟨y6, vs47, b48, b49, rfl, mt50, ml51, rfl⟩ := matchListWith_cons_inv ml46
  obtain rfl := matchPattern_bind_inv mt50
  obtain ⟨y7, vs52, b53, b54, rfl, mt55, ml56, rfl⟩ := matchListWith_cons_inv ml51
  obtain rfl := matchPattern_bind_inv mt55
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml56
  -- `let (b0, b1) = UInt8::from_fields(h0, h1)`
  obtain ⟨v60, m61, bs62, c63, c64, d65, mt66, d67, rfl⟩ := d8.letValue_inv
  obtain ⟨vs68, m69, c70, cs71, a72, ev73, rfl⟩ := d65.call_inv
  rw [instanceName_plain_some] at ev73
  obtain ⟨u74, us75, m76, c77, c78, rfl, d79, a80, rfl⟩ := a72.cons_inv
  obtain ⟨l81, rfl, rfl⟩ := d79.var_inv
  simp at l81
  subst l81
  obtain ⟨u82, us83, m84, c85, c86, rfl, d87, a88, rfl⟩ := a80.cons_inv
  obtain ⟨l89, rfl, rfl⟩ := d87.var_inv
  simp at l89
  subst l89
  obtain ⟨rfl, rfl, rfl⟩ := a88.nil_inv
  obtain ⟨ys90, rfl, -, ml91⟩ := matchPattern_tuple_inv mt66
  obtain ⟨z92, zs93, b94, b95, rfl, mt96, ml97, rfl⟩ := matchListWith_cons_inv ml91
  obtain rfl := matchPattern_bind_inv mt96
  obtain ⟨z98, zs99, b100, b101, rfl, mt102, ml103, rfl⟩ := matchListWith_cons_inv ml97
  obtain rfl := matchPattern_bind_inv mt102
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml103
  obtain ⟨hr104, rfl, n0, n1, hn0, hn1, hy0, hy1⟩ := KernelLevels.u8FromFields_eval_inv ev73.erase
  injection hr104 with hr104
  injection hr104 with hz92 hr104
  injection hr104 with hz98 _
  subst hz92 hz98
  subst hy0 hy1
  -- `let (b2, b3) = UInt8::from_fields(h2, h3)`
  obtain ⟨v110, m111, bs112, c113, c114, d115, mt116, d117, rfl⟩ := d67.letValue_inv
  obtain ⟨vs118, m119, c120, cs121, a122, ev123, rfl⟩ := d115.call_inv
  rw [instanceName_plain_some] at ev123
  obtain ⟨u124, us125, m126, c127, c128, rfl, d129, a130, rfl⟩ := a122.cons_inv
  obtain ⟨l131, rfl, rfl⟩ := d129.var_inv
  simp at l131
  subst l131
  obtain ⟨u132, us133, m134, c135, c136, rfl, d137, a138, rfl⟩ := a130.cons_inv
  obtain ⟨l139, rfl, rfl⟩ := d137.var_inv
  simp at l139
  subst l139
  obtain ⟨rfl, rfl, rfl⟩ := a138.nil_inv
  obtain ⟨ys140, rfl, -, ml141⟩ := matchPattern_tuple_inv mt116
  obtain ⟨z142, zs143, b144, b145, rfl, mt146, ml147, rfl⟩ := matchListWith_cons_inv ml141
  obtain rfl := matchPattern_bind_inv mt146
  obtain ⟨z148, zs149, b150, b151, rfl, mt152, ml153, rfl⟩ := matchListWith_cons_inv ml147
  obtain rfl := matchPattern_bind_inv mt152
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml153
  obtain ⟨hr154, rfl, n2, n3, hn2, hn3, hy2, hy3⟩ := KernelLevels.u8FromFields_eval_inv ev123.erase
  injection hr154 with hr154
  injection hr154 with hz142 hr154
  injection hr154 with hz148 _
  subst hz142 hz148
  subst hy2 hy3
  -- `let (b4, b5) = UInt8::from_fields(h4, h5)`
  obtain ⟨v160, m161, bs162, c163, c164, d165, mt166, d167, rfl⟩ := d117.letValue_inv
  obtain ⟨vs168, m169, c170, cs171, a172, ev173, rfl⟩ := d165.call_inv
  rw [instanceName_plain_some] at ev173
  obtain ⟨u174, us175, m176, c177, c178, rfl, d179, a180, rfl⟩ := a172.cons_inv
  obtain ⟨l181, rfl, rfl⟩ := d179.var_inv
  simp at l181
  subst l181
  obtain ⟨u182, us183, m184, c185, c186, rfl, d187, a188, rfl⟩ := a180.cons_inv
  obtain ⟨l189, rfl, rfl⟩ := d187.var_inv
  simp at l189
  subst l189
  obtain ⟨rfl, rfl, rfl⟩ := a188.nil_inv
  obtain ⟨ys190, rfl, -, ml191⟩ := matchPattern_tuple_inv mt166
  obtain ⟨z192, zs193, b194, b195, rfl, mt196, ml197, rfl⟩ := matchListWith_cons_inv ml191
  obtain rfl := matchPattern_bind_inv mt196
  obtain ⟨z198, zs199, b200, b201, rfl, mt202, ml203, rfl⟩ := matchListWith_cons_inv ml197
  obtain rfl := matchPattern_bind_inv mt202
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml203
  obtain ⟨hr204, rfl, n4, n5, hn4, hn5, hy4, hy5⟩ := KernelLevels.u8FromFields_eval_inv ev173.erase
  injection hr204 with hr204
  injection hr204 with hz192 hr204
  injection hr204 with hz198 _
  subst hz192 hz198
  subst hy4 hy5
  -- `let (b6, b7) = UInt8::from_fields(h6, h7)`
  obtain ⟨v210, m211, bs212, c213, c214, d215, mt216, d217, rfl⟩ := d167.letValue_inv
  obtain ⟨vs218, m219, c220, cs221, a222, ev223, rfl⟩ := d215.call_inv
  rw [instanceName_plain_some] at ev223
  obtain ⟨u224, us225, m226, c227, c228, rfl, d229, a230, rfl⟩ := a222.cons_inv
  obtain ⟨l231, rfl, rfl⟩ := d229.var_inv
  simp at l231
  subst l231
  obtain ⟨u232, us233, m234, c235, c236, rfl, d237, a238, rfl⟩ := a230.cons_inv
  obtain ⟨l239, rfl, rfl⟩ := d237.var_inv
  simp at l239
  subst l239
  obtain ⟨rfl, rfl, rfl⟩ := a238.nil_inv
  obtain ⟨ys240, rfl, -, ml241⟩ := matchPattern_tuple_inv mt216
  obtain ⟨z242, zs243, b244, b245, rfl, mt246, ml247, rfl⟩ := matchListWith_cons_inv ml241
  obtain rfl := matchPattern_bind_inv mt246
  obtain ⟨z248, zs249, b250, b251, rfl, mt252, ml253, rfl⟩ := matchListWith_cons_inv ml247
  obtain rfl := matchPattern_bind_inv mt252
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml253
  obtain ⟨hr254, rfl, n6, n7, hn6, hn7, hy6, hy7⟩ := KernelLevels.u8FromFields_eval_inv ev223.erase
  injection hr254 with hr254
  injection hr254 with hz242 hr254
  injection hr254 with hz248 _
  subst hz242 hz248
  subst hy6 hy7
  -- `let bytes = [b0, …, b7]`
  obtain ⟨v260, m261, bs262, c263, c264, d265, mt266, d267, rfl⟩ := d217.letValue_inv
  obtain ⟨vals268, a269, rfl⟩ := d265.array_inv
  obtain ⟨w270, ws271, m272, c273, c274, rfl, d275, a276, rfl⟩ := a269.cons_inv
  obtain ⟨l277, rfl, rfl⟩ := d275.var_inv
  simp at l277
  subst l277
  obtain ⟨w278, ws279, m280, c281, c282, rfl, d283, a284, rfl⟩ := a276.cons_inv
  obtain ⟨l285, rfl, rfl⟩ := d283.var_inv
  simp at l285
  subst l285
  obtain ⟨w286, ws287, m288, c289, c290, rfl, d291, a292, rfl⟩ := a284.cons_inv
  obtain ⟨l293, rfl, rfl⟩ := d291.var_inv
  simp at l293
  subst l293
  obtain ⟨w294, ws295, m296, c297, c298, rfl, d299, a300, rfl⟩ := a292.cons_inv
  obtain ⟨l301, rfl, rfl⟩ := d299.var_inv
  simp at l301
  subst l301
  obtain ⟨w302, ws303, m304, c305, c306, rfl, d307, a308, rfl⟩ := a300.cons_inv
  obtain ⟨l309, rfl, rfl⟩ := d307.var_inv
  simp at l309
  subst l309
  obtain ⟨w310, ws311, m312, c313, c314, rfl, d315, a316, rfl⟩ := a308.cons_inv
  obtain ⟨l317, rfl, rfl⟩ := d315.var_inv
  simp at l317
  subst l317
  obtain ⟨w318, ws319, m320, c321, c322, rfl, d323, a324, rfl⟩ := a316.cons_inv
  obtain ⟨l325, rfl, rfl⟩ := d323.var_inv
  simp at l325
  subst l325
  obtain ⟨w326, ws327, m328, c329, c330, rfl, d331, a332, rfl⟩ := a324.cons_inv
  obtain ⟨l333, rfl, rfl⟩ := d331.var_inv
  simp at l333
  subst l333
  obtain ⟨rfl, rfl, rfl⟩ := a332.nil_inv
  obtain rfl := matchPattern_bind_inv mt266
  -- `constrain_eq!(to_field(bytes), value)`
  obtain ⟨v340, m341, bs342, c343, c344, d345, mt346, d347, rfl⟩ := d267.letValue_inv
  obtain ⟨vs348, a349, ap350⟩ := d345.builtin_inv
  obtain ⟨t351, ts352, m353, c354, c355, rfl, d356, a357, rfl⟩ := a349.cons_inv
  obtain ⟨vs358, m359, c360, cs361, a362, ev363, rfl⟩ := d356.call_inv
  rw [instanceName_plain_some] at ev363
  obtain ⟨q364, qs365, m366, c367, c368, rfl, d369, a370, rfl⟩ := a362.cons_inv
  obtain ⟨l371, rfl, rfl⟩ := d369.var_inv
  simp at l371
  subst l371
  obtain ⟨rfl, rfl, rfl⟩ := a370.nil_inv
  obtain ⟨t372, ts373, m374, c375, c376, rfl, d377, a378, rfl⟩ := a357.cons_inv
  obtain ⟨l379, rfl, rfl⟩ := d377.var_inv
  simp at l379
  subst l379
  obtain ⟨rfl, rfl, rfl⟩ := a378.nil_inv
  obtain ⟨heq380, rfl⟩ := Builtin.assertEq_inv ap350
  obtain rfl := matchPattern_wildcard_inv mt346
  -- `bytes`
  obtain ⟨l381, rfl, rfl⟩ := d347.var_inv
  simp at l381
  subst l381
  -- the bytes recompose to the value, below `2^56`
  have hlt := leBytes8_lt hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn7
  have hval := u64Value_leBytes8 hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn7
  have hrep := repU64_ofNatLT h hlt
  rw [hval] at hrep
  obtain ⟨h56, ht, rfl⟩ := u64_to_field_spec hrep ev363
  rw [UInt64.toNat_ofNatLT] at h56 ht
  subst ht
  exact ⟨leBytes8 n0 n1 n2 n3 n4 n5 n6 n7, h56, heq380.symm, hval.symm, rfl⟩

/-! ## `UInt64::mul_column` -/

set_option maxHeartbeats 1000000 in
/-- **Every derivation of `UInt64::mul_column` is a run of its mirror**: the hint's five
bytes are range-checked and must recompose to the column value, which is therefore below
`2^40` and is returned as its low two bytes and next three bytes. -/
theorem mulColumn_complete : Mirrors.«UInt64::mul_column».Complete := by
  intro x h h' r ev
  obtain ⟨cs, ob⟩ := ev.observe
  rcases Obs.«UInt64::mul_column».obs ob with
    ⟨k10, m15, cs25, v28, v29, xr0, xr1, m64, cs74, v77, v78, xc0, xc1, m113, cs123, v126, xc2,
      w147, v170, m179, x184, y185, m186, x192, y193, m194, cs203, y215, cs225, y237, x244, y245,
      m246, x252, y253, m254, cs263, y275, cs285, y297, cs307, ty12, pr38, pr48, ev27, pr87, pr97,
      ev76, pr136, ev125, ev205, ev227, op221, op199, ev265, ev287, op281, op259, ev309, op303,
      op251, op243, op191, heq318, rfl, rfl, -⟩
  obtain ⟨hr27, rfl, a0, a1, ha0, ha1, rfl, rfl⟩ := KernelLevels.u8FromFields_eval_inv ev27.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr27
  obtain ⟨rfl, rfl⟩ := hr27
  obtain ⟨hr76, rfl, c0, c1, hc0, hc1, rfl, rfl⟩ := KernelLevels.u8FromFields_eval_inv ev76.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr76
  obtain ⟨rfl, rfl⟩ := hr76
  obtain ⟨hr125, rfl, c2, z, hc2, hz, rfl, hz0⟩ := KernelLevels.u8FromFields_eval_inv ev125.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr125
  obtain ⟨rfl, rfl⟩ := hr125
  obtain ⟨rfl, rfl, -⟩ := Obs.«UInt8::to_field».obs ev205
  obtain ⟨rfl, rfl, -⟩ := Obs.«UInt8::to_field».obs ev227
  obtain ⟨rfl, rfl, -⟩ := Obs.«UInt8::to_field».obs ev265
  obtain ⟨rfl, rfl, -⟩ := Obs.«UInt8::to_field».obs ev287
  obtain ⟨rfl, rfl, -⟩ := Obs.«UInt8::to_field».obs ev309
  simp only [evalBinOp, Except.ok.injEq] at op221
  subst op221
  simp only [evalBinOp, Except.ok.injEq] at op199
  subst op199
  simp only [evalBinOp, Except.ok.injEq] at op281
  subst op281
  simp only [evalBinOp, Except.ok.injEq] at op259
  subst op259
  simp only [evalBinOp, Except.ok.injEq] at op303
  subst op303
  simp only [evalBinOp, Except.ok.injEq] at op251
  subst op251
  simp only [evalBinOp, Except.ok.injEq] at op243
  subst op243
  simp only [evalBinOp, Except.ok.injEq] at op191
  subst op191
  subst heq318
  have hN : (((a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2) : Nat)) : F) =
      (a0 : F) + 256 * (a1 : F) + 65536 * ((c0 : F) + 256 * (c1 : F) + 65536 * (c2 : F)) := by
    push_cast <;> ring
  have hlt : a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2) < 1099511627776 := by omega
  have hval : (((a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2) : Nat)) : F).val =
      a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2) :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have d0 : (a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2)) % 256 = a0 := by omega
  have d1 : (a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2)) / 256 % 256 = a1 := by omega
  have d2 : (a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2)) / 65536 % 256 = c0 := by
    omega
  have d3 : (a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2)) / 16777216 % 256 = c1 := by
    omega
  have d4 : (a0 + 256 * a1 + 65536 * (c0 + 256 * c1 + 65536 * c2)) / 4294967296 % 256 = c2 := by
    omega
  refine ⟨1, fun k hk => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [← hN]
  simp only [Mirrors.«UInt64::mul_column», hval, hlt, ↓reduceIte, d0, d1, d2, d3, d4]

end IxVM.Refinement.Lib
