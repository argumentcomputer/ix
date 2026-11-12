import IxVMRefinement.Obs.Bytes
import IxVMRefinement.Obs.UInt8
import IxVMRefinement.Core.Obs
import Aiur.Library.Bytes.Correctness
import Aiur.Library.U64.Goldilocks
import Mathlib.Tactic.IntervalCases

/-! # `Bytes::address_eq`, over observed derivations

`address_eq(a, b)` on two represented addresses answers `1` exactly when they are equal,
and allocates nothing (`address_eq_spec`). The derivation computes the hand-written
model `Aiur.Library.Bytes.addressEq` (the first byte, then `address_eq_tail`'s five packed
limbs), which `Aiur.Library.Bytes.address_eq_spec` decides. The generator emits no path
lemma for `Bytes::address_eq_tail` (its variable lookups are costly); `tail_eval` is that
inversion written out, over arbitrary field elements for the 31 bytes it reads. -/

namespace IxVM.Refinement.Lib

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxVM.Refinement.Obs (W)
open IxVM (F)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The type of `Bytes::Address`: 32 field elements. -/
abbrev addrTy : Aiur.Ty := .tuple (List.replicate 32 .field)

/-- A 7-byte limb packed as `address_eq_tail` packs it, low byte first. -/
def pack7 (x0 x1 x2 x3 x4 x5 x6 : F) : F :=
  ((((((x6 * 256 + x5) * 256 + x4) * 256 + x3) * 256 + x2) * 256 + x1) * 256 + x0)

/-- The 3-byte limb, low byte first. -/
def pack3 (x0 x1 x2 : F) : F := (x2 * 256 + x1) * 256 + x0

/-- The value `Bytes::address_eq_tail` computes from the two addresses' last 31 bytes (as
field elements): its five packed limbs compared in order. -/
def tailModel (u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : F) : F :=
  if pack7 u1 u2 u3 u4 u5 u6 u7 - pack7 v1 v2 v3 v4 v5 v6 v7 = 0 then
    if pack7 u8 u9 u10 u11 u12 u13 u14 - pack7 v8 v9 v10 v11 v12 v13 v14 = 0 then
      if pack7 u15 u16 u17 u18 u19 u20 u21 - pack7 v15 v16 v17 v18 v19 v20 v21 = 0 then
        if pack7 u22 u23 u24 u25 u26 u27 u28 - pack7 v22 v23 v24 v25 v26 v27 v28 = 0 then
          if pack3 u29 u30 u31 - pack3 v29 v30 v31 = 0 then
            1
          else 0
        else 0
      else 0
    else 0
  else 0

/-- **`Bytes::address_eq_tail` on two loaded addresses computes `tailModel`** of their last
31 bytes, and allocates nothing. The generator skips this function (its variable
lookups are costly); the inversion below is its script, written out. -/
theorem tail_eval {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {w0 z0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : F}
    (hx : loadValue h x = .ok (.tuple [.field w0, .field u1, .field u2, .field u3, .field u4, .field u5, .field u6, .field u7, .field u8, .field u9, .field u10, .field u11, .field u12, .field u13, .field u14, .field u15, .field u16, .field u17, .field u18, .field u19, .field u20, .field u21, .field u22, .field u23, .field u24, .field u25, .field u26, .field u27, .field u28, .field u29, .field u30, .field u31]))
    (hy : loadValue h y = .ok (.tuple [.field z0, .field v1, .field v2, .field v3, .field v4, .field v5, .field v6, .field v7, .field v8, .field v9, .field v10, .field v11, .field v12, .field v13, .field v14, .field v15, .field v16, .field v17, .field v18, .field v19, .field v20, .field v21, .field v22, .field v23, .field v24, .field v25, .field v26, .field v27, .field v28, .field v29, .field v30, .field v31]))
    (ev : ObsFn W "Bytes::address_eq_tail" [x, y] h r h' cs) :
    r = .field (tailModel u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31) ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.Bytes.address_eq_tail.lookup
    (by simp [IxVM.Bytes.address_eq_tail, ControlLower.hasControl]) ev
  simp only [IxVM.Bytes.address_eq_tail] at d0
  obtain ⟨qv1, qm2, qbs3, qc4, qc5, qd6, qmt7, qd8, rfl⟩ := d0.letValue_inv
  obtain ⟨qp9, qd10, qld11⟩ := qd6.load_inv
  obtain ⟨ql12, rfl, rfl⟩ := qd10.var_inv
  simp at ql12
  subst ql12
  obtain ⟨qvs13, qhv14, -, qml15⟩ := matchPattern_array_inv qmt7
  subst qhv14
  obtain ⟨qw16, qvs17, qb18, qb19, rfl, qmt20, qml21, rfl⟩ := matchListWith_cons_inv qml15
  obtain rfl := matchPattern_wildcard_inv qmt20
  obtain ⟨xa1, qvs22, qb23, qb24, rfl, qmt25, qml26, rfl⟩ := matchListWith_cons_inv qml21
  obtain rfl := matchPattern_bind_inv qmt25
  obtain ⟨xa2, qvs27, qb28, qb29, rfl, qmt30, qml31, rfl⟩ := matchListWith_cons_inv qml26
  obtain rfl := matchPattern_bind_inv qmt30
  obtain ⟨xa3, qvs32, qb33, qb34, rfl, qmt35, qml36, rfl⟩ := matchListWith_cons_inv qml31
  obtain rfl := matchPattern_bind_inv qmt35
  obtain ⟨xa4, qvs37, qb38, qb39, rfl, qmt40, qml41, rfl⟩ := matchListWith_cons_inv qml36
  obtain rfl := matchPattern_bind_inv qmt40
  obtain ⟨xa5, qvs42, qb43, qb44, rfl, qmt45, qml46, rfl⟩ := matchListWith_cons_inv qml41
  obtain rfl := matchPattern_bind_inv qmt45
  obtain ⟨xa6, qvs47, qb48, qb49, rfl, qmt50, qml51, rfl⟩ := matchListWith_cons_inv qml46
  obtain rfl := matchPattern_bind_inv qmt50
  obtain ⟨xa7, qvs52, qb53, qb54, rfl, qmt55, qml56, rfl⟩ := matchListWith_cons_inv qml51
  obtain rfl := matchPattern_bind_inv qmt55
  obtain ⟨xa8, qvs57, qb58, qb59, rfl, qmt60, qml61, rfl⟩ := matchListWith_cons_inv qml56
  obtain rfl := matchPattern_bind_inv qmt60
  obtain ⟨xa9, qvs62, qb63, qb64, rfl, qmt65, qml66, rfl⟩ := matchListWith_cons_inv qml61
  obtain rfl := matchPattern_bind_inv qmt65
  obtain ⟨xa10, qvs67, qb68, qb69, rfl, qmt70, qml71, rfl⟩ := matchListWith_cons_inv qml66
  obtain rfl := matchPattern_bind_inv qmt70
  obtain ⟨xa11, qvs72, qb73, qb74, rfl, qmt75, qml76, rfl⟩ := matchListWith_cons_inv qml71
  obtain rfl := matchPattern_bind_inv qmt75
  obtain ⟨xa12, qvs77, qb78, qb79, rfl, qmt80, qml81, rfl⟩ := matchListWith_cons_inv qml76
  obtain rfl := matchPattern_bind_inv qmt80
  obtain ⟨xa13, qvs82, qb83, qb84, rfl, qmt85, qml86, rfl⟩ := matchListWith_cons_inv qml81
  obtain rfl := matchPattern_bind_inv qmt85
  obtain ⟨xa14, qvs87, qb88, qb89, rfl, qmt90, qml91, rfl⟩ := matchListWith_cons_inv qml86
  obtain rfl := matchPattern_bind_inv qmt90
  obtain ⟨xa15, qvs92, qb93, qb94, rfl, qmt95, qml96, rfl⟩ := matchListWith_cons_inv qml91
  obtain rfl := matchPattern_bind_inv qmt95
  obtain ⟨xa16, qvs97, qb98, qb99, rfl, qmt100, qml101, rfl⟩ := matchListWith_cons_inv qml96
  obtain rfl := matchPattern_bind_inv qmt100
  obtain ⟨xa17, qvs102, qb103, qb104, rfl, qmt105, qml106, rfl⟩ := matchListWith_cons_inv qml101
  obtain rfl := matchPattern_bind_inv qmt105
  obtain ⟨xa18, qvs107, qb108, qb109, rfl, qmt110, qml111, rfl⟩ := matchListWith_cons_inv qml106
  obtain rfl := matchPattern_bind_inv qmt110
  obtain ⟨xa19, qvs112, qb113, qb114, rfl, qmt115, qml116, rfl⟩ := matchListWith_cons_inv qml111
  obtain rfl := matchPattern_bind_inv qmt115
  obtain ⟨xa20, qvs117, qb118, qb119, rfl, qmt120, qml121, rfl⟩ := matchListWith_cons_inv qml116
  obtain rfl := matchPattern_bind_inv qmt120
  obtain ⟨xa21, qvs122, qb123, qb124, rfl, qmt125, qml126, rfl⟩ := matchListWith_cons_inv qml121
  obtain rfl := matchPattern_bind_inv qmt125
  obtain ⟨xa22, qvs127, qb128, qb129, rfl, qmt130, qml131, rfl⟩ := matchListWith_cons_inv qml126
  obtain rfl := matchPattern_bind_inv qmt130
  obtain ⟨xa23, qvs132, qb133, qb134, rfl, qmt135, qml136, rfl⟩ := matchListWith_cons_inv qml131
  obtain rfl := matchPattern_bind_inv qmt135
  obtain ⟨xa24, qvs137, qb138, qb139, rfl, qmt140, qml141, rfl⟩ := matchListWith_cons_inv qml136
  obtain rfl := matchPattern_bind_inv qmt140
  obtain ⟨xa25, qvs142, qb143, qb144, rfl, qmt145, qml146, rfl⟩ := matchListWith_cons_inv qml141
  obtain rfl := matchPattern_bind_inv qmt145
  obtain ⟨xa26, qvs147, qb148, qb149, rfl, qmt150, qml151, rfl⟩ := matchListWith_cons_inv qml146
  obtain rfl := matchPattern_bind_inv qmt150
  obtain ⟨xa27, qvs152, qb153, qb154, rfl, qmt155, qml156, rfl⟩ := matchListWith_cons_inv qml151
  obtain rfl := matchPattern_bind_inv qmt155
  obtain ⟨xa28, qvs157, qb158, qb159, rfl, qmt160, qml161, rfl⟩ := matchListWith_cons_inv qml156
  obtain rfl := matchPattern_bind_inv qmt160
  obtain ⟨xa29, qvs162, qb163, qb164, rfl, qmt165, qml166, rfl⟩ := matchListWith_cons_inv qml161
  obtain rfl := matchPattern_bind_inv qmt165
  obtain ⟨xa30, qvs167, qb168, qb169, rfl, qmt170, qml171, rfl⟩ := matchListWith_cons_inv qml166
  obtain rfl := matchPattern_bind_inv qmt170
  obtain ⟨xa31, qvs172, qb173, qb174, rfl, qmt175, qml176, rfl⟩ := matchListWith_cons_inv qml171
  obtain rfl := matchPattern_bind_inv qmt175
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv qml176
  rw [hx] at qld11
  injection qld11 with qld11
  injection qld11 with qld11
  injection qld11 with qe177 qld11
  subst qe177
  injection qld11 with qe178 qld11
  subst qe178
  injection qld11 with qe179 qld11
  subst qe179
  injection qld11 with qe180 qld11
  subst qe180
  injection qld11 with qe181 qld11
  subst qe181
  injection qld11 with qe182 qld11
  subst qe182
  injection qld11 with qe183 qld11
  subst qe183
  injection qld11 with qe184 qld11
  subst qe184
  injection qld11 with qe185 qld11
  subst qe185
  injection qld11 with qe186 qld11
  subst qe186
  injection qld11 with qe187 qld11
  subst qe187
  injection qld11 with qe188 qld11
  subst qe188
  injection qld11 with qe189 qld11
  subst qe189
  injection qld11 with qe190 qld11
  subst qe190
  injection qld11 with qe191 qld11
  subst qe191
  injection qld11 with qe192 qld11
  subst qe192
  injection qld11 with qe193 qld11
  subst qe193
  injection qld11 with qe194 qld11
  subst qe194
  injection qld11 with qe195 qld11
  subst qe195
  injection qld11 with qe196 qld11
  subst qe196
  injection qld11 with qe197 qld11
  subst qe197
  injection qld11 with qe198 qld11
  subst qe198
  injection qld11 with qe199 qld11
  subst qe199
  injection qld11 with qe200 qld11
  subst qe200
  injection qld11 with qe201 qld11
  subst qe201
  injection qld11 with qe202 qld11
  subst qe202
  injection qld11 with qe203 qld11
  subst qe203
  injection qld11 with qe204 qld11
  subst qe204
  injection qld11 with qe205 qld11
  subst qe205
  injection qld11 with qe206 qld11
  subst qe206
  injection qld11 with qe207 qld11
  subst qe207
  injection qld11 with qe208 qld11
  subst qe208
  obtain ⟨qv209, qm210, qbs211, qc212, qc213, qd214, qmt215, qd216, rfl⟩ := qd8.letValue_inv
  obtain ⟨qp217, qd218, qld219⟩ := qd214.load_inv
  obtain ⟨ql220, rfl, rfl⟩ := qd218.var_inv
  simp at ql220
  subst ql220
  obtain ⟨qvs221, qhv222, -, qml223⟩ := matchPattern_array_inv qmt215
  subst qhv222
  obtain ⟨qw224, qvs225, qb226, qb227, rfl, qmt228, qml229, rfl⟩ := matchListWith_cons_inv qml223
  obtain rfl := matchPattern_wildcard_inv qmt228
  obtain ⟨xb1, qvs230, qb231, qb232, rfl, qmt233, qml234, rfl⟩ := matchListWith_cons_inv qml229
  obtain rfl := matchPattern_bind_inv qmt233
  obtain ⟨xb2, qvs235, qb236, qb237, rfl, qmt238, qml239, rfl⟩ := matchListWith_cons_inv qml234
  obtain rfl := matchPattern_bind_inv qmt238
  obtain ⟨xb3, qvs240, qb241, qb242, rfl, qmt243, qml244, rfl⟩ := matchListWith_cons_inv qml239
  obtain rfl := matchPattern_bind_inv qmt243
  obtain ⟨xb4, qvs245, qb246, qb247, rfl, qmt248, qml249, rfl⟩ := matchListWith_cons_inv qml244
  obtain rfl := matchPattern_bind_inv qmt248
  obtain ⟨xb5, qvs250, qb251, qb252, rfl, qmt253, qml254, rfl⟩ := matchListWith_cons_inv qml249
  obtain rfl := matchPattern_bind_inv qmt253
  obtain ⟨xb6, qvs255, qb256, qb257, rfl, qmt258, qml259, rfl⟩ := matchListWith_cons_inv qml254
  obtain rfl := matchPattern_bind_inv qmt258
  obtain ⟨xb7, qvs260, qb261, qb262, rfl, qmt263, qml264, rfl⟩ := matchListWith_cons_inv qml259
  obtain rfl := matchPattern_bind_inv qmt263
  obtain ⟨xb8, qvs265, qb266, qb267, rfl, qmt268, qml269, rfl⟩ := matchListWith_cons_inv qml264
  obtain rfl := matchPattern_bind_inv qmt268
  obtain ⟨xb9, qvs270, qb271, qb272, rfl, qmt273, qml274, rfl⟩ := matchListWith_cons_inv qml269
  obtain rfl := matchPattern_bind_inv qmt273
  obtain ⟨xb10, qvs275, qb276, qb277, rfl, qmt278, qml279, rfl⟩ := matchListWith_cons_inv qml274
  obtain rfl := matchPattern_bind_inv qmt278
  obtain ⟨xb11, qvs280, qb281, qb282, rfl, qmt283, qml284, rfl⟩ := matchListWith_cons_inv qml279
  obtain rfl := matchPattern_bind_inv qmt283
  obtain ⟨xb12, qvs285, qb286, qb287, rfl, qmt288, qml289, rfl⟩ := matchListWith_cons_inv qml284
  obtain rfl := matchPattern_bind_inv qmt288
  obtain ⟨xb13, qvs290, qb291, qb292, rfl, qmt293, qml294, rfl⟩ := matchListWith_cons_inv qml289
  obtain rfl := matchPattern_bind_inv qmt293
  obtain ⟨xb14, qvs295, qb296, qb297, rfl, qmt298, qml299, rfl⟩ := matchListWith_cons_inv qml294
  obtain rfl := matchPattern_bind_inv qmt298
  obtain ⟨xb15, qvs300, qb301, qb302, rfl, qmt303, qml304, rfl⟩ := matchListWith_cons_inv qml299
  obtain rfl := matchPattern_bind_inv qmt303
  obtain ⟨xb16, qvs305, qb306, qb307, rfl, qmt308, qml309, rfl⟩ := matchListWith_cons_inv qml304
  obtain rfl := matchPattern_bind_inv qmt308
  obtain ⟨xb17, qvs310, qb311, qb312, rfl, qmt313, qml314, rfl⟩ := matchListWith_cons_inv qml309
  obtain rfl := matchPattern_bind_inv qmt313
  obtain ⟨xb18, qvs315, qb316, qb317, rfl, qmt318, qml319, rfl⟩ := matchListWith_cons_inv qml314
  obtain rfl := matchPattern_bind_inv qmt318
  obtain ⟨xb19, qvs320, qb321, qb322, rfl, qmt323, qml324, rfl⟩ := matchListWith_cons_inv qml319
  obtain rfl := matchPattern_bind_inv qmt323
  obtain ⟨xb20, qvs325, qb326, qb327, rfl, qmt328, qml329, rfl⟩ := matchListWith_cons_inv qml324
  obtain rfl := matchPattern_bind_inv qmt328
  obtain ⟨xb21, qvs330, qb331, qb332, rfl, qmt333, qml334, rfl⟩ := matchListWith_cons_inv qml329
  obtain rfl := matchPattern_bind_inv qmt333
  obtain ⟨xb22, qvs335, qb336, qb337, rfl, qmt338, qml339, rfl⟩ := matchListWith_cons_inv qml334
  obtain rfl := matchPattern_bind_inv qmt338
  obtain ⟨xb23, qvs340, qb341, qb342, rfl, qmt343, qml344, rfl⟩ := matchListWith_cons_inv qml339
  obtain rfl := matchPattern_bind_inv qmt343
  obtain ⟨xb24, qvs345, qb346, qb347, rfl, qmt348, qml349, rfl⟩ := matchListWith_cons_inv qml344
  obtain rfl := matchPattern_bind_inv qmt348
  obtain ⟨xb25, qvs350, qb351, qb352, rfl, qmt353, qml354, rfl⟩ := matchListWith_cons_inv qml349
  obtain rfl := matchPattern_bind_inv qmt353
  obtain ⟨xb26, qvs355, qb356, qb357, rfl, qmt358, qml359, rfl⟩ := matchListWith_cons_inv qml354
  obtain rfl := matchPattern_bind_inv qmt358
  obtain ⟨xb27, qvs360, qb361, qb362, rfl, qmt363, qml364, rfl⟩ := matchListWith_cons_inv qml359
  obtain rfl := matchPattern_bind_inv qmt363
  obtain ⟨xb28, qvs365, qb366, qb367, rfl, qmt368, qml369, rfl⟩ := matchListWith_cons_inv qml364
  obtain rfl := matchPattern_bind_inv qmt368
  obtain ⟨xb29, qvs370, qb371, qb372, rfl, qmt373, qml374, rfl⟩ := matchListWith_cons_inv qml369
  obtain rfl := matchPattern_bind_inv qmt373
  obtain ⟨xb30, qvs375, qb376, qb377, rfl, qmt378, qml379, rfl⟩ := matchListWith_cons_inv qml374
  obtain rfl := matchPattern_bind_inv qmt378
  obtain ⟨xb31, qvs380, qb381, qb382, rfl, qmt383, qml384, rfl⟩ := matchListWith_cons_inv qml379
  obtain rfl := matchPattern_bind_inv qmt383
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv qml384
  rw [hy] at qld219
  injection qld219 with qld219
  injection qld219 with qld219
  injection qld219 with qe385 qld219
  subst qe385
  injection qld219 with qe386 qld219
  subst qe386
  injection qld219 with qe387 qld219
  subst qe387
  injection qld219 with qe388 qld219
  subst qe388
  injection qld219 with qe389 qld219
  subst qe389
  injection qld219 with qe390 qld219
  subst qe390
  injection qld219 with qe391 qld219
  subst qe391
  injection qld219 with qe392 qld219
  subst qe392
  injection qld219 with qe393 qld219
  subst qe393
  injection qld219 with qe394 qld219
  subst qe394
  injection qld219 with qe395 qld219
  subst qe395
  injection qld219 with qe396 qld219
  subst qe396
  injection qld219 with qe397 qld219
  subst qe397
  injection qld219 with qe398 qld219
  subst qe398
  injection qld219 with qe399 qld219
  subst qe399
  injection qld219 with qe400 qld219
  subst qe400
  injection qld219 with qe401 qld219
  subst qe401
  injection qld219 with qe402 qld219
  subst qe402
  injection qld219 with qe403 qld219
  subst qe403
  injection qld219 with qe404 qld219
  subst qe404
  injection qld219 with qe405 qld219
  subst qe405
  injection qld219 with qe406 qld219
  subst qe406
  injection qld219 with qe407 qld219
  subst qe407
  injection qld219 with qe408 qld219
  subst qe408
  injection qld219 with qe409 qld219
  subst qe409
  injection qld219 with qe410 qld219
  subst qe410
  injection qld219 with qe411 qld219
  subst qe411
  injection qld219 with qe412 qld219
  subst qe412
  injection qld219 with qe413 qld219
  subst qe413
  injection qld219 with qe414 qld219
  subst qe414
  injection qld219 with qe415 qld219
  subst qe415
  injection qld219 with qe416 qld219
  subst qe416
  obtain ⟨qv417, qm418, qbs419, qc420, qc421, qd422, qmt423, qd424, rfl⟩ := qd216.letValue_inv
  obtain ⟨qx425, qy426, qm427, qc428, qc429, qd430, qd431, qop432, rfl⟩ := qd422.binary_inv
  obtain ⟨qx433, qy434, qm435, qc436, qc437, qd438, qd439, qop440, rfl⟩ := qd430.binary_inv
  obtain ⟨qx441, qy442, qm443, qc444, qc445, qd446, qd447, qop448, rfl⟩ := qd438.binary_inv
  obtain ⟨qx449, qy450, qm451, qc452, qc453, qd454, qd455, qop456, rfl⟩ := qd446.binary_inv
  obtain ⟨qx457, qy458, qm459, qc460, qc461, qd462, qd463, qop464, rfl⟩ := qd454.binary_inv
  obtain ⟨qx465, qy466, qm467, qc468, qc469, qd470, qd471, qop472, rfl⟩ := qd462.binary_inv
  obtain ⟨qx473, qy474, qm475, qc476, qc477, qd478, qd479, qop480, rfl⟩ := qd470.binary_inv
  obtain ⟨qx481, qy482, qm483, qc484, qc485, qd486, qd487, qop488, rfl⟩ := qd478.binary_inv
  obtain ⟨qx489, qy490, qm491, qc492, qc493, qd494, qd495, qop496, rfl⟩ := qd486.binary_inv
  obtain ⟨qx497, qy498, qm499, qc500, qc501, qd502, qd503, qop504, rfl⟩ := qd494.binary_inv
  obtain ⟨qx505, qy506, qm507, qc508, qc509, qd510, qd511, qop512, rfl⟩ := qd502.binary_inv
  obtain ⟨qx513, qy514, qm515, qc516, qc517, qd518, qd519, qop520, rfl⟩ := qd510.binary_inv
  obtain ⟨qvs521, qm522, qc523, qcs524, qa525, qev526, rfl⟩ := qd518.call_inv
  rw [instanceName_plain_some] at qev526
  obtain ⟨qv527, qvs528, qm529, qc530, qc531, rfl, qd532, qa533, rfl⟩ := qa525.cons_inv
  obtain ⟨ql534, rfl, rfl⟩ := qd532.var_inv
  simp at ql534
  subst ql534
  obtain ⟨rfl, rfl, rfl⟩ := qa533.nil_inv
  obtain ⟨qhe535, qhe536, -⟩ := Obs.«UInt8::to_field».obs qev526
  subst qhe535 qhe536
  obtain ⟨rfl, rfl, rfl⟩ := qd519.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop520
  subst qop520
  obtain ⟨qvs537, qm538, qc539, qcs540, qa541, qev542, rfl⟩ := qd511.call_inv
  rw [instanceName_plain_some] at qev542
  obtain ⟨qv543, qvs544, qm545, qc546, qc547, rfl, qd548, qa549, rfl⟩ := qa541.cons_inv
  obtain ⟨ql550, rfl, rfl⟩ := qd548.var_inv
  simp at ql550
  subst ql550
  obtain ⟨rfl, rfl, rfl⟩ := qa549.nil_inv
  obtain ⟨qhe551, qhe552, -⟩ := Obs.«UInt8::to_field».obs qev542
  subst qhe551 qhe552
  simp only [evalBinOp, Except.ok.injEq] at qop512
  subst qop512
  obtain ⟨rfl, rfl, rfl⟩ := qd503.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop504
  subst qop504
  obtain ⟨qvs553, qm554, qc555, qcs556, qa557, qev558, rfl⟩ := qd495.call_inv
  rw [instanceName_plain_some] at qev558
  obtain ⟨qv559, qvs560, qm561, qc562, qc563, rfl, qd564, qa565, rfl⟩ := qa557.cons_inv
  obtain ⟨ql566, rfl, rfl⟩ := qd564.var_inv
  simp at ql566
  subst ql566
  obtain ⟨rfl, rfl, rfl⟩ := qa565.nil_inv
  obtain ⟨qhe567, qhe568, -⟩ := Obs.«UInt8::to_field».obs qev558
  subst qhe567 qhe568
  simp only [evalBinOp, Except.ok.injEq] at qop496
  subst qop496
  obtain ⟨rfl, rfl, rfl⟩ := qd487.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop488
  subst qop488
  obtain ⟨qvs569, qm570, qc571, qcs572, qa573, qev574, rfl⟩ := qd479.call_inv
  rw [instanceName_plain_some] at qev574
  obtain ⟨qv575, qvs576, qm577, qc578, qc579, rfl, qd580, qa581, rfl⟩ := qa573.cons_inv
  obtain ⟨ql582, rfl, rfl⟩ := qd580.var_inv
  simp at ql582
  subst ql582
  obtain ⟨rfl, rfl, rfl⟩ := qa581.nil_inv
  obtain ⟨qhe583, qhe584, -⟩ := Obs.«UInt8::to_field».obs qev574
  subst qhe583 qhe584
  simp only [evalBinOp, Except.ok.injEq] at qop480
  subst qop480
  obtain ⟨rfl, rfl, rfl⟩ := qd471.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop472
  subst qop472
  obtain ⟨qvs585, qm586, qc587, qcs588, qa589, qev590, rfl⟩ := qd463.call_inv
  rw [instanceName_plain_some] at qev590
  obtain ⟨qv591, qvs592, qm593, qc594, qc595, rfl, qd596, qa597, rfl⟩ := qa589.cons_inv
  obtain ⟨ql598, rfl, rfl⟩ := qd596.var_inv
  simp at ql598
  subst ql598
  obtain ⟨rfl, rfl, rfl⟩ := qa597.nil_inv
  obtain ⟨qhe599, qhe600, -⟩ := Obs.«UInt8::to_field».obs qev590
  subst qhe599 qhe600
  simp only [evalBinOp, Except.ok.injEq] at qop464
  subst qop464
  obtain ⟨rfl, rfl, rfl⟩ := qd455.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop456
  subst qop456
  obtain ⟨qvs601, qm602, qc603, qcs604, qa605, qev606, rfl⟩ := qd447.call_inv
  rw [instanceName_plain_some] at qev606
  obtain ⟨qv607, qvs608, qm609, qc610, qc611, rfl, qd612, qa613, rfl⟩ := qa605.cons_inv
  obtain ⟨ql614, rfl, rfl⟩ := qd612.var_inv
  simp at ql614
  subst ql614
  obtain ⟨rfl, rfl, rfl⟩ := qa613.nil_inv
  obtain ⟨qhe615, qhe616, -⟩ := Obs.«UInt8::to_field».obs qev606
  subst qhe615 qhe616
  simp only [evalBinOp, Except.ok.injEq] at qop448
  subst qop448
  obtain ⟨rfl, rfl, rfl⟩ := qd439.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop440
  subst qop440
  obtain ⟨qvs617, qm618, qc619, qcs620, qa621, qev622, rfl⟩ := qd431.call_inv
  rw [instanceName_plain_some] at qev622
  obtain ⟨qv623, qvs624, qm625, qc626, qc627, rfl, qd628, qa629, rfl⟩ := qa621.cons_inv
  obtain ⟨ql630, rfl, rfl⟩ := qd628.var_inv
  simp at ql630
  subst ql630
  obtain ⟨rfl, rfl, rfl⟩ := qa629.nil_inv
  obtain ⟨qhe631, qhe632, -⟩ := Obs.«UInt8::to_field».obs qev622
  subst qhe631 qhe632
  simp only [evalBinOp, Except.ok.injEq] at qop432
  subst qop432
  obtain rfl := matchPattern_bind_inv qmt423
  obtain ⟨qv633, qm634, qbs635, qc636, qc637, qd638, qmt639, qd640, rfl⟩ := qd424.letValue_inv
  obtain ⟨qx641, qy642, qm643, qc644, qc645, qd646, qd647, qop648, rfl⟩ := qd638.binary_inv
  obtain ⟨qx649, qy650, qm651, qc652, qc653, qd654, qd655, qop656, rfl⟩ := qd646.binary_inv
  obtain ⟨qx657, qy658, qm659, qc660, qc661, qd662, qd663, qop664, rfl⟩ := qd654.binary_inv
  obtain ⟨qx665, qy666, qm667, qc668, qc669, qd670, qd671, qop672, rfl⟩ := qd662.binary_inv
  obtain ⟨qx673, qy674, qm675, qc676, qc677, qd678, qd679, qop680, rfl⟩ := qd670.binary_inv
  obtain ⟨qx681, qy682, qm683, qc684, qc685, qd686, qd687, qop688, rfl⟩ := qd678.binary_inv
  obtain ⟨qx689, qy690, qm691, qc692, qc693, qd694, qd695, qop696, rfl⟩ := qd686.binary_inv
  obtain ⟨qx697, qy698, qm699, qc700, qc701, qd702, qd703, qop704, rfl⟩ := qd694.binary_inv
  obtain ⟨qx705, qy706, qm707, qc708, qc709, qd710, qd711, qop712, rfl⟩ := qd702.binary_inv
  obtain ⟨qx713, qy714, qm715, qc716, qc717, qd718, qd719, qop720, rfl⟩ := qd710.binary_inv
  obtain ⟨qx721, qy722, qm723, qc724, qc725, qd726, qd727, qop728, rfl⟩ := qd718.binary_inv
  obtain ⟨qx729, qy730, qm731, qc732, qc733, qd734, qd735, qop736, rfl⟩ := qd726.binary_inv
  obtain ⟨qvs737, qm738, qc739, qcs740, qa741, qev742, rfl⟩ := qd734.call_inv
  rw [instanceName_plain_some] at qev742
  obtain ⟨qv743, qvs744, qm745, qc746, qc747, rfl, qd748, qa749, rfl⟩ := qa741.cons_inv
  obtain ⟨ql750, rfl, rfl⟩ := qd748.var_inv
  simp at ql750
  subst ql750
  obtain ⟨rfl, rfl, rfl⟩ := qa749.nil_inv
  obtain ⟨qhe751, qhe752, -⟩ := Obs.«UInt8::to_field».obs qev742
  subst qhe751 qhe752
  obtain ⟨rfl, rfl, rfl⟩ := qd735.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop736
  subst qop736
  obtain ⟨qvs753, qm754, qc755, qcs756, qa757, qev758, rfl⟩ := qd727.call_inv
  rw [instanceName_plain_some] at qev758
  obtain ⟨qv759, qvs760, qm761, qc762, qc763, rfl, qd764, qa765, rfl⟩ := qa757.cons_inv
  obtain ⟨ql766, rfl, rfl⟩ := qd764.var_inv
  simp at ql766
  subst ql766
  obtain ⟨rfl, rfl, rfl⟩ := qa765.nil_inv
  obtain ⟨qhe767, qhe768, -⟩ := Obs.«UInt8::to_field».obs qev758
  subst qhe767 qhe768
  simp only [evalBinOp, Except.ok.injEq] at qop728
  subst qop728
  obtain ⟨rfl, rfl, rfl⟩ := qd719.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop720
  subst qop720
  obtain ⟨qvs769, qm770, qc771, qcs772, qa773, qev774, rfl⟩ := qd711.call_inv
  rw [instanceName_plain_some] at qev774
  obtain ⟨qv775, qvs776, qm777, qc778, qc779, rfl, qd780, qa781, rfl⟩ := qa773.cons_inv
  obtain ⟨ql782, rfl, rfl⟩ := qd780.var_inv
  simp at ql782
  subst ql782
  obtain ⟨rfl, rfl, rfl⟩ := qa781.nil_inv
  obtain ⟨qhe783, qhe784, -⟩ := Obs.«UInt8::to_field».obs qev774
  subst qhe783 qhe784
  simp only [evalBinOp, Except.ok.injEq] at qop712
  subst qop712
  obtain ⟨rfl, rfl, rfl⟩ := qd703.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop704
  subst qop704
  obtain ⟨qvs785, qm786, qc787, qcs788, qa789, qev790, rfl⟩ := qd695.call_inv
  rw [instanceName_plain_some] at qev790
  obtain ⟨qv791, qvs792, qm793, qc794, qc795, rfl, qd796, qa797, rfl⟩ := qa789.cons_inv
  obtain ⟨ql798, rfl, rfl⟩ := qd796.var_inv
  simp at ql798
  subst ql798
  obtain ⟨rfl, rfl, rfl⟩ := qa797.nil_inv
  obtain ⟨qhe799, qhe800, -⟩ := Obs.«UInt8::to_field».obs qev790
  subst qhe799 qhe800
  simp only [evalBinOp, Except.ok.injEq] at qop696
  subst qop696
  obtain ⟨rfl, rfl, rfl⟩ := qd687.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop688
  subst qop688
  obtain ⟨qvs801, qm802, qc803, qcs804, qa805, qev806, rfl⟩ := qd679.call_inv
  rw [instanceName_plain_some] at qev806
  obtain ⟨qv807, qvs808, qm809, qc810, qc811, rfl, qd812, qa813, rfl⟩ := qa805.cons_inv
  obtain ⟨ql814, rfl, rfl⟩ := qd812.var_inv
  simp at ql814
  subst ql814
  obtain ⟨rfl, rfl, rfl⟩ := qa813.nil_inv
  obtain ⟨qhe815, qhe816, -⟩ := Obs.«UInt8::to_field».obs qev806
  subst qhe815 qhe816
  simp only [evalBinOp, Except.ok.injEq] at qop680
  subst qop680
  obtain ⟨rfl, rfl, rfl⟩ := qd671.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop672
  subst qop672
  obtain ⟨qvs817, qm818, qc819, qcs820, qa821, qev822, rfl⟩ := qd663.call_inv
  rw [instanceName_plain_some] at qev822
  obtain ⟨qv823, qvs824, qm825, qc826, qc827, rfl, qd828, qa829, rfl⟩ := qa821.cons_inv
  obtain ⟨ql830, rfl, rfl⟩ := qd828.var_inv
  simp at ql830
  subst ql830
  obtain ⟨rfl, rfl, rfl⟩ := qa829.nil_inv
  obtain ⟨qhe831, qhe832, -⟩ := Obs.«UInt8::to_field».obs qev822
  subst qhe831 qhe832
  simp only [evalBinOp, Except.ok.injEq] at qop664
  subst qop664
  obtain ⟨rfl, rfl, rfl⟩ := qd655.literal_inv
  simp only [evalBinOp, Except.ok.injEq] at qop656
  subst qop656
  obtain ⟨qvs833, qm834, qc835, qcs836, qa837, qev838, rfl⟩ := qd647.call_inv
  rw [instanceName_plain_some] at qev838
  obtain ⟨qv839, qvs840, qm841, qc842, qc843, rfl, qd844, qa845, rfl⟩ := qa837.cons_inv
  obtain ⟨ql846, rfl, rfl⟩ := qd844.var_inv
  simp at ql846
  subst ql846
  obtain ⟨rfl, rfl, rfl⟩ := qa845.nil_inv
  obtain ⟨qhe847, qhe848, -⟩ := Obs.«UInt8::to_field».obs qev838
  subst qhe847 qhe848
  simp only [evalBinOp, Except.ok.injEq] at qop648
  subst qop648
  obtain rfl := matchPattern_bind_inv qmt639
  obtain ⟨qv849, qm850, qbs851, qbody852, qc853, qc854, qd855, qsel856, qd857, rfl⟩ := qd640.matchValue_inv
  obtain ⟨qx858, qy859, qm860, qc861, qc862, qd863, qd864, qop865, rfl⟩ := qd855.binary_inv
  obtain ⟨ql866, rfl, rfl⟩ := qd863.var_inv
  simp at ql866
  subst ql866
  obtain ⟨ql867, rfl, rfl⟩ := qd864.var_inv
  simp at ql867
  subst ql867
  simp only [evalBinOp, Except.ok.injEq] at qop865
  subst qop865
  rcases selectArm_cons_inv qsel856 with ⟨qmt868, rfl⟩ | ⟨qnm869, qsel870⟩
  · obtain ⟨qhv871, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 0) qmt868
    have qE872 : (pack7 u1 u2 u3 u4 u5 u6 u7 - pack7 v1 v2 v3 v4 v5 v6 v7 : F) = 0 := Value.field.inj qhv871
    obtain ⟨qv873, qm874, qbs875, qc876, qc877, qd878, qmt879, qd880, rfl⟩ := qd857.letValue_inv
    obtain ⟨qx881, qy882, qm883, qc884, qc885, qd886, qd887, qop888, rfl⟩ := qd878.binary_inv
    obtain ⟨qx889, qy890, qm891, qc892, qc893, qd894, qd895, qop896, rfl⟩ := qd886.binary_inv
    obtain ⟨qx897, qy898, qm899, qc900, qc901, qd902, qd903, qop904, rfl⟩ := qd894.binary_inv
    obtain ⟨qx905, qy906, qm907, qc908, qc909, qd910, qd911, qop912, rfl⟩ := qd902.binary_inv
    obtain ⟨qx913, qy914, qm915, qc916, qc917, qd918, qd919, qop920, rfl⟩ := qd910.binary_inv
    obtain ⟨qx921, qy922, qm923, qc924, qc925, qd926, qd927, qop928, rfl⟩ := qd918.binary_inv
    obtain ⟨qx929, qy930, qm931, qc932, qc933, qd934, qd935, qop936, rfl⟩ := qd926.binary_inv
    obtain ⟨qx937, qy938, qm939, qc940, qc941, qd942, qd943, qop944, rfl⟩ := qd934.binary_inv
    obtain ⟨qx945, qy946, qm947, qc948, qc949, qd950, qd951, qop952, rfl⟩ := qd942.binary_inv
    obtain ⟨qx953, qy954, qm955, qc956, qc957, qd958, qd959, qop960, rfl⟩ := qd950.binary_inv
    obtain ⟨qx961, qy962, qm963, qc964, qc965, qd966, qd967, qop968, rfl⟩ := qd958.binary_inv
    obtain ⟨qx969, qy970, qm971, qc972, qc973, qd974, qd975, qop976, rfl⟩ := qd966.binary_inv
    obtain ⟨qvs977, qm978, qc979, qcs980, qa981, qev982, rfl⟩ := qd974.call_inv
    rw [instanceName_plain_some] at qev982
    obtain ⟨qv983, qvs984, qm985, qc986, qc987, rfl, qd988, qa989, rfl⟩ := qa981.cons_inv
    obtain ⟨ql990, rfl, rfl⟩ := qd988.var_inv
    simp at ql990
    subst ql990
    obtain ⟨rfl, rfl, rfl⟩ := qa989.nil_inv
    obtain ⟨qhe991, qhe992, -⟩ := Obs.«UInt8::to_field».obs qev982
    subst qhe991 qhe992
    obtain ⟨rfl, rfl, rfl⟩ := qd975.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop976
    subst qop976
    obtain ⟨qvs993, qm994, qc995, qcs996, qa997, qev998, rfl⟩ := qd967.call_inv
    rw [instanceName_plain_some] at qev998
    obtain ⟨qv999, qvs1000, qm1001, qc1002, qc1003, rfl, qd1004, qa1005, rfl⟩ := qa997.cons_inv
    obtain ⟨ql1006, rfl, rfl⟩ := qd1004.var_inv
    simp at ql1006
    subst ql1006
    obtain ⟨rfl, rfl, rfl⟩ := qa1005.nil_inv
    obtain ⟨qhe1007, qhe1008, -⟩ := Obs.«UInt8::to_field».obs qev998
    subst qhe1007 qhe1008
    simp only [evalBinOp, Except.ok.injEq] at qop968
    subst qop968
    obtain ⟨rfl, rfl, rfl⟩ := qd959.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop960
    subst qop960
    obtain ⟨qvs1009, qm1010, qc1011, qcs1012, qa1013, qev1014, rfl⟩ := qd951.call_inv
    rw [instanceName_plain_some] at qev1014
    obtain ⟨qv1015, qvs1016, qm1017, qc1018, qc1019, rfl, qd1020, qa1021, rfl⟩ := qa1013.cons_inv
    obtain ⟨ql1022, rfl, rfl⟩ := qd1020.var_inv
    simp at ql1022
    subst ql1022
    obtain ⟨rfl, rfl, rfl⟩ := qa1021.nil_inv
    obtain ⟨qhe1023, qhe1024, -⟩ := Obs.«UInt8::to_field».obs qev1014
    subst qhe1023 qhe1024
    simp only [evalBinOp, Except.ok.injEq] at qop952
    subst qop952
    obtain ⟨rfl, rfl, rfl⟩ := qd943.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop944
    subst qop944
    obtain ⟨qvs1025, qm1026, qc1027, qcs1028, qa1029, qev1030, rfl⟩ := qd935.call_inv
    rw [instanceName_plain_some] at qev1030
    obtain ⟨qv1031, qvs1032, qm1033, qc1034, qc1035, rfl, qd1036, qa1037, rfl⟩ := qa1029.cons_inv
    obtain ⟨ql1038, rfl, rfl⟩ := qd1036.var_inv
    simp at ql1038
    subst ql1038
    obtain ⟨rfl, rfl, rfl⟩ := qa1037.nil_inv
    obtain ⟨qhe1039, qhe1040, -⟩ := Obs.«UInt8::to_field».obs qev1030
    subst qhe1039 qhe1040
    simp only [evalBinOp, Except.ok.injEq] at qop936
    subst qop936
    obtain ⟨rfl, rfl, rfl⟩ := qd927.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop928
    subst qop928
    obtain ⟨qvs1041, qm1042, qc1043, qcs1044, qa1045, qev1046, rfl⟩ := qd919.call_inv
    rw [instanceName_plain_some] at qev1046
    obtain ⟨qv1047, qvs1048, qm1049, qc1050, qc1051, rfl, qd1052, qa1053, rfl⟩ := qa1045.cons_inv
    obtain ⟨ql1054, rfl, rfl⟩ := qd1052.var_inv
    simp at ql1054
    subst ql1054
    obtain ⟨rfl, rfl, rfl⟩ := qa1053.nil_inv
    obtain ⟨qhe1055, qhe1056, -⟩ := Obs.«UInt8::to_field».obs qev1046
    subst qhe1055 qhe1056
    simp only [evalBinOp, Except.ok.injEq] at qop920
    subst qop920
    obtain ⟨rfl, rfl, rfl⟩ := qd911.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop912
    subst qop912
    obtain ⟨qvs1057, qm1058, qc1059, qcs1060, qa1061, qev1062, rfl⟩ := qd903.call_inv
    rw [instanceName_plain_some] at qev1062
    obtain ⟨qv1063, qvs1064, qm1065, qc1066, qc1067, rfl, qd1068, qa1069, rfl⟩ := qa1061.cons_inv
    obtain ⟨ql1070, rfl, rfl⟩ := qd1068.var_inv
    simp at ql1070
    subst ql1070
    obtain ⟨rfl, rfl, rfl⟩ := qa1069.nil_inv
    obtain ⟨qhe1071, qhe1072, -⟩ := Obs.«UInt8::to_field».obs qev1062
    subst qhe1071 qhe1072
    simp only [evalBinOp, Except.ok.injEq] at qop904
    subst qop904
    obtain ⟨rfl, rfl, rfl⟩ := qd895.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop896
    subst qop896
    obtain ⟨qvs1073, qm1074, qc1075, qcs1076, qa1077, qev1078, rfl⟩ := qd887.call_inv
    rw [instanceName_plain_some] at qev1078
    obtain ⟨qv1079, qvs1080, qm1081, qc1082, qc1083, rfl, qd1084, qa1085, rfl⟩ := qa1077.cons_inv
    obtain ⟨ql1086, rfl, rfl⟩ := qd1084.var_inv
    simp at ql1086
    subst ql1086
    obtain ⟨rfl, rfl, rfl⟩ := qa1085.nil_inv
    obtain ⟨qhe1087, qhe1088, -⟩ := Obs.«UInt8::to_field».obs qev1078
    subst qhe1087 qhe1088
    simp only [evalBinOp, Except.ok.injEq] at qop888
    subst qop888
    obtain rfl := matchPattern_bind_inv qmt879
    obtain ⟨qv1089, qm1090, qbs1091, qc1092, qc1093, qd1094, qmt1095, qd1096, rfl⟩ := qd880.letValue_inv
    obtain ⟨qx1097, qy1098, qm1099, qc1100, qc1101, qd1102, qd1103, qop1104, rfl⟩ := qd1094.binary_inv
    obtain ⟨qx1105, qy1106, qm1107, qc1108, qc1109, qd1110, qd1111, qop1112, rfl⟩ := qd1102.binary_inv
    obtain ⟨qx1113, qy1114, qm1115, qc1116, qc1117, qd1118, qd1119, qop1120, rfl⟩ := qd1110.binary_inv
    obtain ⟨qx1121, qy1122, qm1123, qc1124, qc1125, qd1126, qd1127, qop1128, rfl⟩ := qd1118.binary_inv
    obtain ⟨qx1129, qy1130, qm1131, qc1132, qc1133, qd1134, qd1135, qop1136, rfl⟩ := qd1126.binary_inv
    obtain ⟨qx1137, qy1138, qm1139, qc1140, qc1141, qd1142, qd1143, qop1144, rfl⟩ := qd1134.binary_inv
    obtain ⟨qx1145, qy1146, qm1147, qc1148, qc1149, qd1150, qd1151, qop1152, rfl⟩ := qd1142.binary_inv
    obtain ⟨qx1153, qy1154, qm1155, qc1156, qc1157, qd1158, qd1159, qop1160, rfl⟩ := qd1150.binary_inv
    obtain ⟨qx1161, qy1162, qm1163, qc1164, qc1165, qd1166, qd1167, qop1168, rfl⟩ := qd1158.binary_inv
    obtain ⟨qx1169, qy1170, qm1171, qc1172, qc1173, qd1174, qd1175, qop1176, rfl⟩ := qd1166.binary_inv
    obtain ⟨qx1177, qy1178, qm1179, qc1180, qc1181, qd1182, qd1183, qop1184, rfl⟩ := qd1174.binary_inv
    obtain ⟨qx1185, qy1186, qm1187, qc1188, qc1189, qd1190, qd1191, qop1192, rfl⟩ := qd1182.binary_inv
    obtain ⟨qvs1193, qm1194, qc1195, qcs1196, qa1197, qev1198, rfl⟩ := qd1190.call_inv
    rw [instanceName_plain_some] at qev1198
    obtain ⟨qv1199, qvs1200, qm1201, qc1202, qc1203, rfl, qd1204, qa1205, rfl⟩ := qa1197.cons_inv
    obtain ⟨ql1206, rfl, rfl⟩ := qd1204.var_inv
    simp at ql1206
    subst ql1206
    obtain ⟨rfl, rfl, rfl⟩ := qa1205.nil_inv
    obtain ⟨qhe1207, qhe1208, -⟩ := Obs.«UInt8::to_field».obs qev1198
    subst qhe1207 qhe1208
    obtain ⟨rfl, rfl, rfl⟩ := qd1191.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop1192
    subst qop1192
    obtain ⟨qvs1209, qm1210, qc1211, qcs1212, qa1213, qev1214, rfl⟩ := qd1183.call_inv
    rw [instanceName_plain_some] at qev1214
    obtain ⟨qv1215, qvs1216, qm1217, qc1218, qc1219, rfl, qd1220, qa1221, rfl⟩ := qa1213.cons_inv
    obtain ⟨ql1222, rfl, rfl⟩ := qd1220.var_inv
    simp at ql1222
    subst ql1222
    obtain ⟨rfl, rfl, rfl⟩ := qa1221.nil_inv
    obtain ⟨qhe1223, qhe1224, -⟩ := Obs.«UInt8::to_field».obs qev1214
    subst qhe1223 qhe1224
    simp only [evalBinOp, Except.ok.injEq] at qop1184
    subst qop1184
    obtain ⟨rfl, rfl, rfl⟩ := qd1175.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop1176
    subst qop1176
    obtain ⟨qvs1225, qm1226, qc1227, qcs1228, qa1229, qev1230, rfl⟩ := qd1167.call_inv
    rw [instanceName_plain_some] at qev1230
    obtain ⟨qv1231, qvs1232, qm1233, qc1234, qc1235, rfl, qd1236, qa1237, rfl⟩ := qa1229.cons_inv
    obtain ⟨ql1238, rfl, rfl⟩ := qd1236.var_inv
    simp at ql1238
    subst ql1238
    obtain ⟨rfl, rfl, rfl⟩ := qa1237.nil_inv
    obtain ⟨qhe1239, qhe1240, -⟩ := Obs.«UInt8::to_field».obs qev1230
    subst qhe1239 qhe1240
    simp only [evalBinOp, Except.ok.injEq] at qop1168
    subst qop1168
    obtain ⟨rfl, rfl, rfl⟩ := qd1159.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop1160
    subst qop1160
    obtain ⟨qvs1241, qm1242, qc1243, qcs1244, qa1245, qev1246, rfl⟩ := qd1151.call_inv
    rw [instanceName_plain_some] at qev1246
    obtain ⟨qv1247, qvs1248, qm1249, qc1250, qc1251, rfl, qd1252, qa1253, rfl⟩ := qa1245.cons_inv
    obtain ⟨ql1254, rfl, rfl⟩ := qd1252.var_inv
    simp at ql1254
    subst ql1254
    obtain ⟨rfl, rfl, rfl⟩ := qa1253.nil_inv
    obtain ⟨qhe1255, qhe1256, -⟩ := Obs.«UInt8::to_field».obs qev1246
    subst qhe1255 qhe1256
    simp only [evalBinOp, Except.ok.injEq] at qop1152
    subst qop1152
    obtain ⟨rfl, rfl, rfl⟩ := qd1143.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop1144
    subst qop1144
    obtain ⟨qvs1257, qm1258, qc1259, qcs1260, qa1261, qev1262, rfl⟩ := qd1135.call_inv
    rw [instanceName_plain_some] at qev1262
    obtain ⟨qv1263, qvs1264, qm1265, qc1266, qc1267, rfl, qd1268, qa1269, rfl⟩ := qa1261.cons_inv
    obtain ⟨ql1270, rfl, rfl⟩ := qd1268.var_inv
    simp at ql1270
    subst ql1270
    obtain ⟨rfl, rfl, rfl⟩ := qa1269.nil_inv
    obtain ⟨qhe1271, qhe1272, -⟩ := Obs.«UInt8::to_field».obs qev1262
    subst qhe1271 qhe1272
    simp only [evalBinOp, Except.ok.injEq] at qop1136
    subst qop1136
    obtain ⟨rfl, rfl, rfl⟩ := qd1127.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop1128
    subst qop1128
    obtain ⟨qvs1273, qm1274, qc1275, qcs1276, qa1277, qev1278, rfl⟩ := qd1119.call_inv
    rw [instanceName_plain_some] at qev1278
    obtain ⟨qv1279, qvs1280, qm1281, qc1282, qc1283, rfl, qd1284, qa1285, rfl⟩ := qa1277.cons_inv
    obtain ⟨ql1286, rfl, rfl⟩ := qd1284.var_inv
    simp at ql1286
    subst ql1286
    obtain ⟨rfl, rfl, rfl⟩ := qa1285.nil_inv
    obtain ⟨qhe1287, qhe1288, -⟩ := Obs.«UInt8::to_field».obs qev1278
    subst qhe1287 qhe1288
    simp only [evalBinOp, Except.ok.injEq] at qop1120
    subst qop1120
    obtain ⟨rfl, rfl, rfl⟩ := qd1111.literal_inv
    simp only [evalBinOp, Except.ok.injEq] at qop1112
    subst qop1112
    obtain ⟨qvs1289, qm1290, qc1291, qcs1292, qa1293, qev1294, rfl⟩ := qd1103.call_inv
    rw [instanceName_plain_some] at qev1294
    obtain ⟨qv1295, qvs1296, qm1297, qc1298, qc1299, rfl, qd1300, qa1301, rfl⟩ := qa1293.cons_inv
    obtain ⟨ql1302, rfl, rfl⟩ := qd1300.var_inv
    simp at ql1302
    subst ql1302
    obtain ⟨rfl, rfl, rfl⟩ := qa1301.nil_inv
    obtain ⟨qhe1303, qhe1304, -⟩ := Obs.«UInt8::to_field».obs qev1294
    subst qhe1303 qhe1304
    simp only [evalBinOp, Except.ok.injEq] at qop1104
    subst qop1104
    obtain rfl := matchPattern_bind_inv qmt1095
    obtain ⟨qv1305, qm1306, qbs1307, qbody1308, qc1309, qc1310, qd1311, qsel1312, qd1313, rfl⟩ := qd1096.matchValue_inv
    obtain ⟨qx1314, qy1315, qm1316, qc1317, qc1318, qd1319, qd1320, qop1321, rfl⟩ := qd1311.binary_inv
    obtain ⟨ql1322, rfl, rfl⟩ := qd1319.var_inv
    simp at ql1322
    subst ql1322
    obtain ⟨ql1323, rfl, rfl⟩ := qd1320.var_inv
    simp at ql1323
    subst ql1323
    simp only [evalBinOp, Except.ok.injEq] at qop1321
    subst qop1321
    rcases selectArm_cons_inv qsel1312 with ⟨qmt1324, rfl⟩ | ⟨qnm1325, qsel1326⟩
    · obtain ⟨qhv1327, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 0) qmt1324
      have qE1328 : (pack7 u8 u9 u10 u11 u12 u13 u14 - pack7 v8 v9 v10 v11 v12 v13 v14 : F) = 0 := Value.field.inj qhv1327
      obtain ⟨qv1329, qm1330, qbs1331, qc1332, qc1333, qd1334, qmt1335, qd1336, rfl⟩ := qd1313.letValue_inv
      obtain ⟨qx1337, qy1338, qm1339, qc1340, qc1341, qd1342, qd1343, qop1344, rfl⟩ := qd1334.binary_inv
      obtain ⟨qx1345, qy1346, qm1347, qc1348, qc1349, qd1350, qd1351, qop1352, rfl⟩ := qd1342.binary_inv
      obtain ⟨qx1353, qy1354, qm1355, qc1356, qc1357, qd1358, qd1359, qop1360, rfl⟩ := qd1350.binary_inv
      obtain ⟨qx1361, qy1362, qm1363, qc1364, qc1365, qd1366, qd1367, qop1368, rfl⟩ := qd1358.binary_inv
      obtain ⟨qx1369, qy1370, qm1371, qc1372, qc1373, qd1374, qd1375, qop1376, rfl⟩ := qd1366.binary_inv
      obtain ⟨qx1377, qy1378, qm1379, qc1380, qc1381, qd1382, qd1383, qop1384, rfl⟩ := qd1374.binary_inv
      obtain ⟨qx1385, qy1386, qm1387, qc1388, qc1389, qd1390, qd1391, qop1392, rfl⟩ := qd1382.binary_inv
      obtain ⟨qx1393, qy1394, qm1395, qc1396, qc1397, qd1398, qd1399, qop1400, rfl⟩ := qd1390.binary_inv
      obtain ⟨qx1401, qy1402, qm1403, qc1404, qc1405, qd1406, qd1407, qop1408, rfl⟩ := qd1398.binary_inv
      obtain ⟨qx1409, qy1410, qm1411, qc1412, qc1413, qd1414, qd1415, qop1416, rfl⟩ := qd1406.binary_inv
      obtain ⟨qx1417, qy1418, qm1419, qc1420, qc1421, qd1422, qd1423, qop1424, rfl⟩ := qd1414.binary_inv
      obtain ⟨qx1425, qy1426, qm1427, qc1428, qc1429, qd1430, qd1431, qop1432, rfl⟩ := qd1422.binary_inv
      obtain ⟨qvs1433, qm1434, qc1435, qcs1436, qa1437, qev1438, rfl⟩ := qd1430.call_inv
      rw [instanceName_plain_some] at qev1438
      obtain ⟨qv1439, qvs1440, qm1441, qc1442, qc1443, rfl, qd1444, qa1445, rfl⟩ := qa1437.cons_inv
      obtain ⟨ql1446, rfl, rfl⟩ := qd1444.var_inv
      simp at ql1446
      subst ql1446
      obtain ⟨rfl, rfl, rfl⟩ := qa1445.nil_inv
      obtain ⟨qhe1447, qhe1448, -⟩ := Obs.«UInt8::to_field».obs qev1438
      subst qhe1447 qhe1448
      obtain ⟨rfl, rfl, rfl⟩ := qd1431.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1432
      subst qop1432
      obtain ⟨qvs1449, qm1450, qc1451, qcs1452, qa1453, qev1454, rfl⟩ := qd1423.call_inv
      rw [instanceName_plain_some] at qev1454
      obtain ⟨qv1455, qvs1456, qm1457, qc1458, qc1459, rfl, qd1460, qa1461, rfl⟩ := qa1453.cons_inv
      obtain ⟨ql1462, rfl, rfl⟩ := qd1460.var_inv
      simp at ql1462
      subst ql1462
      obtain ⟨rfl, rfl, rfl⟩ := qa1461.nil_inv
      obtain ⟨qhe1463, qhe1464, -⟩ := Obs.«UInt8::to_field».obs qev1454
      subst qhe1463 qhe1464
      simp only [evalBinOp, Except.ok.injEq] at qop1424
      subst qop1424
      obtain ⟨rfl, rfl, rfl⟩ := qd1415.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1416
      subst qop1416
      obtain ⟨qvs1465, qm1466, qc1467, qcs1468, qa1469, qev1470, rfl⟩ := qd1407.call_inv
      rw [instanceName_plain_some] at qev1470
      obtain ⟨qv1471, qvs1472, qm1473, qc1474, qc1475, rfl, qd1476, qa1477, rfl⟩ := qa1469.cons_inv
      obtain ⟨ql1478, rfl, rfl⟩ := qd1476.var_inv
      simp at ql1478
      subst ql1478
      obtain ⟨rfl, rfl, rfl⟩ := qa1477.nil_inv
      obtain ⟨qhe1479, qhe1480, -⟩ := Obs.«UInt8::to_field».obs qev1470
      subst qhe1479 qhe1480
      simp only [evalBinOp, Except.ok.injEq] at qop1408
      subst qop1408
      obtain ⟨rfl, rfl, rfl⟩ := qd1399.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1400
      subst qop1400
      obtain ⟨qvs1481, qm1482, qc1483, qcs1484, qa1485, qev1486, rfl⟩ := qd1391.call_inv
      rw [instanceName_plain_some] at qev1486
      obtain ⟨qv1487, qvs1488, qm1489, qc1490, qc1491, rfl, qd1492, qa1493, rfl⟩ := qa1485.cons_inv
      obtain ⟨ql1494, rfl, rfl⟩ := qd1492.var_inv
      simp at ql1494
      subst ql1494
      obtain ⟨rfl, rfl, rfl⟩ := qa1493.nil_inv
      obtain ⟨qhe1495, qhe1496, -⟩ := Obs.«UInt8::to_field».obs qev1486
      subst qhe1495 qhe1496
      simp only [evalBinOp, Except.ok.injEq] at qop1392
      subst qop1392
      obtain ⟨rfl, rfl, rfl⟩ := qd1383.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1384
      subst qop1384
      obtain ⟨qvs1497, qm1498, qc1499, qcs1500, qa1501, qev1502, rfl⟩ := qd1375.call_inv
      rw [instanceName_plain_some] at qev1502
      obtain ⟨qv1503, qvs1504, qm1505, qc1506, qc1507, rfl, qd1508, qa1509, rfl⟩ := qa1501.cons_inv
      obtain ⟨ql1510, rfl, rfl⟩ := qd1508.var_inv
      simp at ql1510
      subst ql1510
      obtain ⟨rfl, rfl, rfl⟩ := qa1509.nil_inv
      obtain ⟨qhe1511, qhe1512, -⟩ := Obs.«UInt8::to_field».obs qev1502
      subst qhe1511 qhe1512
      simp only [evalBinOp, Except.ok.injEq] at qop1376
      subst qop1376
      obtain ⟨rfl, rfl, rfl⟩ := qd1367.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1368
      subst qop1368
      obtain ⟨qvs1513, qm1514, qc1515, qcs1516, qa1517, qev1518, rfl⟩ := qd1359.call_inv
      rw [instanceName_plain_some] at qev1518
      obtain ⟨qv1519, qvs1520, qm1521, qc1522, qc1523, rfl, qd1524, qa1525, rfl⟩ := qa1517.cons_inv
      obtain ⟨ql1526, rfl, rfl⟩ := qd1524.var_inv
      simp at ql1526
      subst ql1526
      obtain ⟨rfl, rfl, rfl⟩ := qa1525.nil_inv
      obtain ⟨qhe1527, qhe1528, -⟩ := Obs.«UInt8::to_field».obs qev1518
      subst qhe1527 qhe1528
      simp only [evalBinOp, Except.ok.injEq] at qop1360
      subst qop1360
      obtain ⟨rfl, rfl, rfl⟩ := qd1351.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1352
      subst qop1352
      obtain ⟨qvs1529, qm1530, qc1531, qcs1532, qa1533, qev1534, rfl⟩ := qd1343.call_inv
      rw [instanceName_plain_some] at qev1534
      obtain ⟨qv1535, qvs1536, qm1537, qc1538, qc1539, rfl, qd1540, qa1541, rfl⟩ := qa1533.cons_inv
      obtain ⟨ql1542, rfl, rfl⟩ := qd1540.var_inv
      simp at ql1542
      subst ql1542
      obtain ⟨rfl, rfl, rfl⟩ := qa1541.nil_inv
      obtain ⟨qhe1543, qhe1544, -⟩ := Obs.«UInt8::to_field».obs qev1534
      subst qhe1543 qhe1544
      simp only [evalBinOp, Except.ok.injEq] at qop1344
      subst qop1344
      obtain rfl := matchPattern_bind_inv qmt1335
      obtain ⟨qv1545, qm1546, qbs1547, qc1548, qc1549, qd1550, qmt1551, qd1552, rfl⟩ := qd1336.letValue_inv
      obtain ⟨qx1553, qy1554, qm1555, qc1556, qc1557, qd1558, qd1559, qop1560, rfl⟩ := qd1550.binary_inv
      obtain ⟨qx1561, qy1562, qm1563, qc1564, qc1565, qd1566, qd1567, qop1568, rfl⟩ := qd1558.binary_inv
      obtain ⟨qx1569, qy1570, qm1571, qc1572, qc1573, qd1574, qd1575, qop1576, rfl⟩ := qd1566.binary_inv
      obtain ⟨qx1577, qy1578, qm1579, qc1580, qc1581, qd1582, qd1583, qop1584, rfl⟩ := qd1574.binary_inv
      obtain ⟨qx1585, qy1586, qm1587, qc1588, qc1589, qd1590, qd1591, qop1592, rfl⟩ := qd1582.binary_inv
      obtain ⟨qx1593, qy1594, qm1595, qc1596, qc1597, qd1598, qd1599, qop1600, rfl⟩ := qd1590.binary_inv
      obtain ⟨qx1601, qy1602, qm1603, qc1604, qc1605, qd1606, qd1607, qop1608, rfl⟩ := qd1598.binary_inv
      obtain ⟨qx1609, qy1610, qm1611, qc1612, qc1613, qd1614, qd1615, qop1616, rfl⟩ := qd1606.binary_inv
      obtain ⟨qx1617, qy1618, qm1619, qc1620, qc1621, qd1622, qd1623, qop1624, rfl⟩ := qd1614.binary_inv
      obtain ⟨qx1625, qy1626, qm1627, qc1628, qc1629, qd1630, qd1631, qop1632, rfl⟩ := qd1622.binary_inv
      obtain ⟨qx1633, qy1634, qm1635, qc1636, qc1637, qd1638, qd1639, qop1640, rfl⟩ := qd1630.binary_inv
      obtain ⟨qx1641, qy1642, qm1643, qc1644, qc1645, qd1646, qd1647, qop1648, rfl⟩ := qd1638.binary_inv
      obtain ⟨qvs1649, qm1650, qc1651, qcs1652, qa1653, qev1654, rfl⟩ := qd1646.call_inv
      rw [instanceName_plain_some] at qev1654
      obtain ⟨qv1655, qvs1656, qm1657, qc1658, qc1659, rfl, qd1660, qa1661, rfl⟩ := qa1653.cons_inv
      obtain ⟨ql1662, rfl, rfl⟩ := qd1660.var_inv
      simp at ql1662
      subst ql1662
      obtain ⟨rfl, rfl, rfl⟩ := qa1661.nil_inv
      obtain ⟨qhe1663, qhe1664, -⟩ := Obs.«UInt8::to_field».obs qev1654
      subst qhe1663 qhe1664
      obtain ⟨rfl, rfl, rfl⟩ := qd1647.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1648
      subst qop1648
      obtain ⟨qvs1665, qm1666, qc1667, qcs1668, qa1669, qev1670, rfl⟩ := qd1639.call_inv
      rw [instanceName_plain_some] at qev1670
      obtain ⟨qv1671, qvs1672, qm1673, qc1674, qc1675, rfl, qd1676, qa1677, rfl⟩ := qa1669.cons_inv
      obtain ⟨ql1678, rfl, rfl⟩ := qd1676.var_inv
      simp at ql1678
      subst ql1678
      obtain ⟨rfl, rfl, rfl⟩ := qa1677.nil_inv
      obtain ⟨qhe1679, qhe1680, -⟩ := Obs.«UInt8::to_field».obs qev1670
      subst qhe1679 qhe1680
      simp only [evalBinOp, Except.ok.injEq] at qop1640
      subst qop1640
      obtain ⟨rfl, rfl, rfl⟩ := qd1631.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1632
      subst qop1632
      obtain ⟨qvs1681, qm1682, qc1683, qcs1684, qa1685, qev1686, rfl⟩ := qd1623.call_inv
      rw [instanceName_plain_some] at qev1686
      obtain ⟨qv1687, qvs1688, qm1689, qc1690, qc1691, rfl, qd1692, qa1693, rfl⟩ := qa1685.cons_inv
      obtain ⟨ql1694, rfl, rfl⟩ := qd1692.var_inv
      simp at ql1694
      subst ql1694
      obtain ⟨rfl, rfl, rfl⟩ := qa1693.nil_inv
      obtain ⟨qhe1695, qhe1696, -⟩ := Obs.«UInt8::to_field».obs qev1686
      subst qhe1695 qhe1696
      simp only [evalBinOp, Except.ok.injEq] at qop1624
      subst qop1624
      obtain ⟨rfl, rfl, rfl⟩ := qd1615.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1616
      subst qop1616
      obtain ⟨qvs1697, qm1698, qc1699, qcs1700, qa1701, qev1702, rfl⟩ := qd1607.call_inv
      rw [instanceName_plain_some] at qev1702
      obtain ⟨qv1703, qvs1704, qm1705, qc1706, qc1707, rfl, qd1708, qa1709, rfl⟩ := qa1701.cons_inv
      obtain ⟨ql1710, rfl, rfl⟩ := qd1708.var_inv
      simp at ql1710
      subst ql1710
      obtain ⟨rfl, rfl, rfl⟩ := qa1709.nil_inv
      obtain ⟨qhe1711, qhe1712, -⟩ := Obs.«UInt8::to_field».obs qev1702
      subst qhe1711 qhe1712
      simp only [evalBinOp, Except.ok.injEq] at qop1608
      subst qop1608
      obtain ⟨rfl, rfl, rfl⟩ := qd1599.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1600
      subst qop1600
      obtain ⟨qvs1713, qm1714, qc1715, qcs1716, qa1717, qev1718, rfl⟩ := qd1591.call_inv
      rw [instanceName_plain_some] at qev1718
      obtain ⟨qv1719, qvs1720, qm1721, qc1722, qc1723, rfl, qd1724, qa1725, rfl⟩ := qa1717.cons_inv
      obtain ⟨ql1726, rfl, rfl⟩ := qd1724.var_inv
      simp at ql1726
      subst ql1726
      obtain ⟨rfl, rfl, rfl⟩ := qa1725.nil_inv
      obtain ⟨qhe1727, qhe1728, -⟩ := Obs.«UInt8::to_field».obs qev1718
      subst qhe1727 qhe1728
      simp only [evalBinOp, Except.ok.injEq] at qop1592
      subst qop1592
      obtain ⟨rfl, rfl, rfl⟩ := qd1583.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1584
      subst qop1584
      obtain ⟨qvs1729, qm1730, qc1731, qcs1732, qa1733, qev1734, rfl⟩ := qd1575.call_inv
      rw [instanceName_plain_some] at qev1734
      obtain ⟨qv1735, qvs1736, qm1737, qc1738, qc1739, rfl, qd1740, qa1741, rfl⟩ := qa1733.cons_inv
      obtain ⟨ql1742, rfl, rfl⟩ := qd1740.var_inv
      simp at ql1742
      subst ql1742
      obtain ⟨rfl, rfl, rfl⟩ := qa1741.nil_inv
      obtain ⟨qhe1743, qhe1744, -⟩ := Obs.«UInt8::to_field».obs qev1734
      subst qhe1743 qhe1744
      simp only [evalBinOp, Except.ok.injEq] at qop1576
      subst qop1576
      obtain ⟨rfl, rfl, rfl⟩ := qd1567.literal_inv
      simp only [evalBinOp, Except.ok.injEq] at qop1568
      subst qop1568
      obtain ⟨qvs1745, qm1746, qc1747, qcs1748, qa1749, qev1750, rfl⟩ := qd1559.call_inv
      rw [instanceName_plain_some] at qev1750
      obtain ⟨qv1751, qvs1752, qm1753, qc1754, qc1755, rfl, qd1756, qa1757, rfl⟩ := qa1749.cons_inv
      obtain ⟨ql1758, rfl, rfl⟩ := qd1756.var_inv
      simp at ql1758
      subst ql1758
      obtain ⟨rfl, rfl, rfl⟩ := qa1757.nil_inv
      obtain ⟨qhe1759, qhe1760, -⟩ := Obs.«UInt8::to_field».obs qev1750
      subst qhe1759 qhe1760
      simp only [evalBinOp, Except.ok.injEq] at qop1560
      subst qop1560
      obtain rfl := matchPattern_bind_inv qmt1551
      obtain ⟨qv1761, qm1762, qbs1763, qbody1764, qc1765, qc1766, qd1767, qsel1768, qd1769, rfl⟩ := qd1552.matchValue_inv
      obtain ⟨qx1770, qy1771, qm1772, qc1773, qc1774, qd1775, qd1776, qop1777, rfl⟩ := qd1767.binary_inv
      obtain ⟨ql1778, rfl, rfl⟩ := qd1775.var_inv
      simp at ql1778
      subst ql1778
      obtain ⟨ql1779, rfl, rfl⟩ := qd1776.var_inv
      simp at ql1779
      subst ql1779
      simp only [evalBinOp, Except.ok.injEq] at qop1777
      subst qop1777
      rcases selectArm_cons_inv qsel1768 with ⟨qmt1780, rfl⟩ | ⟨qnm1781, qsel1782⟩
      · obtain ⟨qhv1783, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 0) qmt1780
        have qE1784 : (pack7 u15 u16 u17 u18 u19 u20 u21 - pack7 v15 v16 v17 v18 v19 v20 v21 : F) = 0 := Value.field.inj qhv1783
        obtain ⟨qv1785, qm1786, qbs1787, qc1788, qc1789, qd1790, qmt1791, qd1792, rfl⟩ := qd1769.letValue_inv
        obtain ⟨qx1793, qy1794, qm1795, qc1796, qc1797, qd1798, qd1799, qop1800, rfl⟩ := qd1790.binary_inv
        obtain ⟨qx1801, qy1802, qm1803, qc1804, qc1805, qd1806, qd1807, qop1808, rfl⟩ := qd1798.binary_inv
        obtain ⟨qx1809, qy1810, qm1811, qc1812, qc1813, qd1814, qd1815, qop1816, rfl⟩ := qd1806.binary_inv
        obtain ⟨qx1817, qy1818, qm1819, qc1820, qc1821, qd1822, qd1823, qop1824, rfl⟩ := qd1814.binary_inv
        obtain ⟨qx1825, qy1826, qm1827, qc1828, qc1829, qd1830, qd1831, qop1832, rfl⟩ := qd1822.binary_inv
        obtain ⟨qx1833, qy1834, qm1835, qc1836, qc1837, qd1838, qd1839, qop1840, rfl⟩ := qd1830.binary_inv
        obtain ⟨qx1841, qy1842, qm1843, qc1844, qc1845, qd1846, qd1847, qop1848, rfl⟩ := qd1838.binary_inv
        obtain ⟨qx1849, qy1850, qm1851, qc1852, qc1853, qd1854, qd1855, qop1856, rfl⟩ := qd1846.binary_inv
        obtain ⟨qx1857, qy1858, qm1859, qc1860, qc1861, qd1862, qd1863, qop1864, rfl⟩ := qd1854.binary_inv
        obtain ⟨qx1865, qy1866, qm1867, qc1868, qc1869, qd1870, qd1871, qop1872, rfl⟩ := qd1862.binary_inv
        obtain ⟨qx1873, qy1874, qm1875, qc1876, qc1877, qd1878, qd1879, qop1880, rfl⟩ := qd1870.binary_inv
        obtain ⟨qx1881, qy1882, qm1883, qc1884, qc1885, qd1886, qd1887, qop1888, rfl⟩ := qd1878.binary_inv
        obtain ⟨qvs1889, qm1890, qc1891, qcs1892, qa1893, qev1894, rfl⟩ := qd1886.call_inv
        rw [instanceName_plain_some] at qev1894
        obtain ⟨qv1895, qvs1896, qm1897, qc1898, qc1899, rfl, qd1900, qa1901, rfl⟩ := qa1893.cons_inv
        obtain ⟨ql1902, rfl, rfl⟩ := qd1900.var_inv
        simp at ql1902
        subst ql1902
        obtain ⟨rfl, rfl, rfl⟩ := qa1901.nil_inv
        obtain ⟨qhe1903, qhe1904, -⟩ := Obs.«UInt8::to_field».obs qev1894
        subst qhe1903 qhe1904
        obtain ⟨rfl, rfl, rfl⟩ := qd1887.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop1888
        subst qop1888
        obtain ⟨qvs1905, qm1906, qc1907, qcs1908, qa1909, qev1910, rfl⟩ := qd1879.call_inv
        rw [instanceName_plain_some] at qev1910
        obtain ⟨qv1911, qvs1912, qm1913, qc1914, qc1915, rfl, qd1916, qa1917, rfl⟩ := qa1909.cons_inv
        obtain ⟨ql1918, rfl, rfl⟩ := qd1916.var_inv
        simp at ql1918
        subst ql1918
        obtain ⟨rfl, rfl, rfl⟩ := qa1917.nil_inv
        obtain ⟨qhe1919, qhe1920, -⟩ := Obs.«UInt8::to_field».obs qev1910
        subst qhe1919 qhe1920
        simp only [evalBinOp, Except.ok.injEq] at qop1880
        subst qop1880
        obtain ⟨rfl, rfl, rfl⟩ := qd1871.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop1872
        subst qop1872
        obtain ⟨qvs1921, qm1922, qc1923, qcs1924, qa1925, qev1926, rfl⟩ := qd1863.call_inv
        rw [instanceName_plain_some] at qev1926
        obtain ⟨qv1927, qvs1928, qm1929, qc1930, qc1931, rfl, qd1932, qa1933, rfl⟩ := qa1925.cons_inv
        obtain ⟨ql1934, rfl, rfl⟩ := qd1932.var_inv
        simp at ql1934
        subst ql1934
        obtain ⟨rfl, rfl, rfl⟩ := qa1933.nil_inv
        obtain ⟨qhe1935, qhe1936, -⟩ := Obs.«UInt8::to_field».obs qev1926
        subst qhe1935 qhe1936
        simp only [evalBinOp, Except.ok.injEq] at qop1864
        subst qop1864
        obtain ⟨rfl, rfl, rfl⟩ := qd1855.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop1856
        subst qop1856
        obtain ⟨qvs1937, qm1938, qc1939, qcs1940, qa1941, qev1942, rfl⟩ := qd1847.call_inv
        rw [instanceName_plain_some] at qev1942
        obtain ⟨qv1943, qvs1944, qm1945, qc1946, qc1947, rfl, qd1948, qa1949, rfl⟩ := qa1941.cons_inv
        obtain ⟨ql1950, rfl, rfl⟩ := qd1948.var_inv
        simp at ql1950
        subst ql1950
        obtain ⟨rfl, rfl, rfl⟩ := qa1949.nil_inv
        obtain ⟨qhe1951, qhe1952, -⟩ := Obs.«UInt8::to_field».obs qev1942
        subst qhe1951 qhe1952
        simp only [evalBinOp, Except.ok.injEq] at qop1848
        subst qop1848
        obtain ⟨rfl, rfl, rfl⟩ := qd1839.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop1840
        subst qop1840
        obtain ⟨qvs1953, qm1954, qc1955, qcs1956, qa1957, qev1958, rfl⟩ := qd1831.call_inv
        rw [instanceName_plain_some] at qev1958
        obtain ⟨qv1959, qvs1960, qm1961, qc1962, qc1963, rfl, qd1964, qa1965, rfl⟩ := qa1957.cons_inv
        obtain ⟨ql1966, rfl, rfl⟩ := qd1964.var_inv
        simp at ql1966
        subst ql1966
        obtain ⟨rfl, rfl, rfl⟩ := qa1965.nil_inv
        obtain ⟨qhe1967, qhe1968, -⟩ := Obs.«UInt8::to_field».obs qev1958
        subst qhe1967 qhe1968
        simp only [evalBinOp, Except.ok.injEq] at qop1832
        subst qop1832
        obtain ⟨rfl, rfl, rfl⟩ := qd1823.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop1824
        subst qop1824
        obtain ⟨qvs1969, qm1970, qc1971, qcs1972, qa1973, qev1974, rfl⟩ := qd1815.call_inv
        rw [instanceName_plain_some] at qev1974
        obtain ⟨qv1975, qvs1976, qm1977, qc1978, qc1979, rfl, qd1980, qa1981, rfl⟩ := qa1973.cons_inv
        obtain ⟨ql1982, rfl, rfl⟩ := qd1980.var_inv
        simp at ql1982
        subst ql1982
        obtain ⟨rfl, rfl, rfl⟩ := qa1981.nil_inv
        obtain ⟨qhe1983, qhe1984, -⟩ := Obs.«UInt8::to_field».obs qev1974
        subst qhe1983 qhe1984
        simp only [evalBinOp, Except.ok.injEq] at qop1816
        subst qop1816
        obtain ⟨rfl, rfl, rfl⟩ := qd1807.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop1808
        subst qop1808
        obtain ⟨qvs1985, qm1986, qc1987, qcs1988, qa1989, qev1990, rfl⟩ := qd1799.call_inv
        rw [instanceName_plain_some] at qev1990
        obtain ⟨qv1991, qvs1992, qm1993, qc1994, qc1995, rfl, qd1996, qa1997, rfl⟩ := qa1989.cons_inv
        obtain ⟨ql1998, rfl, rfl⟩ := qd1996.var_inv
        simp at ql1998
        subst ql1998
        obtain ⟨rfl, rfl, rfl⟩ := qa1997.nil_inv
        obtain ⟨qhe1999, qhe2000, -⟩ := Obs.«UInt8::to_field».obs qev1990
        subst qhe1999 qhe2000
        simp only [evalBinOp, Except.ok.injEq] at qop1800
        subst qop1800
        obtain rfl := matchPattern_bind_inv qmt1791
        obtain ⟨qv2001, qm2002, qbs2003, qc2004, qc2005, qd2006, qmt2007, qd2008, rfl⟩ := qd1792.letValue_inv
        obtain ⟨qx2009, qy2010, qm2011, qc2012, qc2013, qd2014, qd2015, qop2016, rfl⟩ := qd2006.binary_inv
        obtain ⟨qx2017, qy2018, qm2019, qc2020, qc2021, qd2022, qd2023, qop2024, rfl⟩ := qd2014.binary_inv
        obtain ⟨qx2025, qy2026, qm2027, qc2028, qc2029, qd2030, qd2031, qop2032, rfl⟩ := qd2022.binary_inv
        obtain ⟨qx2033, qy2034, qm2035, qc2036, qc2037, qd2038, qd2039, qop2040, rfl⟩ := qd2030.binary_inv
        obtain ⟨qx2041, qy2042, qm2043, qc2044, qc2045, qd2046, qd2047, qop2048, rfl⟩ := qd2038.binary_inv
        obtain ⟨qx2049, qy2050, qm2051, qc2052, qc2053, qd2054, qd2055, qop2056, rfl⟩ := qd2046.binary_inv
        obtain ⟨qx2057, qy2058, qm2059, qc2060, qc2061, qd2062, qd2063, qop2064, rfl⟩ := qd2054.binary_inv
        obtain ⟨qx2065, qy2066, qm2067, qc2068, qc2069, qd2070, qd2071, qop2072, rfl⟩ := qd2062.binary_inv
        obtain ⟨qx2073, qy2074, qm2075, qc2076, qc2077, qd2078, qd2079, qop2080, rfl⟩ := qd2070.binary_inv
        obtain ⟨qx2081, qy2082, qm2083, qc2084, qc2085, qd2086, qd2087, qop2088, rfl⟩ := qd2078.binary_inv
        obtain ⟨qx2089, qy2090, qm2091, qc2092, qc2093, qd2094, qd2095, qop2096, rfl⟩ := qd2086.binary_inv
        obtain ⟨qx2097, qy2098, qm2099, qc2100, qc2101, qd2102, qd2103, qop2104, rfl⟩ := qd2094.binary_inv
        obtain ⟨qvs2105, qm2106, qc2107, qcs2108, qa2109, qev2110, rfl⟩ := qd2102.call_inv
        rw [instanceName_plain_some] at qev2110
        obtain ⟨qv2111, qvs2112, qm2113, qc2114, qc2115, rfl, qd2116, qa2117, rfl⟩ := qa2109.cons_inv
        obtain ⟨ql2118, rfl, rfl⟩ := qd2116.var_inv
        simp at ql2118
        subst ql2118
        obtain ⟨rfl, rfl, rfl⟩ := qa2117.nil_inv
        obtain ⟨qhe2119, qhe2120, -⟩ := Obs.«UInt8::to_field».obs qev2110
        subst qhe2119 qhe2120
        obtain ⟨rfl, rfl, rfl⟩ := qd2103.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop2104
        subst qop2104
        obtain ⟨qvs2121, qm2122, qc2123, qcs2124, qa2125, qev2126, rfl⟩ := qd2095.call_inv
        rw [instanceName_plain_some] at qev2126
        obtain ⟨qv2127, qvs2128, qm2129, qc2130, qc2131, rfl, qd2132, qa2133, rfl⟩ := qa2125.cons_inv
        obtain ⟨ql2134, rfl, rfl⟩ := qd2132.var_inv
        simp at ql2134
        subst ql2134
        obtain ⟨rfl, rfl, rfl⟩ := qa2133.nil_inv
        obtain ⟨qhe2135, qhe2136, -⟩ := Obs.«UInt8::to_field».obs qev2126
        subst qhe2135 qhe2136
        simp only [evalBinOp, Except.ok.injEq] at qop2096
        subst qop2096
        obtain ⟨rfl, rfl, rfl⟩ := qd2087.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop2088
        subst qop2088
        obtain ⟨qvs2137, qm2138, qc2139, qcs2140, qa2141, qev2142, rfl⟩ := qd2079.call_inv
        rw [instanceName_plain_some] at qev2142
        obtain ⟨qv2143, qvs2144, qm2145, qc2146, qc2147, rfl, qd2148, qa2149, rfl⟩ := qa2141.cons_inv
        obtain ⟨ql2150, rfl, rfl⟩ := qd2148.var_inv
        simp at ql2150
        subst ql2150
        obtain ⟨rfl, rfl, rfl⟩ := qa2149.nil_inv
        obtain ⟨qhe2151, qhe2152, -⟩ := Obs.«UInt8::to_field».obs qev2142
        subst qhe2151 qhe2152
        simp only [evalBinOp, Except.ok.injEq] at qop2080
        subst qop2080
        obtain ⟨rfl, rfl, rfl⟩ := qd2071.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop2072
        subst qop2072
        obtain ⟨qvs2153, qm2154, qc2155, qcs2156, qa2157, qev2158, rfl⟩ := qd2063.call_inv
        rw [instanceName_plain_some] at qev2158
        obtain ⟨qv2159, qvs2160, qm2161, qc2162, qc2163, rfl, qd2164, qa2165, rfl⟩ := qa2157.cons_inv
        obtain ⟨ql2166, rfl, rfl⟩ := qd2164.var_inv
        simp at ql2166
        subst ql2166
        obtain ⟨rfl, rfl, rfl⟩ := qa2165.nil_inv
        obtain ⟨qhe2167, qhe2168, -⟩ := Obs.«UInt8::to_field».obs qev2158
        subst qhe2167 qhe2168
        simp only [evalBinOp, Except.ok.injEq] at qop2064
        subst qop2064
        obtain ⟨rfl, rfl, rfl⟩ := qd2055.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop2056
        subst qop2056
        obtain ⟨qvs2169, qm2170, qc2171, qcs2172, qa2173, qev2174, rfl⟩ := qd2047.call_inv
        rw [instanceName_plain_some] at qev2174
        obtain ⟨qv2175, qvs2176, qm2177, qc2178, qc2179, rfl, qd2180, qa2181, rfl⟩ := qa2173.cons_inv
        obtain ⟨ql2182, rfl, rfl⟩ := qd2180.var_inv
        simp at ql2182
        subst ql2182
        obtain ⟨rfl, rfl, rfl⟩ := qa2181.nil_inv
        obtain ⟨qhe2183, qhe2184, -⟩ := Obs.«UInt8::to_field».obs qev2174
        subst qhe2183 qhe2184
        simp only [evalBinOp, Except.ok.injEq] at qop2048
        subst qop2048
        obtain ⟨rfl, rfl, rfl⟩ := qd2039.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop2040
        subst qop2040
        obtain ⟨qvs2185, qm2186, qc2187, qcs2188, qa2189, qev2190, rfl⟩ := qd2031.call_inv
        rw [instanceName_plain_some] at qev2190
        obtain ⟨qv2191, qvs2192, qm2193, qc2194, qc2195, rfl, qd2196, qa2197, rfl⟩ := qa2189.cons_inv
        obtain ⟨ql2198, rfl, rfl⟩ := qd2196.var_inv
        simp at ql2198
        subst ql2198
        obtain ⟨rfl, rfl, rfl⟩ := qa2197.nil_inv
        obtain ⟨qhe2199, qhe2200, -⟩ := Obs.«UInt8::to_field».obs qev2190
        subst qhe2199 qhe2200
        simp only [evalBinOp, Except.ok.injEq] at qop2032
        subst qop2032
        obtain ⟨rfl, rfl, rfl⟩ := qd2023.literal_inv
        simp only [evalBinOp, Except.ok.injEq] at qop2024
        subst qop2024
        obtain ⟨qvs2201, qm2202, qc2203, qcs2204, qa2205, qev2206, rfl⟩ := qd2015.call_inv
        rw [instanceName_plain_some] at qev2206
        obtain ⟨qv2207, qvs2208, qm2209, qc2210, qc2211, rfl, qd2212, qa2213, rfl⟩ := qa2205.cons_inv
        obtain ⟨ql2214, rfl, rfl⟩ := qd2212.var_inv
        simp at ql2214
        subst ql2214
        obtain ⟨rfl, rfl, rfl⟩ := qa2213.nil_inv
        obtain ⟨qhe2215, qhe2216, -⟩ := Obs.«UInt8::to_field».obs qev2206
        subst qhe2215 qhe2216
        simp only [evalBinOp, Except.ok.injEq] at qop2016
        subst qop2016
        obtain rfl := matchPattern_bind_inv qmt2007
        obtain ⟨qv2217, qm2218, qbs2219, qbody2220, qc2221, qc2222, qd2223, qsel2224, qd2225, rfl⟩ := qd2008.matchValue_inv
        obtain ⟨qx2226, qy2227, qm2228, qc2229, qc2230, qd2231, qd2232, qop2233, rfl⟩ := qd2223.binary_inv
        obtain ⟨ql2234, rfl, rfl⟩ := qd2231.var_inv
        simp at ql2234
        subst ql2234
        obtain ⟨ql2235, rfl, rfl⟩ := qd2232.var_inv
        simp at ql2235
        subst ql2235
        simp only [evalBinOp, Except.ok.injEq] at qop2233
        subst qop2233
        rcases selectArm_cons_inv qsel2224 with ⟨qmt2236, rfl⟩ | ⟨qnm2237, qsel2238⟩
        · obtain ⟨qhv2239, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 0) qmt2236
          have qE2240 : (pack7 u22 u23 u24 u25 u26 u27 u28 - pack7 v22 v23 v24 v25 v26 v27 v28 : F) = 0 := Value.field.inj qhv2239
          obtain ⟨qv2241, qm2242, qbs2243, qc2244, qc2245, qd2246, qmt2247, qd2248, rfl⟩ := qd2225.letValue_inv
          obtain ⟨qx2249, qy2250, qm2251, qc2252, qc2253, qd2254, qd2255, qop2256, rfl⟩ := qd2246.binary_inv
          obtain ⟨qx2257, qy2258, qm2259, qc2260, qc2261, qd2262, qd2263, qop2264, rfl⟩ := qd2254.binary_inv
          obtain ⟨qx2265, qy2266, qm2267, qc2268, qc2269, qd2270, qd2271, qop2272, rfl⟩ := qd2262.binary_inv
          obtain ⟨qx2273, qy2274, qm2275, qc2276, qc2277, qd2278, qd2279, qop2280, rfl⟩ := qd2270.binary_inv
          obtain ⟨qvs2281, qm2282, qc2283, qcs2284, qa2285, qev2286, rfl⟩ := qd2278.call_inv
          rw [instanceName_plain_some] at qev2286
          obtain ⟨qv2287, qvs2288, qm2289, qc2290, qc2291, rfl, qd2292, qa2293, rfl⟩ := qa2285.cons_inv
          obtain ⟨ql2294, rfl, rfl⟩ := qd2292.var_inv
          simp at ql2294
          subst ql2294
          obtain ⟨rfl, rfl, rfl⟩ := qa2293.nil_inv
          obtain ⟨qhe2295, qhe2296, -⟩ := Obs.«UInt8::to_field».obs qev2286
          subst qhe2295 qhe2296
          obtain ⟨rfl, rfl, rfl⟩ := qd2279.literal_inv
          simp only [evalBinOp, Except.ok.injEq] at qop2280
          subst qop2280
          obtain ⟨qvs2297, qm2298, qc2299, qcs2300, qa2301, qev2302, rfl⟩ := qd2271.call_inv
          rw [instanceName_plain_some] at qev2302
          obtain ⟨qv2303, qvs2304, qm2305, qc2306, qc2307, rfl, qd2308, qa2309, rfl⟩ := qa2301.cons_inv
          obtain ⟨ql2310, rfl, rfl⟩ := qd2308.var_inv
          simp at ql2310
          subst ql2310
          obtain ⟨rfl, rfl, rfl⟩ := qa2309.nil_inv
          obtain ⟨qhe2311, qhe2312, -⟩ := Obs.«UInt8::to_field».obs qev2302
          subst qhe2311 qhe2312
          simp only [evalBinOp, Except.ok.injEq] at qop2272
          subst qop2272
          obtain ⟨rfl, rfl, rfl⟩ := qd2263.literal_inv
          simp only [evalBinOp, Except.ok.injEq] at qop2264
          subst qop2264
          obtain ⟨qvs2313, qm2314, qc2315, qcs2316, qa2317, qev2318, rfl⟩ := qd2255.call_inv
          rw [instanceName_plain_some] at qev2318
          obtain ⟨qv2319, qvs2320, qm2321, qc2322, qc2323, rfl, qd2324, qa2325, rfl⟩ := qa2317.cons_inv
          obtain ⟨ql2326, rfl, rfl⟩ := qd2324.var_inv
          simp at ql2326
          subst ql2326
          obtain ⟨rfl, rfl, rfl⟩ := qa2325.nil_inv
          obtain ⟨qhe2327, qhe2328, -⟩ := Obs.«UInt8::to_field».obs qev2318
          subst qhe2327 qhe2328
          simp only [evalBinOp, Except.ok.injEq] at qop2256
          subst qop2256
          obtain rfl := matchPattern_bind_inv qmt2247
          obtain ⟨qv2329, qm2330, qbs2331, qc2332, qc2333, qd2334, qmt2335, qd2336, rfl⟩ := qd2248.letValue_inv
          obtain ⟨qx2337, qy2338, qm2339, qc2340, qc2341, qd2342, qd2343, qop2344, rfl⟩ := qd2334.binary_inv
          obtain ⟨qx2345, qy2346, qm2347, qc2348, qc2349, qd2350, qd2351, qop2352, rfl⟩ := qd2342.binary_inv
          obtain ⟨qx2353, qy2354, qm2355, qc2356, qc2357, qd2358, qd2359, qop2360, rfl⟩ := qd2350.binary_inv
          obtain ⟨qx2361, qy2362, qm2363, qc2364, qc2365, qd2366, qd2367, qop2368, rfl⟩ := qd2358.binary_inv
          obtain ⟨qvs2369, qm2370, qc2371, qcs2372, qa2373, qev2374, rfl⟩ := qd2366.call_inv
          rw [instanceName_plain_some] at qev2374
          obtain ⟨qv2375, qvs2376, qm2377, qc2378, qc2379, rfl, qd2380, qa2381, rfl⟩ := qa2373.cons_inv
          obtain ⟨ql2382, rfl, rfl⟩ := qd2380.var_inv
          simp at ql2382
          subst ql2382
          obtain ⟨rfl, rfl, rfl⟩ := qa2381.nil_inv
          obtain ⟨qhe2383, qhe2384, -⟩ := Obs.«UInt8::to_field».obs qev2374
          subst qhe2383 qhe2384
          obtain ⟨rfl, rfl, rfl⟩ := qd2367.literal_inv
          simp only [evalBinOp, Except.ok.injEq] at qop2368
          subst qop2368
          obtain ⟨qvs2385, qm2386, qc2387, qcs2388, qa2389, qev2390, rfl⟩ := qd2359.call_inv
          rw [instanceName_plain_some] at qev2390
          obtain ⟨qv2391, qvs2392, qm2393, qc2394, qc2395, rfl, qd2396, qa2397, rfl⟩ := qa2389.cons_inv
          obtain ⟨ql2398, rfl, rfl⟩ := qd2396.var_inv
          simp at ql2398
          subst ql2398
          obtain ⟨rfl, rfl, rfl⟩ := qa2397.nil_inv
          obtain ⟨qhe2399, qhe2400, -⟩ := Obs.«UInt8::to_field».obs qev2390
          subst qhe2399 qhe2400
          simp only [evalBinOp, Except.ok.injEq] at qop2360
          subst qop2360
          obtain ⟨rfl, rfl, rfl⟩ := qd2351.literal_inv
          simp only [evalBinOp, Except.ok.injEq] at qop2352
          subst qop2352
          obtain ⟨qvs2401, qm2402, qc2403, qcs2404, qa2405, qev2406, rfl⟩ := qd2343.call_inv
          rw [instanceName_plain_some] at qev2406
          obtain ⟨qv2407, qvs2408, qm2409, qc2410, qc2411, rfl, qd2412, qa2413, rfl⟩ := qa2405.cons_inv
          obtain ⟨ql2414, rfl, rfl⟩ := qd2412.var_inv
          simp at ql2414
          subst ql2414
          obtain ⟨rfl, rfl, rfl⟩ := qa2413.nil_inv
          obtain ⟨qhe2415, qhe2416, -⟩ := Obs.«UInt8::to_field».obs qev2406
          subst qhe2415 qhe2416
          simp only [evalBinOp, Except.ok.injEq] at qop2344
          subst qop2344
          obtain rfl := matchPattern_bind_inv qmt2335
          obtain ⟨qv2417, qm2418, qbs2419, qbody2420, qc2421, qc2422, qd2423, qsel2424, qd2425, rfl⟩ := qd2336.matchValue_inv
          obtain ⟨qx2426, qy2427, qm2428, qc2429, qc2430, qd2431, qd2432, qop2433, rfl⟩ := qd2423.binary_inv
          obtain ⟨ql2434, rfl, rfl⟩ := qd2431.var_inv
          simp at ql2434
          subst ql2434
          obtain ⟨ql2435, rfl, rfl⟩ := qd2432.var_inv
          simp at ql2435
          subst ql2435
          simp only [evalBinOp, Except.ok.injEq] at qop2433
          subst qop2433
          rcases selectArm_cons_inv qsel2424 with ⟨qmt2436, rfl⟩ | ⟨qnm2437, qsel2438⟩
          · obtain ⟨qhv2439, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 0) qmt2436
            have qE2440 : (pack3 u29 u30 u31 - pack3 v29 v30 v31 : F) = 0 := Value.field.inj qhv2439
            obtain ⟨rfl, rfl, rfl⟩ := qd2425.literal_inv
            refine ⟨?_, rfl⟩
            unfold tailModel
            rw [if_pos qE872, if_pos qE1328, if_pos qE1784, if_pos qE2240, if_pos qE2440]
            try rfl
          · have qhne2441 := MatchesConst.none_inv (MatchesConst.literal 0) qnm2437
            have qN2442 : ¬ ((pack3 u29 u30 u31 - pack3 v29 v30 v31 : F) = 0) := fun e => qhne2441 (congrArg Value.field e)
            rcases selectArm_cons_inv qsel2438 with ⟨qmt2443, rfl⟩ | ⟨qnm2444, qsel2445⟩
            · obtain rfl := matchPattern_wildcard_inv qmt2443
              obtain ⟨rfl, rfl, rfl⟩ := qd2425.literal_inv
              refine ⟨?_, rfl⟩
              unfold tailModel
              rw [if_pos qE872, if_pos qE1328, if_pos qE1784, if_pos qE2240, if_neg qN2442]
              try rfl
            · exact (matchPattern_wildcard_none qnm2444).elim
        · have qhne2446 := MatchesConst.none_inv (MatchesConst.literal 0) qnm2237
          have qN2447 : ¬ ((pack7 u22 u23 u24 u25 u26 u27 u28 - pack7 v22 v23 v24 v25 v26 v27 v28 : F) = 0) := fun e => qhne2446 (congrArg Value.field e)
          rcases selectArm_cons_inv qsel2238 with ⟨qmt2448, rfl⟩ | ⟨qnm2449, qsel2450⟩
          · obtain rfl := matchPattern_wildcard_inv qmt2448
            obtain ⟨rfl, rfl, rfl⟩ := qd2225.literal_inv
            refine ⟨?_, rfl⟩
            unfold tailModel
            rw [if_pos qE872, if_pos qE1328, if_pos qE1784, if_neg qN2447]
            try rfl
          · exact (matchPattern_wildcard_none qnm2449).elim
      · have qhne2451 := MatchesConst.none_inv (MatchesConst.literal 0) qnm1781
        have qN2452 : ¬ ((pack7 u15 u16 u17 u18 u19 u20 u21 - pack7 v15 v16 v17 v18 v19 v20 v21 : F) = 0) := fun e => qhne2451 (congrArg Value.field e)
        rcases selectArm_cons_inv qsel1782 with ⟨qmt2453, rfl⟩ | ⟨qnm2454, qsel2455⟩
        · obtain rfl := matchPattern_wildcard_inv qmt2453
          obtain ⟨rfl, rfl, rfl⟩ := qd1769.literal_inv
          refine ⟨?_, rfl⟩
          unfold tailModel
          rw [if_pos qE872, if_pos qE1328, if_neg qN2452]
          try rfl
        · exact (matchPattern_wildcard_none qnm2454).elim
    · have qhne2456 := MatchesConst.none_inv (MatchesConst.literal 0) qnm1325
      have qN2457 : ¬ ((pack7 u8 u9 u10 u11 u12 u13 u14 - pack7 v8 v9 v10 v11 v12 v13 v14 : F) = 0) := fun e => qhne2456 (congrArg Value.field e)
      rcases selectArm_cons_inv qsel1326 with ⟨qmt2458, rfl⟩ | ⟨qnm2459, qsel2460⟩
      · obtain rfl := matchPattern_wildcard_inv qmt2458
        obtain ⟨rfl, rfl, rfl⟩ := qd1313.literal_inv
        refine ⟨?_, rfl⟩
        unfold tailModel
        rw [if_pos qE872, if_neg qN2457]
        try rfl
      · exact (matchPattern_wildcard_none qnm2459).elim
  · have qhne2461 := MatchesConst.none_inv (MatchesConst.literal 0) qnm869
    have qN2462 : ¬ ((pack7 u1 u2 u3 u4 u5 u6 u7 - pack7 v1 v2 v3 v4 v5 v6 v7 : F) = 0) := fun e => qhne2461 (congrArg Value.field e)
    rcases selectArm_cons_inv qsel870 with ⟨qmt2463, rfl⟩ | ⟨qnm2464, qsel2465⟩
    · obtain rfl := matchPattern_wildcard_inv qmt2463
      obtain ⟨rfl, rfl, rfl⟩ := qd857.literal_inv
      refine ⟨?_, rfl⟩
      unfold tailModel
      rw [if_neg qN2462]
      try rfl
    · exact (matchPattern_wildcard_none qnm2464).elim

/-! ## Addresses -/

/-- An address's bytes, listed. -/
theorem vec32_toList (a : Bytes.Address) : a.toList = [a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10], a[11], a[12], a[13], a[14], a[15], a[16], a[17], a[18], a[19], a[20], a[21], a[22], a[23], a[24], a[25], a[26], a[27], a[28], a[29], a[30], a[31]] := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < 32 := by simpa using h1
    interval_cases i <;> first | rfl | simp

/-- **A represented address loads as its 32 bytes.** -/
theorem load_addr {h : Heap F} {a : Bytes.Address} {x : SourceValue F}
    (ha : Bytes.RepAddressRef addrTy h a x) :
    loadValue h x = .ok (.tuple [.field (a[0].toNat : F), .field (a[1].toNat : F), .field (a[2].toNat : F), .field (a[3].toNat : F), .field (a[4].toNat : F), .field (a[5].toNat : F), .field (a[6].toNat : F), .field (a[7].toNat : F), .field (a[8].toNat : F), .field (a[9].toNat : F), .field (a[10].toNat : F), .field (a[11].toNat : F), .field (a[12].toNat : F), .field (a[13].toNat : F), .field (a[14].toNat : F), .field (a[15].toNat : F), .field (a[16].toNat : F), .field (a[17].toNat : F), .field (a[18].toNat : F), .field (a[19].toNat : F), .field (a[20].toNat : F), .field (a[21].toNat : F), .field (a[22].toNat : F), .field (a[23].toNat : F), .field (a[24].toNat : F), .field (a[25].toNat : F), .field (a[26].toNat : F), .field (a[27].toNat : F), .field (a[28].toNat : F), .field (a[29].toNat : F), .field (a[30].toNat : F), .field (a[31].toNat : F)]) := by
  obtain ⟨addr, v, rfl, cell, hv⟩ := ha
  have hv' : v = .tuple [.field (a[0].toNat : F), .field (a[1].toNat : F), .field (a[2].toNat : F), .field (a[3].toNat : F), .field (a[4].toNat : F), .field (a[5].toNat : F), .field (a[6].toNat : F), .field (a[7].toNat : F), .field (a[8].toNat : F), .field (a[9].toNat : F), .field (a[10].toNat : F), .field (a[11].toNat : F), .field (a[12].toNat : F), .field (a[13].toNat : F), .field (a[14].toNat : F), .field (a[15].toNat : F), .field (a[16].toNat : F), .field (a[17].toNat : F), .field (a[18].toNat : F), .field (a[19].toNat : F), .field (a[20].toNat : F), .field (a[21].toNat : F), .field (a[22].toNat : F), .field (a[23].toNat : F), .field (a[24].toNat : F), .field (a[25].toNat : F), .field (a[26].toNat : F), .field (a[27].toNat : F), .field (a[28].toNat : F), .field (a[29].toNat : F), .field (a[30].toNat : F), .field (a[31].toNat : F)] := by
    have hv2 : v = .tuple (a.toList.map fun c => .field (c.toNat : F)) := hv
    rw [hv2, vec32_toList]
    rfl
  subst hv'
  simp [loadValue, cell, Value.type, bind, Except.bind, pure, Except.pure, List.replicate_succ,
    Aiur.Ty.tuple.injEq]

/-- The first projection of a tuple. -/
theorem projectValue_zero {v r : SourceValue F} {vs : List (SourceValue F)}
    (h : projectValue (.tuple (v :: vs)) 0 = .ok r) : r = v := by
  have e : projectValue (.tuple (v :: vs) : SourceValue F) 0 = .ok v := by
    first | rfl | simp [projectValue, bind, Except.bind, pure, Except.pure]
  rw [e] at h
  injection h with h
  exact h.symm

/-- `addressEqTail` is `tailModel` of the two addresses' last 31 bytes. -/
theorem addressEqTail_eq (a b : Bytes.Address) :
    Bytes.addressEqTail F a b = tailModel (a[1].toNat : F) (a[2].toNat : F) (a[3].toNat : F) (a[4].toNat : F) (a[5].toNat : F) (a[6].toNat : F) (a[7].toNat : F) (a[8].toNat : F) (a[9].toNat : F) (a[10].toNat : F) (a[11].toNat : F) (a[12].toNat : F) (a[13].toNat : F) (a[14].toNat : F) (a[15].toNat : F) (a[16].toNat : F) (a[17].toNat : F) (a[18].toNat : F) (a[19].toNat : F) (a[20].toNat : F) (a[21].toNat : F) (a[22].toNat : F) (a[23].toNat : F) (a[24].toNat : F) (a[25].toNat : F) (a[26].toNat : F) (a[27].toNat : F) (a[28].toNat : F) (a[29].toNat : F) (a[30].toNat : F) (a[31].toNat : F) (b[1].toNat : F) (b[2].toNat : F) (b[3].toNat : F) (b[4].toNat : F) (b[5].toNat : F) (b[6].toNat : F) (b[7].toNat : F) (b[8].toNat : F) (b[9].toNat : F) (b[10].toNat : F) (b[11].toNat : F) (b[12].toNat : F) (b[13].toNat : F) (b[14].toNat : F) (b[15].toNat : F) (b[16].toNat : F) (b[17].toNat : F) (b[18].toNat : F) (b[19].toNat : F) (b[20].toNat : F) (b[21].toNat : F) (b[22].toNat : F) (b[23].toNat : F) (b[24].toNat : F) (b[25].toNat : F) (b[26].toNat : F) (b[27].toNat : F) (b[28].toNat : F) (b[29].toNat : F) (b[30].toNat : F) (b[31].toNat : F)  := rfl

/-- **`Bytes::address_eq`**: on two represented addresses, `1` if they are equal and `0`
otherwise; no allocation. -/
theorem address_eq_spec {x y r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a b : Bytes.Address}
    (ev : ObsFn W "Bytes::address_eq" [x, y] h r h' cs)
    (ha : Bytes.RepAddressRef addrTy h a x) (hb : Bytes.RepAddressRef addrTy h b y) :
    r = .field (if a = b then 1 else 0) ∧ h' = h := by
  have hxl := load_addr ha
  have hyl := load_addr hb
  have hspec := Bytes.address_eq_spec Aiur.Library.U64.Goldilocks.compatible a b
  suffices hr : r = .field (Bytes.addressEq F a b) ∧ h' = h by
    exact ⟨hr.1.trans (congrArg Value.field hspec), hr.2⟩
  rcases Obs.«Bytes::address_eq».obs ev with
    ⟨v1, v13, m26, x34, y35, m36, cs45, v48, cs62, v65, cs83, ld11, ld23, pr57, ev47, pr74, ev64,
      op41, ev85, -⟩ |
    ⟨v1, v13, v25, m26, x34, y35, m36, cs45, v48, cs62, v65, ld11, ld23, pr57, ev47, pr74, ev64,
      op41, hne, rfl, rfl, -⟩
  · rw [hxl] at ld11
    injection ld11 with ld11
    subst ld11
    rw [hyl] at ld23
    injection ld23 with ld23
    subst ld23
    obtain rfl := projectValue_zero pr57
    obtain rfl := projectValue_zero pr74
    obtain ⟨he1, he2, -⟩ := Obs.«UInt8::to_field».obs ev47
    subst he1 he2
    obtain ⟨he3, he4, -⟩ := Obs.«UInt8::to_field».obs ev64
    subst he3 he4
    simp only [evalBinOp, Except.ok.injEq] at op41
    have e0 : ((a[0].toNat : F) - (b[0].toNat : F)) = 0 := Value.field.inj op41
    have haddr : Bytes.addressEq F a b = Bytes.addressEqTail F a b := if_pos e0
    obtain ⟨hr, rfl⟩ := tail_eval hxl hyl ev85
    refine ⟨?_, rfl⟩
    rw [hr, haddr, addressEqTail_eq]
  · rw [hxl] at ld11
    injection ld11 with ld11
    subst ld11
    rw [hyl] at ld23
    injection ld23 with ld23
    subst ld23
    obtain rfl := projectValue_zero pr57
    obtain rfl := projectValue_zero pr74
    obtain ⟨he1, he2, -⟩ := Obs.«UInt8::to_field».obs ev47
    subst he1 he2
    obtain ⟨he3, he4, -⟩ := Obs.«UInt8::to_field».obs ev64
    subst he3 he4
    simp only [evalBinOp, Except.ok.injEq] at op41
    subst op41
    have n0 : ¬ (((a[0].toNat : F) - (b[0].toNat : F)) = 0) := fun e => hne (congrArg Value.field e)
    have haddr : Bytes.addressEq F a b = 0 := if_neg n0
    refine ⟨?_, rfl⟩
    rw [haddr]

end IxVM.Refinement.Lib
