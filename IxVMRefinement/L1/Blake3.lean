import IxVMRefinement.L1.Layer
import Mathlib.Tactic.IntervalCases

/-! # `Blake3::hash` and the digest checks at source level

* `hash_spec`: every derivation of `Blake3::hash` on a byte stream returns the model
  `Aiur.Library.Blake3.hashModel`, which is `Blake3.Pure.digest` for inputs of fewer than
  `2^64` bytes (`hash_digest_spec`).
* `verify_bytes_against_spec`: a derivation of `Blake3::verify_bytes_against(bytes, expected)`
  pins the 32 entries of `expected` to the BLAKE3 digest of `bytes` (no range check of
  `expected` is needed: the comparison itself makes them bytes), so a represented address
  `expected` is that digest. The derivation calls `Blake3::hash` on the stream at the heap it
  was given (`verify_hash_call`).
* `bytes_to_addr_spec`: `Blake3::bytes_to_addr` stores the digest.
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
open Blake3.Pure (CV)
open Aiur.Library.Blake3 (compressLayer hashModel hashBlocks)

/-! ## `Blake3::hash` -/

@[simp] theorem type_tuple (xs : List (SourceValue F)) :
    (Value.tuple xs : SourceValue F).type = .tuple (xs.map Value.type) := by
  rw [Value.type]

/-- **`Blake3::hash`** computes the model `Aiur.Library.Blake3.hashModel` of its byte stream. -/
theorem hash_spec {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hs : Stream h bytes inp) (ev : ObsFn W "Blake3::hash" [inp] h r h' cs) :
    Heap.Extends h h' ∧ r = vecV (hashModel bytes) := by
  obtain ⟨v1, m2, cs12, cs18, v21, m23, cs31, m53, m65, m76, ev14, hm61, hm73, hm84, ev33, ev20,
    -⟩ := «Blake3::hash».obs ev
  obtain ⟨rfl, hm2⟩ := iv_src ev14
  subst m2
  subst hm61 hm73 hm84
  have hcc : loadValue (h ++ [(.tuple (List.replicate 8 (.field 0)) : SourceValue F)] ++
      [vecV Blake3.Pure.iv] ++ [.construct "Blake3::LayerNode" "Nil" []])
      (.ptr (.tuple (List.map Value.type (List.replicate 8 ((.field 0) : SourceValue F))))
        h.length) = .ok (u64v 0) := by
    have e := loadValue_snoc h (.tuple (List.replicate 8 (.field 0)) : SourceValue F)
    rw [type_tuple] at e
    rw [u64v_zero]
    exact loadValue_extend ((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)) e
  obtain ⟨ext1, hst⟩ := hash_blocks_spec bytes (n := 0) (c := 0) (cv := Blake3.Pure.iv)
    (layer := []) (by omega) (by exact hs.mono (extends3 _ _ _ _)) hcc
    (by exact loadValue_extend (Heap.Extends.snoc _ _) (loadValue_snoc _ _))
    (by exact stack_nil_snoc _) (by simpa only [Nat.cast_zero] using ev33)
  obtain ⟨ext2, rfl⟩ := compress_layer_spec _ hst ev20
  refine ⟨(extends3 _ _ _ _).trans (ext1.trans ext2), ?_⟩
  rw [List.reverse_reverse]
  rfl

/-- **`Blake3::hash` computes BLAKE3**: on fewer than `2^64` bytes, the bytes of its result
are `Blake3.Pure.digest`. -/
theorem hash_digest_spec {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hs : Stream h bytes inp) (native : Blake3.Pure.NativeInput bytes)
    (ev : ObsFn W "Blake3::hash" [inp] h r h' cs) :
    Heap.Extends h h' ∧ r = vecV (hashModel bytes) ∧
      Blake3.Pure.cvBytes (hashModel bytes) = Blake3.Pure.digest bytes :=
  ⟨(hash_spec hs ev).1, (hash_spec hs ev).2, Aiur.Library.Blake3.hash_model_spec bytes native⟩

/-! ## Digests -/

/-- A 32-byte digest or address as a value (`[U8; 32]`): `RepAddress`'s form. -/
def digestV (d : Vector UInt8 32) : SourceValue F := .tuple (d.toList.map bv)

theorem repAddress_iff {h : Heap F} {d : Vector UInt8 32} {v : SourceValue F} :
    Aiur.Library.Bytes.RepAddress h d v ↔ v = digestV d := Iff.rfl

theorem proj_digestV (d : Vector UInt8 32) (i : Nat) (hi : i < 32) :
    projectValue (digestV d : SourceValue F) i = .ok (bv d[i]) := by
  have hl : i < (d.toList.map bv : List (SourceValue F)).length := by simpa using hi
  rw [digestV, proj_getElem _ _ hl]
  simp

theorem proj_wv_0 (w : UInt32) :
    projectValue (wv w : SourceValue F) 0 = .ok (bv (Blake3.Pure.wordBytes w)[0]) := rfl
theorem proj_wv_1 (w : UInt32) :
    projectValue (wv w : SourceValue F) 1 = .ok (bv (Blake3.Pure.wordBytes w)[1]) := rfl
theorem proj_wv_2 (w : UInt32) :
    projectValue (wv w : SourceValue F) 2 = .ok (bv (Blake3.Pure.wordBytes w)[2]) := rfl
theorem proj_wv_3 (w : UInt32) :
    projectValue (wv w : SourceValue F) 3 = .ok (bv (Blake3.Pure.wordBytes w)[3]) := rfl

theorem digest_list (cv : CV) :
    ((Blake3.Pure.cvBytes cv).toList.map bv : List (SourceValue F)) =
      [bv (Blake3.Pure.wordBytes cv[0])[0], bv (Blake3.Pure.wordBytes cv[0])[1],
        bv (Blake3.Pure.wordBytes cv[0])[2], bv (Blake3.Pure.wordBytes cv[0])[3],
        bv (Blake3.Pure.wordBytes cv[1])[0], bv (Blake3.Pure.wordBytes cv[1])[1],
        bv (Blake3.Pure.wordBytes cv[1])[2], bv (Blake3.Pure.wordBytes cv[1])[3],
        bv (Blake3.Pure.wordBytes cv[2])[0], bv (Blake3.Pure.wordBytes cv[2])[1],
        bv (Blake3.Pure.wordBytes cv[2])[2], bv (Blake3.Pure.wordBytes cv[2])[3],
        bv (Blake3.Pure.wordBytes cv[3])[0], bv (Blake3.Pure.wordBytes cv[3])[1],
        bv (Blake3.Pure.wordBytes cv[3])[2], bv (Blake3.Pure.wordBytes cv[3])[3],
        bv (Blake3.Pure.wordBytes cv[4])[0], bv (Blake3.Pure.wordBytes cv[4])[1],
        bv (Blake3.Pure.wordBytes cv[4])[2], bv (Blake3.Pure.wordBytes cv[4])[3],
        bv (Blake3.Pure.wordBytes cv[5])[0], bv (Blake3.Pure.wordBytes cv[5])[1],
        bv (Blake3.Pure.wordBytes cv[5])[2], bv (Blake3.Pure.wordBytes cv[5])[3],
        bv (Blake3.Pure.wordBytes cv[6])[0], bv (Blake3.Pure.wordBytes cv[6])[1],
        bv (Blake3.Pure.wordBytes cv[6])[2], bv (Blake3.Pure.wordBytes cv[6])[3],
        bv (Blake3.Pure.wordBytes cv[7])[0], bv (Blake3.Pure.wordBytes cv[7])[1],
        bv (Blake3.Pure.wordBytes cv[7])[2], bv (Blake3.Pure.wordBytes cv[7])[3]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, Vector.length_toList] at h1
  simp only [List.getElem_map, Vector.getElem_toList, Blake3.Pure.cvBytes, Vector.getElem_ofFn]
  interval_cases i <;> rfl

/-- **`Blake3::digest_bytes`** lays out a chaining value's bytes (`Blake3.Pure.cvBytes`). -/
theorem digest_bytes_spec {cv : CV} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "Blake3::digest_bytes" [vecV cv] h r h' cs) :
    r = digestV (Blake3.Pure.cvBytes cv) ∧ h' = h := by
  obtain ⟨v1, m2, cs12, v15, v26, m27, cs37, v40, v51, m52, cs62, v65, v76, m77, cs87, v90, v101,
    m102, cs112, v115, v126, m127, cs137, v140, v151, m152, cs162, v165, v176, m177, cs187, v190,
    v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217,
    v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231, v232,
    v233, v234, pr24, ev14, pr49, ev39, pr74, ev64, pr99, ev89, pr124, ev114, pr149, ev139,
    pr174, ev164, pr199, ev189, he235, pr244, pr254, pr264, pr274, pr284, pr294, pr304, pr314,
    pr324, pr334, pr344, pr354, pr364, pr374, pr384, pr394, pr404, pr414, pr424, pr434, pr444,
    pr454, pr464, pr474, pr484, pr494, pr504, pr514, pr524, pr534, pr544, pr554, he556,
    -⟩ := «Blake3::digest_bytes».obs ev
  obtain rfl := ok_inj ((proj_vecV cv 0 (by decide)).symm.trans pr24)
  obtain rfl := ok_inj ((proj_vecV cv 1 (by decide)).symm.trans pr49)
  obtain rfl := ok_inj ((proj_vecV cv 2 (by decide)).symm.trans pr74)
  obtain rfl := ok_inj ((proj_vecV cv 3 (by decide)).symm.trans pr99)
  obtain rfl := ok_inj ((proj_vecV cv 4 (by decide)).symm.trans pr124)
  obtain rfl := ok_inj ((proj_vecV cv 5 (by decide)).symm.trans pr149)
  obtain rfl := ok_inj ((proj_vecV cv 6 (by decide)).symm.trans pr174)
  obtain rfl := ok_inj ((proj_vecV cv 7 (by decide)).symm.trans pr199)
  obtain ⟨rfl, hm2⟩ := u32_toBytes ev14
  obtain ⟨rfl, hm27⟩ := u32_toBytes ev39
  obtain ⟨rfl, hm52⟩ := u32_toBytes ev64
  obtain ⟨rfl, hm77⟩ := u32_toBytes ev89
  obtain ⟨rfl, hm102⟩ := u32_toBytes ev114
  obtain ⟨rfl, hm127⟩ := u32_toBytes ev139
  obtain ⟨rfl, hm152⟩ := u32_toBytes ev164
  obtain ⟨rfl, hm177⟩ := u32_toBytes ev189
  subst m2
  subst m27
  subst m52
  subst m77
  subst m102
  subst m127
  subst m152
  subst m177
  obtain rfl := ok_inj ((proj_wv_0 _).symm.trans pr244)
  obtain rfl := ok_inj ((proj_wv_1 _).symm.trans pr254)
  obtain rfl := ok_inj ((proj_wv_2 _).symm.trans pr264)
  obtain rfl := ok_inj ((proj_wv_3 _).symm.trans pr274)
  obtain rfl := ok_inj ((proj_wv_0 _).symm.trans pr284)
  obtain rfl := ok_inj ((proj_wv_1 _).symm.trans pr294)
  obtain rfl := ok_inj ((proj_wv_2 _).symm.trans pr304)
  obtain rfl := ok_inj ((proj_wv_3 _).symm.trans pr314)
  obtain rfl := ok_inj ((proj_wv_0 _).symm.trans pr324)
  obtain rfl := ok_inj ((proj_wv_1 _).symm.trans pr334)
  obtain rfl := ok_inj ((proj_wv_2 _).symm.trans pr344)
  obtain rfl := ok_inj ((proj_wv_3 _).symm.trans pr354)
  obtain rfl := ok_inj ((proj_wv_0 _).symm.trans pr364)
  obtain rfl := ok_inj ((proj_wv_1 _).symm.trans pr374)
  obtain rfl := ok_inj ((proj_wv_2 _).symm.trans pr384)
  obtain rfl := ok_inj ((proj_wv_3 _).symm.trans pr394)
  obtain rfl := ok_inj ((proj_wv_0 _).symm.trans pr404)
  obtain rfl := ok_inj ((proj_wv_1 _).symm.trans pr414)
  obtain rfl := ok_inj ((proj_wv_2 _).symm.trans pr424)
  obtain rfl := ok_inj ((proj_wv_3 _).symm.trans pr434)
  obtain rfl := ok_inj ((proj_wv_0 _).symm.trans pr444)
  obtain rfl := ok_inj ((proj_wv_1 _).symm.trans pr454)
  obtain rfl := ok_inj ((proj_wv_2 _).symm.trans pr464)
  obtain rfl := ok_inj ((proj_wv_3 _).symm.trans pr474)
  obtain rfl := ok_inj ((proj_wv_0 _).symm.trans pr484)
  obtain rfl := ok_inj ((proj_wv_1 _).symm.trans pr494)
  obtain rfl := ok_inj ((proj_wv_2 _).symm.trans pr504)
  obtain rfl := ok_inj ((proj_wv_3 _).symm.trans pr514)
  obtain rfl := ok_inj ((proj_wv_0 _).symm.trans pr524)
  obtain rfl := ok_inj ((proj_wv_1 _).symm.trans pr534)
  obtain rfl := ok_inj ((proj_wv_2 _).symm.trans pr544)
  obtain rfl := ok_inj ((proj_wv_3 _).symm.trans pr554)
  subst he235
  refine ⟨?_, by subst_vars; rfl⟩
  rw [digestV, digest_list]

/-- **`Blake3::address_to_fields`** reads the first 32 entries of its argument
(`UInt8::to_field` is the identity on a byte's field). -/
theorem address_to_fields_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "Blake3::address_to_fields" [x] h r h' cs) :
    h' = h ∧ ∃ l : List (SourceValue F), r = .tuple l ∧
      ∀ i, i < 32 → projectValue x i = .ok (l.getD i (.tuple [])) := by
  obtain ⟨v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21,
    v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, m37, cs45, v48, m60, cs68,
    v71, m83, cs91, v94, m106, cs114, v117, m129, cs137, v140, m152, cs160, v163, m175, cs183,
    v186, m198, cs206, v209, m221, cs229, v232, m244, cs252, v255, m267, cs275, v278, m290, cs298,
    v301, m313, cs321, v324, m336, cs344, v347, m359, cs367, v370, m382, cs390, v393, m405, cs413,
    v416, m428, cs436, v439, m451, cs459, v462, m474, cs482, v485, m497, cs505, v508, m520, cs528,
    v531, m543, cs551, v554, m566, cs574, v577, m589, cs597, v600, m612, cs620, v623, m635, cs643,
    v646, m658, cs666, v669, m681, cs689, v692, m704, cs712, v715, m727, cs735, v738, m750, cs758,
    v761, he35, pr57, ev47, pr80, ev70, pr103, ev93, pr126, ev116, pr149, ev139, pr172, ev162,
    pr195, ev185, pr218, ev208, pr241, ev231, pr264, ev254, pr287, ev277, pr310, ev300, pr333,
    ev323, pr356, ev346, pr379, ev369, pr402, ev392, pr425, ev415, pr448, ev438, pr471, ev461,
    pr494, ev484, pr517, ev507, pr540, ev530, pr563, ev553, pr586, ev576, pr609, ev599, pr632,
    ev622, pr655, ev645, pr678, ev668, pr701, ev691, pr724, ev714, pr747, ev737, pr770, ev760,
    he772, -⟩ := «Blake3::address_to_fields».obs ev
  obtain ⟨rfl, rfl⟩ := u8_toField ev47
  obtain ⟨rfl, rfl⟩ := u8_toField ev70
  obtain ⟨rfl, rfl⟩ := u8_toField ev93
  obtain ⟨rfl, rfl⟩ := u8_toField ev116
  obtain ⟨rfl, rfl⟩ := u8_toField ev139
  obtain ⟨rfl, rfl⟩ := u8_toField ev162
  obtain ⟨rfl, rfl⟩ := u8_toField ev185
  obtain ⟨rfl, rfl⟩ := u8_toField ev208
  obtain ⟨rfl, rfl⟩ := u8_toField ev231
  obtain ⟨rfl, rfl⟩ := u8_toField ev254
  obtain ⟨rfl, rfl⟩ := u8_toField ev277
  obtain ⟨rfl, rfl⟩ := u8_toField ev300
  obtain ⟨rfl, rfl⟩ := u8_toField ev323
  obtain ⟨rfl, rfl⟩ := u8_toField ev346
  obtain ⟨rfl, rfl⟩ := u8_toField ev369
  obtain ⟨rfl, rfl⟩ := u8_toField ev392
  obtain ⟨rfl, rfl⟩ := u8_toField ev415
  obtain ⟨rfl, rfl⟩ := u8_toField ev438
  obtain ⟨rfl, rfl⟩ := u8_toField ev461
  obtain ⟨rfl, rfl⟩ := u8_toField ev484
  obtain ⟨rfl, rfl⟩ := u8_toField ev507
  obtain ⟨rfl, rfl⟩ := u8_toField ev530
  obtain ⟨rfl, rfl⟩ := u8_toField ev553
  obtain ⟨rfl, rfl⟩ := u8_toField ev576
  obtain ⟨rfl, rfl⟩ := u8_toField ev599
  obtain ⟨rfl, rfl⟩ := u8_toField ev622
  obtain ⟨rfl, rfl⟩ := u8_toField ev645
  obtain ⟨rfl, rfl⟩ := u8_toField ev668
  obtain ⟨rfl, rfl⟩ := u8_toField ev691
  obtain ⟨rfl, rfl⟩ := u8_toField ev714
  obtain ⟨rfl, rfl⟩ := u8_toField ev737
  obtain ⟨rfl, rfl⟩ := u8_toField ev760
  subst he35 he772
  refine ⟨rfl, _, rfl, ?_⟩
  intro i hi
  interval_cases i
  all_goals assumption

/-! ## `Blake3::verify_bytes_against` and `Blake3::bytes_to_addr` -/

/-- **`Blake3::verify_bytes_against(bytes, expected)`** pins the first 32 entries of `expected`
to the bytes of `hashModel` of the stream, and calls `Blake3::hash` on the stream at the heap
it was given. -/
theorem verify_spec {bytes : List UInt8} {inp expected r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hs : Stream h bytes inp)
    (ev : ObsFn W "Blake3::verify_bytes_against" [inp, expected] h r h' cs) :
    Heap.Extends h h' ∧ (⟨"Blake3::hash", [inp], h⟩ : Call F) ∈ cs ∧
      ∀ i, (hi : i < 32) →
        projectValue expected i = .ok (bv (Blake3.Pure.cvBytes (hashModel bytes))[i]) := by
  obtain ⟨v1, m2, cs12, v34, v35, m37, cs45, v48, m50, cs58, m70, cs78, ev14, ev60, ev47, ev80,
    heq89, he92, he93, hc94⟩ := «Blake3::verify_bytes_against».obs ev
  obtain ⟨ext1, rfl⟩ := hash_spec hs ev14
  obtain ⟨rfl, hm50⟩ := digest_bytes_spec ev60
  obtain ⟨hm37, l1, rfl, hl1⟩ := address_to_fields_spec ev47
  obtain ⟨hm70, l2, rfl, hl2⟩ := address_to_fields_spec ev80
  have e : l1 = l2 := Value.tuple.inj heq89
  subst e
  refine ⟨?_, by rw [hc94]; simp, ?_⟩
  · rw [he93, hm70, hm37, hm50]
    exact ext1
  intro i hi
  rw [hl2 i hi, ← hl1 i hi, proj_digestV _ i hi]

/-- **The hash call of `verify_bytes_against`**: its derivation's calls include
`Blake3::hash` on the stream, at the heap `verify_bytes_against` was given. -/
theorem verify_hash_call {bytes : List UInt8} {inp expected r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hs : Stream h bytes inp)
    (ev : ObsFn W "Blake3::verify_bytes_against" [inp, expected] h r h' cs) :
    (⟨"Blake3::hash", [inp], h⟩ : Call F) ∈ cs :=
  (verify_spec hs ev).2.1

theorem digest_eq_of_proj {addr d : Vector UInt8 32} {expected : SourceValue F}
    (ha : expected = digestV addr)
    (hp : ∀ i, (hi : i < 32) → projectValue expected i = .ok (bv d[i])) : d = addr := by
  subst ha
  apply Vector.ext
  intro i hi
  have e := (proj_digestV addr i hi).symm.trans (hp i hi)
  exact (bv_inj (ok_inj e)).symm

/-- **`Blake3::verify_bytes_against` accepts only the BLAKE3 digest**: if `expected` represents
the address `addr` (`RepAddress`) and the stream holds fewer than `2^64` bytes, an accepting
derivation forces `Blake3.Pure.digest bytes = addr`. -/
theorem verify_bytes_against_spec {bytes : List UInt8} {addr : Blake3.Pure.Digest}
    {inp expected r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hs : Stream h bytes inp) (ha : Aiur.Library.Bytes.RepAddress h addr expected)
    (native : Blake3.Pure.NativeInput bytes)
    (ev : ObsFn W "Blake3::verify_bytes_against" [inp, expected] h r h' cs) :
    Blake3.Pure.digest bytes = addr := by
  rw [← Aiur.Library.Blake3.hash_model_spec bytes native]
  exact digest_eq_of_proj ha (verify_spec hs ev).2.2

/-- **`Blake3::bytes_to_addr`** stores `cvBytes (hashModel bytes)` (the BLAKE3 digest, for
fewer than `2^64` bytes) and returns a pointer to it. -/
theorem bytes_to_addr_spec {bytes : List UInt8} {inp r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hs : Stream h bytes inp)
    (ev : ObsFn W "Blake3::bytes_to_addr" [inp] h r h' cs) :
    Heap.Extends h h' ∧
      loadValue h' r = .ok (digestV (Blake3.Pure.cvBytes (hashModel bytes))) ∧
      (⟨"Blake3::hash", [inp], h⟩ : Call F) ∈ cs := by
  obtain ⟨v1, m2, cs12, v23, m24, cs31, ev14, he27, hm26, ev33, hc42⟩ :=
    «Blake3::bytes_to_addr».obs ev
  obtain ⟨ext1, rfl⟩ := hash_spec hs ev14
  obtain ⟨rfl, hm24⟩ := digest_bytes_spec ev33
  subst m24
  subst he27 hm26
  exact ⟨ext1.trans (Heap.Extends.snoc _ _), loadValue_snoc _ _, by rw [hc42]; simp⟩

end IxVM.Refinement.L1
