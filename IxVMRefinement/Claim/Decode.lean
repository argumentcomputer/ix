import IxVMRefinement.Claim.RoleTable
import IxVMRefinement.Obs.IxVM0
import IxVMRefinement.Obs.KernelClaim0
import IxVMRefinement.Obs.KernelClaim1
import IxVMRefinement.Obs.KernelClaim2
import IxVMRefinement.Obs.IxonSerialize1
import IxC.Ixon.Verify.ConstantTables

/-! # Claim decoding, assumption-tree verification, and entry dispatch for L6

Connects `IxVM::verify_claim` (`KernelClaim::run_claim`) on an `InScope` claim to its decoded
`Ix.Claim`, role-table admission (`RCFullRep`), seed extraction (`ClaimSeeds`, including Merkle
assumption-tree verification in `load_assumption_tree` against `V.trees` modulo
`V.HashedCollision`), and the resulting seed-check / walk obligations (`assert_claimable` +
`run_check_transitive` for `.check`, `walk_leaves_owned` for `.checkEnv`). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Obs (W)
open IxVM (F)
open Ix (Claim ClaimContext AssumptionTree)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## Address representation and `ByteArray` helpers -/

theorem digestV_type (d : Vector UInt8 32) : (L1.digestV d).type = addrTy := by
  rw [L1.digestV, Value.type, addrTy]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [L1.bv, Value.type]

theorem repAddressRef_of_load_digestV {h : Heap F} {r : SourceValue F} {d : Vector UInt8 32}
    (hl : loadValue h r = .ok (L1.digestV d)) :
    Bytes.RepAddressRef addrTy h d r := by
  cases r with
  | ptr ty n =>
    cases cell : h[n]? with
    | none => simp [loadValue, cell] at hl
    | some v =>
      by_cases ht : v.type = ty
      · subst ht
        have hv : v = L1.digestV d := by
          have e : loadValue h (.ptr v.type n) = .ok v := by
            simp [loadValue, cell, bind, Except.bind, pure, Except.pure]
          exact Except.ok.inj (e.symm.trans hl)
        subst hv
        rw [digestV_type]
        exact ⟨n, L1.digestV d, rfl, cell, rfl⟩
      · simp [loadValue, cell, ht, bind, Except.bind, pure, Except.pure] at hl
  | _ => simp [loadValue] at hl

private theorem byteArray_eq_of_toList {x y : ByteArray} (h : x.data.toList = y.data.toList) :
    x = y :=
  ByteArray.ext (Array.toList_inj.mp h)

private theorem blake3Pure_hash_size (b : ByteArray) :
    (Address.blake3Pure b).hash.size = 32 := by
  cases b with
  | mk arr =>
    have h := L1.blake3Pure_eq arr.toList
    simp only [Array.toArray_toList] at h
    rw [h]
    simp [L1.ixAddr, ByteArray.size]

private theorem treeRoot_hash_size : ∀ t : AssumptionTree, (treeRoot t).hash.size = 32
  | .leaf a => by
    unfold treeRoot Ix.HostAdmission.Merkle.leaf
    rw [Address.admissionHash_eq]
    exact blake3Pure_hash_size _
  | .padding => by
    simp [treeRoot, Ix.HostAdmission.Merkle.padding, ByteArray.size]
  | .node l r => by
    unfold treeRoot Ix.HostAdmission.Merkle.node
    rw [Address.admissionHash_eq]
    exact blake3Pure_hash_size _

/-! ## `IxonSerialize::put_address`, `leaf_hash`, and `node_hash` -/

private theorem vector32_toList (a : Vector UInt8 32) :
    [a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7],
     a[8], a[9], a[10], a[11], a[12], a[13], a[14], a[15],
     a[16], a[17], a[18], a[19], a[20], a[21], a[22], a[23],
     a[24], a[25], a[26], a[27], a[28], a[29], a[30], a[31]] = a.toList := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_cons, List.length_nil] at h1
  simp only [Vector.getElem_toList]
  interval_cases i <;> rfl

theorem put_address_spec {a : Bytes.Address} {rest : List UInt8}
    {x_a x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ha : Bytes.RepAddressRef addrTy h a x_a)
    (hrest : L1.Stream h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_address" [x_a, x_rest] h r h' calls) :
    Heap.Extends h h' ∧ L1.Stream h' (a.toList ++ rest) r := by
  have ext := ev.heap_extends
  obtain ⟨v1, m14, v28, m48, v62, m82, v96, m116, v130, m150, v164, m184, v198, m218, v232, m252,
    v266, m286, v300, m320, v334, m354, v368, m388, v402, m422, v436, m456, v470, m490, v504, m524,
    v538, m558, v572, m592, v606, m626, v640, m660, v674, m694, v708, m728, v742, m762, v776, m796,
    v810, m830, v844, m864, v878, m898, v912, m932, v946, m966, v980, m1000, v1014, m1034, v1048,
    v1075, ld11, hm24, pr38, hm58, pr72, hm92, pr106, hm126, pr140, hm160, pr174, hm194, pr208,
    hm228, pr242, hm262, pr276, hm296, pr310, hm330, pr344, hm364, pr378, hm398, pr412, hm432,
    pr446, hm466, pr480, hm500, pr514, hm534, pr548, hm568, pr582, hm602, pr616, hm636, pr650,
    hm670, pr684, hm704, pr718, hm738, pr752, hm772, pr786, hm806, pr820, hm840, pr854, hm874,
    pr888, hm908, pr922, hm942, pr956, hm976, pr990, hm1010, pr1024, hm1044, pr1058, he1071,
    hm1070, pr1085, _⟩ := Obs.«IxonSerialize::put_address».obs ev
  have hv1 := L1.load_repAddressRef ha ld11
  subst hv1
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 31 (by decide)).symm.trans pr38)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 30 (by decide)).symm.trans pr72)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 29 (by decide)).symm.trans pr106)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 28 (by decide)).symm.trans pr140)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 27 (by decide)).symm.trans pr174)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 26 (by decide)).symm.trans pr208)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 25 (by decide)).symm.trans pr242)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 24 (by decide)).symm.trans pr276)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 23 (by decide)).symm.trans pr310)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 22 (by decide)).symm.trans pr344)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 21 (by decide)).symm.trans pr378)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 20 (by decide)).symm.trans pr412)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 19 (by decide)).symm.trans pr446)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 18 (by decide)).symm.trans pr480)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 17 (by decide)).symm.trans pr514)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 16 (by decide)).symm.trans pr548)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 15 (by decide)).symm.trans pr582)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 14 (by decide)).symm.trans pr616)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 13 (by decide)).symm.trans pr650)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 12 (by decide)).symm.trans pr684)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 11 (by decide)).symm.trans pr718)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 10 (by decide)).symm.trans pr752)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 9 (by decide)).symm.trans pr786)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 8 (by decide)).symm.trans pr820)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 7 (by decide)).symm.trans pr854)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 6 (by decide)).symm.trans pr888)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 5 (by decide)).symm.trans pr922)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 4 (by decide)).symm.trans pr956)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 3 (by decide)).symm.trans pr990)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 2 (by decide)).symm.trans pr1024)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 1 (by decide)).symm.trans pr1058)
  obtain rfl := L1.ok_inj ((L1.proj_digestV a 0 (by decide)).symm.trans pr1085)
  have hs31 : L1.Stream m14 (a[31] :: rest) (.ptr (.enum byteStreamEnum) h.length) := by
    rw [hm24]; exact L1.stream_cons_snoc hrest
  have hs30 : L1.Stream m48 (a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m14.length) := by
    rw [hm58]; exact L1.stream_cons_snoc hs31
  have hs29 : L1.Stream m82 (a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m48.length) := by
    rw [hm92]; exact L1.stream_cons_snoc hs30
  have hs28 : L1.Stream m116 (a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m82.length) := by
    rw [hm126]; exact L1.stream_cons_snoc hs29
  have hs27 : L1.Stream m150 (a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m116.length) := by
    rw [hm160]; exact L1.stream_cons_snoc hs28
  have hs26 : L1.Stream m184 (a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m150.length) := by
    rw [hm194]; exact L1.stream_cons_snoc hs27
  have hs25 : L1.Stream m218 (a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m184.length) := by
    rw [hm228]; exact L1.stream_cons_snoc hs26
  have hs24 : L1.Stream m252 (a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m218.length) := by
    rw [hm262]; exact L1.stream_cons_snoc hs25
  have hs23 : L1.Stream m286 (a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m252.length) := by
    rw [hm296]; exact L1.stream_cons_snoc hs24
  have hs22 : L1.Stream m320 (a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m286.length) := by
    rw [hm330]; exact L1.stream_cons_snoc hs23
  have hs21 : L1.Stream m354 (a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m320.length) := by
    rw [hm364]; exact L1.stream_cons_snoc hs22
  have hs20 : L1.Stream m388 (a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m354.length) := by
    rw [hm398]; exact L1.stream_cons_snoc hs21
  have hs19 : L1.Stream m422 (a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m388.length) := by
    rw [hm432]; exact L1.stream_cons_snoc hs20
  have hs18 : L1.Stream m456 (a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m422.length) := by
    rw [hm466]; exact L1.stream_cons_snoc hs19
  have hs17 : L1.Stream m490 (a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m456.length) := by
    rw [hm500]; exact L1.stream_cons_snoc hs18
  have hs16 : L1.Stream m524 (a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m490.length) := by
    rw [hm534]; exact L1.stream_cons_snoc hs17
  have hs15 : L1.Stream m558 (a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m524.length) := by
    rw [hm568]; exact L1.stream_cons_snoc hs16
  have hs14 : L1.Stream m592 (a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m558.length) := by
    rw [hm602]; exact L1.stream_cons_snoc hs15
  have hs13 : L1.Stream m626 (a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m592.length) := by
    rw [hm636]; exact L1.stream_cons_snoc hs14
  have hs12 : L1.Stream m660 (a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m626.length) := by
    rw [hm670]; exact L1.stream_cons_snoc hs13
  have hs11 : L1.Stream m694 (a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m660.length) := by
    rw [hm704]; exact L1.stream_cons_snoc hs12
  have hs10 : L1.Stream m728 (a[10] :: a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m694.length) := by
    rw [hm738]; exact L1.stream_cons_snoc hs11
  have hs9 : L1.Stream m762 (a[9] :: a[10] :: a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m728.length) := by
    rw [hm772]; exact L1.stream_cons_snoc hs10
  have hs8 : L1.Stream m796 (a[8] :: a[9] :: a[10] :: a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m762.length) := by
    rw [hm806]; exact L1.stream_cons_snoc hs9
  have hs7 : L1.Stream m830 (a[7] :: a[8] :: a[9] :: a[10] :: a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m796.length) := by
    rw [hm840]; exact L1.stream_cons_snoc hs8
  have hs6 : L1.Stream m864 (a[6] :: a[7] :: a[8] :: a[9] :: a[10] :: a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m830.length) := by
    rw [hm874]; exact L1.stream_cons_snoc hs7
  have hs5 : L1.Stream m898 (a[5] :: a[6] :: a[7] :: a[8] :: a[9] :: a[10] :: a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m864.length) := by
    rw [hm908]; exact L1.stream_cons_snoc hs6
  have hs4 : L1.Stream m932 (a[4] :: a[5] :: a[6] :: a[7] :: a[8] :: a[9] :: a[10] :: a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m898.length) := by
    rw [hm942]; exact L1.stream_cons_snoc hs5
  have hs3 : L1.Stream m966 (a[3] :: a[4] :: a[5] :: a[6] :: a[7] :: a[8] :: a[9] :: a[10] :: a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m932.length) := by
    rw [hm976]; exact L1.stream_cons_snoc hs4
  have hs2 : L1.Stream m1000 (a[2] :: a[3] :: a[4] :: a[5] :: a[6] :: a[7] :: a[8] :: a[9] :: a[10] :: a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m966.length) := by
    rw [hm1010]; exact L1.stream_cons_snoc hs3
  have hs1 : L1.Stream m1034 (a[1] :: a[2] :: a[3] :: a[4] :: a[5] :: a[6] :: a[7] :: a[8] :: a[9] :: a[10] :: a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) (.ptr (.enum byteStreamEnum) m1000.length) := by
    rw [hm1044]; exact L1.stream_cons_snoc hs2
  have hs0 : L1.Stream h' (a[0] :: a[1] :: a[2] :: a[3] :: a[4] :: a[5] :: a[6] :: a[7] :: a[8] :: a[9] :: a[10] :: a[11] :: a[12] :: a[13] :: a[14] :: a[15] :: a[16] :: a[17] :: a[18] :: a[19] :: a[20] :: a[21] :: a[22] :: a[23] :: a[24] :: a[25] :: a[26] :: a[27] :: a[28] :: a[29] :: a[30] :: a[31] :: rest) r := by
    rw [hm1070, he1071]; exact L1.stream_cons_snoc hs1
  exact ⟨ext, by simpa only [← vector32_toList, List.cons_append, List.nil_append] using hs0⟩

theorem leaf_hash_spec {a : Bytes.Address}
    {x_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ha : Bytes.RepAddressRef addrTy h a x_addr)
    (ev : ObsFn W "KernelClaim::leaf_hash" [x_addr] h r h' calls) :
    Heap.Extends h h' ∧
    Hashed calls (ByteArray.mk #[0] ++ (ixAddr a).hash) ∧
    ∃ d : Bytes.Address, Bytes.RepAddressRef addrTy h' d r ∧
      ixAddr d = Ix.HostAdmission.Merkle.leaf (ixAddr a) := by
  obtain ⟨v1, m2, cs12, m25, m38, cs70, hm33, ev14, hm48, ev72, hc81⟩ :=
    Obs.«KernelClaim::leaf_hash».obs ev
  have ext25 : Heap.Extends h m25 := hm33 ▸ Heap.Extends.snoc h _
  have hnil : L1.Stream m25 [] (.ptr (.enum byteStreamEnum) h.length) := by
    rw [hm33]; exact L1.stream_nil_snoc h
  obtain ⟨ext1, hs1⟩ := put_address_spec (Bytes.repAddressRef_heapMono₂ addrTy ext25 ha) hnil ev14
  rw [List.append_nil] at hs1
  have hbv0 : L1.bv 0 = .field 0 := by simp [L1.bv]
  have ext38 : Heap.Extends m2 m38 := hm48 ▸ Heap.Extends.snoc m2 _
  have hs0 : L1.Stream m38 (0 :: a.toList) (.ptr (.enum byteStreamEnum) m2.length) := by
    rw [hm48, ← hbv0]; exact L1.stream_cons_snoc hs1
  obtain ⟨ext2, hld, hcall⟩ := L1.bytes_to_addr_spec hs0 ev72
  have hmod : Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel (0 :: a.toList)) =
      Blake3.Pure.digest (0 :: a.toList) :=
    Aiur.Library.Blake3.hash_model_spec _ (L1.native_of_lt (by simp))
  rw [hmod] at hld
  have hba : (⟨(0 :: a.toList).toArray⟩ : ByteArray) = ByteArray.mk #[0] ++ (ixAddr a).hash := by
    apply byteArray_eq_of_toList
    simp [ixAddr]
  have hhashed : Hashed calls (ByteArray.mk #[0] ++ (ixAddr a).hash) := by
    rw [← hba]
    exact L1.hashed_of_call (by rw [hc81]; simp [hcall]) hs0
  refine ⟨ext25.trans (ext1.trans (ext38.trans ext2)), hhashed,
    Blake3.Pure.digest (0 :: a.toList), repAddressRef_of_load_digestV hld, ?_⟩
  change L1.ixAddr (Blake3.Pure.digest (0 :: a.toList)) = _
  rw [← L1.blake3Pure_eq, hba, Ix.HostAdmission.Merkle.leaf, Address.admissionHash_eq]

theorem node_hash_spec {al ar : Bytes.Address}
    {x_l x_r r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hl : Bytes.RepAddressRef addrTy h al x_l)
    (hr : Bytes.RepAddressRef addrTy h ar x_r)
    (ev : ObsFn W "KernelClaim::node_hash" [x_l, x_r] h r h' calls) :
    Heap.Extends h h' ∧
    Hashed calls (ByteArray.mk #[1] ++ (ixAddr al).hash ++ (ixAddr ar).hash) ∧
    ∃ d : Bytes.Address, Bytes.RepAddressRef addrTy h' d r ∧
      ixAddr d = Ix.HostAdmission.Merkle.node (ixAddr al) (ixAddr ar) := by
  obtain ⟨v1, m2, cs12, v16, m25, cs33, m46, m59, cs91, hm54, ev35, ev14, hm69, ev93, hc102⟩ :=
    Obs.«KernelClaim::node_hash».obs ev
  have ext46 : Heap.Extends h m46 := hm54 ▸ Heap.Extends.snoc h _
  have hnil : L1.Stream m46 [] (.ptr (.enum byteStreamEnum) h.length) := by
    rw [hm54]; exact L1.stream_nil_snoc h
  obtain ⟨extR, hsR⟩ := put_address_spec (Bytes.repAddressRef_heapMono₂ addrTy ext46 hr) hnil ev35
  rw [List.append_nil] at hsR
  obtain ⟨extL, hsL⟩ :=
    put_address_spec (Bytes.repAddressRef_heapMono₂ addrTy (ext46.trans extR) hl) hsR ev14
  have hbv1 : L1.bv 1 = .field 1 := by simp [L1.bv]
  have ext59 : Heap.Extends m2 m59 := hm69 ▸ Heap.Extends.snoc m2 _
  have hs1 : L1.Stream m59 (1 :: (al.toList ++ ar.toList)) (.ptr (.enum byteStreamEnum) m2.length) := by
    rw [hm69, ← hbv1]; exact L1.stream_cons_snoc hsL
  obtain ⟨ext2, hld, hcall⟩ := L1.bytes_to_addr_spec hs1 ev93
  have hmod : Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel (1 :: (al.toList ++ ar.toList))) =
      Blake3.Pure.digest (1 :: (al.toList ++ ar.toList)) :=
    Aiur.Library.Blake3.hash_model_spec _ (L1.native_of_lt (by simp))
  rw [hmod] at hld
  have hba : (⟨(1 :: (al.toList ++ ar.toList)).toArray⟩ : ByteArray) =
      ByteArray.mk #[1] ++ (ixAddr al).hash ++ (ixAddr ar).hash := by
    apply byteArray_eq_of_toList
    simp [ixAddr, List.append_assoc]
  have hhashed : Hashed calls (ByteArray.mk #[1] ++ (ixAddr al).hash ++ (ixAddr ar).hash) := by
    rw [← hba]
    exact L1.hashed_of_call (by rw [hc102]; simp [hcall]) hs1
  refine ⟨ext46.trans (extR.trans (extL.trans (ext59.trans ext2))), hhashed,
    Blake3.Pure.digest (1 :: (al.toList ++ ar.toList)), repAddressRef_of_load_digestV hld, ?_⟩
  change L1.ixAddr (Blake3.Pure.digest (1 :: (al.toList ++ ar.toList))) = _
  rw [← L1.blake3Pure_eq, hba, Ix.HostAdmission.Merkle.node, Address.admissionHash_eq]

/-! ## `parse_atree_body`, `load_assumption_tree`, and `addr_set_build` -/

theorem parse_atree_body_spec {bytes : List UInt8}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hs : L1.Stream h bytes x_stream)
    (ev : ObsFn W "KernelClaim::parse_atree_body" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (t' : AssumptionTree) (k : Nat) (rootB : Bytes.Address) (as : List Bytes.Address)
      (rootPtr leavesPtr restPtr : SourceValue F),
      1 ≤ k ∧ k ≤ bytes.length ∧
      r = .tuple [rootPtr, leavesPtr, restPtr] ∧
      Bytes.RepAddressRef addrTy h' rootB rootPtr ∧
      ixAddr rootB = treeRoot t' ∧
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as leavesPtr ∧
      as.map ixAddr = treeLeaves t' ∧
      (∀ img ∈ treeImages t', Hashed calls img) ∧
      L1.Stream h' (bytes.drop k) restPtr := by
  suffices H : ∀ n, ∀ {bytes : List UInt8} {x_stream r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)}, bytes.length = n →
      L1.Stream h bytes x_stream →
      ObsFn W "KernelClaim::parse_atree_body" [x_stream] h r h' calls →
      Heap.Extends h h' ∧
      ∃ (t' : AssumptionTree) (k : Nat) (rootB : Bytes.Address) (as : List Bytes.Address)
        (rootPtr leavesPtr restPtr : SourceValue F),
        1 ≤ k ∧ k ≤ bytes.length ∧
        r = .tuple [rootPtr, leavesPtr, restPtr] ∧
        Bytes.RepAddressRef addrTy h' rootB rootPtr ∧
        ixAddr rootB = treeRoot t' ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as leavesPtr ∧
        as.map ixAddr = treeLeaves t' ∧
        (∀ img ∈ treeImages t', Hashed calls img) ∧
        L1.Stream h' (bytes.drop k) restPtr from
    H bytes.length rfl hs ev
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro bytes x_stream r h h' calls hlen_eq hs ev
    rcases Obs.«KernelClaim::parse_atree_body».obs ev with
      ⟨m2, cs12, x_tag, x_s, m37, cs48, m64, cs74, x_addr, x_s2, v98, m99, cs109, m134, m156,
        ev14, ev50, ev76, ev111, rfl, hm142, hm164, rfl, hc176⟩ |
      ⟨m2, cs12, x_tag, x_s, m37, cs48, m189, m201,
        ev14, ev50, rfl, hm197, hm209, rfl, _⟩ |
      ⟨m2, cs12, x_tag, x_s, m37, cs48, m228, cs238, x_lh, x_ll, x_s2, m268, cs278,
        x_rh, x_rl, x_s3, v307, m308, cs318, v340, m351, cs359,
        ev14, ev50, ev240, ev280, ev320, rfl, ev361, rfl, hc386⟩
    · -- Leaf (`tag = 0`)
      obtain ⟨rfl, b, rest1, _, hb, hs1, htag⟩ := Deserialize.readByte_refines hs ev14.erase
      injection htag with htag'; simp only [List.cons.injEq, and_true] at htag'
      obtain ⟨rfl, rfl⟩ := htag'
      obtain ⟨_, rfl⟩ := L1.u8_toField ev50
      obtain ⟨extA, hlenA, addrPtr, restPtr2, htupA, haddr, hs2⟩ :=
        Deserialize.getAddress_refines hs1 ev76.erase
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupA
      obtain ⟨rfl, rfl⟩ := htupA
      let aB := Deserialize.takeAddress rest1 hlenA
      obtain ⟨extH, hhashed, rootB, hroot, hix_root⟩ := leaf_hash_spec haddr ev111
      have ext156 : Heap.Extends m99 m156 := hm164 ▸ Heap.Extends.snoc m99 _
      have ext134 : Heap.Extends m156 m134 := hm142 ▸ Heap.Extends.snoc m156 _
      have extPost := ext156.trans ext134
      have hnil_l : RepList addrListEnum (Bytes.RepAddressRef addrTy) m156 []
          (.ptr (.enum addrListEnum) m99.length) := by
        rw [hm164]; exact Lib.rep_store_nil m99
      have hcons_l : RepList addrListEnum (Bytes.RepAddressRef addrTy) m134 [aB]
          (.ptr (.enum addrListEnum) m156.length) := by
        rw [hm142]
        exact Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy)
          (Bytes.repAddressRef_heapMono₂ addrTy (extH.trans ext156) haddr) hnil_l
      refine ⟨extA.trans (extH.trans extPost), .leaf (ixAddr aB), 33, rootB, [aB],
        v98, _, x_s2, by omega, by rw [hb]; simp; omega, rfl,
        Bytes.repAddressRef_heapMono₂ addrTy extPost hroot, hix_root,
        hcons_l, rfl, ?_, ?_⟩
      · intro img himg
        simp only [treeImages, List.mem_singleton] at himg
        subst himg
        exact hashed_mono (by intro c hc; rw [hc176]; simp [hc]) hhashed
      · rw [hb]
        simpa using hs2.mono (extH.trans extPost)
    · -- Padding (`tag = 1`)
      obtain ⟨rfl, b, rest1, _, hb, hs1, htag⟩ := Deserialize.readByte_refines hs ev14.erase
      injection htag with htag'; simp only [List.cons.injEq, and_true] at htag'
      obtain ⟨rfl, rfl⟩ := htag'
      obtain ⟨_, rfl⟩ := L1.u8_toField ev50
      have ext189 : Heap.Extends h m189 := hm197 ▸ Heap.Extends.snoc h _
      have ext201 : Heap.Extends m189 m201 := hm209 ▸ Heap.Extends.snoc m189 _
      have extPost := ext189.trans ext201
      let zeroB : Bytes.Address := Vector.replicate 32 0
      have hdig0 : L1.digestV zeroB = .tuple (List.replicate 32 (.field 0)) := by
        simp [L1.digestV, zeroB, L1.bv]
      have hld0 : loadValue m189
          (.ptr (.tuple (List.map Value.type (List.replicate 32 ((.field 0) : SourceValue F))))
            h.length) = .ok (L1.digestV zeroB) := by
        rw [hdig0, hm197]
        simpa [Value.type] using L1.loadValue_snoc h (.tuple (List.replicate 32 (.field 0)))
      have hroot : Bytes.RepAddressRef addrTy m201 zeroB _ :=
        Bytes.repAddressRef_heapMono₂ addrTy ext201 (repAddressRef_of_load_digestV hld0)
      have hnil_l : RepList addrListEnum (Bytes.RepAddressRef addrTy) m201 []
          (.ptr (.enum addrListEnum) m189.length) := by
        rw [hm209]; exact Lib.rep_store_nil m189
      have hix_zero : ixAddr zeroB = Ix.HostAdmission.Merkle.padding := by
        unfold ixAddr zeroB Ix.HostAdmission.Merkle.padding
        congr 1
        apply byteArray_eq_of_toList
        simp
      refine ⟨extPost, .padding, 1, zeroB, [], _, _, x_s, by omega, by rw [hb]; simp, rfl,
        hroot, hix_zero, hnil_l, rfl, by simp [treeImages], ?_⟩
      rw [hb]
      simpa using hs1.mono extPost
    · -- Node (`tag = 2`)
      obtain ⟨rfl, b, rest1, _, hb, hs1, htag⟩ := Deserialize.readByte_refines hs ev14.erase
      injection htag with htag'; simp only [List.cons.injEq, and_true] at htag'
      obtain ⟨rfl, rfl⟩ := htag'
      obtain ⟨_, rfl⟩ := L1.u8_toField ev50
      have hlt1 : rest1.length < n := by rw [← hlen_eq, hb]; simp
      obtain ⟨extL, tL, kL, lhB, asL, _, _, _, hkL_ge, hkL_le, htupL, hrepL, hixL, hlL, hmapL,
        hhashL, hsL⟩ := ih rest1.length hlt1 rfl hs1 ev240
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupL
      obtain ⟨rfl, rfl, rfl⟩ := htupL
      have hlt2 : (rest1.drop kL).length < n := by rw [List.length_drop]; omega
      obtain ⟨extR, tR, kR, rhB, asR, _, _, _, hkR_ge, hkR_le, htupR, hrepR, hixR, hlR, hmapR,
        hhashR, hsR⟩ := ih (rest1.drop kL).length hlt2 rfl hsL ev280
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupR
      obtain ⟨rfl, rfl, rfl⟩ := htupR
      obtain ⟨extN, hhashN, nhB, hrepN, hixN⟩ :=
        node_hash_spec (Bytes.repAddressRef_heapMono₂ addrTy extR hrepL) hrepR ev320
      have hsym_cat : (Instance.mk "Lists::concat" [.ptr (.array .field 32)]).symbol =
          Obs.Names.«Lists::concat<&[Field; 32]>» :=
        Obs.Names.«Lists::concat<&[Field; 32]>».symbol
      have hsym_node : (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol = addrListEnum :=
        Obs.Names.«Lists::Node<&[Field; 32]>».symbol
      rw [← hsym_cat] at ev361
      have extCat := ev361.heap_extends
      have hlL' : RepList (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol
          (Bytes.RepAddressRef addrTy) m308 asL x_ll := by
        rw [hsym_node]
        exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) (extR.trans extN) hlL
      have hlR' : RepList (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol
          (Bytes.RepAddressRef addrTy) m308 asR x_rl := by
        rw [hsym_node]
        exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) extN hlR
      have hlCat : RepList addrListEnum (Bytes.RepAddressRef addrTy) m351 (asL ++ asR) v340 := by
        rw [← hsym_node]
        exact Lib.Lists.concat_spec (Bytes.repAddressRef_heapMono₂ addrTy) ev361 hlL' hlR'
      rw [List.length_drop] at hkR_le
      refine ⟨extL.trans (extR.trans (extN.trans extCat)),
        .node tL tR, 1 + kL + kR, nhB, asL ++ asR, v307, v340, x_s3,
        by omega, by rw [hb]; simp; omega, rfl,
        Bytes.repAddressRef_heapMono₂ addrTy extCat hrepN,
        by rw [hixN, hixL, hixR]; rfl,
        hlCat,
        by rw [List.map_append, hmapL, hmapR]; rfl,
        ?_, ?_⟩
      · intro img himg
        simp only [treeImages, List.mem_cons, List.mem_append] at himg
        rcases himg with rfl | himgL | himgR
        · rw [← hixL, ← hixR]
          exact hashed_mono (by intro c hc; rw [hc386]; simp [hc]) hhashN
        · exact hashed_mono (by intro c hc; rw [hc386]; simp [hc]) (hhashL img himgL)
        · exact hashed_mono (by intro c hc; rw [hc386]; simp [hc]) (hhashR img himgR)
      · rw [hb, show 1 + kL + kR = (kL + kR) + 1 by omega, List.drop_succ_cons, ← List.drop_drop]
        exact hsR.mono extCat

private theorem byte0_ne_byte1 {b₀ b₁ : ByteArray} :
    ByteArray.mk #[1] ++ b₁ ≠ ByteArray.mk #[0] ++ b₀ := by
  intro h
  have hl := congrArg (fun x : ByteArray => x.data.toList) h
  simp at hl

theorem treeRoot_collision_or_eq {V : View} {extra : List ByteArray} {calls : List (Call F)}
    {t₀ : AssumptionTree} (ht₀ : t₀ ∈ V.trees) :
    ∀ {t t' : AssumptionTree},
      (∀ img ∈ treeImages t, img ∈ treeImages t₀) →
      (∀ img ∈ treeImages t', Hashed calls img) →
      treeRoot t = treeRoot t' →
      V.HashedCollision extra calls ∨ t = t' := by
  intro t
  induction t with
  | leaf a =>
    intro t' hsub hhashed hroot
    have hheld_mem : ByteArray.mk #[0] ++ a.hash ∈ treeImages t₀ :=
      hsub _ (by simp [treeImages])
    have hheld_hash : Address.blake3Pure (ByteArray.mk #[0] ++ a.hash) = treeRoot (.leaf a) := by
      simp [treeRoot, Ix.HostAdmission.Merkle.leaf, Address.admissionHash_eq]
    have hpre : V.Preimage (treeRoot (.leaf a)) (ByteArray.mk #[0] ++ a.hash) :=
      .inr (.inr (.inr ⟨t₀, ht₀, hheld_mem, hheld_hash⟩))
    cases t' with
    | leaf a' =>
      have himg_hash : Hashed calls (ByteArray.mk #[0] ++ a'.hash) :=
        hhashed _ (by simp [treeImages])
      have himg_blk : Address.blake3Pure (ByteArray.mk #[0] ++ a'.hash) = treeRoot (.leaf a) := by
        rw [hroot]; simp [treeRoot, Ix.HostAdmission.Merkle.leaf, Address.admissionHash_eq]
      by_cases heq : ByteArray.mk #[0] ++ a'.hash = ByteArray.mk #[0] ++ a.hash
      · right
        have hl := congrArg (fun x : ByteArray => x.data.toList) heq
        simp only [ByteArray.data_append, Array.toList_append, List.singleton_append,
          List.cons.injEq] at hl
        have ha_eq : a' = a := by
          cases a; cases a'
          congr 1
          exact byteArray_eq_of_toList hl
        rw [ha_eq]
      · exact .inl (.inl ⟨treeRoot (.leaf a), _, _, .inl hpre, himg_hash, heq, himg_blk⟩)
    | padding =>
      have hpad : treeRoot (.leaf a) = Ix.HostAdmission.Merkle.padding := hroot
      rw [hpad] at hpre hheld_hash
      exact .inl (.inr ⟨_, .inl hpre, hheld_hash⟩)
    | node l' r' =>
      let img := ByteArray.mk #[1] ++ (treeRoot l').hash ++ (treeRoot r').hash
      have himg_hash : Hashed calls img := hhashed _ (by simp [treeImages, img])
      have himg_blk : Address.blake3Pure img = treeRoot (.leaf a) := by
        rw [hroot]; simp [treeRoot, Ix.HostAdmission.Merkle.node, Address.admissionHash_eq, img]
      have hne : img ≠ ByteArray.mk #[0] ++ a.hash := by
        dsimp [img]; rw [ByteArray.append_assoc]; exact byte0_ne_byte1
      exact .inl (.inl ⟨treeRoot (.leaf a), _, _, .inl hpre, himg_hash, hne, himg_blk⟩)
  | padding =>
    intro t' _ hhashed hroot
    cases t' with
    | padding => exact .inr rfl
    | leaf a' =>
      have himg_hash : Hashed calls (ByteArray.mk #[0] ++ a'.hash) :=
        hhashed _ (by simp [treeImages])
      have himg_blk : Address.blake3Pure (ByteArray.mk #[0] ++ a'.hash) =
          Ix.HostAdmission.Merkle.padding := by
        simpa [treeRoot, Ix.HostAdmission.Merkle.leaf, Address.admissionHash_eq] using hroot.symm
      exact .inl (.inr ⟨_, .inr himg_hash, himg_blk⟩)
    | node l' r' =>
      let img := ByteArray.mk #[1] ++ (treeRoot l').hash ++ (treeRoot r').hash
      have himg_hash : Hashed calls img := hhashed _ (by simp [treeImages, img])
      have himg_blk : Address.blake3Pure img = Ix.HostAdmission.Merkle.padding := by
        simpa [treeRoot, Ix.HostAdmission.Merkle.node, Address.admissionHash_eq, img] using
          hroot.symm
      exact .inl (.inr ⟨_, .inr himg_hash, himg_blk⟩)
  | node l r ihl ihr =>
    intro t' hsub hhashed hroot
    let held := ByteArray.mk #[1] ++ (treeRoot l).hash ++ (treeRoot r).hash
    have hheld_mem : held ∈ treeImages t₀ := hsub _ (by simp [treeImages, held])
    have hheld_hash : Address.blake3Pure held = treeRoot (.node l r) := by
      simp [treeRoot, Ix.HostAdmission.Merkle.node, Address.admissionHash_eq, held]
    have hpre : V.Preimage (treeRoot (.node l r)) held :=
      .inr (.inr (.inr ⟨t₀, ht₀, hheld_mem, hheld_hash⟩))
    cases t' with
    | padding =>
      have hpad : treeRoot (.node l r) = Ix.HostAdmission.Merkle.padding := hroot
      rw [hpad] at hpre hheld_hash
      exact .inl (.inr ⟨_, .inl hpre, hheld_hash⟩)
    | leaf a' =>
      let img := ByteArray.mk #[0] ++ a'.hash
      have himg_hash : Hashed calls img := hhashed _ (by simp [treeImages, img])
      have himg_blk : Address.blake3Pure img = treeRoot (.node l r) := by
        rw [hroot]; simp [treeRoot, Ix.HostAdmission.Merkle.leaf, Address.admissionHash_eq, img]
      have hne : img ≠ held := by
        intro heq
        dsimp [img, held] at heq
        rw [ByteArray.append_assoc] at heq
        exact byte0_ne_byte1 heq.symm
      exact .inl (.inl ⟨treeRoot (.node l r), _, _, .inl hpre, himg_hash, hne, himg_blk⟩)
    | node l' r' =>
      let img := ByteArray.mk #[1] ++ (treeRoot l').hash ++ (treeRoot r').hash
      have himg_hash : Hashed calls img := hhashed _ (by simp [treeImages, img])
      have himg_blk : Address.blake3Pure img = treeRoot (.node l r) := by
        rw [hroot]; simp [treeRoot, Ix.HostAdmission.Merkle.node, Address.admissionHash_eq, img]
      by_cases heq : img = held
      case neg =>
        exact .inl (.inl ⟨treeRoot (.node l r), _, _, .inl hpre, himg_hash, heq, himg_blk⟩)
      have hl_list := congrArg (fun x : ByteArray => x.data.toList) heq
      dsimp [img, held] at hl_list
      simp only [ByteArray.data_append, Array.toList_append, List.cons_append, List.nil_append,
        List.cons.injEq] at hl_list
      have hsz_l' : (treeRoot l').hash.data.toList.length = 32 := by
        simpa [ByteArray.size] using treeRoot_hash_size l'
      have hsz_l : (treeRoot l).hash.data.toList.length = 32 := by
        simpa [ByteArray.size] using treeRoot_hash_size l
      obtain ⟨hl_eq, hr_eq⟩ := List.append_inj hl_list (hsz_l'.trans hsz_l.symm)
      have hroot_l : treeRoot l = treeRoot l' := by
        cases h1 : treeRoot l; cases h2 : treeRoot l'
        simp only [h1, h2] at hl_eq
        exact congrArg Address.mk (byteArray_eq_of_toList hl_eq.symm)
      have hroot_r : treeRoot r = treeRoot r' := by
        cases h1 : treeRoot r; cases h2 : treeRoot r'
        simp only [h1, h2] at hr_eq
        exact congrArg Address.mk (byteArray_eq_of_toList hr_eq.symm)
      rcases ihl (fun x hx => hsub x (by simp [treeImages, hx]))
        (fun x hx => hhashed x (by simp [treeImages, hx])) hroot_l with hcoll | rfl
      · exact .inl hcoll
      rcases ihr (fun x hx => hsub x (by simp [treeImages, hx]))
        (fun x hx => hhashed x (by simp [treeImages, hx])) hroot_r with hcoll | rfl
      · exact .inl hcoll
      exact .inr rfl

theorem load_assumption_tree_spec {V : View} {extra : List ByteArray}
    {tTree : AssumptionTree} (htTree : tTree ∈ V.trees)
    {x_root r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hroot : S0.addr h x_root (treeRoot tTree))
    (ev : ObsFn W "KernelClaim::load_assumption_tree" [x_root] h r h' calls) :
    V.HashedCollision extra calls ∨
    (Heap.Extends h h' ∧
      ∃ as : List Bytes.Address,
        as.map ixAddr = treeLeaves tTree ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as r) := by
  obtain ⟨rootB, hrep_root, hix_root⟩ := hroot
  obtain ⟨v1, m14, cs24, x_idx, x_len, v55, m56, cs66, m93, cs103, x_tag, x_s,
    v138, m141, cs149, m168, cs178, x_computed_root, x_leaves, x_rest, v222,
    v245, v246, m248, cs256, m268, cs276,
    ld11, ev26, ev68, ev105, ev151, _, ev180, ld217, ld232, ev258, ev278,
    heq287, rfl, rfl, hc291⟩ := Obs.«KernelClaim::load_assumption_tree».obs ev
  have hv1 : v1 = L1.digestV rootB := L1.load_repAddressRef hrep_root ld11
  have hm14 := L1.io_get_info_spec ev26
  subst hm14
  obtain ⟨extRead, rawBytes, _, -, hs0⟩ := L1.read_finite_byte_stream_spec ev68
  obtain ⟨rfl, _, rest1, _, _, hs1, htag⟩ := Deserialize.readByte_refines hs0 ev105.erase
  injection htag with htag'; simp only [List.cons.injEq, and_true] at htag'
  obtain ⟨rfl, rfl⟩ := htag'
  obtain ⟨_, rfl⟩ := L1.u8_toField ev151
  obtain ⟨extParse, t', k, compB, as, _, _, _, _, _, htupP, hrepComp, hixComp, hlLeaves,
    hmapLeaves, hhashP, _⟩ := parse_atree_body_spec hs1 ev180
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupP
  obtain ⟨rfl, rfl, rfl⟩ := htupP
  have hv222 : v222 = L1.digestV compB := L1.load_repAddressRef hrepComp ld232
  obtain ⟨rfl, l1, rfl, hl1⟩ := L1.address_to_fields_spec ev258
  obtain ⟨rfl, l2, rfl, hl2⟩ := L1.address_to_fields_spec ev278
  have hl_eq : l1 = l2 := Value.tuple.inj heq287
  subst hl_eq
  have hcomp_eq : compB = rootB := by
    refine L1.digest_eq_of_proj hv1 ?_
    intro i hi
    rw [hl2 i hi, ← hl1 i hi, hv222, L1.proj_digestV _ i hi]
  subst hcomp_eq
  have hroot_eq : treeRoot tTree = treeRoot t' := hix_root.symm.trans hixComp
  have hhash_calls : ∀ img ∈ treeImages t', Hashed calls img := fun img himg =>
    hashed_mono (by intro c hc; rw [hc291]; simp [hc]) (hhashP img himg)
  rcases treeRoot_collision_or_eq (extra := extra) htTree (fun _ hx => hx) hhash_calls hroot_eq with
    hcoll | rfl
  · exact .inl hcoll
  · exact .inr ⟨extRead.trans extParse, as, hmapLeaves, hlLeaves⟩

theorem addr_set_build_spec {as : List Bytes.Address} {S : List _root_.Address}
    {x_leaves x_acc r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hl : RepList addrListEnum (Bytes.RepAddressRef addrTy) h as x_leaves)
    (hacc : RepAddrSet h S x_acc)
    (ev : ObsFn W "KernelClaim::addr_set_build" [x_leaves, x_acc] h r h' calls) :
    Heap.Extends h h' ∧
    RepAddrSet h' (as.reverse.map ixAddr ++ S) r := by
  induction as generalizing S x_leaves x_acc r h h' calls with
  | nil =>
    rcases Obs.«KernelClaim::addr_set_build».obs ev with
      ⟨_, rfl, rfl, _⟩ | ⟨_, _, _, _, _, _, ld12, _⟩
    · refine ⟨Heap.Extends.refl h, ?_⟩
      simpa using hacc
    · cases Lib.rep_cons_of_load hl ld12 with
      | intro _ h' => rcases h' with ⟨_, he, _⟩; cases he
  | cons a as' ih =>
    rcases Obs.«KernelClaim::addr_set_build».obs ev with
      ⟨ld12, _⟩ | ⟨x_a, x_rest, cs44, v48, m57, cs65, ld12, ev67, ev46, _⟩
    · cases Lib.rep_nil_of_load hl ld12
    · obtain ⟨a', as'', he, ha, hrest⟩ := Lib.rep_cons_of_load hl ld12
      injection he with h1 h2; subst h1 h2
      have hsym_ins : (Instance.mk "RBTreeMap::rbtree_map_insert" [.field]).symbol =
          Obs.Names.«RBTreeMap::rbtree_map_insert<Field>» := rfl
      rw [← hsym_ins] at ev67
      obtain ⟨ext1, hacc1⟩ := rbtree_set_insert_spec ha hacc ev67
      obtain ⟨ext2, hres⟩ := ih
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext1 hrest) hacc1 ev46
      refine ⟨ext1.trans ext2, ?_⟩
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using hres

/-! ## `pack_word`, `pack_digest`, and `packDigest` injectivity -/

theorem pack_word_spec {w : UInt32} {r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "Blake3::pack_word" [L1.wv w] h r h' calls) :
    r = .field (((Blake3.Pure.wordBytes w)[0].toNat +
      256 * (Blake3.Pure.wordBytes w)[1].toNat +
      65536 * (Blake3.Pure.wordBytes w)[2].toNat +
      16777216 * (Blake3.Pure.wordBytes w)[3].toNat : Nat) : F) ∧ h' = h := by
  obtain ⟨cs4, v7, m9, cs17, ev19, ev6, _⟩ := Obs.«Blake3::pack_word».obs ev
  obtain ⟨rfl, rfl, _⟩ := Obs.«UInt32::compact_field».obs ev6
  obtain ⟨hr, rfl⟩ := L1.u32_compact (b0 := (Blake3.Pure.wordBytes w)[0])
    (b1 := (Blake3.Pure.wordBytes w)[1]) (b2 := (Blake3.Pure.wordBytes w)[2])
    (b3 := (Blake3.Pure.wordBytes w)[3]) ev19
  rw [hr, Aiur.Library.Blake3.wordOfBytes_toNat]
  exact ⟨rfl, rfl⟩

private theorem packDigest_cv_word (cv : Blake3.Pure.CV) (k : Fin 8) :
    .field (((Blake3.Pure.wordBytes cv[k.val])[0].toNat +
      256 * (Blake3.Pure.wordBytes cv[k.val])[1].toNat +
      65536 * (Blake3.Pure.wordBytes cv[k.val])[2].toNat +
      16777216 * (Blake3.Pure.wordBytes cv[k.val])[3].toNat : Nat) : F) =
    (Value.field (packDigest (ixAddr (Blake3.Pure.cvBytes cv)) k) : SourceValue F) := by
  rcases k with ⟨kv, hkv⟩
  unfold packDigest ixAddr
  congr 1
  congr 1
  have getD_cv : ∀ m (hm : m < 32),
      ((Blake3.Pure.cvBytes cv).toArray.getD m 0) = (Blake3.Pure.cvBytes cv)[m] := by
    intro m hm
    have hsz : m < (Blake3.Pure.cvBytes cv).toArray.size := by simpa using hm
    simp [Array.getD, hsz]
  interval_cases kv <;>
    simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add,
      getD_cv _ (by decide), Blake3.Pure.cvBytes, Vector.getElem_ofFn] <;>
    rfl

theorem pack_digest_spec {cv : Blake3.Pure.CV} {r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn W "Blake3::pack_digest" [L1.vecV cv] h r h' calls) :
    r = digestValue (packDigest (ixAddr (Blake3.Pure.cvBytes cv))) ∧ h' = h := by
  obtain ⟨v3, v4, v5, v6, v7, v8, v9, v10, m13, cs21, v24, m36, cs44, v47, m59, cs67, v70,
    m82, cs90, v93, m105, cs113, v116, m128, cs136, v139, m151, cs159, v162, m174, cs182, v185,
    rfl, pr33, ev23, pr56, ev46, pr79, ev69, pr102, ev92, pr125, ev115, pr148, ev138, pr171,
    ev161, pr194, ev184, rfl, _⟩ := Obs.«Blake3::pack_digest».obs ev
  obtain rfl := L1.ok_inj ((L1.proj_vecV cv 0 (by decide)).symm.trans pr33)
  obtain rfl := L1.ok_inj ((L1.proj_vecV cv 1 (by decide)).symm.trans pr56)
  obtain rfl := L1.ok_inj ((L1.proj_vecV cv 2 (by decide)).symm.trans pr79)
  obtain rfl := L1.ok_inj ((L1.proj_vecV cv 3 (by decide)).symm.trans pr102)
  obtain rfl := L1.ok_inj ((L1.proj_vecV cv 4 (by decide)).symm.trans pr125)
  obtain rfl := L1.ok_inj ((L1.proj_vecV cv 5 (by decide)).symm.trans pr148)
  obtain rfl := L1.ok_inj ((L1.proj_vecV cv 6 (by decide)).symm.trans pr171)
  obtain rfl := L1.ok_inj ((L1.proj_vecV cv 7 (by decide)).symm.trans pr194)
  obtain ⟨hv3, rfl⟩ := pack_word_spec ev23
  obtain ⟨hv4, rfl⟩ := pack_word_spec ev46
  obtain ⟨hv5, rfl⟩ := pack_word_spec ev69
  obtain ⟨hv6, rfl⟩ := pack_word_spec ev92
  obtain ⟨hv7, rfl⟩ := pack_word_spec ev115
  obtain ⟨hv8, rfl⟩ := pack_word_spec ev138
  obtain ⟨hv9, rfl⟩ := pack_word_spec ev161
  obtain ⟨hv10, rfl⟩ := pack_word_spec ev184
  refine ⟨?_, rfl⟩
  rw [hv3, packDigest_cv_word cv ⟨0, by decide⟩,
      hv4, packDigest_cv_word cv ⟨1, by decide⟩,
      hv5, packDigest_cv_word cv ⟨2, by decide⟩,
      hv6, packDigest_cv_word cv ⟨3, by decide⟩,
      hv7, packDigest_cv_word cv ⟨4, by decide⟩,
      hv8, packDigest_cv_word cv ⟨5, by decide⟩,
      hv9, packDigest_cv_word cv ⟨6, by decide⟩,
      hv10, packDigest_cv_word cv ⟨7, by decide⟩]
  rfl

theorem digestValue_inj {d₁ d₂ : Digest} (h : digestValue d₁ = digestValue d₂) : d₁ = d₂ := by
  simp only [digestValue, List.ofFn_succ, List.ofFn_zero, Fin.isValue, Value.tuple.injEq,
    List.cons.injEq, Value.field.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  funext ⟨i, hi⟩
  interval_cases i <;> assumption

theorem packDigest_inj {a₁ a₂ : _root_.Address}
    (h₁ : a₁.hash.size = 32) (h₂ : a₂.hash.size = 32)
    (hp : packDigest a₁ = packDigest a₂) : a₁ = a₂ := by
  cases a₁ with | mk bs₁ =>
  cases a₂ with | mk bs₂ =>
  congr 1
  apply ByteArray.ext
  apply Array.ext (by simpa [ByteArray.size] using h₁.trans h₂.symm)
  intro k hk1 hk2
  have hk32 : k < 32 := by simpa [ByteArray.size] using hk1
  have hword := congrFun hp ⟨k / 4, by omega⟩
  unfold packDigest at hword
  simp only at hword
  have b_lt : ∀ (bs : ByteArray) (m : Nat), (bs.data.getD m 0).toNat < 256 :=
    fun bs m => (bs.data.getD m 0).toNat_lt
  have hw1 : (bs₁.data.getD (4 * (k / 4)) 0).toNat +
      256 * (bs₁.data.getD (4 * (k / 4) + 1) 0).toNat +
      65536 * (bs₁.data.getD (4 * (k / 4) + 2) 0).toNat +
      16777216 * (bs₁.data.getD (4 * (k / 4) + 3) 0).toNat < 4294967296 := by
    have := b_lt bs₁ (4 * (k / 4))
    have := b_lt bs₁ (4 * (k / 4) + 1)
    have := b_lt bs₁ (4 * (k / 4) + 2)
    have := b_lt bs₁ (4 * (k / 4) + 3)
    omega
  have hw2 : (bs₂.data.getD (4 * (k / 4)) 0).toNat +
      256 * (bs₂.data.getD (4 * (k / 4) + 1) 0).toNat +
      65536 * (bs₂.data.getD (4 * (k / 4) + 2) 0).toNat +
      16777216 * (bs₂.data.getD (4 * (k / 4) + 3) 0).toNat < 4294967296 := by
    have := b_lt bs₂ (4 * (k / 4))
    have := b_lt bs₂ (4 * (k / 4) + 1)
    have := b_lt bs₂ (4 * (k / 4) + 2)
    have := b_lt bs₂ (4 * (k / 4) + 3)
    omega
  have hnat := natCast_inj_of_lt_u32 hw1 hw2 hword
  have h0_1 := b_lt bs₁ (4 * (k / 4))
  have h1_1 := b_lt bs₁ (4 * (k / 4) + 1)
  have h2_1 := b_lt bs₁ (4 * (k / 4) + 2)
  have h3_1 := b_lt bs₁ (4 * (k / 4) + 3)
  have h0_2 := b_lt bs₂ (4 * (k / 4))
  have h1_2 := b_lt bs₂ (4 * (k / 4) + 1)
  have h2_2 := b_lt bs₂ (4 * (k / 4) + 2)
  have h3_2 := b_lt bs₂ (4 * (k / 4) + 3)
  have hbyte : (bs₁.data.getD k 0).toNat = (bs₂.data.getD k 0).toNat := by
    have hrem : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hrem with hr | hr | hr | hr
    · have hk_eq : k = 4 * (k / 4) := by omega
      rw [hk_eq]; omega
    · have hk_eq : k = 4 * (k / 4) + 1 := by omega
      rw [hk_eq]; omega
    · have hk_eq : k = 4 * (k / 4) + 2 := by omega
      rw [hk_eq]; omega
    · have hk_eq : k = 4 * (k / 4) + 3 := by omega
      rw [hk_eq]; omega
  simp only [Array.getD, hk1, hk2, ↓reduceDIte] at hbyte
  exact UInt8.ext hbyte

/-! ## `Ixon` `GetM` alignment for `get_address`, `get_opt_addr`, `get_claim_context` -/

theorem getAddress_of_drop {bytes : List UInt8} {i : Nat} (hlen : 32 ≤ (bytes.drop i).length) :
    (Ixon.Serialize.get : Ixon.GetM _root_.Address) { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok (ixAddr (Deserialize.takeAddress (bytes.drop i) hlen))
        { idx := i + 32, bytes := ⟨bytes.toArray⟩ } := by
  have hi_le : i ≤ bytes.length := by rw [List.length_drop] at hlen; omega
  have hsz : i + 32 ≤ (ByteArray.mk bytes.toArray).size := by
    simp only [ByteArray.size, List.size_toArray]
    rw [List.length_drop] at hlen
    omega
  let before : ByteArray := ⟨(bytes.take i).toArray⟩
  let chunk : ByteArray := ⟨((bytes.drop i).take 32).toArray⟩
  let after : ByteArray := ⟨((bytes.drop i).drop 32).toArray⟩
  have hsplit : (⟨bytes.toArray⟩ : ByteArray) = before ++ chunk ++ after := by
    apply byteArray_eq_of_toList
    simp only [before, chunk, after, ByteArray.data_append, Array.toList_append,
      List.toList_toArray]
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  have hbef_sz : before.size = i := by
    simp [before, ByteArray.size, Nat.min_eq_left hi_le]
  have hchk_sz : chunk.size = 32 := by
    simp [chunk, ByteArray.size, Nat.min_eq_left hlen]
  have hext : (⟨bytes.toArray⟩ : ByteArray).extract i (i + 32) = chunk := by
    rw [hsplit, ← hbef_sz, ← hchk_sz]
    exact Ixon.Verify.ConstantTables.middle_extract before chunk after
  change (Address.mk <$> Ixon.getBytes 32) { idx := i, bytes := ⟨bytes.toArray⟩ } = _
  simp only [Functor.map, EStateM.map, Ixon.getBytes, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, set, EStateM.set, pure, EStateM.pure, hsz, ↓reduceIte, hext]
  rfl

theorem get_opt_addr_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : ObsFn W "KernelClaim::get_opt_addr" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (opt : Option _root_.Address) (k : Nat) (optVal restPtr : SourceValue F),
      Claim.getOptAddr { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok opt { idx := i + k, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [optVal, restPtr] ∧
      (match opt with
       | none => optVal = .construct Obs.Names.«Options::Option<&[Field; 32]>» "None" []
       | some a => ∃ addrPtr,
           optVal = .construct Obs.Names.«Options::Option<&[Field; 32]>» "Some" [addrPtr] ∧
           S0.addr h' addrPtr a) ∧
      L1.Stream h' (bytes.drop (i + k)) restPtr := by
  rcases Obs.«KernelClaim::get_opt_addr».obs ev with
    ⟨m2, cs12, x_tag, x_s, m37, cs48, ev14, ev50, rfl, rfl, _⟩ |
    ⟨m2, cs12, x_tag, x_s, m37, cs48, m92, cs102, x_addr, x_s2, ev14, ev50, ev104, rfl, rfl, _⟩
  · obtain ⟨rfl, b, rest1, _, hb, hs1, htag⟩ := Deserialize.readByte_refines hs ev14.erase
    injection htag with htag'; simp only [List.cons.injEq, and_true] at htag'
    obtain ⟨rfl, rfl⟩ := htag'
    obtain ⟨hval, rfl⟩ := L1.u8_toField ev50
    have hb0 : b = 0 := by
      have h0 : (b.toNat : F) = ((0 : Nat) : F) := by simpa using Value.field.inj hval.symm
      exact UInt8.ext (natCast_inj_of_lt_u32 (by have := b.toNat_lt; omega) (by decide) h0)
    subst hb0
    obtain ⟨hu8, hdrop1, -⟩ := Deserialize.getU8_of_drop_cons hb
    refine ⟨Heap.Extends.refl h, none, 1, _, x_s, ?_, rfl, rfl, by rwa [hdrop1]⟩
    simp [Claim.getOptAddr, bind, EStateM.bind, pure, EStateM.pure, hu8]
  · obtain ⟨rfl, b, rest1, _, hb, hs1, htag⟩ := Deserialize.readByte_refines hs ev14.erase
    injection htag with htag'; simp only [List.cons.injEq, and_true] at htag'
    obtain ⟨rfl, rfl⟩ := htag'
    obtain ⟨hval, rfl⟩ := L1.u8_toField ev50
    have hb1 : b = 1 := by
      have h1 : (b.toNat : F) = ((1 : Nat) : F) := by simpa using Value.field.inj hval.symm
      exact UInt8.ext (natCast_inj_of_lt_u32 (by have := b.toNat_lt; omega) (by decide) h1)
    subst hb1
    obtain ⟨hu8, hdrop1, -⟩ := Deserialize.getU8_of_drop_cons hb
    rw [← hdrop1] at hs1
    obtain ⟨extA, hlenA, addrPtr, restPtr2, htupA, haddr, hs2⟩ :=
      Deserialize.getAddress_refines hs1 ev104.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htupA
    obtain ⟨rfl, rfl⟩ := htupA
    have hgetA := getAddress_of_drop hlenA
    rw [List.drop_drop, Nat.add_assoc] at hs2
    rw [Nat.add_assoc] at hgetA
    refine ⟨extA, some (ixAddr (Deserialize.takeAddress _ hlenA)), 33, _, x_s2, ?_, rfl,
      ⟨x_addr, rfl, _, haddr, rfl⟩, hs2⟩
    simp [Claim.getOptAddr, bind, EStateM.bind, pure, EStateM.pure, hu8, hgetA]

theorem get_claim_context_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : ObsFn W "KernelClaim::get_claim_context" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (ctx : ClaimContext) (k : Nat) (x_binding x_axioms x_s3 : SourceValue F),
      Claim.getContext { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ctx { idx := i + k, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [x_binding, x_axioms, x_s3] ∧
      S0.addr h' x_binding ctx.binding ∧
      (ctx.axioms = none →
        x_axioms = .construct Obs.Names.«Options::Option<&[Field; 32]>» "None" []) ∧
      L1.Stream h' (bytes.drop (i + k)) x_s3 := by
  obtain ⟨m2, cs12, x_spec, x_s, v47, m50, cs58, v62, m71, cs79, m90, cs100,
    x_binding, x_s2, m125, cs135, x_axioms, x_s3,
    ev14, ev81, ev60, _, ev102, ev137, rfl, rfl, _⟩ :=
    Obs.«KernelClaim::get_claim_context».obs ev
  obtain ⟨ext1, hlen1, _, _, htup1, _, hs1⟩ := Deserialize.getAddress_refines hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup1
  obtain ⟨rfl, rfl⟩ := htup1
  rw [List.drop_drop] at hs1
  have hget1 := getAddress_of_drop hlen1
  have extMid := ev81.heap_extends.trans ev60.heap_extends
  obtain ⟨ext2, hlen2, _, _, htup2, hbind, hs2⟩ :=
    Deserialize.getAddress_refines (hs1.mono extMid) ev102.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup2
  obtain ⟨rfl, rfl⟩ := htup2
  rw [List.drop_drop] at hs2
  have hget2 := getAddress_of_drop hlen2
  obtain ⟨ext3, optAx, kOpt, _, _, hgetOpt, htup3, hoptRep, hs3⟩ := get_opt_addr_spec hs2 ev137
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup3
  obtain ⟨rfl, rfl⟩ := htup3
  refine ⟨ext1.trans (extMid.trans (ext2.trans ext3)),
    { spec := ixAddr (Deserialize.takeAddress _ hlen1)
      binding := ixAddr (Deserialize.takeAddress _ hlen2)
      axioms := optAx },
    32 + 32 + kOpt, x_binding, x_axioms, x_s3, ?_, rfl,
    ⟨_, Bytes.repAddressRef_heapMono₂ addrTy ext3 hbind, rfl⟩, ?_, ?_⟩
  · simp only [Claim.getContext, bind, EStateM.bind, pure, EStateM.pure, hget1, hget2]
    simpa only [Nat.add_assoc] using hgetOpt
  · intro hnone
    dsimp only at hnone
    subst hnone
    exact hoptRep
  · simpa only [Nat.add_assoc] using hs3

/-! ## `run_check_env` on `asm = None` and `RCFullRep` -/

theorem run_check_env_none_spec {V : View} {extra : List ByteArray}
    {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Nat}
    {tTree : AssumptionTree} (htTree : tTree ∈ V.trees)
    {x_rc x_env_root r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrc : RCFullRep t bAddr lim h x_rc)
    (hroot : S0.addr h x_env_root (treeRoot tTree))
    (ev : ObsFn W "KernelClaim::run_check_env"
      [x_rc, x_env_root, .construct Obs.Names.«Options::Option<&[Field; 32]>» "None" []]
      h r h' calls) :
    V.HashedCollision extra calls ∨
    ∃ (as : List Bytes.Address) (m₁ : Heap F) (x_leaves : SourceValue F) (cs₁ : List (Call F)),
      treeLeaves tTree ≠ [] ∧
      as.map ixAddr = treeLeaves tTree ∧
      RCFullRep t bAddr lim m₁ x_rc ∧
      RepList addrListEnum (Bytes.RepAddressRef addrTy) m₁ as x_leaves ∧
      ObsFn W "KernelClaim::walk_leaves_owned" [x_rc, x_leaves] m₁ r h' cs₁ ∧
      (⟨"KernelClaim::walk_leaves_owned", [x_rc, x_leaves], m₁⟩ : Call F) ∈ calls ∧
      (∀ cl ∈ cs₁, cl ∈ calls) := by
  rcases Obs.«KernelClaim::run_check_env».obs ev with
    ⟨v1, m2, cs12, v98, m99, cs101, m124, cs135, cs155,
      ev14, sg106, _, ev137, ev157, hc174⟩ |
    ⟨v1, m2, cs12, v98, m99, cs101, m124, cs135, _, _, _, _, _, _, _, _, _,
      ev14, sg106, _, ev137, _, _, hc264⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hne266, _⟩
  · rcases load_assumption_tree_spec (V := V) (extra := extra) htTree hroot ev14 with
      hcoll | ⟨ext1, as, hmap, hlLeaves⟩
    · exact .inl (hashedCollision_mono (by intro c hc; rw [hc174]; simp [hc]) hcoll)
    · rcases sg106 with ⟨_, heq67, _⟩ | ⟨w80, w81, ld34, _, rfl, rfl⟩
      · simp at heq67
      · obtain ⟨a0, as0, hcons_as, _, _⟩ := Lib.rep_cons_of_load hlLeaves ld34
        have hne_leaves : treeLeaves tTree ≠ [] := by
          rw [← hmap, hcons_as]; simp
        have hrc2 := hrc.mono ext1
        obtain ⟨_, rfl⟩ := role_ctx_axioms_spec hrc2 ev137
        exact .inr ⟨as, m2, v1, cs155, hne_leaves, hmap, hrc2, hlLeaves, ev157,
          by rw [hc174]; simp, fun cl hcl => by rw [hc174]; simp [hcl]⟩
  · rcases load_assumption_tree_spec (V := V) (extra := extra) htTree hroot ev14 with
      hcoll | ⟨ext1, _, _, _⟩
    · exact .inl (hashedCollision_mono (by intro c hc; rw [hc264]; simp [hc]) hcoll)
    · have extSeg := sg106.casesOn (fun _ _ _ he _ => he ▸ Heap.Extends.refl _)
        (fun _ _ _ _ he _ => he ▸ Heap.Extends.refl _)
      obtain ⟨hax, _⟩ := role_ctx_axioms_spec (hrc.mono (ext1.trans extSeg)) ev137
      simp at hax
  · exact absurd rfl (hne266 [] rfl)

/-! ## `Claim.de` alignment helpers and `IxVM::verify_claim` entry refinement -/

private theorem getScope_ok_inv {variant : UInt64} {bs : List UInt8} {i : Nat}
    {fmt valByte : UInt8}
    (h1 : Ixon.getU8 { idx := i, bytes := ⟨bs.toArray⟩ } =
      .ok fmt { idx := i + 1, bytes := ⟨bs.toArray⟩ })
    (h2 : Ixon.getU8 { idx := i + 1, bytes := ⟨bs.toArray⟩ } =
      .ok valByte { idx := i + 2, bytes := ⟨bs.toArray⟩ })
    {w : UInt8} {st : Ixon.GetState}
    (hok : Claim.getScope variant { idx := i, bytes := ⟨bs.toArray⟩ } = .ok w st) :
    w = valByte ∧ st = { idx := i + 2, bytes := ⟨bs.toArray⟩ } := by
  unfold Claim.getScope at hok
  simp only [bind, EStateM.bind, pure, EStateM.pure, h1] at hok
  by_cases hfmt : (fmt == Ixon.Env.OBJECT_FORMAT) = true
  case neg =>
    simp [unless, hfmt, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok
  simp only [unless, hfmt, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure, h2] at hok
  by_cases hc1 : (valByte == Claim.validatorForVariant variant) = true
  · simp [hc1] at hok; exact hok.symm.imp Eq.symm Eq.symm
  simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc2 : (valByte == Claim.VALIDATOR_ERASED_LEAN_ASSUMED &&
      Claim.variantMayAssume variant) = true
  · simp [hc2] at hok; exact hok.symm.imp Eq.symm Eq.symm
  simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc3 : (valByte == Claim.VALIDATOR_ERASED_LEAN_CLASS &&
      variant == Claim.VARIANT_CHECK_ENV_CLAIM) = true
  · simp [hc3] at hok; exact hok.symm.imp Eq.symm Eq.symm
  simp only [hc3, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hc4 : (Claim.validatorForVariant variant == Claim.VALIDATOR_ERASED_LEAN &&
      valByte == Claim.VALIDATOR_ERASED_LEAN_RETIRED) = true
  · simp [hc4, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok
  · simp [hc4, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok

private theorem getPayload_inScope_variant {variant : UInt64} {valByte : UInt8}
    {s : Ixon.GetState} {c : Claim} {st : Ixon.GetState}
    (hok : Claim.getPayload variant valByte s = .ok c st)
    (hscope : IxVM.Consistency.InScope c) :
    variant = 4 ∨ variant = 5 := by
  unfold Claim.getPayload at hok
  by_cases hv3 : (variant == Claim.VARIANT_EVAL_CLAIM) = true
  · simp only [hv3, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv3, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv4 : (variant == Claim.VARIANT_CHECK_CLAIM) = true
  · exact .inl (beq_iff_eq.mp hv4)
  simp only [hv4, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv5 : (variant == Claim.VARIANT_CHECK_ENV_CLAIM) = true
  · exact .inr (beq_iff_eq.mp hv5)
  simp only [hv5, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv6 : (variant == Claim.VARIANT_REVEAL_CLAIM) = true
  · simp only [hv6, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv6, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv7 : (variant == Claim.VARIANT_CONTAINS_CLAIM) = true
  · simp only [hv7, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv7, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv8 : (variant == Claim.VARIANT_CATALOG_CLAIM) = true
  · simp only [hv8, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp only [hv8, Bool.false_eq_true, ↓reduceIte] at hok
  by_cases hv10 : (variant == Claim.VARIANT_BINDING_CLAIM) = true
  · simp only [hv10, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure] at hok
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    rcases Ixon.Verify.TagN.bind_ok_inv hok with ⟨_, _, _, hok⟩
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok
    cases hscope
  simp [hv10, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hok

private theorem load_role_ctx_validator_3_or_4
    {x_binding : SourceValue F} {valByte : UInt8} {x_axioms r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelRoles::load_role_ctx"
      [x_binding, .field (valByte.toNat : F), x_axioms] h r h' calls) :
    valByte = 3 ∨ valByte = 4 := by
  have hb_lt : valByte.toNat < 4294967296 := by have := valByte.toNat_lt; omega
  rcases Obs.«KernelRoles::load_role_ctx».obs ev with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hv148, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, hv191, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, heq246, _⟩
  · have h3 : (valByte.toNat : F) = ((3 : Nat) : F) := by simpa using Value.field.inj hv148
    exact .inl (UInt8.ext (natCast_inj_of_lt_u32 hb_lt (by decide) h3))
  · have h4 : (valByte.toNat : F) = ((4 : Nat) : F) := by simpa using Value.field.inj hv191
    exact .inr (UInt8.ext (natCast_inj_of_lt_u32 hb_lt (by decide) h4))
  · simp at heq246

theorem verify_claim_decode_spec
    (hDef : Ix.Cert.RoleClosure.DefaultAdmits)
    {d : Digest} {value : SourceValue F} {heap : Heap F} {calls : List (Call F)}
    (ev : ObsFn W verifyClaim [digestValue d] [] value heap calls)
    {bytes : ByteArray} {c : Claim}
    (hde : Claim.de bytes = .ok c)
    (hpack : packDigest (Address.blake3Pure bytes) = d)
    (hscope : IxVM.Consistency.InScope c)
    {V : View} {seeds : List _root_.Address} {b : Ix.Kernel.Admission.Binding}
    (hseeds : IxVM.Consistency.ClaimSeeds c V seeds)
    (hRT : IxVM.Consistency.ReaderTable c V b) :
    V.HashedCollision (bytes :: b.bytes :: IxVM.Consistency.committedImages) calls ∨
    ∃ t : Ix.Kernel.RoleTable,
      Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t ∧
      ((∃ (a : _root_.Address) (h₁ h₂ h₃ : Heap F) (x_rc x_a v₁ v₂ : SourceValue F)
          (cs₁ cs₂ : List (Call F)),
          seeds = [a] ∧
          RCFullRep t b.address 77 h₁ x_rc ∧
          S0.addr h₁ x_a a ∧
          ObsFn W "KernelClaim::assert_claimable" [x_rc, x_a] h₁ v₁ h₂ cs₁ ∧
          ObsFn W "KernelClaim::run_check_transitive" [x_rc, x_a] h₂ v₂ h₃ cs₂ ∧
          (⟨"KernelClaim::assert_claimable", [x_rc, x_a], h₁⟩ : Call F) ∈ calls ∧
          (⟨"KernelClaim::run_check_transitive", [x_rc, x_a], h₂⟩ : Call F) ∈ calls ∧
          (∀ cl ∈ cs₁, cl ∈ calls) ∧
          (∀ cl ∈ cs₂, cl ∈ calls)) ∨
       (∃ (as : List Bytes.Address) (h₁ h₂ : Heap F) (x_rc x_leaves v₁ : SourceValue F)
          (cs₁ : List (Call F)),
          seeds ≠ [] ∧
          as.map ixAddr = seeds ∧
          RCFullRep t b.address 77 h₁ x_rc ∧
          RepList addrListEnum (Bytes.RepAddressRef addrTy) h₁ as x_leaves ∧
          ObsFn W "KernelClaim::walk_leaves_owned" [x_rc, x_leaves] h₁ v₁ h₂ cs₁ ∧
          (⟨"KernelClaim::walk_leaves_owned", [x_rc, x_leaves], h₁⟩ : Call F) ∈ calls ∧
          (∀ cl ∈ cs₁, cl ∈ calls))) := by
  obtain ⟨t, hadm⟩ := readerTable_admits hDef hRT
  obtain ⟨cs_run, ev_run, hc_top⟩ := Obs.«IxVM::verify_claim».obs ev
  have hsub_run : ∀ cl ∈ cs_run, cl ∈ calls := fun cl hcl => by rw [hc_top]; simp [hcl]
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelClaim.run_claim.lookup
    (by simp [IxVM.KernelClaim.run_claim, ControlLower.hasControl]) ev_run
  simp only [IxVM.KernelClaim.run_claim] at d0
  -- 1. `let (idx, len) = hint::<(Field, Field)>("ixvm.io.claim", digest);`
  obtain ⟨v_hint, m_hint, bs_hint, c_hint, c1, d_hint, mt_hint, d1, rfl⟩ := d0.letValue_inv
  obtain ⟨_, _, d_harg, _, rfl⟩ := d_hint.hint_inv
  obtain ⟨_, rfl, rfl⟩ := d_harg.var_inv
  obtain ⟨_, hv_hint, -, ml_hint⟩ := matchPattern_tuple_inv mt_hint
  subst hv_hint
  obtain ⟨x_idx, _, _, _, rfl, mt_idx, ml_hint1, rfl⟩ := matchListWith_cons_inv ml_hint
  obtain rfl := matchPattern_bind_inv mt_idx
  obtain ⟨x_len, _, _, _, rfl, mt_len, ml_hint2, rfl⟩ := matchListWith_cons_inv ml_hint1
  obtain rfl := matchPattern_bind_inv mt_len
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_hint2
  -- 2. `let bytes = IxByteStream::read_finite_byte_stream(0, idx, len);`
  obtain ⟨x_bytes, m_read, bs_read, c_read, c2, d_read, mt_read, d2, rfl⟩ := d1.letValue_inv
  obtain ⟨_, _, _, cs_read, a_read, ev_read, rfl⟩ := d_read.call_inv
  rw [instanceName_plain_some] at ev_read
  obtain ⟨_, _, _, _, _, rfl, d_r0, a_read1, rfl⟩ := a_read.cons_inv
  obtain ⟨rfl, rfl, rfl⟩ := d_r0.literal_inv
  obtain ⟨_, _, _, _, _, rfl, d_r1, a_read2, rfl⟩ := a_read1.cons_inv
  obtain ⟨l_r1, rfl, rfl⟩ := d_r1.var_inv; simp at l_r1; subst l_r1
  obtain ⟨_, _, _, _, _, rfl, d_r2, a_read3, rfl⟩ := a_read2.cons_inv
  obtain ⟨l_r2, rfl, rfl⟩ := d_r2.var_inv; simp at l_r2; subst l_r2
  obtain ⟨rfl, rfl, rfl⟩ := a_read3.nil_inv
  obtain rfl := matchPattern_bind_inv mt_read
  obtain ⟨_, rawBytes, hraw_lt, -, hst_raw⟩ := L1.read_finite_byte_stream_spec ev_read
  -- 3. `let h = Blake3::hash(bytes);`
  obtain ⟨x_h, m_hash, bs_hash, c_hash, c3, d_hash, mt_hash, d3, rfl⟩ := d2.letValue_inv
  obtain ⟨_, _, _, cs_hash, a_hash, ev_hash, rfl⟩ := d_hash.call_inv
  rw [instanceName_plain_some] at ev_hash
  obtain ⟨_, _, _, _, _, rfl, d_h0, a_hash1, rfl⟩ := a_hash.cons_inv
  obtain ⟨l_h0, rfl, rfl⟩ := d_h0.var_inv; simp at l_h0; subst l_h0
  obtain ⟨rfl, rfl, rfl⟩ := a_hash1.nil_inv
  obtain rfl := matchPattern_bind_inv mt_hash
  obtain ⟨ext_hash, rfl, hcv_raw⟩ :=
    L1.hash_digest_spec hst_raw (L1.native_of_lt hraw_lt) ev_hash
  have hhashed_raw : Hashed calls ⟨rawBytes.toArray⟩ :=
    L1.hashed_of_call (hsub_run _ (by simp [instanceName_plain_some])) hst_raw
  -- 4. `assert_eq!(Blake3::pack_digest(h), digest, ...);`
  obtain ⟨_, m_eq1, bs_eq1, c_eq1, c4, d_eq1, mt_eq1, d4, rfl⟩ := d3.letValue_inv
  obtain ⟨_, a_eq1, ap_eq1⟩ := d_eq1.builtin_inv
  obtain ⟨v_pd, _, m_pd, _, _, rfl, d_pd, a_eq1', rfl⟩ := a_eq1.cons_inv
  obtain ⟨_, _, _, cs_pd, a_pd, ev_pd, rfl⟩ := d_pd.call_inv
  rw [instanceName_plain_some] at ev_pd
  obtain ⟨_, _, _, _, _, rfl, d_pd0, a_pd1, rfl⟩ := a_pd.cons_inv
  obtain ⟨l_pd0, rfl, rfl⟩ := d_pd0.var_inv; simp at l_pd0; subst l_pd0
  obtain ⟨rfl, rfl, rfl⟩ := a_pd1.nil_inv
  obtain ⟨_, _, _, _, _, rfl, d_dig, a_eq1'', rfl⟩ := a_eq1'.cons_inv
  obtain ⟨l_dig, rfl, rfl⟩ := d_dig.var_inv; simp at l_dig; subst l_dig
  obtain ⟨rfl, rfl, rfl⟩ := a_eq1''.nil_inv
  obtain ⟨heq_pd, rfl⟩ := Builtin.assertEq_inv ap_eq1
  obtain rfl := matchPattern_wildcard_inv mt_eq1
  obtain ⟨hv_pd, rfl⟩ := pack_digest_spec ev_pd
  rw [hv_pd, hcv_raw] at heq_pd
  have hblk_eq : Address.blake3Pure ⟨rawBytes.toArray⟩ = Address.blake3Pure bytes := by
    apply packDigest_inj (blake3Pure_hash_size _) (blake3Pure_hash_size _)
    have hp := digestValue_inj heq_pd
    rw [← hpack] at hp
    simpa [L1.blake3Pure_eq] using hp
  by_cases heq_bytes : (⟨rawBytes.toArray⟩ : ByteArray) = bytes
  case neg =>
    exact .inl (.inl ⟨Address.blake3Pure bytes, bytes, ⟨rawBytes.toArray⟩,
      .inr (.inl ⟨by simp, rfl⟩), hhashed_raw, heq_bytes, hblk_eq⟩)
  -- No collision on the claim's bytes: `⟨rawBytes.toArray⟩ = bytes`
  subst heq_bytes
  -- Unpack `Claim.de ⟨rawBytes.toArray⟩ = .ok c`
  have hget_top : ∃ st_end, Claim.get { idx := 0, bytes := ⟨rawBytes.toArray⟩ } = .ok c st_end := by
    unfold Claim.de Ixon.runGetExact EStateM.run at hde
    cases hres : Claim.get { idx := 0, bytes := ⟨rawBytes.toArray⟩ } with
    | error e s => simp [hres] at hde
    | ok c' s =>
      simp only [hres] at hde
      by_cases hidx : s.idx = (ByteArray.mk rawBytes.toArray).size
      · simp [hidx] at hde; subst hde; exact ⟨s, rfl⟩
      · simp [hidx] at hde
  obtain ⟨st_end, hget_claim⟩ := hget_top
  -- 5. `let (tag, s) = IxonDeserialize::get_tagn4(bytes);`
  obtain ⟨v_tagn, m_tagn, bs_tagn, c_tagn, c5, d_tagn, mt_tagn, d5, rfl⟩ := d4.letValue_inv
  obtain ⟨_, _, _, cs_tagn, a_tagn, ev_tagn, rfl⟩ := d_tagn.call_inv
  rw [instanceName_plain_some] at ev_tagn
  obtain ⟨_, _, _, _, _, rfl, d_tn0, a_tn1, rfl⟩ := a_tagn.cons_inv
  obtain ⟨l_tn0, rfl, rfl⟩ := d_tn0.var_inv; simp at l_tn0; subst l_tn0
  obtain ⟨rfl, rfl, rfl⟩ := a_tn1.nil_inv
  obtain ⟨_, hv_tagn, -, ml_tagn⟩ := matchPattern_tuple_inv mt_tagn
  subst hv_tagn
  obtain ⟨x_tag0, _, _, _, rfl, mt_tag0, ml_tagn1, rfl⟩ := matchListWith_cons_inv ml_tagn
  obtain rfl := matchPattern_bind_inv mt_tag0
  obtain ⟨x_s0, _, _, _, rfl, mt_s0, ml_tagn2, rfl⟩ := matchListWith_cons_inv ml_tagn1
  obtain rfl := matchPattern_bind_inv mt_s0
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_tagn2
  obtain ⟨rfl, tag, n1, restPtr1, hok_tag, hs_n1, htagn_tup⟩ :=
    TagN.getTagN4_refines_at (i := 0) (by simpa using hst_raw.mono ext_hash) ev_tagn.erase
  simp only [Nat.zero_add] at hok_tag hs_n1
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htagn_tup
  obtain ⟨rfl, rfl⟩ := htagn_tup
  -- 6. `let (flag, size) = tag;`
  obtain ⟨v_ft, m_ft, bs_ft, c_ft, c6, d_ft, mt_ft, d6, rfl⟩ := d5.letValue_inv
  obtain ⟨l_ft, rfl, rfl⟩ := d_ft.var_inv; simp at l_ft
  obtain ⟨_, hv_ft, -, ml_ft⟩ := matchPattern_tuple_inv mt_ft
  rw [← l_ft] at hv_ft
  simp only [Value.tuple.injEq] at hv_ft
  subst hv_ft
  obtain ⟨x_flag, _, _, _, hxf, mt_flag, ml_ft1, rfl⟩ := matchListWith_cons_inv ml_ft
  obtain rfl := matchPattern_bind_inv mt_flag
  obtain ⟨x_size, _, _, _, hxs, mt_size, ml_ft2, rfl⟩ := matchListWith_cons_inv ml_ft1
  obtain rfl := matchPattern_bind_inv mt_size
  obtain ⟨_, rfl⟩ := matchListWith_nil_inv ml_ft2
  simp only [List.cons.injEq] at hxf hxs
  obtain ⟨rfl, hxf'⟩ := hxf
  rw [hxf'] at hxs
  obtain ⟨rfl, _⟩ := hxs
  -- 7. `assert_eq!(flag, 14, ...);`
  obtain ⟨_, m_eq2, bs_eq2, c_eq2, c7, d_eq2, mt_eq2, d7, rfl⟩ := d6.letValue_inv
  have ext_eq2 := d_eq2.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_eq2
  -- 8. `let [_, sz1, sz2, sz3, sz4, sz5, sz6, sz7] = size;`
  obtain ⟨_, m_sz, bs_sz, c_sz, c8, d_sz, mt_sz, d8, rfl⟩ := d7.letValue_inv
  obtain ⟨l_sz0, rfl, rfl⟩ := d_sz.var_inv; simp at l_sz0
  obtain ⟨_, hv_sz, -, ml_sz0⟩ := matchPattern_array_inv mt_sz
  rw [← l_sz0, TagN.u64Value] at hv_sz
  simp only [Value.tuple.injEq] at hv_sz
  subst hv_sz
  obtain ⟨_, _, _, _, hsz0, mt_w0, ml_sz1, rfl⟩ := matchListWith_cons_inv ml_sz0
  obtain rfl := matchPattern_wildcard_inv mt_w0
  obtain ⟨sz1, _, _, _, hsz1, mt_w1, ml_sz2, rfl⟩ := matchListWith_cons_inv ml_sz1
  obtain rfl := matchPattern_bind_inv mt_w1
  obtain ⟨sz2, _, _, _, hsz2, mt_w2, ml_sz3, rfl⟩ := matchListWith_cons_inv ml_sz2
  obtain rfl := matchPattern_bind_inv mt_w2
  obtain ⟨sz3, _, _, _, hsz3, mt_w3, ml_sz4, rfl⟩ := matchListWith_cons_inv ml_sz3
  obtain rfl := matchPattern_bind_inv mt_w3
  obtain ⟨sz4, _, _, _, hsz4, mt_w4, ml_sz5, rfl⟩ := matchListWith_cons_inv ml_sz4
  obtain rfl := matchPattern_bind_inv mt_w4
  obtain ⟨sz5, _, _, _, hsz5, mt_w5, ml_sz6, rfl⟩ := matchListWith_cons_inv ml_sz5
  obtain rfl := matchPattern_bind_inv mt_w5
  obtain ⟨sz6, _, _, _, hsz6, mt_w6, ml_sz7, rfl⟩ := matchListWith_cons_inv ml_sz6
  obtain rfl := matchPattern_bind_inv mt_w6
  obtain ⟨sz7, _, _, _, hsz7, mt_w7, ml_sz8, rfl⟩ := matchListWith_cons_inv ml_sz7
  obtain rfl := matchPattern_bind_inv mt_w7
  have hml8 : bs_sz = [("sz1", sz1), ("sz2", sz2), ("sz3", sz3), ("sz4", sz4),
      ("sz5", sz5), ("sz6", sz6), ("sz7", sz7)] := by
    simp only [List.cons.injEq] at hsz0
    rw [hsz0.2] at hsz1; simp only [List.cons.injEq] at hsz1
    rw [hsz1.2] at hsz2; simp only [List.cons.injEq] at hsz2
    rw [hsz2.2] at hsz3; simp only [List.cons.injEq] at hsz3
    rw [hsz3.2] at hsz4; simp only [List.cons.injEq] at hsz4
    rw [hsz4.2] at hsz5; simp only [List.cons.injEq] at hsz5
    rw [hsz5.2] at hsz6; simp only [List.cons.injEq] at hsz6
    rw [hsz6.2] at hsz7; simp only [List.cons.injEq] at hsz7
    rw [hsz7.2] at ml_sz8
    obtain ⟨_, rfl⟩ := matchListWith_nil_inv ml_sz8
    rfl
  rw [hml8] at d8
  -- 9. `assert_eq!(sz1 + ... + sz7, 0, ...);`
  obtain ⟨_, m_eq3, bs_eq3, c_eq3, c9, d_eq3, mt_eq3, d9, rfl⟩ := d8.letValue_inv
  have ext_eq3 := d_eq3.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_eq3
  -- 10. `let variant = size[0];`
  obtain ⟨x_variant, m_var, bs_var, c_var, c10, d_var, mt_var, d10, rfl⟩ := d9.letValue_inv
  obtain ⟨p_sz, d_szv, pr_sz0⟩ := d_var.index_inv
  obtain ⟨l_szv, rfl, rfl⟩ := d_szv.var_inv; simp at l_szv; subst l_szv
  obtain rfl := matchPattern_bind_inv mt_var
  -- 11. `let (format, s) = IxonDeserialize::read_byte(s);`
  obtain ⟨v_fmt, m_fmt, bs_fmt, c_fmt, c11, d_fmt, mt_fmt, d11, rfl⟩ := d10.letValue_inv
  obtain ⟨_, _, _, cs_fmt, a_fmt, ev_fmt, rfl⟩ := d_fmt.call_inv
  rw [instanceName_plain_some] at ev_fmt
  obtain ⟨_, _, _, _, _, rfl, d_f0, a_f1, rfl⟩ := a_fmt.cons_inv
  obtain ⟨l_f0, rfl, rfl⟩ := d_f0.var_inv; simp at l_f0; subst l_f0
  obtain ⟨rfl, rfl, rfl⟩ := a_f1.nil_inv
  obtain ⟨_, hv_fmt, -, ml_fmt⟩ := matchPattern_tuple_inv mt_fmt
  subst hv_fmt
  obtain ⟨x_fmt, _, _, _, rfl, mt_xfmt, ml_fmt1, rfl⟩ := matchListWith_cons_inv ml_fmt
  obtain rfl := matchPattern_bind_inv mt_xfmt
  obtain ⟨x_s1, _, _, _, rfl, mt_xs1, ml_fmt2, rfl⟩ := matchListWith_cons_inv ml_fmt1
  obtain rfl := matchPattern_bind_inv mt_xs1
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_fmt2
  obtain ⟨rfl, fmtByte, restFmt, _, hcons_fmt, hs_fmt, htup_fmt⟩ :=
    Deserialize.readByte_refines (hs_n1.mono (ext_eq2.trans ext_eq3)) ev_fmt.erase
  injection htup_fmt with htup_fmt'; simp only [List.cons.injEq, and_true] at htup_fmt'
  obtain ⟨rfl, rfl⟩ := htup_fmt'
  obtain ⟨hu8_fmt, hdrop_fmt, -⟩ := Deserialize.getU8_of_drop_cons hcons_fmt
  rw [← hdrop_fmt] at hs_fmt
  -- 12. `assert_eq!(UInt8::to_field(format), 4, ...);`
  obtain ⟨_, m_eq4, bs_eq4, c_eq4, c12, d_eq4, mt_eq4, d12, rfl⟩ := d11.letValue_inv
  have ext_eq4 := d_eq4.heap_extends
  obtain rfl := matchPattern_wildcard_inv mt_eq4
  -- 13. `let (validator, s) = IxonDeserialize::read_byte(s);`
  obtain ⟨v_val, m_val, bs_val, c_val, c13, d_val, mt_val, d13, rfl⟩ := d12.letValue_inv
  obtain ⟨_, _, _, cs_val, a_val, ev_val, rfl⟩ := d_val.call_inv
  rw [instanceName_plain_some] at ev_val
  obtain ⟨_, _, _, _, _, rfl, d_v0, a_v1, rfl⟩ := a_val.cons_inv
  obtain ⟨l_v0, rfl, rfl⟩ := d_v0.var_inv; simp at l_v0; subst l_v0
  obtain ⟨rfl, rfl, rfl⟩ := a_v1.nil_inv
  obtain ⟨_, hv_val, -, ml_val⟩ := matchPattern_tuple_inv mt_val
  subst hv_val
  obtain ⟨x_val, _, _, _, rfl, mt_xval, ml_val1, rfl⟩ := matchListWith_cons_inv ml_val
  obtain rfl := matchPattern_bind_inv mt_xval
  obtain ⟨x_s2, _, _, _, rfl, mt_xs2, ml_val2, rfl⟩ := matchListWith_cons_inv ml_val1
  obtain rfl := matchPattern_bind_inv mt_xs2
  obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_val2
  obtain ⟨rfl, valByte, restVal, _, hcons_val, hs_val, htup_val⟩ :=
    Deserialize.readByte_refines (hs_fmt.mono ext_eq4) ev_val.erase
  injection htup_val with htup_val'; simp only [List.cons.injEq, and_true] at htup_val'
  obtain ⟨rfl, rfl⟩ := htup_val'
  obtain ⟨hu8_val, hdrop_val, -⟩ := Deserialize.getU8_of_drop_cons hcons_val
  rw [← hdrop_val] at hs_val
  rw [Nat.add_assoc] at hu8_val hs_val
  -- Align `Claim.get` through `getTagN 4` and `getScope`
  unfold Claim.get at hget_claim
  simp only [bind, EStateM.bind, hok_tag] at hget_claim
  by_cases hflag_ne : (tag.flag != Claim.FLAG_CLAIM) = true
  · simp [hflag_ne, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hget_claim
  simp only [hflag_ne, Bool.false_eq_true, ↓reduceIte] at hget_claim
  by_cases hret9 : (tag.value == Claim.VARIANT_RESOURCE_CLAIM_RETIRED) = true
  · simp [hret9, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at hget_claim
  simp only [hret9, Bool.false_eq_true, ↓reduceIte] at hget_claim
  obtain ⟨w_val, st_scope, hok_scope, hok_payload⟩ := Ixon.Verify.TagN.bind_ok_inv hget_claim
  obtain ⟨rfl, rfl⟩ := getScope_ok_inv hu8_fmt hu8_val hok_scope
  have hvar_45 := getPayload_inScope_variant hok_payload hscope
  -- 14. `match UInt8::to_field(variant) { ... }`
  obtain ⟨v_scrut, m_scrut, bs_arm, body_arm, c_scrut, c_arm, d_scrut, sel_arm, d_arm, rfl⟩ :=
    d13.matchValue_inv
  obtain ⟨_, _, _, cs_scrut, a_scrut, ev_scrut, rfl⟩ := d_scrut.call_inv
  rw [instanceName_plain_some] at ev_scrut
  obtain ⟨_, _, _, _, _, rfl, d_sc0, a_sc1, rfl⟩ := a_scrut.cons_inv
  obtain ⟨l_sc0, rfl, rfl⟩ := d_sc0.var_inv; simp at l_sc0; subst l_sc0
  obtain ⟨rfl, rfl, rfl⟩ := a_sc1.nil_inv
  obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_scrut
  have hsub_arm : ∀ cl ∈ c_arm, cl ∈ calls := fun cl hcl =>
    hsub_run cl (by simp [hcl])
  rcases hvar_45 with htv4 | htv5
  · -- Variant 4 (`Claim.check`)
    rw [htv4] at pr_sz0 hok_payload
    change projectValue (TagN.u64Value 4) 0 = .ok x_variant at pr_sz0
    simp only [TagN.u64Value, projectValue, List.getElem?_cons_zero, Except.ok.injEq] at pr_sz0
    subst pr_sz0
    -- Select arm `4`: skip `3`, match `4`
    rcases selectArm_cons_inv sel_arm with ⟨mt3, _⟩ | ⟨_, sel_arm1⟩
    · obtain ⟨heq34, _⟩ := MatchesConst.some_inv (MatchesConst.literal 3) mt3
      simp at heq34
    rcases selectArm_cons_inv sel_arm1 with ⟨mt4, rfl⟩ | ⟨nm4, _⟩
    case inr =>
      exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal 4) nm4)
    obtain ⟨_, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 4) mt4
    -- Arm 4 body:
    -- `let (binding, axioms, s) = get_claim_context(s);`
    obtain ⟨_, m_ctx, bs_ctx, c_ctx, ca1, d_ctx, mt_ctx, da1, rfl⟩ := d_arm.letValue_inv
    obtain ⟨_, _, _, cs_ctx, a_ctx, ev_ctx, rfl⟩ := d_ctx.call_inv
    rw [instanceName_plain_some] at ev_ctx
    obtain ⟨_, _, _, _, _, rfl, d_cx0, a_cx1, rfl⟩ := a_ctx.cons_inv
    obtain ⟨l_cx0, rfl, rfl⟩ := d_cx0.var_inv; simp at l_cx0; subst l_cx0
    obtain ⟨rfl, rfl, rfl⟩ := a_cx1.nil_inv
    obtain ⟨_, hv_ctx, -, ml_ctx⟩ := matchPattern_tuple_inv mt_ctx
    subst hv_ctx
    obtain ⟨x_binding, _, _, _, rfl, mt_xb, ml_ctx1, rfl⟩ := matchListWith_cons_inv ml_ctx
    obtain rfl := matchPattern_bind_inv mt_xb
    obtain ⟨x_axioms, _, _, _, rfl, mt_xax, ml_ctx2, rfl⟩ := matchListWith_cons_inv ml_ctx1
    obtain rfl := matchPattern_bind_inv mt_xax
    obtain ⟨x_s3, _, _, _, rfl, mt_xs3, ml_ctx3, rfl⟩ := matchListWith_cons_inv ml_ctx2
    obtain rfl := matchPattern_bind_inv mt_xs3
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_ctx3
    obtain ⟨ext_ctx, ctx, kCtx, _, _, _, hget_ctx, htup_ctx, haddr_bind, hax_none, hs_ctx⟩ :=
      get_claim_context_spec hs_val ev_ctx
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_ctx
    obtain ⟨rfl, rfl, rfl⟩ := htup_ctx
    -- `let rc = KernelRoles::load_role_ctx(binding, UInt8::to_field(validator), axioms);`
    obtain ⟨x_rc, m_rc, bs_rc, c_rc, ca2, d_rc, mt_rc, da2, rfl⟩ := da1.letValue_inv
    obtain ⟨_, _, _, cs_rc, a_rc, ev_rc, rfl⟩ := d_rc.call_inv
    rw [instanceName_plain_some] at ev_rc
    obtain ⟨_, _, _, _, _, rfl, d_rc0, a_rc1, rfl⟩ := a_rc.cons_inv
    obtain ⟨l_rc0, rfl, rfl⟩ := d_rc0.var_inv; simp at l_rc0; subst l_rc0
    obtain ⟨_, _, _, _, _, rfl, d_rc1, a_rc2, rfl⟩ := a_rc1.cons_inv
    obtain ⟨_, _, _, cs_rc_v, a_rc_v, ev_rc_v, rfl⟩ := d_rc1.call_inv
    rw [instanceName_plain_some] at ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rcv0, a_rcv1, rfl⟩ := a_rc_v.cons_inv
    obtain ⟨l_rcv0, rfl, rfl⟩ := d_rcv0.var_inv; simp at l_rcv0; subst l_rcv0
    obtain ⟨rfl, rfl, rfl⟩ := a_rcv1.nil_inv
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rc2, a_rc3, rfl⟩ := a_rc2.cons_inv
    obtain ⟨l_rc2, rfl, rfl⟩ := d_rc2.var_inv; simp at l_rc2; subst l_rc2
    obtain ⟨rfl, rfl, rfl⟩ := a_rc3.nil_inv
    obtain rfl := matchPattern_bind_inv mt_rc
    -- `let (target, s2) = IxonDeserialize::get_address(s);`
    obtain ⟨_, m_tgt, bs_tgt, c_tgt, ca3, d_tgt, mt_tgt, da3, rfl⟩ := da2.letValue_inv
    obtain ⟨_, _, _, cs_tgt, a_tgt, ev_tgt, rfl⟩ := d_tgt.call_inv
    rw [instanceName_plain_some] at ev_tgt
    obtain ⟨_, _, _, _, _, rfl, d_tg0, a_tg1, rfl⟩ := a_tgt.cons_inv
    obtain ⟨l_tg0, rfl, rfl⟩ := d_tg0.var_inv; simp at l_tg0; subst l_tg0
    obtain ⟨rfl, rfl, rfl⟩ := a_tg1.nil_inv
    obtain ⟨_, hv_tgt, -, ml_tgt⟩ := matchPattern_tuple_inv mt_tgt
    subst hv_tgt
    obtain ⟨x_target, _, _, _, rfl, mt_xt, ml_tgt1, rfl⟩ := matchListWith_cons_inv ml_tgt
    obtain rfl := matchPattern_bind_inv mt_xt
    obtain ⟨x_s4, _, _, _, rfl, mt_xs4, ml_tgt2, rfl⟩ := matchListWith_cons_inv ml_tgt1
    obtain rfl := matchPattern_bind_inv mt_xs4
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_tgt2
    -- `let (asm, rest) = get_opt_addr(s2);`
    obtain ⟨_, m_asm, bs_asm, c_asm, ca4, d_asm, mt_asm, da4, rfl⟩ := da3.letValue_inv
    obtain ⟨_, _, _, cs_asm, a_asm, ev_asm, rfl⟩ := d_asm.call_inv
    rw [instanceName_plain_some] at ev_asm
    obtain ⟨_, _, _, _, _, rfl, d_as0, a_as1, rfl⟩ := a_asm.cons_inv
    obtain ⟨l_as0, rfl, rfl⟩ := d_as0.var_inv; simp at l_as0; subst l_as0
    obtain ⟨rfl, rfl, rfl⟩ := a_as1.nil_inv
    obtain ⟨_, hv_asm, -, ml_asm⟩ := matchPattern_tuple_inv mt_asm
    subst hv_asm
    obtain ⟨x_asm, _, _, _, rfl, mt_xasm, ml_asm1, rfl⟩ := matchListWith_cons_inv ml_asm
    obtain rfl := matchPattern_bind_inv mt_xasm
    obtain ⟨x_rest, _, _, _, rfl, mt_xrest, ml_asm2, rfl⟩ := matchListWith_cons_inv ml_asm1
    obtain rfl := matchPattern_bind_inv mt_xrest
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_asm2
    -- `let Lists::Node::Nil = (*(rest));`
    obtain ⟨_, m_nil, bs_nil, c_nil, ca5, d_nil, mt_nil, da5, rfl⟩ := da4.letValue_inv
    obtain ⟨_, d_nil_v, _⟩ := d_nil.load_inv
    obtain ⟨_, rfl, rfl⟩ := d_nil_v.var_inv
    obtain ⟨_, _, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
    -- `assert_claimable(rc, target);`
    obtain ⟨v_ac, m_ac, bs_ac, c_ac, ca6, d_ac, mt_ac, da6, rfl⟩ := da5.letValue_inv
    obtain ⟨_, _, _, cs_ac, a_ac, ev_ac, rfl⟩ := d_ac.call_inv
    rw [instanceName_plain_some] at ev_ac
    obtain ⟨_, _, _, _, _, rfl, d_ac0, a_ac1, rfl⟩ := a_ac.cons_inv
    obtain ⟨l_ac0, rfl, rfl⟩ := d_ac0.var_inv; simp at l_ac0; subst l_ac0
    obtain ⟨_, _, _, _, _, rfl, d_ac1, a_ac2, rfl⟩ := a_ac1.cons_inv
    obtain ⟨l_ac1, rfl, rfl⟩ := d_ac1.var_inv; simp at l_ac1; subst l_ac1
    obtain ⟨rfl, rfl, rfl⟩ := a_ac2.nil_inv
    obtain rfl := matchPattern_wildcard_inv mt_ac
    -- `match asm { None => run_check_transitive(rc, target), Some(r) => ... };`
    obtain ⟨v_mw, m_mw, bs_mw, c_mw, ca7, d_mw, mt_mw, _, rfl⟩ := da6.letValue_inv
    obtain rfl := matchPattern_wildcard_inv mt_mw
    obtain ⟨_, _, bs_asm_m, body_asm_m, _, c_asm_body, d_asm_sc, sel_asm, d_asm_body, rfl⟩ :=
      d_mw.matchValue_inv
    obtain ⟨l_asm_sc, rfl, rfl⟩ := d_asm_sc.var_inv; simp at l_asm_sc; subst l_asm_sc
    -- Align `getPayload 4 valByte` with `get_claim_context`, `get_address`, `get_opt_addr`
    have ext_rc0 := ev_rc.heap_extends
    obtain ⟨ext_tgt, hlen_tgt, _, _, htup_tgt, haddr_tgt, hs_tgt⟩ :=
      Deserialize.getAddress_refines (hs_ctx.mono ext_rc0) ev_tgt.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_tgt
    obtain ⟨rfl, rfl⟩ := htup_tgt
    rw [List.drop_drop] at hs_tgt
    have hget_tgt := getAddress_of_drop hlen_tgt
    obtain ⟨ext_asm, optAsm, kAsm, _, _, hget_asm, htup_asm, hopt_asm, _⟩ :=
      get_opt_addr_spec hs_tgt ev_asm
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_asm
    obtain ⟨rfl, rfl⟩ := htup_asm
    unfold Claim.getPayload at hok_payload
    have hv3_f : (4 == Claim.VARIANT_EVAL_CLAIM) = false := rfl
    have hv4_t : (4 == Claim.VARIANT_CHECK_CLAIM) = true := rfl
    simp only [hv3_f, hv4_t, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure,
      EStateM.pure, hget_ctx, hget_tgt, hget_asm] at hok_payload
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok_payload
    obtain ⟨hb_assumed, hctx_ax, hasm_none⟩ := hscope
    dsimp only at hb_assumed hctx_ax
    subst hasm_none
    have hval3 : valByte = 3 := by
      rcases load_role_ctx_validator_3_or_4 ev_rc with rfl | rfl
      · rfl
      · simp [Claim.VALIDATOR_ERASED_LEAN_ASSUMED] at hb_assumed
    subst hval3
    have hx_ax := hax_none hctx_ax
    rw [hx_ax] at ev_rc
    obtain ⟨ctx', hctx_some, hb_addr⟩ := hRT.1
    simp only [Claim.context?, Option.some.injEq] at hctx_some
    have hb_eq : b.address = ctx.binding := by rw [hb_addr, ← hctx_some]
    rw [← hb_eq] at haddr_bind
    rcases load_role_ctx_spec (V := V)
        (extra := bytes :: b.bytes :: IxVM.Consistency.committedImages)
        hadm (by simp) haddr_bind ev_rc with hcoll | ⟨_, hrc_rep⟩
    · exact .inl (hashedCollision_mono
        (fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hcl])) hcoll)
    dsimp only at hopt_asm
    subst hopt_asm
    rcases selectArm_cons_inv sel_asm with ⟨mt_none, rfl⟩ | ⟨nm_none, _⟩
    case inr =>
      have hne_none := matchPattern_construct_none (by trivial) nm_none
      rw [Obs.Names.n253830841395321305] at hne_none
      exact absurd rfl (hne_none [] rfl)
    obtain ⟨_, _, -, ml_none⟩ := matchPattern_construct_inv mt_none
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_none
    obtain ⟨_, _, _, cs_tr, a_tr, ev_tr, rfl⟩ := d_asm_body.call_inv
    rw [instanceName_plain_some] at ev_tr
    obtain ⟨_, _, _, _, _, rfl, d_tr0, a_tr1, rfl⟩ := a_tr.cons_inv
    obtain ⟨l_tr0, rfl, rfl⟩ := d_tr0.var_inv; simp at l_tr0; subst l_tr0
    obtain ⟨_, _, _, _, _, rfl, d_tr1, a_tr2, rfl⟩ := a_tr1.cons_inv
    obtain ⟨l_tr1, rfl, rfl⟩ := d_tr1.var_inv; simp at l_tr1; subst l_tr1
    obtain ⟨rfl, rfl, rfl⟩ := a_tr2.nil_inv
    obtain ⟨_, hseeds_eq⟩ := hseeds
    exact .inr ⟨t, hadm, .inl ⟨_, m_asm, m_ac, m_mw, x_rc, x_target, v_ac, v_mw, cs_ac, cs_tr,
      hseeds_eq, hrc_rep.mono (ext_tgt.trans ext_asm),
      ⟨_, Bytes.repAddressRef_heapMono₂ addrTy ext_asm haddr_tgt, rfl⟩,
      ev_ac, ev_tr,
      hsub_arm _ (by simp [instanceName_plain_some]),
      hsub_arm _ (by simp [instanceName_plain_some]),
      fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hcl]),
      fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hcl])⟩⟩
  · -- Variant 5 (`Claim.checkEnv`)
    rw [htv5] at pr_sz0 hok_payload
    change projectValue (TagN.u64Value 5) 0 = .ok x_variant at pr_sz0
    simp only [TagN.u64Value, projectValue, List.getElem?_cons_zero, Except.ok.injEq] at pr_sz0
    subst pr_sz0
    -- Select arm `5`: skip `3`, skip `4`, match `5`
    rcases selectArm_cons_inv sel_arm with ⟨mt3, _⟩ | ⟨_, sel_arm1⟩
    · obtain ⟨heq35, _⟩ := MatchesConst.some_inv (MatchesConst.literal 3) mt3
      simp at heq35
    rcases selectArm_cons_inv sel_arm1 with ⟨mt4, _⟩ | ⟨_, sel_arm2⟩
    · obtain ⟨heq45, _⟩ := MatchesConst.some_inv (MatchesConst.literal 4) mt4
      simp at heq45
    rcases selectArm_cons_inv sel_arm2 with ⟨mt5, rfl⟩ | ⟨nm5, _⟩
    case inr =>
      exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal 5) nm5)
    obtain ⟨_, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 5) mt5
    -- Arm 5 body:
    -- `let (binding, axioms, s) = get_claim_context(s);`
    obtain ⟨_, m_ctx, bs_ctx, c_ctx, ca1, d_ctx, mt_ctx, da1, rfl⟩ := d_arm.letValue_inv
    obtain ⟨_, _, _, cs_ctx, a_ctx, ev_ctx, rfl⟩ := d_ctx.call_inv
    rw [instanceName_plain_some] at ev_ctx
    obtain ⟨_, _, _, _, _, rfl, d_cx0, a_cx1, rfl⟩ := a_ctx.cons_inv
    obtain ⟨l_cx0, rfl, rfl⟩ := d_cx0.var_inv; simp at l_cx0; subst l_cx0
    obtain ⟨rfl, rfl, rfl⟩ := a_cx1.nil_inv
    obtain ⟨_, hv_ctx, -, ml_ctx⟩ := matchPattern_tuple_inv mt_ctx
    subst hv_ctx
    obtain ⟨x_binding, _, _, _, rfl, mt_xb, ml_ctx1, rfl⟩ := matchListWith_cons_inv ml_ctx
    obtain rfl := matchPattern_bind_inv mt_xb
    obtain ⟨x_axioms, _, _, _, rfl, mt_xax, ml_ctx2, rfl⟩ := matchListWith_cons_inv ml_ctx1
    obtain rfl := matchPattern_bind_inv mt_xax
    obtain ⟨x_s3, _, _, _, rfl, mt_xs3, ml_ctx3, rfl⟩ := matchListWith_cons_inv ml_ctx2
    obtain rfl := matchPattern_bind_inv mt_xs3
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_ctx3
    obtain ⟨ext_ctx, ctx, kCtx, _, _, _, hget_ctx, htup_ctx, haddr_bind, hax_none, hs_ctx⟩ :=
      get_claim_context_spec hs_val ev_ctx
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_ctx
    obtain ⟨rfl, rfl, rfl⟩ := htup_ctx
    -- `let rc = KernelRoles::load_role_ctx(binding, UInt8::to_field(validator), axioms);`
    obtain ⟨x_rc, m_rc, bs_rc, c_rc, ca2, d_rc, mt_rc, da2, rfl⟩ := da1.letValue_inv
    obtain ⟨_, _, _, cs_rc, a_rc, ev_rc, rfl⟩ := d_rc.call_inv
    rw [instanceName_plain_some] at ev_rc
    obtain ⟨_, _, _, _, _, rfl, d_rc0, a_rc1, rfl⟩ := a_rc.cons_inv
    obtain ⟨l_rc0, rfl, rfl⟩ := d_rc0.var_inv; simp at l_rc0; subst l_rc0
    obtain ⟨_, _, _, _, _, rfl, d_rc1, a_rc2, rfl⟩ := a_rc1.cons_inv
    obtain ⟨_, _, _, cs_rc_v, a_rc_v, ev_rc_v, rfl⟩ := d_rc1.call_inv
    rw [instanceName_plain_some] at ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rcv0, a_rcv1, rfl⟩ := a_rc_v.cons_inv
    obtain ⟨l_rcv0, rfl, rfl⟩ := d_rcv0.var_inv; simp at l_rcv0; subst l_rcv0
    obtain ⟨rfl, rfl, rfl⟩ := a_rcv1.nil_inv
    obtain ⟨rfl, rfl⟩ := L1.u8_toField ev_rc_v
    obtain ⟨_, _, _, _, _, rfl, d_rc2, a_rc3, rfl⟩ := a_rc2.cons_inv
    obtain ⟨l_rc2, rfl, rfl⟩ := d_rc2.var_inv; simp at l_rc2; subst l_rc2
    obtain ⟨rfl, rfl, rfl⟩ := a_rc3.nil_inv
    obtain rfl := matchPattern_bind_inv mt_rc
    -- `let (root, s2) = IxonDeserialize::get_address(s);`
    obtain ⟨_, m_rt, bs_rt, c_rt, ca3, d_rt, mt_rt, da3, rfl⟩ := da2.letValue_inv
    obtain ⟨_, _, _, cs_rt, a_rt, ev_rt, rfl⟩ := d_rt.call_inv
    rw [instanceName_plain_some] at ev_rt
    obtain ⟨_, _, _, _, _, rfl, d_rt0, a_rt1, rfl⟩ := a_rt.cons_inv
    obtain ⟨l_rt0, rfl, rfl⟩ := d_rt0.var_inv; simp at l_rt0; subst l_rt0
    obtain ⟨rfl, rfl, rfl⟩ := a_rt1.nil_inv
    obtain ⟨_, hv_rt, -, ml_rt⟩ := matchPattern_tuple_inv mt_rt
    subst hv_rt
    obtain ⟨x_root, _, _, _, rfl, mt_xrt, ml_rt1, rfl⟩ := matchListWith_cons_inv ml_rt
    obtain rfl := matchPattern_bind_inv mt_xrt
    obtain ⟨x_s4, _, _, _, rfl, mt_xs4, ml_rt2, rfl⟩ := matchListWith_cons_inv ml_rt1
    obtain rfl := matchPattern_bind_inv mt_xs4
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_rt2
    -- `let (asm, rest) = get_opt_addr(s2);`
    obtain ⟨_, m_asm, bs_asm, c_asm, ca4, d_asm, mt_asm, da4, rfl⟩ := da3.letValue_inv
    obtain ⟨_, _, _, cs_asm, a_asm, ev_asm, rfl⟩ := d_asm.call_inv
    rw [instanceName_plain_some] at ev_asm
    obtain ⟨_, _, _, _, _, rfl, d_as0, a_as1, rfl⟩ := a_asm.cons_inv
    obtain ⟨l_as0, rfl, rfl⟩ := d_as0.var_inv; simp at l_as0; subst l_as0
    obtain ⟨rfl, rfl, rfl⟩ := a_as1.nil_inv
    obtain ⟨_, hv_asm, -, ml_asm⟩ := matchPattern_tuple_inv mt_asm
    subst hv_asm
    obtain ⟨x_asm, _, _, _, rfl, mt_xasm, ml_asm1, rfl⟩ := matchListWith_cons_inv ml_asm
    obtain rfl := matchPattern_bind_inv mt_xasm
    obtain ⟨x_rest, _, _, _, rfl, mt_xrest, ml_asm2, rfl⟩ := matchListWith_cons_inv ml_asm1
    obtain rfl := matchPattern_bind_inv mt_xrest
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_asm2
    -- `let Lists::Node::Nil = (*(rest));`
    obtain ⟨_, m_nil, bs_nil, c_nil, ca5, d_nil, mt_nil, da5, rfl⟩ := da4.letValue_inv
    obtain ⟨_, d_nil_v, _⟩ := d_nil.load_inv
    obtain ⟨_, rfl, rfl⟩ := d_nil_v.var_inv
    obtain ⟨_, _, -, ml_nil⟩ := matchPattern_construct_inv mt_nil
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nil
    -- `run_check_env(rc, root, asm);`
    obtain ⟨v_rce, m_rce, bs_rce, c_rce, ca6, d_rce, mt_rce, _, rfl⟩ := da5.letValue_inv
    obtain ⟨_, _, _, cs_rce, a_rce, ev_rce, rfl⟩ := d_rce.call_inv
    rw [instanceName_plain_some] at ev_rce
    obtain ⟨_, _, _, _, _, rfl, d_ce0, a_ce1, rfl⟩ := a_rce.cons_inv
    obtain ⟨l_ce0, rfl, rfl⟩ := d_ce0.var_inv; simp at l_ce0; subst l_ce0
    obtain ⟨_, _, _, _, _, rfl, d_ce1, a_ce2, rfl⟩ := a_ce1.cons_inv
    obtain ⟨l_ce1, rfl, rfl⟩ := d_ce1.var_inv; simp at l_ce1; subst l_ce1
    obtain ⟨_, _, _, _, _, rfl, d_ce2, a_ce3, rfl⟩ := a_ce2.cons_inv
    obtain ⟨l_ce2, rfl, rfl⟩ := d_ce2.var_inv; simp at l_ce2; subst l_ce2
    obtain ⟨rfl, rfl, rfl⟩ := a_ce3.nil_inv
    obtain rfl := matchPattern_wildcard_inv mt_rce
    -- Align `getPayload 5 valByte`
    have ext_rc0 := ev_rc.heap_extends
    obtain ⟨ext_rt, hlen_rt, _, _, htup_rt, haddr_rt, hs_rt⟩ :=
      Deserialize.getAddress_refines (hs_ctx.mono ext_rc0) ev_rt.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_rt
    obtain ⟨rfl, rfl⟩ := htup_rt
    rw [List.drop_drop] at hs_rt
    have hget_rt := getAddress_of_drop hlen_rt
    obtain ⟨ext_asm, optAsm, kAsm, _, _, hget_asm, htup_asm, hopt_asm, _⟩ :=
      get_opt_addr_spec hs_rt ev_asm
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_asm
    obtain ⟨rfl, rfl⟩ := htup_asm
    unfold Claim.getPayload at hok_payload
    have hv3_f : (5 == Claim.VARIANT_EVAL_CLAIM) = false := rfl
    have hv4_f : (5 == Claim.VARIANT_CHECK_CLAIM) = false := rfl
    have hv5_t : (5 == Claim.VARIANT_CHECK_ENV_CLAIM) = true := rfl
    simp only [hv3_f, hv4_f, hv5_t, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure,
      EStateM.pure, hget_ctx, hget_rt, hget_asm] at hok_payload
    obtain ⟨rfl, _⟩ := Ixon.Verify.TagN.pure_ok_inv hok_payload
    obtain ⟨hb_assumed, hctx_ax, hasm_none⟩ := hscope
    dsimp only at hb_assumed hctx_ax
    subst hasm_none
    have hval3 : valByte = 3 := by
      rcases load_role_ctx_validator_3_or_4 ev_rc with rfl | rfl
      · rfl
      · simp [Claim.VALIDATOR_ERASED_LEAN_ASSUMED] at hb_assumed
    subst hval3
    have hx_ax := hax_none hctx_ax
    rw [hx_ax] at ev_rc
    obtain ⟨ctx', hctx_some, hb_addr⟩ := hRT.1
    simp only [Claim.context?, Option.some.injEq] at hctx_some
    have hb_eq : b.address = ctx.binding := by rw [hb_addr, ← hctx_some]
    rw [← hb_eq] at haddr_bind
    rcases load_role_ctx_spec (V := V)
        (extra := bytes :: b.bytes :: IxVM.Consistency.committedImages)
        hadm (by simp) haddr_bind ev_rc with hcoll | ⟨_, hrc_rep⟩
    · exact .inl (hashedCollision_mono
        (fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hcl])) hcoll)
    dsimp only at hopt_asm
    subst hopt_asm
    obtain ⟨tTree, hv_trees, htree_root, hseeds_eq⟩ := hseeds
    have htTree_mem : tTree ∈ V.trees := by rw [hv_trees]; simp
    have hroot_addr : S0.addr m_asm x_root (treeRoot tTree) :=
      ⟨_, Bytes.repAddressRef_heapMono₂ addrTy ext_asm haddr_rt, htree_root.symm⟩
    rcases run_check_env_none_spec (V := V)
        (extra := bytes :: b.bytes :: IxVM.Consistency.committedImages)
        htTree_mem (hrc_rep.mono (ext_rt.trans ext_asm)) hroot_addr ev_rce with
      hcoll | ⟨as, m₁, x_leaves, cs₁, hne_leaves, hmap_as, hrc_m1, hl_leaves, ev_wlo, hcl_wlo, hsub1⟩
    · exact .inl (hashedCollision_mono
        (fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hcl])) hcoll)
    · rw [← hseeds_eq] at hne_leaves hmap_as
      exact .inr ⟨t, hadm, .inr ⟨as, m₁, m_rce, x_rc, x_leaves, v_rce, cs₁,
        hne_leaves, hmap_as, hrc_m1, hl_leaves, ev_wlo,
        hsub_arm _ (by simp [instanceName_plain_some, hcl_wlo]),
        fun cl hcl => hsub_arm cl (by simp [instanceName_plain_some, hsub1 cl hcl])⟩⟩

end IxVM.Refinement.Claim
