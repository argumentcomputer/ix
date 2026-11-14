import IxVMRefinement.L1.Decode
import IxVMRefinement.L1.Convert
import IxVMRefinement.Obs.IxonSerialize
import IxVMRefinement.Obs.Ingress

/-! # Projection Serialization and Constant Ingress (`Ingress`)

Observed-derivation (`ObsFn`) specifications for:
* projection-record serialization (`IxonSerialize::put_u64_le`, `put_tagn_wide`, `put_tagn_tail`,
  `put_tagn0`, `put_tagn4`, `put_address`, `put_{inductive,constructor,recursor,definition}_proj`,
  `put_constant_info`, `put_{sharing,refs,univs,binders}`, `put_constant`), discharging
  `Core.Specs.Callees.put_constant`;
* stream hashing (`Blake3::bytes_to_addr`) and mutual-block projection-address construction
  (`Ingress::muts_member_at`, `projection_addr`, `build_recur_addrs_walk`, `build_recur_addrs`),
  discharging `Core.Specs.Callees.build_recur_addrs`;
* definition safety/recursor-address helpers (`Ingress::defn_is_unsafe_ci`,
  `defn_member_recur_addrs`) and top-level record ingress (`Ingress::get_ci_dprj`, `get_ci_iprj`,
  `get_ci_cprj`, `get_ci_rprj`, `get_ci`).
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library Aiur.Library.List

namespace IxVM.Refinement.L1

open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Refinement.TagN
open IxVM.Refinement.Deserialize
open Ixon.Verify.Codec
open Ixon.Verify.Codec.ConstantTables
open Ixon.Verify.Codec.NonrecursiveConstant

local notation "W" => IxVM.Refinement.Obs.W

/-! ## Primitive, byte-stream, and address-cell helpers -/

private theorem val_cast_u56_ing {n : Nat} (h : n < 72057594037927936) :
    ZMod.val (n : F) = n := by
  have hP : (72057594037927936 : Nat) < U32.Goldilocks.modulus := by decide
  exact ZMod.val_cast_of_lt (Nat.lt_trans h hP)

private theorem val_cast_le_u56_ing {n : Nat} (h : n ≤ 72057594037927936) :
    ZMod.val (n : F) = n := by
  have hP : (72057594037927936 : Nat) < U32.Goldilocks.modulus := by decide
  exact ZMod.val_cast_of_lt (Nat.lt_of_le_of_lt h hP)

private theorem byteListEnum_eq_names :
    Names.«Lists::Node<Field>» = Core.byteListEnum := rfl

private theorem repU8_bv (h : Heap F) (b : UInt8) :
    RepU8 h b (.field (b.toNat : F)) := rfl

private theorem repU8_ofNatLT (h : Heap F) {n : Nat} (hn : n < 256) :
    RepU8 h n.toUInt8 (.field (n : F)) := by
  show (.field (n : F) : SourceValue F) = .field ((n.toUInt8.toNat : Nat) : F)
  have hmod : n.toUInt8.toNat = n := by
    simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hn]
  rw [hmod]

private theorem snoc_byte {h h' : Heap F} {b : UInt8} {bv_val p : SourceValue F}
    {bs : List UInt8}
    (hm : h' = h ++ [.construct Names.«Lists::Node<Field>» "Cons" [bv_val, p]])
    (hb : RepU8 h b bv_val)
    (hp : Bytes.RepByteStream Core.byteListEnum h bs p) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h' (b :: bs)
        (.ptr (.enum Names.«Lists::Node<Field>») h.length) := by
  rw [hm]
  exact ⟨Heap.Extends.snoc h _, Lib.rep_store_cons repU8_heapMono₂ hb hp⟩

/-- `UInt8::raw_add` on two byte field values returns `(a + b) % 256` and `(a + b) / 256` without
allocation. -/
theorem u8_raw_add_spec {a b : Nat} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : a < 256) (hb : b < 256)
    (ev : ObsFn W "UInt8::raw_add" [.field (a : F), .field (b : F)] h r h' cs) :
    r = .tuple [.field (((a + b) % 256 : Nat) : F), .field (((a + b) / 256 : Nat) : F)] ∧
      h' = h := by
  have hm := ev.erase.map_row Mirrors.«UInt8::raw_add».none
  simp only [mapCall, TagN.rawAdd_row ha hb, Constant.toValue, Value.mapAddress,
    Option.some.injEq, Prod.mk.injEq] at hm
  exact ⟨hm.1.symm, hm.2.symm⟩

/-- `WordLists::length_u64<T>` on an empty list returns `u64Value 0` without allocation. -/
theorem length_u64_nil_eval {t_T : Generic.Ty} {x_list r : SourceValue F} {h h' : Heap F}
    (hload : loadValue h x_list =
      .ok (.construct (Instance.mk "Lists::Node" [t_T]).symbol "Nil" []))
    (ev : EvalFn W (Instance.mk "WordLists::length_u64" [t_T]).symbol [x_list] h r h') :
    r = u64Value 0 ∧ h' = h := by
  have body := ev.function_inv (Mirrors.«WordLists::length_u64».lookup t_T)
    (by simp [IxVM.WordLists.length_u64, ControlLower.hasControl])
  simp only [IxVM.WordLists.length_u64] at body
  obtain ⟨v1, m2, bs3, body4, d5, sel6, d7⟩ := body.matchValue_inv
  obtain ⟨p8, d9, ld10⟩ := d5.load_inv
  obtain ⟨l11, rfl⟩ := d9.var_inv
  simp at l11
  subst l11
  rw [hload] at ld10
  injection ld10 with hv1
  subst v1
  have hctor : constructorName [("T", t_T)] (.named "Lists::Node" [.param "T"]) =
      (Instance.mk "Lists::Node" [t_T]).symbol := by
    simp [constructorName, Generic.Ty.subst, Instance.symbol]
  rcases selectArm_cons_inv sel6 with ⟨mt12, rfl⟩ | ⟨nm12, _⟩
  · obtain ⟨vs13, _, _, ml14⟩ := matchPattern_construct_inv mt12
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml14
    obtain ⟨v15, d16, rfl⟩ := d7.repeat_inv
    have hbyte0 : W.constant "UInt8::BYTE_0" (Generic.Ty.subst [("T", t_T)] .field) =
        .ok (.literal (0 : F)) := Names.c9173999864893739538
    obtain ⟨rfl, rfl⟩ := d16.global_literal_inv hbyte0
    exact ⟨by simp [u64Value, List.replicate], rfl⟩
  · have hne := matchPattern_construct_none (by trivial) nm12
    rw [hctor] at hne
    exact (hne [] rfl rfl).elim

/-- `WordLists::length_u64<T>` on a represented `[]` list returns `u64Value 0` without allocation. -/
theorem length_u64_nil_spec {α : Type*} {t_T : Generic.Ty}
    {R : Heap F → α → SourceValue F → Prop}
    {x_list r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrep : RepList (Instance.mk "Lists::Node" [t_T]).symbol R h [] x_list)
    (ev : ObsFn W (Instance.mk "WordLists::length_u64" [t_T]).symbol [x_list] h r h' cs) :
    r = u64Value 0 ∧ h' = h := by
  cases hrep with
  | nil cell =>
    have hload : loadValue h (.ptr (.enum (Instance.mk "Lists::Node" [t_T]).symbol) _) =
        .ok (.construct (Instance.mk "Lists::Node" [t_T]).symbol "Nil" []) := by
      simp [loadValue, cell, Value.type, bind, Except.bind, pure, Except.pure]
    exact length_u64_nil_eval hload ev.erase

/-- `digestV d` has `Value.type = Core.addrTy`. -/
theorem digestV_type (d : Vector UInt8 32) : (digestV d).type = Core.addrTy := by
  have hlen : d.toList.length = 32 := d.length_toList
  have hmap : ∀ xs : List UInt8,
      (xs.map bv : List (SourceValue F)).map Value.type = List.replicate xs.length .field := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [bv, Value.type, ih, List.replicate_succ]
  simp only [digestV, Value.type, hmap, hlen, Core.addrTy]

/-- Loading `digestV d` from `r` witnesses `Bytes.RepAddressRef Core.addrTy h d r`. -/
theorem repAddressRef_of_load_digestV {h : Heap F} {d : Vector UInt8 32} {r : SourceValue F}
    (hload : loadValue h r = .ok (digestV d)) :
    Bytes.RepAddressRef Core.addrTy h d r := by
  cases r with
  | field _ => simp [loadValue] at hload
  | tuple _ => simp [loadValue] at hload
  | construct _ _ _ => simp [loadValue] at hload
  | ptr ty n =>
    simp only [loadValue] at hload
    cases hcell : h[n]? with
    | none => simp [hcell, bind, Except.bind] at hload
    | some v =>
      simp only [hcell, bind, Except.bind] at hload
      by_cases hty : v.type = ty
      · simp only [hty, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hload
        subst v
        rw [digestV_type d] at hty
        subst ty
        exact ⟨n, digestV d, rfl, hcell, rfl⟩
      · simp [hty] at hload

/-! ## `IxonSerialize`: TagN, address, and projection-record serialization -/

private theorem u64Value_shiftRight8 (x : UInt64) :
    (.tuple [
      .field ((x.toNat / 256 % 256 : Nat) : F),
      .field ((x.toNat / 65536 % 256 : Nat) : F),
      .field ((x.toNat / 16777216 % 256 : Nat) : F),
      .field ((x.toNat / 4294967296 % 256 : Nat) : F),
      .field ((x.toNat / 1099511627776 % 256 : Nat) : F),
      .field ((x.toNat / 281474976710656 % 256 : Nat) : F),
      .field ((x.toNat / 72057594037927936 % 256 : Nat) : F),
      .field 0] : SourceValue F) = u64Value (x >>> 8).toNat := by
  have hx := x.toNat_lt
  have hsh : (x >>> 8).toNat = x.toNat / 256 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rw [hsh]
  unfold u64Value
  have d1 : x.toNat / 256 / 256 = x.toNat / 65536 := by omega
  have d2 : x.toNat / 256 / 65536 = x.toNat / 16777216 := by omega
  have d3 : x.toNat / 256 / 16777216 = x.toNat / 4294967296 := by omega
  have d4 : x.toNat / 256 / 4294967296 = x.toNat / 1099511627776 := by omega
  have d5 : x.toNat / 256 / 1099511627776 = x.toNat / 281474976710656 := by omega
  have d6 : x.toNat / 256 / 281474976710656 = x.toNat / 72057594037927936 := by omega
  have d7 : x.toNat / 256 / 72057594037927936 % 256 = 0 := by omega
  rw [d1, d2, d3, d4, d5, d6, d7]
  simp

private theorem trimmedBytes_zero_toList (x : UInt64) :
    (trimmedBytes x 0).data.toList = [] := rfl

private theorem trimmedBytes_succ_toList (x : UInt64) (k : Nat) :
    (trimmedBytes x (k + 1)).data.toList =
      x.toUInt8 :: (trimmedBytes (x >>> 8) k).data.toList := by
  simp [trimmedBytes, ByteArray.data_append, Array.toList_append, List.toByteArray]

/-- `IxonSerialize::put_u64_le` prepends `trimmedBytes x k` (`k ≤ 8`) before `rest`. -/
theorem put_u64_le_spec (k : Nat) :
    ∀ {x : UInt64} {rest : List UInt8} {x_rest r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      k ≤ 8 →
      Bytes.RepByteStream Core.byteListEnum h rest x_rest →
      ObsFn W "IxonSerialize::put_u64_le" [u64Value x.toNat, .field (k : F), x_rest] h r h' calls →
      Heap.Extends h h' ∧
        Bytes.RepByteStream Core.byteListEnum h' ((trimmedBytes x k).data.toList ++ rest) r := by
  induction k with
  | zero =>
    intro x rest x_rest r h h' calls _ hrest ev
    rcases «IxonSerialize::put_u64_le».obs ev with
      ⟨_, he16, he17, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hne19, _, _, _, _, _, _⟩
    · rw [he16, he17, trimmedBytes_zero_toList, List.nil_append]
      exact ⟨Heap.Extends.refl _, hrest⟩
    · exact (hne19 (by simp)).elim
  | succ k ih =>
    intro x rest x_rest r h h' calls hk hrest ev
    rcases «IxonSerialize::put_u64_le».obs ev with
      ⟨hv14, _, _, _⟩ |
      ⟨x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, x_b8, v157, m166, cs174, v178,
        _, hv33, he152, hm151, op200, ev176, _⟩
    · have hzero := (natCast_eq_zero_iff (a := k + 1) (by omega)).mp (Value.field.inj hv14)
      omega
    · unfold u64Value at hv33
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv33
      rcases hv33 with ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8⟩
      subst x_b1 x_b2 x_b3 x_b4 x_b5 x_b6 x_b7 x_b8
      rw [u64Value_shiftRight8 x] at ev176
      simp only [evalBinOp, Except.ok.injEq] at op200
      have hv178 : v178 = .field (k : F) := by
        rw [← op200]; push_cast; ring_nf
      rw [hv178] at ev176
      obtain ⟨ext1, htail⟩ := ih (by omega) hrest ev176
      have hb1_u8 : RepU8 m166 x.toUInt8 (.field ((x.toNat % 256 : Nat) : F)) := by
        show (.field ((x.toNat % 256 : Nat) : F) : SourceValue F) = .field (x.toUInt8.toNat : F)
        simp [UInt64.toUInt8, UInt8.toNat_ofNat']
      obtain ⟨ext2, hcons⟩ := snoc_byte hm151 hb1_u8 htail
      rw [he152, trimmedBytes_succ_toList, List.cons_append]
      exact ⟨ext1.trans ext2, hcons⟩

private theorem u64Value_neg_pow16 :
    (.tuple [.field 0, .field 0, .field 255, .field 255, .field 255, .field 255, .field 255, .field 255] :
      SourceValue F) = u64Value 18446744073709486080 := by
  decide

private theorem u64Value_neg_pow24 :
    (.tuple [.field 0, .field 0, .field 0, .field 255, .field 255, .field 255, .field 255, .field 255] :
      SourceValue F) = u64Value 18446744073692774400 := by
  decide

private theorem u64Value_neg_pow32 :
    (.tuple [.field 0, .field 0, .field 0, .field 0, .field 255, .field 255, .field 255, .field 255] :
      SourceValue F) = u64Value 18446744069414584320 := by
  decide

private theorem u64Value_neg_end2_0 :
    (.tuple [.field 128, .field 191, .field 255, .field 255, .field 255, .field 255, .field 255, .field 255] :
      SourceValue F) = u64Value 18446744073709535104 := by
  decide

/-- `put_tagn_wide` at rung code `3` (`8` trailing bytes). -/
private theorem put_tagn_wide_3_spec {d : Nat} {rest : List UInt8}
    {x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hd : d < 18446744073709551616)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 3, u64Value d, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h'
        (Ixon.tagNHeader 0 0 (128 + 64 + 3) :: (trimmedBytes d.toUInt64 8).data.toList ++ rest) r := by
  rcases «IxonSerialize::put_tagn_wide».obs ev with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hv68, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hv68, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hv419, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hv419, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, hv756, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, hv756, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, v1080, v1081, m1083, cs1091, v1094, m1111, cs1119,
      _, _, _, _, _, he1076, hm1075, op1108, ev1093, ev1121, _⟩
  · exact absurd (Value.field.inj hv68) (by decide)
  · exact absurd (Value.field.inj hv68) (by decide)
  · exact absurd (Value.field.inj hv419) (by decide)
  · exact absurd (Value.field.inj hv419) (by decide)
  · exact absurd (Value.field.inj hv756) (by decide)
  · exact absurd (Value.field.inj hv756) (by decide)
  · simp only [evalBinOp, Except.ok.injEq] at op1108
    have hv1094 : v1094 = .field (195 : F) := by rw [← op1108]; norm_num
    rw [hv1094] at ev1093
    obtain ⟨hv1080, hm1083, _⟩ := Lib.u8_from_field_spec ev1093
    subst v1080 m1083
    have hd_u64 : d.toUInt64.toNat = d := UInt64.toNat_ofNat_of_lt hd
    rw [← hd_u64] at ev1121
    obtain ⟨ext1, htail⟩ := put_u64_le_spec 8 (Nat.le_refl _) hrest ev1121
    have hhdr : RepU8 m1111 (Ixon.tagNHeader 0 0 (128 + 64 + 3)) (.field (195 : F)) := by
      decide
    obtain ⟨ext2, hcons⟩ := snoc_byte hm1075 hhdr htail
    rw [he1076, List.cons_append]
    exact ⟨ext1.trans ext2, hcons⟩

/-- `put_tagn_wide` at rung code `2` (`4` or `8` trailing bytes). -/
private theorem put_tagn_wide_2_spec {d : Nat} {rest : List UInt8}
    {x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hd : d < 18446744073709551616)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 2, u64Value d, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h'
        ((if d < 4294967296 then
            Ixon.tagNHeader 0 0 (128 + 64 + 2) :: (trimmedBytes d.toUInt64 4).data.toList
          else
            Ixon.tagNHeader 0 0 (128 + 64 + 3) ::
              (trimmedBytes (d - 4294967296).toUInt64 8).data.toList) ++ rest) r := by
  rcases «IxonSerialize::put_tagn_wide».obs ev with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hv68, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hv68, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hv419, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hv419, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨w13, w14, x_d2, x_d3, x_d4, x_d5, x_d6, x_d7,
      m758, x766, y767, m768, x774, y775, m776, x782, y783, m784,
      cs793, cs807, cs821, cs835, v858, v859, m861, cs869, v872, m889, cs897,
      hv11, _, _, _, ev795, ev809, op789, ev823, op781, ev837, op773,
      he854, hm853, op886, ev871, ev899, _⟩ |
    ⟨w13, w14, x_d2, x_d3, x_d4, x_d5, x_d6, x_d7,
      v757, m758, x766, y767, m768, x774, y775, m776, x782, y783, m784,
      cs793, cs807, cs821, cs835, m929, cs939, x_next, w1018, cs1032,
      hv11, _, _, _, ev795, ev809, op789, ev823, op781, ev837, op773,
      hne924, ev941, ev1034, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, hne1067, _, _, _, _, _, _, _⟩
  · exact absurd (Value.field.inj hv68) (by decide)
  · exact absurd (Value.field.inj hv68) (by decide)
  · exact absurd (Value.field.inj hv419) (by decide)
  · exact absurd (Value.field.inj hv419) (by decide)
  · -- `d < 2^32`
    have hv11' := hv11
    unfold u64Value at hv11'
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨_, _, _, _, hd4, hd5, hd6, hd7⟩
    subst x_d4 x_d5 x_d6 x_d7
    obtain ⟨hx782, hm784⟩ := Lib.u8_to_field_spec ev795; subst x782 m784
    obtain ⟨hy783, hm776⟩ := Lib.u8_to_field_spec ev809; subst y783 m776
    obtain ⟨hy775, hm768⟩ := Lib.u8_to_field_spec ev823; subst y775 m768
    obtain ⟨hy767, hm758⟩ := Lib.u8_to_field_spec ev837; subst y767 m758
    simp only [evalBinOp, Except.ok.injEq] at op789 op781 op773
    subst x774 x766
    have hsum_cast : ((((d / 4294967296 % 256 + d / 1099511627776 % 256 +
        d / 281474976710656 % 256 + d / 72057594037927936 % 256 : Nat)) : F)) = 0 := by
      push_cast; exact Value.field.inj op773
    have hsum0 := (natCast_eq_zero_iff (by omega)).mp hsum_cast
    have hd_lt : d < 4294967296 := by omega
    simp only [evalBinOp, Except.ok.injEq] at op886
    have hv872 : v872 = .field (194 : F) := by rw [← op886]; norm_num
    rw [hv872] at ev871
    obtain ⟨hv858, hm861, _⟩ := Lib.u8_from_field_spec ev871
    subst v858 m861
    have hd_u64 : d.toUInt64.toNat = d := UInt64.toNat_ofNat_of_lt hd
    rw [← hd_u64] at ev899
    obtain ⟨ext1, htail⟩ := put_u64_le_spec 4 (by decide) hrest ev899
    have hhdr : RepU8 m889 (Ixon.tagNHeader 0 0 (128 + 64 + 2)) (.field (194 : F)) := by decide
    obtain ⟨ext2, hcons⟩ := snoc_byte hm853 hhdr htail
    rw [if_pos hd_lt, he854, List.cons_append]
    exact ⟨ext1.trans ext2, hcons⟩
  · -- `2^32 ≤ d`
    have hv11' := hv11
    unfold u64Value at hv11'
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨_, _, _, _, hd4, hd5, hd6, hd7⟩
    subst x_d4 x_d5 x_d6 x_d7
    obtain ⟨hx782, hm784⟩ := Lib.u8_to_field_spec ev795; subst x782 m784
    obtain ⟨hy783, hm776⟩ := Lib.u8_to_field_spec ev809; subst y783 m776
    obtain ⟨hy775, hm768⟩ := Lib.u8_to_field_spec ev823; subst y775 m768
    obtain ⟨hy767, hm758⟩ := Lib.u8_to_field_spec ev837; subst y767 m758
    simp only [evalBinOp, Except.ok.injEq] at op789 op781 op773
    subst x774 x766 v757
    have hd_nlt : ¬ d < 4294967296 := by
      intro hlt
      apply hne924
      have h0 : d / 4294967296 % 256 = 0 ∧ d / 1099511627776 % 256 = 0 ∧
          d / 281474976710656 % 256 = 0 ∧ d / 72057594037927936 % 256 = 0 := by omega
      rcases h0 with ⟨e4, e5, e6, e7⟩
      simp [e4, e5, e6, e7]
    rw [u64Value_neg_pow32] at ev941
    obtain ⟨hadd, hm929⟩ := Lib.u64_add_spec (Lib.repU64_ofNatLT h hd)
      (Lib.repU64_ofNatLT h (m := 18446744069414584320) (by decide)) ev941
    subst m929
    simp only [UInt64.toNat_ofNatLT, Value.tuple.injEq, List.cons.injEq, and_true] at hadd
    have hmod : (d + 18446744069414584320) % 18446744073709551616 = d - 4294967296 := by omega
    have hnext : x_next = u64Value (d - 4294967296) := by rw [← hadd.1, hmod]
    rw [hnext, if_neg hd_nlt] at ev1034 ⊢
    exact put_tagn_wide_3_spec (by omega) hrest ev1034
  · exact (hne1067 rfl).elim

/-- `put_tagn_wide` at rung code `1` (`3`, `4`, or `8` trailing bytes). -/
private theorem put_tagn_wide_1_spec {d : Nat} {rest : List UInt8}
    {x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hd : d < 18446744073709551616)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 1, u64Value d, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h'
        ((if d < 16777216 then
            Ixon.tagNHeader 0 0 (128 + 64 + 1) :: (trimmedBytes d.toUInt64 3).data.toList
          else if d - 16777216 < 4294967296 then
            Ixon.tagNHeader 0 0 (128 + 64 + 2) ::
              (trimmedBytes (d - 16777216).toUInt64 4).data.toList
          else
            Ixon.tagNHeader 0 0 (128 + 64 + 3) ::
              (trimmedBytes (d - 16777216 - 4294967296).toUInt64 8).data.toList) ++ rest) r := by
  rcases «IxonSerialize::put_tagn_wide».obs ev with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hv68, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hv68, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨w13, w14, x_d2, x_d3, x_d4, x_d5, x_d6, x_d7,
      m421, x429, y430, m431, x437, y438, m439, x445, y446, m447, x453, y454, m455,
      cs464, cs478, cs492, cs506, cs520, v543, v544, m546, cs554, v557, m574, cs582,
      hv11, _, _, ev466, ev480, op460, ev494, op452, ev508, op444, ev522, op436,
      he539, hm538, op571, ev556, ev584, _⟩ |
    ⟨w13, w14, x_d2, x_d3, x_d4, x_d5, x_d6, x_d7,
      v420, m421, x429, y430, m431, x437, y438, m439, x445, y446, m447, x453, y454, m455,
      cs464, cs478, cs492, cs506, cs520, m614, cs624, x_next, w703, cs717,
      hv11, _, _, ev466, ev480, op460, ev494, op452, ev508, op444, ev522, op436,
      hne609, ev626, ev719, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hne752, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hne752, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hne752, _, _, _, _, _, _, _, _⟩
  · exact absurd (Value.field.inj hv68) (by decide)
  · exact absurd (Value.field.inj hv68) (by decide)
  · -- `d < 2^24`
    have hv11' := hv11
    unfold u64Value at hv11'
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨_, _, _, hd3, hd4, hd5, hd6, hd7⟩
    subst x_d3 x_d4 x_d5 x_d6 x_d7
    obtain ⟨hx453, hm455⟩ := Lib.u8_to_field_spec ev466; subst x453 m455
    obtain ⟨hy454, hm447⟩ := Lib.u8_to_field_spec ev480; subst y454 m447
    obtain ⟨hy446, hm439⟩ := Lib.u8_to_field_spec ev494; subst y446 m439
    obtain ⟨hy438, hm431⟩ := Lib.u8_to_field_spec ev508; subst y438 m431
    obtain ⟨hy430, hm421⟩ := Lib.u8_to_field_spec ev522; subst y430 m421
    simp only [evalBinOp, Except.ok.injEq] at op460 op452 op444 op436
    subst x445 x437 x429
    have hsum_cast : ((((d / 16777216 % 256 + d / 4294967296 % 256 + d / 1099511627776 % 256 +
        d / 281474976710656 % 256 + d / 72057594037927936 % 256 : Nat)) : F)) = 0 := by
      push_cast; exact Value.field.inj op436
    have hsum0 := (natCast_eq_zero_iff (by omega)).mp hsum_cast
    have hd_lt : d < 16777216 := by omega
    simp only [evalBinOp, Except.ok.injEq] at op571
    have hv557 : v557 = .field (193 : F) := by rw [← op571]; norm_num
    rw [hv557] at ev556
    obtain ⟨hv543, hm546, _⟩ := Lib.u8_from_field_spec ev556
    subst v543 m546
    have hd_u64 : d.toUInt64.toNat = d := UInt64.toNat_ofNat_of_lt hd
    rw [← hd_u64] at ev584
    obtain ⟨ext1, htail⟩ := put_u64_le_spec 3 (by decide) hrest ev584
    have hhdr : RepU8 m574 (Ixon.tagNHeader 0 0 (128 + 64 + 1)) (.field (193 : F)) := by decide
    obtain ⟨ext2, hcons⟩ := snoc_byte hm538 hhdr htail
    rw [if_pos hd_lt, he539, List.cons_append]
    exact ⟨ext1.trans ext2, hcons⟩
  · -- `2^24 ≤ d`
    have hv11' := hv11
    unfold u64Value at hv11'
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨_, _, _, hd3, hd4, hd5, hd6, hd7⟩
    subst x_d3 x_d4 x_d5 x_d6 x_d7
    obtain ⟨hx453, hm455⟩ := Lib.u8_to_field_spec ev466; subst x453 m455
    obtain ⟨hy454, hm447⟩ := Lib.u8_to_field_spec ev480; subst y454 m447
    obtain ⟨hy446, hm439⟩ := Lib.u8_to_field_spec ev494; subst y446 m439
    obtain ⟨hy438, hm431⟩ := Lib.u8_to_field_spec ev508; subst y438 m431
    obtain ⟨hy430, hm421⟩ := Lib.u8_to_field_spec ev522; subst y430 m421
    simp only [evalBinOp, Except.ok.injEq] at op460 op452 op444 op436
    subst x445 x437 x429 v420
    have hd_nlt : ¬ d < 16777216 := by
      intro hlt
      apply hne609
      have h0 : d / 16777216 % 256 = 0 ∧ d / 4294967296 % 256 = 0 ∧
          d / 1099511627776 % 256 = 0 ∧ d / 281474976710656 % 256 = 0 ∧
          d / 72057594037927936 % 256 = 0 := by omega
      rcases h0 with ⟨e3, e4, e5, e6, e7⟩
      simp [e3, e4, e5, e6, e7]
    rw [u64Value_neg_pow24] at ev626
    obtain ⟨hadd, hm614⟩ := Lib.u64_add_spec (Lib.repU64_ofNatLT h hd)
      (Lib.repU64_ofNatLT h (m := 18446744073692774400) (by decide)) ev626
    subst m614
    simp only [UInt64.toNat_ofNatLT, Value.tuple.injEq, List.cons.injEq, and_true] at hadd
    have hmod : (d + 18446744073692774400) % 18446744073709551616 = d - 16777216 := by omega
    have hnext : x_next = u64Value (d - 16777216) := by rw [← hadd.1, hmod]
    rw [hnext, if_neg hd_nlt] at ev719 ⊢
    exact put_tagn_wide_2_spec (by omega) hrest ev719
  · exact (hne752 rfl).elim
  · exact (hne752 rfl).elim
  · exact (hne752 rfl).elim

/-- `put_tagn_wide` at rung code `0` (`2`, `3`, `4`, or `8` trailing bytes). -/
private theorem put_tagn_wide_0_spec {d : Nat} {rest : List UInt8}
    {x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hd : d < 18446744073709551616)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 0, u64Value d, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h'
        ((if d < 65536 then
            Ixon.tagNHeader 0 0 (128 + 64) :: (trimmedBytes d.toUInt64 2).data.toList
          else if d - 65536 < 16777216 then
            Ixon.tagNHeader 0 0 (128 + 64 + 1) ::
              (trimmedBytes (d - 65536).toUInt64 3).data.toList
          else if d - 65536 - 16777216 < 4294967296 then
            Ixon.tagNHeader 0 0 (128 + 64 + 2) ::
              (trimmedBytes (d - 65536 - 16777216).toUInt64 4).data.toList
          else
            Ixon.tagNHeader 0 0 (128 + 64 + 3) ::
              (trimmedBytes (d - 65536 - 16777216 - 4294967296).toUInt64 8).data.toList) ++
          rest) r := by
  rcases «IxonSerialize::put_tagn_wide».obs ev with
    ⟨w13, w14, x_d2, x_d3, x_d4, x_d5, x_d6, x_d7,
      m70, x78, y79, m80, x86, y87, m88, x94, y95, m96, x102, y103, m104, x110, y111, m112,
      cs121, cs135, cs149, cs163, cs177, cs191, v214, v215, m217, cs225, m237, cs245,
      hv11, _, ev123, ev137, op117, ev151, op109, ev165, op101, ev179, op93, ev193, op85,
      he210, hm209, ev227, ev247, _⟩ |
    ⟨w13, w14, x_d2, x_d3, x_d4, x_d5, x_d6, x_d7,
      v69, m70, x78, y79, m80, x86, y87, m88, x94, y95, m96, x102, y103, m104, x110, y111, m112,
      cs121, cs135, cs149, cs163, cs177, cs191, m277, cs287, x_next, w366, cs380,
      hv11, _, ev123, ev137, op117, ev151, op109, ev165, op101, ev179, op93, ev193, op85,
      hne272, ev289, ev382, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hne415, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hne415, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hne415, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hne415, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hne415, _, _, _, _, _, _, _, _, _⟩
  · -- `d < 65536`
    have hv11' := hv11
    unfold u64Value at hv11'
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨_, _, hd2, hd3, hd4, hd5, hd6, hd7⟩
    subst x_d2 x_d3 x_d4 x_d5 x_d6 x_d7
    obtain ⟨hx110, hm112⟩ := Lib.u8_to_field_spec ev123; subst x110 m112
    obtain ⟨hy111, hm104⟩ := Lib.u8_to_field_spec ev137; subst y111 m104
    obtain ⟨hy103, hm96⟩ := Lib.u8_to_field_spec ev151; subst y103 m96
    obtain ⟨hy95, hm88⟩ := Lib.u8_to_field_spec ev165; subst y95 m88
    obtain ⟨hy87, hm80⟩ := Lib.u8_to_field_spec ev179; subst y87 m80
    obtain ⟨hy79, hm70⟩ := Lib.u8_to_field_spec ev193; subst y79 m70
    simp only [evalBinOp, Except.ok.injEq] at op117 op109 op101 op93 op85
    subst x102 x94 x86 x78
    have hsum_cast : ((((d / 65536 % 256 + d / 16777216 % 256 + d / 4294967296 % 256 +
        d / 1099511627776 % 256 + d / 281474976710656 % 256 +
        d / 72057594037927936 % 256 : Nat)) : F)) = 0 := by
      push_cast; exact Value.field.inj op85
    have hsum0 := (natCast_eq_zero_iff (by omega)).mp hsum_cast
    have hd_lt : d < 65536 := by omega
    obtain ⟨hv214, hm217, _⟩ := Lib.u8_from_field_spec ev227
    subst v214 m217
    have hd_u64 : d.toUInt64.toNat = d := UInt64.toNat_ofNat_of_lt hd
    rw [← hd_u64] at ev247
    obtain ⟨ext1, htail⟩ := put_u64_le_spec 2 (by decide) hrest ev247
    have hhdr : RepU8 m237 (Ixon.tagNHeader 0 0 (128 + 64)) (.field (192 : F)) := by decide
    obtain ⟨ext2, hcons⟩ := snoc_byte hm209 hhdr htail
    rw [if_pos hd_lt, he210, List.cons_append]
    exact ⟨ext1.trans ext2, hcons⟩
  · -- `65536 ≤ d`
    have hv11' := hv11
    unfold u64Value at hv11'
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨_, _, hd2, hd3, hd4, hd5, hd6, hd7⟩
    subst x_d2 x_d3 x_d4 x_d5 x_d6 x_d7
    obtain ⟨hx110, hm112⟩ := Lib.u8_to_field_spec ev123; subst x110 m112
    obtain ⟨hy111, hm104⟩ := Lib.u8_to_field_spec ev137; subst y111 m104
    obtain ⟨hy103, hm96⟩ := Lib.u8_to_field_spec ev151; subst y103 m96
    obtain ⟨hy95, hm88⟩ := Lib.u8_to_field_spec ev165; subst y95 m88
    obtain ⟨hy87, hm80⟩ := Lib.u8_to_field_spec ev179; subst y87 m80
    obtain ⟨hy79, hm70⟩ := Lib.u8_to_field_spec ev193; subst y79 m70
    simp only [evalBinOp, Except.ok.injEq] at op117 op109 op101 op93 op85
    subst x102 x94 x86 x78 v69
    have hd_nlt : ¬ d < 65536 := by
      intro hlt
      apply hne272
      have h0 : d / 65536 % 256 = 0 ∧ d / 16777216 % 256 = 0 ∧ d / 4294967296 % 256 = 0 ∧
          d / 1099511627776 % 256 = 0 ∧ d / 281474976710656 % 256 = 0 ∧
          d / 72057594037927936 % 256 = 0 := by omega
      rcases h0 with ⟨e2, e3, e4, e5, e6, e7⟩
      simp [e2, e3, e4, e5, e6, e7]
    rw [u64Value_neg_pow16] at ev289
    obtain ⟨hadd, hm277⟩ := Lib.u64_add_spec (Lib.repU64_ofNatLT h hd)
      (Lib.repU64_ofNatLT h (m := 18446744073709486080) (by decide)) ev289
    subst m277
    simp only [UInt64.toNat_ofNatLT, Value.tuple.injEq, List.cons.injEq, and_true] at hadd
    have hmod : (d + 18446744073709486080) % 18446744073709551616 = d - 65536 := by omega
    have hnext : x_next = u64Value (d - 65536) := by rw [← hadd.1, hmod]
    rw [hnext, if_neg hd_nlt] at ev382 ⊢
    exact put_tagn_wide_1_spec (by omega) hrest ev382
  · exact (hne415 rfl).elim
  · exact (hne415 rfl).elim
  · exact (hne415 rfl).elim
  · exact (hne415 rfl).elim
  · exact (hne415 rfl).elim

private theorem tag0Bytes_ge128_toList {val : UInt64} (hge : ¬ val.toNat < 128) :
    (tag0Bytes val).data.toList =
      if val.toNat < 16512 then
        [Ixon.tagNHeader 0 0 (128 + (val.toNat - 128) / 256),
          ((val.toNat - 128) % 256).toUInt8]
      else if val.toNat - 16512 < 65536 then
        Ixon.tagNHeader 0 0 (128 + 64) ::
          (trimmedBytes (val.toNat - 16512).toUInt64 2).data.toList
      else if val.toNat - 16512 - 65536 < 16777216 then
        Ixon.tagNHeader 0 0 (128 + 64 + 1) ::
          (trimmedBytes (val.toNat - 16512 - 65536).toUInt64 3).data.toList
      else if val.toNat - 16512 - 65536 - 16777216 < 4294967296 then
        Ixon.tagNHeader 0 0 (128 + 64 + 2) ::
          (trimmedBytes (val.toNat - 16512 - 65536 - 16777216).toUInt64 4).data.toList
      else
        Ixon.tagNHeader 0 0 (128 + 64 + 3) ::
          (trimmedBytes (val.toNat - 16512 - 65536 - 16777216 - 4294967296).toUInt64 8).data.toList := by
  have h1 : Ixon.tagNEnd1 0 = 128 := by decide
  have h2 : Ixon.tagNEnd2 0 = 16512 := by decide
  have h3 : Ixon.tagNEnd3 0 = 82048 := by decide
  have h4 : Ixon.tagNEnd4 0 = 16859264 := by decide
  have h5 : Ixon.tagNEnd5 0 = 4311826560 := by decide
  unfold tag0Bytes tagNBytes
  simp only [Nat.reduceSub, Nat.reducePow, h1, h2, h3, h4, h5, hge, ↓reduceIte]
  by_cases c2 : val.toNat < 16512
  · simp [c2, ByteArray.data_append, Array.toList_append, List.toByteArray]
  · simp only [c2, ↓reduceIte]
    by_cases c3 : val.toNat < 82048
    · have c3' : val.toNat - 16512 < 65536 := by omega
      simp [c3, c3', ByteArray.data_append, Array.toList_append, List.toByteArray]
    · have c3' : ¬ val.toNat - 16512 < 65536 := by omega
      simp only [c3, c3', ↓reduceIte]
      by_cases c4 : val.toNat < 16859264
      · have c4' : val.toNat - 16512 - 65536 < 16777216 := by omega
        have esub : val.toNat - 82048 = val.toNat - 16512 - 65536 := by omega
        simp [c4, c4', esub, ByteArray.data_append, Array.toList_append, List.toByteArray]
      · have c4' : ¬ val.toNat - 16512 - 65536 < 16777216 := by omega
        simp only [c4, c4', ↓reduceIte]
        by_cases c5 : val.toNat < 4311826560
        · have c5' : val.toNat - 16512 - 65536 - 16777216 < 4294967296 := by omega
          have esub : val.toNat - 16859264 = val.toNat - 16512 - 65536 - 16777216 := by omega
          simp [c5, c5', esub, ByteArray.data_append, Array.toList_append, List.toByteArray]
        · have c5' : ¬ val.toNat - 16512 - 65536 - 16777216 < 4294967296 := by omega
          have esub : val.toNat - 4311826560 =
              val.toNat - 16512 - 65536 - 16777216 - 4294967296 := by omega
          simp [c5, c5', esub, ByteArray.data_append, Array.toList_append, List.toByteArray]

/-- `IxonSerialize::put_tagn_tail` on `f = 0` (`x_base = 0`, `x_h = 64`) for `128 ≤ val.toNat`. -/
private theorem put_tagn_tail_0_spec {val : UInt64} {rest : List UInt8}
    {x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hge : ¬ val.toNat < 128)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_tagn_tail"
      [.field 0, .field 64, u64Value val.toNat, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h' ((tag0Bytes val).data.toList ++ rest) r := by
  have hv_lt := val.toNat_lt
  rw [tag0Bytes_ge128_toList hge]
  rcases «IxonSerialize::put_tagn_tail».obs ev with
    ⟨m2, cs12, v32, v33, m41, cs49, v52, y60, m77, cs85, v88, x_d, x_at_least_r2,
      m154, cs165, m181, cs191, v194, v195, m197, cs205, v208, y226, x_lo, x_no_borrow,
      v255, x263, m265, x271, y272, m273, cs282, v285, cs299, v318, m321, cs329,
      v332, x339, y348, m367,
      op74, op66, ev51, op102, ev87, ev14, ev167,
      pr217, ev207, op240, op232, ev193, pr294, ev284, ev301, op278, op270,
      he314, hm313, op363, op354, op346, ev331, hm375, _⟩ |
    ⟨m2, cs12, v32, v33, m41, cs49, v52, y60, m77, cs85, v88, x_d, x_at_least_r2,
      m154, cs165, cs404, v407, y418,
      op74, op66, ev51, op102, ev87, ev14, ev167, op433, op424, ev406, _⟩
  · -- Rung 2 (`128 ≤ val.toNat < 16512`)
    simp only [evalBinOp, Except.ok.injEq] at op74 op66 op102
    have hv52 : v52 = .field (128 : F) := by rw [← op66, ← op74]; norm_num
    have hv88 : v88 = .field (191 : F) := by rw [← op102]; norm_num
    rw [hv52] at ev51
    obtain ⟨hv32, hm41, _⟩ := Lib.u8_from_field_spec ev51; subst v32 m41
    rw [hv88] at ev87
    obtain ⟨hv33, hm77, _⟩ := Lib.u8_from_field_spec ev87; subst v33 m77
    rw [u64Value_neg_end2_0] at ev14
    obtain ⟨hadd, hm2⟩ := Lib.u64_add_spec (Deserialize.repU64_u64Value h val)
      (Lib.repU64_ofNatLT h (m := 18446744073709535104) (by decide)) ev14
    subst m2
    simp only [UInt64.toNat_ofNatLT, Value.tuple.injEq, List.cons.injEq, and_true] at hadd
    obtain ⟨hcarry0, hm154⟩ := Lib.u8_to_field_spec ev167
    subst m154
    have hdiv0 : (val.toNat + 18446744073709535104) / 18446744073709551616 = 0 := by
      have hc : ((((val.toNat + 18446744073709535104) / 18446744073709551616 : Nat)) : F) = 0 :=
        Value.field.inj (hcarry0.symm.trans hadd.2).symm
      exact (natCast_eq_zero_iff (by omega)).mp hc
    have hlt2 : val.toNat < 16512 := by omega
    have hpr0 : projectValue (u64Value val.toNat : SourceValue F) 0 =
        .ok (.field ((val.toNat % 256 : Nat) : F)) := by
      simp [u64Value, projectValue]
    have hv208 : v208 = .field ((val.toNat % 256 : Nat) : F) :=
      ok_inj (pr217.symm.trans hpr0)
    subst v208
    obtain ⟨hv194, hm197⟩ := Lib.u8_to_field_spec ev207; subst v194 m197
    simp only [evalBinOp, Except.ok.injEq] at op240 op232
    have hv195 : v195 = .field ((128 : Nat) : F) := by rw [← op232, ← op240]; norm_num
    rw [hv195] at ev193
    obtain ⟨hraw, hm181⟩ := u8_raw_add_spec (a := val.toNat % 256) (b := 128)
      (by omega) (by decide) ev193
    subst m181
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hraw
    rcases hraw with ⟨hxlo, hxnb⟩
    subst x_lo x_no_borrow
    have hpr1 : projectValue (u64Value val.toNat : SourceValue F) 1 =
        .ok (.field ((val.toNat / 256 % 256 : Nat) : F)) := by
      simp [u64Value, projectValue]
    have hv285 : v285 = .field ((val.toNat / 256 % 256 : Nat) : F) :=
      ok_inj (pr294.symm.trans hpr1)
    subst v285
    obtain ⟨hx271, hm273⟩ := Lib.u8_to_field_spec ev284; subst x271 m273
    obtain ⟨hy272, hm265⟩ := Lib.u8_to_field_spec ev301; subst y272 m265
    simp only [evalBinOp, Except.ok.injEq] at op278 op270 op363 op354 op346
    subst x263 v255 y348 x339
    have hhi_nat :
        1 ≤ val.toNat / 256 % 256 + (val.toNat % 256 + 128) / 256 ∧
        val.toNat / 256 % 256 + (val.toNat % 256 + 128) / 256 - 1 =
          (val.toNat - 128) / 256 := by omega
    have hlo_nat : (val.toNat % 256 + 128) % 256 = (val.toNat - 128) % 256 := by omega
    have hv332 : v332 = .field (((128 + (val.toNat - 128) / 256 : Nat)) : F) := by
      rw [← op346]
      congr 1
      have hsub_eq : val.toNat / 256 % 256 + (val.toNat % 256 + 128) / 256 =
          (val.toNat - 128) / 256 + 1 := by omega
      have hcast := congrArg (Nat.cast (R := F)) hsub_eq
      push_cast at hcast ⊢
      linear_combination hcast
    rw [hv332] at ev331
    obtain ⟨hv318, hm321, _⟩ := Lib.u8_from_field_spec ev331
    subst v318 m321
    have hlo_u8 : RepU8 h ((val.toNat - 128) % 256).toUInt8
        (.field ((((val.toNat % 256 + 128) % 256 : Nat)) : F)) := by
      rw [hlo_nat]
      exact repU8_ofNatLT h (by omega)
    obtain ⟨ext1, hcons1⟩ := snoc_byte hm375 hlo_u8 hrest
    have hhdr_lt : 128 + (val.toNat - 128) / 256 < 256 := by omega
    have hhdr_u8 : RepU8 m367 (Ixon.tagNHeader 0 0 (128 + (val.toNat - 128) / 256))
        (.field (((128 + (val.toNat - 128) / 256 : Nat)) : F)) := by
      unfold Ixon.tagNHeader
      simp only [UInt8.reduceToNat, Nat.zero_mul, Nat.zero_add]
      exact repU8_ofNatLT m367 hhdr_lt
    obtain ⟨ext2, hcons2⟩ := snoc_byte hm313 hhdr_u8 hcons1
    rw [if_pos hlt2, he314]
    simpa [List.cons_append] using And.intro (ext1.trans ext2) hcons2
  · -- Wide rungs (`16512 ≤ val.toNat`)
    simp only [evalBinOp, Except.ok.injEq] at op74 op66 op102
    have hv52 : v52 = .field (128 : F) := by rw [← op66, ← op74]; norm_num
    have hv88 : v88 = .field (191 : F) := by rw [← op102]; norm_num
    rw [hv52] at ev51
    obtain ⟨hv32, hm41, _⟩ := Lib.u8_from_field_spec ev51; subst v32 m41
    rw [hv88] at ev87
    obtain ⟨hv33, hm77, _⟩ := Lib.u8_from_field_spec ev87; subst v33 m77
    rw [u64Value_neg_end2_0] at ev14
    obtain ⟨hadd, hm2⟩ := Lib.u64_add_spec (Deserialize.repU64_u64Value h val)
      (Lib.repU64_ofNatLT h (m := 18446744073709535104) (by decide)) ev14
    subst m2
    simp only [UInt64.toNat_ofNatLT, Value.tuple.injEq, List.cons.injEq, and_true] at hadd
    obtain ⟨hcarry1, hm154⟩ := Lib.u8_to_field_spec ev167
    subst m154
    have hdiv1 : (val.toNat + 18446744073709535104) / 18446744073709551616 = 1 := by
      have hc : ((((val.toNat + 18446744073709535104) / 18446744073709551616 : Nat)) : F) =
          ((1 : Nat) : F) := by
        simpa using Value.field.inj (hcarry1.symm.trans hadd.2).symm
      exact (natCast_eq_iff (by omega) (by decide)).mp hc
    have hnlt2 : ¬ val.toNat < 16512 := by omega
    have hmod : (val.toNat + 18446744073709535104) % 18446744073709551616 =
        val.toNat - 16512 := by omega
    have hxd : x_d = u64Value (val.toNat - 16512) := by rw [← hadd.1, hmod]
    simp only [evalBinOp, Except.ok.injEq] at op433 op424
    have hv407 : v407 = .field (192 : F) := by rw [← op424, ← op433]; norm_num
    rw [hv407, hxd, if_neg hnlt2] at ev406 ⊢
    exact put_tagn_wide_0_spec (by omega) hrest ev406

/-- `IxonSerialize::put_tagn0` prepends `tag0Bytes val` before `rest`. -/
theorem put_tagn0_spec {val : UInt64} {rest : List UInt8}
    {x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_tagn0" [u64Value val.toNat, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h' ((tag0Bytes val).data.toList ++ rest) r := by
  have hv_lt := val.toNat_lt
  rcases «IxonSerialize::put_tagn0».obs ev with
    ⟨x_v0, x_v1, x_v2, x_v3, x_v4, x_v5, x_v6, x_v7,
      m54, x62, y63, m64, x70, y71, m72, x78, y79, m80, x86, y87, m88, x94, y95, m96,
      x102, y103, m104, cs113, cs127, cs141, cs155, cs169, cs183, cs197, m213, cs224,
      hv11, ev115, ev129, op109, ev143, op101, ev157, op93, ev171, op85, ev185, op77, ev199,
      op69, ev226, he250, hm249, _⟩ |
    ⟨x_v0, x_v1, x_v2, x_v3, x_v4, x_v5, x_v6, x_v7,
      m54, x62, y63, m64, x70, y71, m72, x78, y79, m80, x86, y87, m88, x94, y95, m96,
      x102, y103, m104, cs113, cs127, cs141, cs155, cs169, cs183, cs197, m213, cs224, cs279,
      hv11, ev115, ev129, op109, ev143, op101, ev157, op93, ev171, op85, ev185, op77, ev199,
      op69, ev226, ev281, _⟩ |
    ⟨x_v0, x_v1, x_v2, x_v3, x_v4, x_v5, x_v6, x_v7,
      v53, m54, x62, y63, m64, x70, y71, m72, x78, y79, m80, x86, y87, m88, x94, y95, m96,
      x102, y103, m104, cs113, cs127, cs141, cs155, cs169, cs183, cs197, cs321,
      hv11, ev115, ev129, op109, ev143, op101, ev157, op93, ev171, op85, ev185, op77, ev199,
      op69, hne314, ev323, _⟩
  · -- `val.toNat < 128`
    have hv11' := hv11
    unfold u64Value at hv11'
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7⟩
    subst x_v0 x_v1 x_v2 x_v3 x_v4 x_v5 x_v6 x_v7
    obtain ⟨hx102, hm104⟩ := Lib.u8_to_field_spec ev115; subst x102 m104
    obtain ⟨hy103, hm96⟩ := Lib.u8_to_field_spec ev129; subst y103 m96
    obtain ⟨hy95, hm88⟩ := Lib.u8_to_field_spec ev143; subst y95 m88
    obtain ⟨hy87, hm80⟩ := Lib.u8_to_field_spec ev157; subst y87 m80
    obtain ⟨hy79, hm72⟩ := Lib.u8_to_field_spec ev171; subst y79 m72
    obtain ⟨hy71, hm64⟩ := Lib.u8_to_field_spec ev185; subst y71 m64
    obtain ⟨hy63, hm54⟩ := Lib.u8_to_field_spec ev199; subst y63 m54
    simp only [evalBinOp, Except.ok.injEq] at op109 op101 op93 op85 op77 op69
    subst x94 x86 x78 x70 x62
    have hsum_cast : ((((val.toNat / 256 % 256 + val.toNat / 65536 % 256 +
        val.toNat / 16777216 % 256 + val.toNat / 4294967296 % 256 +
        val.toNat / 1099511627776 % 256 + val.toNat / 281474976710656 % 256 +
        val.toNat / 72057594037927936 % 256 : Nat)) : F)) = 0 := by
      push_cast; exact Value.field.inj op69
    have hsum0 := (natCast_eq_zero_iff (by omega)).mp hsum_cast
    have hv_lt256 : val.toNat < 256 := by omega
    obtain ⟨hlt_eq, hm213⟩ := Lib.u8_less_than_spec
      (repU8_ofNatLT h (n := val.toNat % 256) (by omega))
      (repU8_ofNatLT h (n := 128) (by decide)) ev226
    subst m213
    have hv0_lt128 : val.toNat < 128 := by
      have hb0 : (val.toNat % 256).toUInt8.toNat = val.toNat := by
        simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hv_lt256]
      have hb128 : (128 : Nat).toUInt8.toNat = 128 := by decide
      rw [hb0, hb128] at hlt_eq
      by_contra hge
      rw [if_neg hge] at hlt_eq
      exact absurd (Value.field.inj hlt_eq) (by decide)
    have htag0 : (tag0Bytes val).data.toList = [Ixon.tagNHeader 0 0 val.toNat] := by
      have h1 : Ixon.tagNEnd1 0 = 128 := by decide
      unfold tag0Bytes tagNBytes
      simp [h1, hv0_lt128, List.toByteArray]
    have hhdr_u8 : RepU8 h (Ixon.tagNHeader 0 0 val.toNat)
        (.field ((val.toNat % 256 : Nat) : F)) := by
      unfold Ixon.tagNHeader
      simp only [UInt8.reduceToNat, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hv_lt256]
      exact repU8_ofNatLT h hv_lt256
    obtain ⟨ext1, hcons⟩ := snoc_byte hm249 hhdr_u8 hrest
    rw [htag0, he250, List.singleton_append]
    exact ⟨ext1, hcons⟩
  · -- `128 ≤ val.toNat < 256`
    have hv11' := hv11
    unfold u64Value at hv11'
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7⟩
    subst x_v0 x_v1 x_v2 x_v3 x_v4 x_v5 x_v6 x_v7
    obtain ⟨_, hm104⟩ := Lib.u8_to_field_spec ev115; subst m104
    obtain ⟨_, hm96⟩ := Lib.u8_to_field_spec ev129; subst m96
    obtain ⟨_, hm88⟩ := Lib.u8_to_field_spec ev143; subst m88
    obtain ⟨_, hm80⟩ := Lib.u8_to_field_spec ev157; subst m80
    obtain ⟨_, hm72⟩ := Lib.u8_to_field_spec ev171; subst m72
    obtain ⟨_, hm64⟩ := Lib.u8_to_field_spec ev185; subst m64
    obtain ⟨_, hm54⟩ := Lib.u8_to_field_spec ev199; subst m54
    obtain ⟨hlt_eq, hm213⟩ := Lib.u8_less_than_spec
      (repU8_ofNatLT h (n := val.toNat % 256) (by omega))
      (repU8_ofNatLT h (n := 128) (by decide)) ev226
    subst m213
    have hge128 : ¬ val.toNat < 128 := by
      intro hlt128
      have hb0 : (val.toNat % 256).toUInt8.toNat = val.toNat := by
        simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega : val.toNat < 256)]
      have hb128 : (128 : Nat).toUInt8.toNat = 128 := by decide
      rw [hb0, hb128, if_pos hlt128] at hlt_eq
      exact absurd (Value.field.inj hlt_eq) (by decide)
    exact put_tagn_tail_0_spec hge128 hrest ev281
  · -- `256 ≤ val.toNat`
    have hv11' := hv11
    unfold u64Value at hv11'
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7⟩
    subst x_v0 x_v1 x_v2 x_v3 x_v4 x_v5 x_v6 x_v7
    obtain ⟨hx102, hm104⟩ := Lib.u8_to_field_spec ev115; subst x102 m104
    obtain ⟨hy103, hm96⟩ := Lib.u8_to_field_spec ev129; subst y103 m96
    obtain ⟨hy95, hm88⟩ := Lib.u8_to_field_spec ev143; subst y95 m88
    obtain ⟨hy87, hm80⟩ := Lib.u8_to_field_spec ev157; subst y87 m80
    obtain ⟨hy79, hm72⟩ := Lib.u8_to_field_spec ev171; subst y79 m72
    obtain ⟨hy71, hm64⟩ := Lib.u8_to_field_spec ev185; subst y71 m64
    obtain ⟨hy63, hm54⟩ := Lib.u8_to_field_spec ev199; subst y63 m54
    simp only [evalBinOp, Except.ok.injEq] at op109 op101 op93 op85 op77 op69
    subst x94 x86 x78 x70 x62 v53
    have hge128 : ¬ val.toNat < 128 := by
      intro hlt128
      apply hne314
      have h0 : val.toNat / 256 % 256 = 0 ∧ val.toNat / 65536 % 256 = 0 ∧
          val.toNat / 16777216 % 256 = 0 ∧ val.toNat / 4294967296 % 256 = 0 ∧
          val.toNat / 1099511627776 % 256 = 0 ∧ val.toNat / 281474976710656 % 256 = 0 ∧
          val.toNat / 72057594037927936 % 256 = 0 := by omega
      rcases h0 with ⟨e1, e2, e3, e4, e5, e6, e7⟩
      simp [e1, e2, e3, e4, e5, e6, e7]
    exact put_tagn_tail_0_spec hge128 hrest ev323

/-- `IxonSerialize::put_tagn4` at `flag = 13` and `k < 8` prepends `tag4Bytes 13 k.toUInt64`. -/
theorem put_tagn4_13_small_spec {k : Nat} {rest : List UInt8}
    {x_v x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hk : k < 8)
    (hxv : x_v = u64Value k)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_tagn4" [.field 13, x_v, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h' ((tag4Bytes 13 k.toUInt64).data.toList ++ rest) r := by
  subst x_v
  rcases «IxonSerialize::put_tagn4».obs ev with
    ⟨x_v0, x_v1, x_v2, x_v3, x_v4, x_v5, x_v6, x_v7,
      m54, x62, y63, m64, x70, y71, m72, x78, y79, m80, x86, y87, m88, x94, y95, m96,
      x102, y103, m104, cs113, cs127, cs141, cs155, cs169, cs183, cs197, m213, cs224,
      v254, m257, cs265, v268, m270, x275, y276, cs295,
      hv11, ev115, ev129, _, ev143, _, ev157, _, ev171, _, ev185, _, ev199, _,
      ev226, he250, hm249, op290, ev297, op282, ev267, _⟩ |
    ⟨x_v0, x_v1, x_v2, x_v3, x_v4, x_v5, x_v6, x_v7,
      m54, _, _, m64, _, _, m72, _, _, m80, _, _, m88, _, _, m96, _, _, m104,
      _, _, _, _, _, _, _, m213, _, _, _,
      hv11, ev115, ev129, _, ev143, _, ev157, _, ev171, _, ev185, _, ev199, _, ev226, _, _, _⟩ |
    ⟨x_v0, x_v1, x_v2, x_v3, x_v4, x_v5, x_v6, x_v7,
      v53, m54, x62, y63, m64, x70, y71, m72, x78, y79, m80, x86, y87, m88, x94, y95, m96,
      x102, y103, m104, _, _, _, _, _, _, _, _, _,
      hv11, ev115, ev129, op109, ev143, op101, ev157, op93, ev171, op85, ev185, op77, ev199,
      op69, hne366, _, _, _⟩
  · unfold u64Value at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    rcases hv11 with ⟨hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7⟩
    subst x_v0 x_v1 x_v2 x_v3 x_v4 x_v5 x_v6 x_v7
    obtain ⟨_, hm104⟩ := Lib.u8_to_field_spec ev115; subst m104
    obtain ⟨_, hm96⟩ := Lib.u8_to_field_spec ev129; subst m96
    obtain ⟨_, hm88⟩ := Lib.u8_to_field_spec ev143; subst m88
    obtain ⟨_, hm80⟩ := Lib.u8_to_field_spec ev157; subst m80
    obtain ⟨_, hm72⟩ := Lib.u8_to_field_spec ev171; subst m72
    obtain ⟨_, hm64⟩ := Lib.u8_to_field_spec ev185; subst m64
    obtain ⟨_, hm54⟩ := Lib.u8_to_field_spec ev199; subst m54
    obtain ⟨_, hm213⟩ := Lib.u8_less_than_spec
      (repU8_ofNatLT h (n := k % 256) (by omega))
      (repU8_ofNatLT h (n := 8) (by decide)) ev226
    subst m213
    obtain ⟨hy276, hm270⟩ := Lib.u8_to_field_spec ev297; subst y276 m270
    simp only [evalBinOp, Except.ok.injEq] at op290 op282
    subst x275 v268
    obtain ⟨hv254, hm257, _⟩ := Lib.u8_from_field_spec ev267; subst v254 m257
    have hk_mod : k % 256 = k := Nat.mod_eq_of_lt (by omega)
    have hk_u64 : k.toUInt64.toNat = k := UInt64.toNat_ofNat_of_lt (by omega)
    have htag4 : (tag4Bytes 13 k.toUInt64).data.toList = [Ixon.tagNHeader 4 13 k] := by
      have h1 : Ixon.tagNEnd1 4 = 8 := by decide
      unfold tag4Bytes tagNBytes
      simp [h1, hk_u64, hk, List.toByteArray]
    have hhdr_val : (16 * (13 : F) + ((k % 256 : Nat) : F)) = (((208 + k : Nat)) : F) := by
      rw [hk_mod]; push_cast; ring_nf
    have hhdr_u8 : RepU8 h (Ixon.tagNHeader 4 13 k)
        (.field (16 * (13 : F) + ((k % 256 : Nat) : F))) := by
      rw [hhdr_val]
      unfold Ixon.tagNHeader
      have h208 : (13 : UInt8).toNat * 2 ^ (8 - 4) + k = 208 + k := by
        simp [UInt8.reduceToNat]; omega
      rw [h208]
      exact repU8_ofNatLT h (by omega)
    obtain ⟨ext1, hcons⟩ := snoc_byte hm249 hhdr_u8 hrest
    rw [htag4, he250, List.singleton_append]
    exact ⟨ext1, hcons⟩
  · unfold u64Value at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    rcases hv11 with ⟨hv0, _, _, _, _, _, _, _⟩
    subst x_v0
    obtain ⟨_, hm104⟩ := Lib.u8_to_field_spec ev115; subst m104
    obtain ⟨_, hm96⟩ := Lib.u8_to_field_spec ev129; subst m96
    obtain ⟨_, hm88⟩ := Lib.u8_to_field_spec ev143; subst m88
    obtain ⟨_, hm80⟩ := Lib.u8_to_field_spec ev157; subst m80
    obtain ⟨_, hm72⟩ := Lib.u8_to_field_spec ev171; subst m72
    obtain ⟨_, hm64⟩ := Lib.u8_to_field_spec ev185; subst m64
    obtain ⟨_, hm54⟩ := Lib.u8_to_field_spec ev199; subst m54
    obtain ⟨hlt_eq, _⟩ := Lib.u8_less_than_spec
      (repU8_ofNatLT h (n := k % 256) (by omega))
      (repU8_ofNatLT h (n := 8) (by decide)) ev226
    have hb0 : (k % 256).toUInt8.toNat = k := by
      simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega : k < 256)]
    have hb8 : (8 : Nat).toUInt8.toNat = 8 := by decide
    rw [hb0, hb8, if_pos hk] at hlt_eq
    exact absurd (Value.field.inj hlt_eq) (by decide)
  · unfold u64Value at hv11
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    rcases hv11 with ⟨_, hv1, hv2, hv3, hv4, hv5, hv6, hv7⟩
    subst x_v1 x_v2 x_v3 x_v4 x_v5 x_v6 x_v7
    obtain ⟨hx102, hm104⟩ := Lib.u8_to_field_spec ev115; subst x102 m104
    obtain ⟨hy103, hm96⟩ := Lib.u8_to_field_spec ev129; subst y103 m96
    obtain ⟨hy95, hm88⟩ := Lib.u8_to_field_spec ev143; subst y95 m88
    obtain ⟨hy87, hm80⟩ := Lib.u8_to_field_spec ev157; subst y87 m80
    obtain ⟨hy79, hm72⟩ := Lib.u8_to_field_spec ev171; subst y79 m72
    obtain ⟨hy71, hm64⟩ := Lib.u8_to_field_spec ev185; subst y71 m64
    obtain ⟨hy63, hm54⟩ := Lib.u8_to_field_spec ev199; subst y63 m54
    simp only [evalBinOp, Except.ok.injEq] at op109 op101 op93 op85 op77 op69
    subst x94 x86 x78 x70 x62 v53
    have h0 : k / 256 % 256 = 0 ∧ k / 65536 % 256 = 0 ∧ k / 16777216 % 256 = 0 ∧
        k / 4294967296 % 256 = 0 ∧ k / 1099511627776 % 256 = 0 ∧
        k / 281474976710656 % 256 = 0 ∧ k / 72057594037927936 % 256 = 0 := by omega
    rcases h0 with ⟨e1, e2, e3, e4, e5, e6, e7⟩
    exact (hne366 (by simp [e1, e2, e3, e4, e5, e6, e7])).elim

private theorem vector32_toList_eq (b : Vector UInt8 32) :
    b.toList =
      [b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
       b[8], b[9], b[10], b[11], b[12], b[13], b[14], b[15],
       b[16], b[17], b[18], b[19], b[20], b[21], b[22], b[23],
       b[24], b[25], b[26], b[27], b[28], b[29], b[30], b[31]] := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro i h1 h2
    have hi : i < 32 := by simpa [Vector.length_toList] using h1
    interval_cases i <;> simp

/-- `IxonSerialize::put_address` prepends the 32 bytes of `b` before `rest`. -/
theorem put_address_spec {b : Bytes.Address} {rest : List UInt8}
    {x_a x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ha : Bytes.RepAddressRef Core.addrTy h b x_a)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_address" [x_a, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h' ((Core.ixAddr b).hash.data.toList ++ rest) r := by
  cases «IxonSerialize::put_address».obs ev with
  | run v1 m14 v28 m48 v62 m82 v96 m116 v130 m150 v164 m184 v198 m218 v232 m252
      v266 m286 v300 m320 v334 m354 v368 m388 v402 m422 v436 m456 v470 m490 v504 m524
      v538 m558 v572 m592 v606 m626 v640 m660 v674 m694 v708 m728 v742 m762 v776 m796
      v810 m830 v844 m864 v878 m898 v912 m932 v946 m966 v980 m1000 v1014 m1034 v1048 v1075
      ld11 hm24 pr38 hm58 pr72 hm92 pr106 hm126 pr140 hm160 pr174 hm194 pr208 hm228 pr242
      hm262 pr276 hm296 pr310 hm330 pr344 hm364 pr378 hm398 pr412 hm432 pr446 hm466 pr480
      hm500 pr514 hm534 pr548 hm568 pr582 hm602 pr616 hm636 pr650 hm670 pr684 hm704 pr718
      hm738 pr752 hm772 pr786 hm806 pr820 hm840 pr854 hm874 pr888 hm908 pr922 hm942 pr956
      hm976 pr990 hm1010 pr1024 hm1044 pr1058 he1071 hm1070 pr1085 _ =>
    have hv1 := load_repAddressRef ha ld11
    subst v1
    obtain rfl := ok_inj ((proj_digestV b 31 (by decide)).symm.trans pr38)
    obtain rfl := ok_inj ((proj_digestV b 30 (by decide)).symm.trans pr72)
    obtain rfl := ok_inj ((proj_digestV b 29 (by decide)).symm.trans pr106)
    obtain rfl := ok_inj ((proj_digestV b 28 (by decide)).symm.trans pr140)
    obtain rfl := ok_inj ((proj_digestV b 27 (by decide)).symm.trans pr174)
    obtain rfl := ok_inj ((proj_digestV b 26 (by decide)).symm.trans pr208)
    obtain rfl := ok_inj ((proj_digestV b 25 (by decide)).symm.trans pr242)
    obtain rfl := ok_inj ((proj_digestV b 24 (by decide)).symm.trans pr276)
    obtain rfl := ok_inj ((proj_digestV b 23 (by decide)).symm.trans pr310)
    obtain rfl := ok_inj ((proj_digestV b 22 (by decide)).symm.trans pr344)
    obtain rfl := ok_inj ((proj_digestV b 21 (by decide)).symm.trans pr378)
    obtain rfl := ok_inj ((proj_digestV b 20 (by decide)).symm.trans pr412)
    obtain rfl := ok_inj ((proj_digestV b 19 (by decide)).symm.trans pr446)
    obtain rfl := ok_inj ((proj_digestV b 18 (by decide)).symm.trans pr480)
    obtain rfl := ok_inj ((proj_digestV b 17 (by decide)).symm.trans pr514)
    obtain rfl := ok_inj ((proj_digestV b 16 (by decide)).symm.trans pr548)
    obtain rfl := ok_inj ((proj_digestV b 15 (by decide)).symm.trans pr582)
    obtain rfl := ok_inj ((proj_digestV b 14 (by decide)).symm.trans pr616)
    obtain rfl := ok_inj ((proj_digestV b 13 (by decide)).symm.trans pr650)
    obtain rfl := ok_inj ((proj_digestV b 12 (by decide)).symm.trans pr684)
    obtain rfl := ok_inj ((proj_digestV b 11 (by decide)).symm.trans pr718)
    obtain rfl := ok_inj ((proj_digestV b 10 (by decide)).symm.trans pr752)
    obtain rfl := ok_inj ((proj_digestV b 9 (by decide)).symm.trans pr786)
    obtain rfl := ok_inj ((proj_digestV b 8 (by decide)).symm.trans pr820)
    obtain rfl := ok_inj ((proj_digestV b 7 (by decide)).symm.trans pr854)
    obtain rfl := ok_inj ((proj_digestV b 6 (by decide)).symm.trans pr888)
    obtain rfl := ok_inj ((proj_digestV b 5 (by decide)).symm.trans pr922)
    obtain rfl := ok_inj ((proj_digestV b 4 (by decide)).symm.trans pr956)
    obtain rfl := ok_inj ((proj_digestV b 3 (by decide)).symm.trans pr990)
    obtain rfl := ok_inj ((proj_digestV b 2 (by decide)).symm.trans pr1024)
    obtain rfl := ok_inj ((proj_digestV b 1 (by decide)).symm.trans pr1058)
    obtain rfl := ok_inj ((proj_digestV b 0 (by decide)).symm.trans pr1085)
    obtain ⟨e31, s31⟩ := snoc_byte hm24 (repU8_bv _ b[31]) hrest
    obtain ⟨e30, s30⟩ := snoc_byte hm58 (repU8_bv _ b[30]) s31
    obtain ⟨e29, s29⟩ := snoc_byte hm92 (repU8_bv _ b[29]) s30
    obtain ⟨e28, s28⟩ := snoc_byte hm126 (repU8_bv _ b[28]) s29
    obtain ⟨e27, s27⟩ := snoc_byte hm160 (repU8_bv _ b[27]) s28
    obtain ⟨e26, s26⟩ := snoc_byte hm194 (repU8_bv _ b[26]) s27
    obtain ⟨e25, s25⟩ := snoc_byte hm228 (repU8_bv _ b[25]) s26
    obtain ⟨e24, s24⟩ := snoc_byte hm262 (repU8_bv _ b[24]) s25
    obtain ⟨e23, s23⟩ := snoc_byte hm296 (repU8_bv _ b[23]) s24
    obtain ⟨e22, s22⟩ := snoc_byte hm330 (repU8_bv _ b[22]) s23
    obtain ⟨e21, s21⟩ := snoc_byte hm364 (repU8_bv _ b[21]) s22
    obtain ⟨e20, s20⟩ := snoc_byte hm398 (repU8_bv _ b[20]) s21
    obtain ⟨e19, s19⟩ := snoc_byte hm432 (repU8_bv _ b[19]) s20
    obtain ⟨e18, s18⟩ := snoc_byte hm466 (repU8_bv _ b[18]) s19
    obtain ⟨e17, s17⟩ := snoc_byte hm500 (repU8_bv _ b[17]) s18
    obtain ⟨e16, s16⟩ := snoc_byte hm534 (repU8_bv _ b[16]) s17
    obtain ⟨e15, s15⟩ := snoc_byte hm568 (repU8_bv _ b[15]) s16
    obtain ⟨e14, s14⟩ := snoc_byte hm602 (repU8_bv _ b[14]) s15
    obtain ⟨e13, s13⟩ := snoc_byte hm636 (repU8_bv _ b[13]) s14
    obtain ⟨e12, s12⟩ := snoc_byte hm670 (repU8_bv _ b[12]) s13
    obtain ⟨e11, s11⟩ := snoc_byte hm704 (repU8_bv _ b[11]) s12
    obtain ⟨e10, s10⟩ := snoc_byte hm738 (repU8_bv _ b[10]) s11
    obtain ⟨e9, s9⟩ := snoc_byte hm772 (repU8_bv _ b[9]) s10
    obtain ⟨e8, s8⟩ := snoc_byte hm806 (repU8_bv _ b[8]) s9
    obtain ⟨e7, s7⟩ := snoc_byte hm840 (repU8_bv _ b[7]) s8
    obtain ⟨e6, s6⟩ := snoc_byte hm874 (repU8_bv _ b[6]) s7
    obtain ⟨e5, s5⟩ := snoc_byte hm908 (repU8_bv _ b[5]) s6
    obtain ⟨e4, s4⟩ := snoc_byte hm942 (repU8_bv _ b[4]) s5
    obtain ⟨e3, s3⟩ := snoc_byte hm976 (repU8_bv _ b[3]) s4
    obtain ⟨e2, s2⟩ := snoc_byte hm1010 (repU8_bv _ b[2]) s3
    obtain ⟨e1, s1⟩ := snoc_byte hm1044 (repU8_bv _ b[1]) s2
    obtain ⟨e0, s0⟩ := snoc_byte hm1070 (repU8_bv _ b[0]) s1
    have hhash : (Core.ixAddr b).hash.data.toList = b.toList := by
      simp [Core.ixAddr, Vector.toArray]
    rw [he1071, hhash, vector32_toList_eq b]
    refine ⟨(((((((((((((((((((((((((((((((e31.trans e30).trans e29).trans e28).trans e27).trans
      e26).trans e25).trans e24).trans e23).trans e22).trans e21).trans e20).trans e19).trans
      e18).trans e17).trans e16).trans e15).trans e14).trans e13).trans e12).trans e11).trans
      e10).trans e9).trans e8).trans e7).trans e6).trans e5).trans e4).trans e3).trans e2).trans
      e1).trans e0, ?_⟩
    simpa [List.cons_append] using s0

private theorem put_sharing_nil_spec {rest : List UInt8}
    {x_list x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hl : RepList Core.Specs.Callees.ixExprListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_sharing" [x_list, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h' ((tag0Bytes 0).data.toList ++ rest) r := by
  obtain ⟨v1, m2, cs12, cs26, v30, m39, cs47, ev14, ev49, ev28, _⟩ :=
    «IxonSerialize::put_sharing».obs ev
  rw [← Names.«WordLists::length_u64<&Ixon::Expr>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Expr" [])]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Names.«Lists::Node<&Ixon::Expr>».symbol]
  obtain ⟨hv1, hm2⟩ := length_u64_nil_spec hl' ev14
  subst v1 m2
  rcases «IxonSerialize::put_expr_list».obs ev49 with
    ⟨_, he21, he22, _⟩ | ⟨_, _, _, _, _, _, _, ld12, _, _, _⟩
  · subst v30 m39
    exact put_tagn0_spec (val := 0) hrest ev28
  · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hl ld12
    cases he

private theorem put_refs_nil_spec {rest : List UInt8}
    {x_list x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hl : RepList Core.addrListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_refs" [x_list, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h' ((tag0Bytes 0).data.toList ++ rest) r := by
  obtain ⟨v1, m2, cs12, cs26, v30, m39, cs47, ev14, ev49, ev28, _⟩ :=
    «IxonSerialize::put_refs».obs ev
  rw [← Names.«WordLists::length_u64<&[Field; 32]>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Names.«Lists::Node<&[Field; 32]>».symbol]
  obtain ⟨hv1, hm2⟩ := length_u64_nil_spec hl' ev14
  subst v1 m2
  rcases «IxonSerialize::put_address_list».obs ev49 with
    ⟨_, he21, he22, _⟩ | ⟨_, _, _, _, _, _, ld12, _, _, _⟩
  · subst v30 m39
    exact put_tagn0_spec (val := 0) hrest ev28
  · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hl ld12
    cases he

private theorem put_univs_nil_spec {rest : List UInt8}
    {x_list x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hl : RepList Core.Specs.Callees.ixUnivListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_univs" [x_list, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h' ((tag0Bytes 0).data.toList ++ rest) r := by
  obtain ⟨v1, m2, cs12, cs26, v30, m39, cs47, ev14, ev49, ev28, _⟩ :=
    «IxonSerialize::put_univs».obs ev
  rw [← Names.«WordLists::length_u64<&Ixon::Univ>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Univ" [])]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Names.«Lists::Node<&Ixon::Univ>».symbol]
  obtain ⟨hv1, hm2⟩ := length_u64_nil_spec hl' ev14
  subst v1 m2
  rcases «IxonSerialize::put_univ_list».obs ev49 with
    ⟨_, he21, he22, _⟩ | ⟨_, _, _, _, _, _, _, ld12, _, _, _⟩
  · subst v30 m39
    exact put_tagn0_spec (val := 0) hrest ev28
  · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hl ld12
    cases he

private theorem put_binders_nil_spec {rest : List UInt8}
    {x_list x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hl : RepList Core.Specs.Callees.ixBinderListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_binders" [x_list, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h' ((bindersBytes #[]).data.toList ++ rest) r := by
  obtain ⟨v1, m2, cs12, cs26, v30, m39, cs47, ev14, ev49, ev28, _⟩ :=
    «IxonSerialize::put_binders».obs ev
  rw [← Names.«WordLists::length_u64<Ixon::BinderBlock>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.named "Ixon::BinderBlock" []]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Names.«Lists::Node<Ixon::BinderBlock>».symbol]
  obtain ⟨hv1, hm2⟩ := length_u64_nil_spec hl' ev14
  subst v1 m2
  rcases «IxonSerialize::put_binder_block_list».obs ev49 with
    ⟨_, he21, he22, _⟩ | ⟨_, _, _, _, _, _, ld12, _, _, _⟩
  · subst v30 m39
    have hbnd : (bindersBytes #[]).data.toList = (tag0Bytes 0).data.toList := by
      simp [bindersBytes, listBytes, ByteArray.data_append]
    rw [hbnd]
    exact put_tagn0_spec (val := 0) hrest ev28
  · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hl ld12
    cases he

private theorem projInfoRep_wireWF {h : Heap F} {info : Ixon.ConstantInfo} {iv : SourceValue F}
    (hinfo : Core.Specs.Callees.ProjInfoRep h info iv) :
    NonrecursiveInfoWireWF info := by
  cases info with
  | cPrj p =>
    obtain ⟨_, _, _, b, _, _, _, _, hblk⟩ := hinfo
    refine .cPrj ?_
    rw [← hblk]; simp [AddressWireWF, Core.ixAddr, ByteArray.size, Vector.size_toArray]
  | rPrj p =>
    obtain ⟨_, _, b, _, _, _, hblk⟩ := hinfo
    refine .rPrj ?_
    rw [← hblk]; simp [AddressWireWF, Core.ixAddr, ByteArray.size, Vector.size_toArray]
  | iPrj p =>
    obtain ⟨_, _, b, _, _, _, hblk⟩ := hinfo
    refine .iPrj ?_
    rw [← hblk]; simp [AddressWireWF, Core.ixAddr, ByteArray.size, Vector.size_toArray]
  | dPrj p =>
    obtain ⟨_, _, b, _, _, _, hblk⟩ := hinfo
    refine .dPrj ?_
    rw [← hblk]; simp [AddressWireWF, Core.ixAddr, ByteArray.size, Vector.size_toArray]
  | defn _ | recr _ | axio _ | quot _ | muts _ => cases hinfo

private theorem projInfoRep_mono {h₁ h₂ : Heap F} {info : Ixon.ConstantInfo} {iv : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hinfo : Core.Specs.Callees.ProjInfoRep h₁ info iv) :
    Core.Specs.Callees.ProjInfoRep h₂ info iv := by
  cases info with
  | cPrj p =>
    obtain ⟨vi, vj, bp, b, rfl, hvi, hvj, hbp, hblk⟩ := hinfo
    exact ⟨vi, vj, bp, b, rfl, hvi, hvj, Bytes.repAddressRef_heapMono₂ Core.addrTy ext hbp, hblk⟩
  | rPrj p =>
    obtain ⟨vi, bp, b, rfl, hvi, hbp, hblk⟩ := hinfo
    exact ⟨vi, bp, b, rfl, hvi, Bytes.repAddressRef_heapMono₂ Core.addrTy ext hbp, hblk⟩
  | iPrj p =>
    obtain ⟨vi, bp, b, rfl, hvi, hbp, hblk⟩ := hinfo
    exact ⟨vi, bp, b, rfl, hvi, Bytes.repAddressRef_heapMono₂ Core.addrTy ext hbp, hblk⟩
  | dPrj p =>
    obtain ⟨vi, bp, b, rfl, hvi, hbp, hblk⟩ := hinfo
    exact ⟨vi, bp, b, rfl, hvi, Bytes.repAddressRef_heapMono₂ Core.addrTy ext hbp, hblk⟩
  | defn _ | recr _ | axio _ | quot _ | muts _ => cases hinfo

private theorem serConstant_proj_eq {info : Ixon.ConstantInfo} (hwf : NonrecursiveInfoWireWF info) :
    (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩).data.toList =
      (nonrecursiveInfoBytes info).data.toList ++
        (tag0Bytes 0).data.toList ++ (tag0Bytes 0).data.toList ++
        (tag0Bytes 0).data.toList ++ (bindersBytes #[]).data.toList := by
  have hcwf : NonrecursiveConstantWireWF ⟨info, #[], #[], #[], #[]⟩ :=
    { info := hwf
      sharingCount := by decide
      sharingEntries := by simp
      refsCount := by decide
      refsEntries := by simp
      univsCount := by decide
      univsEntries := by simp
      binders := by simp [Ixon.bindersWireWF] }
  have hser : Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩ =
      nonrecursiveConstantBytes ⟨info, #[], #[], #[], #[]⟩ := by
    unfold Ixon.serConstant
    exact (putConstant_writes_nonrecursive ⟨info, #[], #[], #[], #[]⟩ hcwf).runPut
  rw [hser]
  simp [nonrecursiveConstantBytes, listBytes, ByteArray.data_append, Array.toList_append,
    List.append_assoc]

/-- **`IxonSerialize::put_constant` on any projection record with empty tables** prepends
`Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩` before `rest`, discharging
`Core.Specs.Callees.put_constant`. -/
theorem put_constant_proj_spec {info : Ixon.ConstantInfo} {rest : List UInt8}
    {cv x_rest r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hcv : Core.Specs.Callees.ProjConstRep h info cv)
    (hrest : Bytes.RepByteStream Core.byteListEnum h rest x_rest)
    (ev : ObsFn W "IxonSerialize::put_constant" [cv, x_rest] h r h' calls) :
    Heap.Extends h h' ∧
      Bytes.RepByteStream Core.byteListEnum h'
        ((Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩).data.toList ++ rest) r := by
  obtain ⟨iv, p1, p2, p3, p4, rfl, hinfo, hp1, hp2, hp3, hp4⟩ := hcv
  have hwf := projInfoRep_wireWF hinfo
  rw [serConstant_proj_eq hwf]
  cases info with
  | defn _ | recr _ | axio _ | quot _ | muts _ => cases hinfo
  | cPrj p =>
    obtain ⟨vi, vj, bp, b, rfl, hvi, hvj, hbp, hblk⟩ := hinfo
    rcases «IxonSerialize::put_constant».obs ev with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨x_sh, x_rf, x_un, x_bd, v42, m43, cs53, v57, m66, cs74, v78, m87, cs95,
        v99, m108, cs116, w664, cs673, v678, m750, cs758,
        hv15, ev118, ev97, ev76, ev55, ev760, ev675, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩
    any_goals simp at hv15
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨⟨_, _, hw⟩, rfl, rfl, rfl, rfl⟩
    subst w664
    obtain ⟨e1, s1⟩ := put_binders_nil_spec hp4 hrest ev118
    obtain ⟨e2, s2⟩ := put_univs_nil_spec (hp3.mono (fun _ _ _ _ _ t => t) e1) s1 ev97
    obtain ⟨e3, s3⟩ := put_refs_nil_spec (hp2.mono (fun _ _ _ _ _ t => t) (e1.trans e2)) s2 ev76
    obtain ⟨e4, s4⟩ := put_sharing_nil_spec
      (hp1.mono (fun _ _ _ _ _ t => t) ((e1.trans e2).trans e3)) s3 ev55
    have e14 := ((e1.trans e2).trans e3).trans e4
    rcases «IxonSerialize::put_constant_info».obs ev760 with
      ⟨_, _, hv, _, _⟩ | ⟨_, _, _, hv, _, _⟩ | ⟨_, _, _, _, hv, _, _⟩ |
      ⟨_, _, _, _, _, hv, _, _⟩ |
      ⟨x_prj, _, _, _, _, _, hv, ev167, _⟩ |
      ⟨_, _, _, _, _, _, hne, _, _, _⟩ |
      ⟨_, _, _, _, _, _, hne, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, hne, _, _, _, _, _⟩
    · simp at hv
    · simp at hv
    · simp at hv
    · simp at hv
    · simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, rfl⟩
      obtain ⟨x_idx, x_cidx, x_block, _, v39, m48, _, v60, m69, _, hv_p, ev79, ev58, ev37, _⟩ :=
        «IxonSerialize::put_constructor_proj».obs ev167
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv_p
      rcases hv_p with ⟨_, _, rfl, rfl, rfl⟩
      obtain ⟨e5, s5⟩ := put_address_spec
        (Bytes.repAddressRef_heapMono₂ Core.addrTy e14 hbp) s4 ev79
      rw [Lib.repU64_eq hvj] at ev58
      obtain ⟨e6, s6⟩ := put_tagn0_spec s5 ev58
      rw [Lib.repU64_eq hvi] at ev37
      obtain ⟨e7, s7⟩ := put_tagn0_spec s6 ev37
      obtain ⟨e8, s8⟩ := put_tagn4_13_small_spec (k := 4) (by decide)
        (by decide) s7 ev675
      refine ⟨((((e14.trans e5).trans e6).trans e7).trans e8), ?_⟩
      rw [hblk] at s8
      simpa [nonrecursiveInfoBytes, constructorProjBytes, Ixon.Constant.FLAG,
        Ixon.ConstantInfo.CONST_CPRJ, ByteArray.data_append, Array.toList_append,
        List.append_assoc] using s8
    · exact (hne [_] rfl rfl).elim
    · exact (hne [_] rfl rfl).elim
    · exact (hne [_] rfl rfl).elim
  | rPrj p =>
    obtain ⟨vi, bp, b, rfl, hvi, hbp, hblk⟩ := hinfo
    rcases «IxonSerialize::put_constant».obs ev with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨x_sh, x_rf, x_un, x_bd, v42, m43, cs53, v57, m66, cs74, v78, m87, cs95,
        v99, m108, cs116, w785, cs794, v799, m871, cs879,
        hv15, ev118, ev97, ev76, ev55, ev881, ev796, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩
    any_goals simp at hv15
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨⟨_, _, hw⟩, rfl, rfl, rfl, rfl⟩
    subst w785
    obtain ⟨e1, s1⟩ := put_binders_nil_spec hp4 hrest ev118
    obtain ⟨e2, s2⟩ := put_univs_nil_spec (hp3.mono (fun _ _ _ _ _ t => t) e1) s1 ev97
    obtain ⟨e3, s3⟩ := put_refs_nil_spec (hp2.mono (fun _ _ _ _ _ t => t) (e1.trans e2)) s2 ev76
    obtain ⟨e4, s4⟩ := put_sharing_nil_spec
      (hp1.mono (fun _ _ _ _ _ t => t) ((e1.trans e2).trans e3)) s3 ev55
    have e14 := ((e1.trans e2).trans e3).trans e4
    rcases «IxonSerialize::put_constant_info».obs ev881 with
      ⟨_, _, hv, _, _⟩ | ⟨_, _, _, hv, _, _⟩ | ⟨_, _, _, _, hv, _, _⟩ |
      ⟨_, _, _, _, _, hv, _, _⟩ | ⟨_, _, _, _, _, _, hv, _, _⟩ |
      ⟨x_prj, _, _, _, _, _, _, hv, ev202, _⟩ |
      ⟨_, _, _, _, _, _, _, hne, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, hne, _, _, _, _⟩
    · simp at hv
    · simp at hv
    · simp at hv
    · simp at hv
    · simp at hv
    · simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, rfl⟩
      obtain ⟨x_idx, x_block, _, v34, m43', _, hv_p, ev53, ev32, _⟩ :=
        «IxonSerialize::put_recursor_proj».obs ev202
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv_p
      rcases hv_p with ⟨_, _, rfl, rfl⟩
      obtain ⟨e5, s5⟩ := put_address_spec
        (Bytes.repAddressRef_heapMono₂ Core.addrTy e14 hbp) s4 ev53
      rw [Lib.repU64_eq hvi] at ev32
      obtain ⟨e6, s6⟩ := put_tagn0_spec s5 ev32
      obtain ⟨e7, s7⟩ := put_tagn4_13_small_spec (k := 5) (by decide)
        (by decide) s6 ev796
      refine ⟨(((e14.trans e5).trans e6).trans e7), ?_⟩
      rw [hblk] at s7
      simpa [nonrecursiveInfoBytes, recursorProjBytes, Ixon.Constant.FLAG,
        Ixon.ConstantInfo.CONST_RPRJ, ByteArray.data_append, Array.toList_append,
        List.append_assoc] using s7
    · exact (hne [_] rfl rfl).elim
    · exact (hne [_] rfl rfl).elim
  | iPrj p =>
    obtain ⟨vi, bp, b, rfl, hvi, hbp, hblk⟩ := hinfo
    rcases «IxonSerialize::put_constant».obs ev with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨x_sh, x_rf, x_un, x_bd, v42, m43, cs53, v57, m66, cs74, v78, m87, cs95,
        v99, m108, cs116, w906, cs915, v920, m992, cs1000,
        hv15, ev118, ev97, ev76, ev55, ev1002, ev917, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩
    any_goals simp at hv15
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨⟨_, _, hw⟩, rfl, rfl, rfl, rfl⟩
    subst w906
    obtain ⟨e1, s1⟩ := put_binders_nil_spec hp4 hrest ev118
    obtain ⟨e2, s2⟩ := put_univs_nil_spec (hp3.mono (fun _ _ _ _ _ t => t) e1) s1 ev97
    obtain ⟨e3, s3⟩ := put_refs_nil_spec (hp2.mono (fun _ _ _ _ _ t => t) (e1.trans e2)) s2 ev76
    obtain ⟨e4, s4⟩ := put_sharing_nil_spec
      (hp1.mono (fun _ _ _ _ _ t => t) ((e1.trans e2).trans e3)) s3 ev55
    have e14 := ((e1.trans e2).trans e3).trans e4
    rcases «IxonSerialize::put_constant_info».obs ev1002 with
      ⟨_, _, hv, _, _⟩ | ⟨_, _, _, hv, _, _⟩ | ⟨_, _, _, _, hv, _, _⟩ |
      ⟨_, _, _, _, _, hv, _, _⟩ | ⟨_, _, _, _, _, _, hv, _, _⟩ |
      ⟨_, _, _, _, _, _, _, hv, _, _⟩ |
      ⟨x_prj, _, _, _, _, _, _, _, hv, ev237, _⟩ |
      ⟨_, _, _, _, _, _, _, _, hne, _, _, _⟩
    · simp at hv
    · simp at hv
    · simp at hv
    · simp at hv
    · simp at hv
    · simp at hv
    · simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, rfl⟩
      obtain ⟨x_idx, x_block, _, v34, m43', _, hv_p, ev53, ev32, _⟩ :=
        «IxonSerialize::put_inductive_proj».obs ev237
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv_p
      rcases hv_p with ⟨_, _, rfl, rfl⟩
      obtain ⟨e5, s5⟩ := put_address_spec
        (Bytes.repAddressRef_heapMono₂ Core.addrTy e14 hbp) s4 ev53
      rw [Lib.repU64_eq hvi] at ev32
      obtain ⟨e6, s6⟩ := put_tagn0_spec s5 ev32
      obtain ⟨e7, s7⟩ := put_tagn4_13_small_spec (k := 6) (by decide)
        (by decide) s6 ev917
      refine ⟨(((e14.trans e5).trans e6).trans e7), ?_⟩
      rw [hblk] at s7
      simpa [nonrecursiveInfoBytes, inductiveProjBytes, Ixon.Constant.FLAG,
        Ixon.ConstantInfo.CONST_IPRJ, ByteArray.data_append, Array.toList_append,
        List.append_assoc] using s7
    · exact (hne [_] rfl rfl).elim
  | dPrj p =>
    obtain ⟨vi, bp, b, rfl, hvi, hbp, hblk⟩ := hinfo
    rcases «IxonSerialize::put_constant».obs ev with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv15, _, _, _, _, _, _, _⟩ |
      ⟨x_sh, x_rf, x_un, x_bd, v42, m43, cs53, v57, m66, cs74, v78, m87, cs95,
        v99, m108, cs116, w1027, cs1036, v1041, m1113, cs1121,
        hv15, ev118, ev97, ev76, ev55, ev1123, ev1038, _⟩
    any_goals simp at hv15
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨⟨_, _, hw⟩, rfl, rfl, rfl, rfl⟩
    subst w1027
    obtain ⟨e1, s1⟩ := put_binders_nil_spec hp4 hrest ev118
    obtain ⟨e2, s2⟩ := put_univs_nil_spec (hp3.mono (fun _ _ _ _ _ t => t) e1) s1 ev97
    obtain ⟨e3, s3⟩ := put_refs_nil_spec (hp2.mono (fun _ _ _ _ _ t => t) (e1.trans e2)) s2 ev76
    obtain ⟨e4, s4⟩ := put_sharing_nil_spec
      (hp1.mono (fun _ _ _ _ _ t => t) ((e1.trans e2).trans e3)) s3 ev55
    have e14 := ((e1.trans e2).trans e3).trans e4
    rcases «IxonSerialize::put_constant_info».obs ev1123 with
      ⟨_, _, hv, _, _⟩ | ⟨_, _, _, hv, _, _⟩ | ⟨_, _, _, _, hv, _, _⟩ |
      ⟨_, _, _, _, _, hv, _, _⟩ | ⟨_, _, _, _, _, _, hv, _, _⟩ |
      ⟨_, _, _, _, _, _, _, hv, _, _⟩ | ⟨_, _, _, _, _, _, _, _, hv, _, _⟩ |
      ⟨x_prj, _, _, _, _, _, _, _, _, hv, ev272, _⟩
    · simp at hv
    · simp at hv
    · simp at hv
    · simp at hv
    · simp at hv
    · simp at hv
    · simp at hv
    · simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, rfl⟩
      obtain ⟨x_idx, x_block, _, v34, m43', _, hv_p, ev53, ev32, _⟩ :=
        «IxonSerialize::put_definition_proj».obs ev272
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv_p
      rcases hv_p with ⟨_, _, rfl, rfl⟩
      obtain ⟨e5, s5⟩ := put_address_spec
        (Bytes.repAddressRef_heapMono₂ Core.addrTy e14 hbp) s4 ev53
      rw [Lib.repU64_eq hvi] at ev32
      obtain ⟨e6, s6⟩ := put_tagn0_spec s5 ev32
      obtain ⟨e7, s7⟩ := put_tagn4_13_small_spec (k := 7) (by decide)
        (by decide) s6 ev1038
      refine ⟨(((e14.trans e5).trans e6).trans e7), ?_⟩
      rw [hblk] at s7
      simpa [nonrecursiveInfoBytes, definitionProjBytes, Ixon.Constant.FLAG,
        Ixon.ConstantInfo.CONST_DPRJ, ByteArray.data_append, Array.toList_append,
        List.append_assoc] using s7

/-! ## `Blake3::bytes_to_addr` and mutual-block projection addresses -/

private theorem tag0Bytes_size_le (v : UInt64) : (tag0Bytes v).size ≤ 9 := by
  unfold tag0Bytes tagNBytes
  simp only
  split_ifs <;> simp [ByteArray.size_append, trimmedBytes_size, List.toByteArray]

private theorem serConstant_proj_length_lt {h : Heap F} {info : Ixon.ConstantInfo}
    {iv : SourceValue F} (hinfo : Core.Specs.Callees.ProjInfoRep h info iv) :
    (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩).data.toList.length < 4294967296 := by
  have hwf := projInfoRep_wireWF hinfo
  have hinfo_sz : (nonrecursiveInfoBytes info).size ≤ 51 := by
    cases info with
    | defn _ | recr _ | axio _ | quot _ | muts _ => cases hinfo
    | cPrj p =>
      cases hwf with
      | cPrj hb =>
        have h1 := tag0Bytes_size_le p.idx
        have h2 := tag0Bytes_size_le p.cidx
        have ht4 : (tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_CPRJ).size = 1 := by decide
        simp only [nonrecursiveInfoBytes, constructorProjBytes, ByteArray.size_append, ht4]
        rw [hb]; omega
    | rPrj p =>
      cases hwf with
      | rPrj hb =>
        have h1 := tag0Bytes_size_le p.idx
        have ht4 : (tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_RPRJ).size = 1 := by decide
        simp only [nonrecursiveInfoBytes, recursorProjBytes, ByteArray.size_append, ht4]
        rw [hb]; omega
    | iPrj p =>
      cases hwf with
      | iPrj hb =>
        have h1 := tag0Bytes_size_le p.idx
        have ht4 : (tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_IPRJ).size = 1 := by decide
        simp only [nonrecursiveInfoBytes, inductiveProjBytes, ByteArray.size_append, ht4]
        rw [hb]; omega
    | dPrj p =>
      cases hwf with
      | dPrj hb =>
        have h1 := tag0Bytes_size_le p.idx
        have ht4 : (tag4Bytes Ixon.Constant.FLAG Ixon.ConstantInfo.CONST_DPRJ).size = 1 := by decide
        simp only [nonrecursiveInfoBytes, definitionProjBytes, ByteArray.size_append, ht4]
        rw [hb]; omega
  rw [serConstant_proj_eq hwf]
  have ht0 : (tag0Bytes 0).data.toList.length = 1 := by decide
  have hbd0 : (bindersBytes #[]).data.toList.length = 1 := by decide
  have hisz : (nonrecursiveInfoBytes info).data.toList.length = (nonrecursiveInfoBytes info).size := by
    simp [ByteArray.size]
  simp only [List.length_append, ht0, hbd0, hisz]
  omega

private theorem byteArray_of_toList (ba : ByteArray) :
    (⟨ba.data.toList.toArray⟩ : ByteArray) = ba := by
  cases ba with
  | mk data => simp

private theorem core_to_repIxonAddressRef {h : Heap F} {b : Bytes.Address} {ptr : SourceValue F}
    (hb : Bytes.RepAddressRef Core.addrTy h b ptr) :
    RepIxonAddressRef h (Core.ixAddr b) ptr :=
  ⟨b, rfl, hb⟩

/-- `Blake3::bytes_to_addr` on a stream of `< 2^32` bytes stores the BLAKE3 digest as a
`RepAddressRef` whose `ixAddr` is `Address.blake3Pure`. -/
theorem bytes_to_addr_native_spec {bytes : List UInt8} {inp r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hlen : bytes.length < 4294967296)
    (hs : Bytes.RepByteStream Core.byteListEnum h bytes inp)
    (ev : ObsFn W "Blake3::bytes_to_addr" [inp] h r h' cs) :
    Heap.Extends h h' ∧
      ∃ a : Bytes.Address, Bytes.RepAddressRef Core.addrTy h' a r ∧
        Core.ixAddr a = Address.blake3Pure ⟨bytes.toArray⟩ := by
  have hs' : Stream h bytes inp := hs
  obtain ⟨ext, ld, _⟩ := bytes_to_addr_spec hs' ev
  rw [Aiur.Library.Blake3.hash_model_spec bytes (native_of_lt hlen)] at ld
  refine ⟨ext, Blake3.Pure.digest bytes, repAddressRef_of_load_digestV ld, ?_⟩
  exact (blake3Pure_eq bytes).symm

/-- `Blake3::bytes_to_addr` under `Bounded cs` (discharging `Core.Specs.Callees.bytes_to_addr`). -/
theorem bytes_to_addr_bounded_spec {bytes : List UInt8} {inp r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hbounded : IxVM.Consistency.Bounded cs)
    (hs : Bytes.RepByteStream Core.byteListEnum h bytes inp)
    (ev : ObsFn W "Blake3::bytes_to_addr" [inp] h r h' cs) :
    Heap.Extends h h' ∧
      ∃ a : Bytes.Address, Bytes.RepAddressRef Core.addrTy h' a r ∧
        Core.ixAddr a = Address.blake3Pure ⟨bytes.toArray⟩ := by
  have hs' : Stream h bytes inp := hs
  obtain ⟨_, _, hcall⟩ := bytes_to_addr_spec hs' ev
  have hlen39 : bytes.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbounded hcall (List.mem_singleton.mpr rfl) hs
  have hlen64 : Blake3.Pure.NativeInput bytes := by
    show bytes.length < 2 ^ 64
    omega
  obtain ⟨ext, ld, _⟩ := bytes_to_addr_spec hs' ev
  rw [Aiur.Library.Blake3.hash_model_spec bytes hlen64] at ld
  refine ⟨ext, Blake3.Pure.digest bytes, repAddressRef_of_load_digestV ld, ?_⟩
  exact (blake3Pure_eq bytes).symm

/-- `Ingress::muts_member_at` looks up member `idx.val` of any represented `MutConst` list
without allocation. -/
theorem muts_member_at_spec {R : Heap F → Ixon.MutConst → SourceValue F → Prop}
    {ms : List Ixon.MutConst} :
    ∀ {idx : F} {x_members r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      RepList Core.Specs.Callees.mutListEnum R h ms x_members →
      ObsFn W "Ingress::muts_member_at" [x_members, .field idx] h r h' calls →
      h' = h ∧ idx.val < ms.length ∧ ∃ mc, ms[idx.val]? = some mc ∧ R h mc r := by
  induction ms with
  | nil =>
    intro idx x_members r h h' calls hms ev
    rcases «Ingress::muts_member_at».obs ev with
      ⟨_, _, ld12, _, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _, _, _⟩
    · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hms ld12
      cases he
    · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hms ld12
      cases he
  | cons m rest ih =>
    intro idx x_members r h h' calls hms ev
    rcases «Ingress::muts_member_at».obs ev with
      ⟨x_m, x_rest, ld12, hv43, he45, he46, _⟩ |
      ⟨x_m, x_rest, cs55, v59, ld12, hne48, op80, ev57, _⟩
    · have hidx0 : idx = 0 := Value.field.inj hv43
      subst idx r h'
      obtain ⟨m', rest', he, hm, _⟩ := Lib.rep_cons_of_load hms ld12
      injection he with hm_eq hrest_eq; subst m' rest'
      exact ⟨rfl, by simp [ZMod.val_zero], m, by simp [ZMod.val_zero], hm⟩
    · have hidx_ne : idx ≠ 0 := fun e => hne48 (congrArg Value.field e)
      obtain ⟨m', rest', he, _, hrest⟩ := Lib.rep_cons_of_load hms ld12
      injection he with hm_eq hrest_eq; subst m' rest'
      have hv59 := Lib.sub_one_inv op80
      subst v59
      obtain ⟨hh', hlt, mc, hget, hmc⟩ := ih hrest ev57
      have hpred := Lib.val_sub_one hidx_ne
      refine ⟨hh', ?_, mc, ?_, hmc⟩
      · simp only [List.length_cons]; omega
      · rw [← hpred]; simpa using hget

private theorem mutShape_heapMono₂ : HeapMono₂ Core.Specs.Callees.MutShape :=
  fun _ _ _ _ _ rep => rep

/-- `Ingress::projection_addr` computes the projection-record address of member `idx.val` of `ms`
at block `b` (and checks `idx.val < 2^56`). -/
theorem projection_addr_spec {ms : List Ixon.MutConst} {b : Bytes.Address} {idx : F}
    {x_members x_block_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hms : Core.Specs.Callees.MembersRep h ms x_members)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn W "Ingress::projection_addr" [x_members, x_block_addr, .field idx] h r h' calls) :
    Heap.Extends h h' ∧ idx.val < 72057594037927936 ∧ idx.val < ms.length ∧
      ∃ (mc : Ixon.MutConst) (a : Bytes.Address),
        ms[idx.val]? = some mc ∧
        Bytes.RepAddressRef Core.addrTy h' a r ∧
        Core.ixAddr a =
          Core.projAddr (Core.Specs.Callees.memberProjInfo (Core.ixAddr b) idx.val mc) := by
  obtain ⟨v1, m2, cs12, v31, m32, cs42, v198, m199, cs201,
      m231, m244, m257, m270, v282, m283, cs293, m306, cs321,
      ev14, ev44, sg206, hm239, hm252, hm265, hm278, hm314, ev295, ev323, _⟩ :=
    «Ingress::projection_addr».obs ev
  obtain ⟨hm2, hidx_len, mc, hget, hmc⟩ := muts_member_at_spec hms ev14
  subst m2
  obtain ⟨n, hn56, hidx_eq, hv31, hm32⟩ := Lib.u64_from_field_spec ev44
  subst m32
  have hn_val : idx.val = n := by
    rw [Value.field.inj hidx_eq, val_cast_u56_ing hn56]
  have hidx56 : idx.val < 72057594037927936 := by omega
  have hrep_u64 : RepU64 h idx.val.toUInt64 v31 := by
    rw [hv31, ← hn_val]
    have hu64 : idx.val.toUInt64.toNat = idx.val := UInt64.toNat_ofNat_of_lt (by omega)
    rw [← hu64]
    exact Deserialize.repU64_u64Value h idx.val.toUInt64
  let info := Core.Specs.Callees.memberProjInfo (Core.ixAddr b) idx.val mc
  have hinfo_step : m199 = h ∧ Core.Specs.Callees.ProjInfoRep h info v198 := by
    cases mc with
    | defn d =>
      obtain ⟨dv, rfl⟩ := hmc
      rcases sg206 with
        ⟨_, _, he79, he105, _⟩ | ⟨_, hne107, _, _, _, _⟩ | ⟨_, hne107, _, _, _, _, _⟩
      · exact ⟨he105, v31, x_block_addr, b, he79, hrep_u64, hb, rfl⟩
      · exact (hne107 [dv] rfl rfl).elim
      · exact (hne107 [dv] rfl rfl).elim
    | indc ind =>
      obtain ⟨iv, rfl⟩ := hmc
      rcases sg206 with
        ⟨_, hv67, _, _, _⟩ | ⟨_, _, _, he124, he150, _⟩ | ⟨_, _, hne152, _, _, _, _⟩
      · simp [Core.Specs.Callees.mutCtor] at hv67
      · exact ⟨he150, v31, x_block_addr, b, he124, hrep_u64, hb, rfl⟩
      · exact (hne152 [iv] rfl rfl).elim
    | recr rc =>
      obtain ⟨rv, rfl⟩ := hmc
      rcases sg206 with
        ⟨_, hv67, _, _, _⟩ | ⟨_, _, hv112, _, _, _⟩ | ⟨_, _, _, _, he169, he195, _⟩
      · simp [Core.Specs.Callees.mutCtor] at hv67
      · simp [Core.Specs.Callees.mutCtor] at hv112
      · exact ⟨he195, v31, x_block_addr, b, he169, hrep_u64, hb, rfl⟩
  rcases hinfo_step with ⟨hm199, hinfo⟩
  subst m199
  have e1 : Heap.Extends h m231 := by rw [hm239]; exact Heap.Extends.snoc h _
  have p1 : RepList Core.Specs.Callees.ixExprListEnum (fun _ (_ : Unit) _ => True) m231 []
      (.ptr (.enum Names.«Lists::Node<&Ixon::Expr>») h.length) := by
    rw [hm239]; exact Lib.rep_store_nil h
  have e2 : Heap.Extends m231 m244 := by rw [hm252]; exact Heap.Extends.snoc m231 _
  have p2 : RepList Core.addrListEnum (fun _ (_ : Unit) _ => True) m244 []
      (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m231.length) := by
    rw [hm252]; exact Lib.rep_store_nil m231
  have e3 : Heap.Extends m244 m257 := by rw [hm265]; exact Heap.Extends.snoc m244 _
  have p3 : RepList Core.Specs.Callees.ixUnivListEnum (fun _ (_ : Unit) _ => True) m257 []
      (.ptr (.enum Names.«Lists::Node<&Ixon::Univ>») m244.length) := by
    rw [hm265]; exact Lib.rep_store_nil m244
  have e4 : Heap.Extends m257 m270 := by rw [hm278]; exact Heap.Extends.snoc m257 _
  have p4 : RepList Core.Specs.Callees.ixBinderListEnum (fun _ (_ : Unit) _ => True) m270 []
      (.ptr (.enum Names.«Lists::Node<Ixon::BinderBlock>») m257.length) := by
    rw [hm278]; exact Lib.rep_store_nil m257
  have e5 : Heap.Extends m270 m306 := by rw [hm314]; exact Heap.Extends.snoc m270 _
  have hnil_bytes : Bytes.RepByteStream Core.byteListEnum m306 []
      (.ptr (.enum Names.«Lists::Node<Field>») m270.length) := by
    rw [hm314]; exact Lib.rep_store_nil m270
  have e15 := (((e1.trans e2).trans e3).trans e4).trans e5
  have hcv : Core.Specs.Callees.ProjConstRep m306 info
      (.construct "Ixon::Constant" "Mk"
        [v198,
         .ptr (.enum Names.«Lists::Node<&Ixon::Expr>») h.length,
         .ptr (.enum Names.«Lists::Node<&[Field; 32]>») m231.length,
         .ptr (.enum Names.«Lists::Node<&Ixon::Univ>») m244.length,
         .ptr (.enum Names.«Lists::Node<Ixon::BinderBlock>») m257.length]) :=
    ⟨v198, _, _, _, _, rfl, projInfoRep_mono e15 hinfo,
      p1.mono (fun _ _ _ _ _ t => t) (((e2.trans e3).trans e4).trans e5),
      p2.mono (fun _ _ _ _ _ t => t) ((e3.trans e4).trans e5),
      p3.mono (fun _ _ _ _ _ t => t) (e4.trans e5),
      p4.mono (fun _ _ _ _ _ t => t) e5⟩
  obtain ⟨e_put, s_put⟩ := put_constant_proj_spec hcv hnil_bytes ev295
  rw [List.append_nil] at s_put
  have hlen_ser := serConstant_proj_length_lt hinfo
  obtain ⟨e_b2a, a, ha_rep, ha_eq⟩ := bytes_to_addr_native_spec hlen_ser s_put ev323
  rw [byteArray_of_toList] at ha_eq
  exact ⟨(e15.trans e_put).trans e_b2a, hidx56, hidx_len, mc, a, hget, ha_rep, ha_eq⟩

/-- Projection addresses of a suffix `cur` starting at index `k` of block `b`. -/
def blockRecurAddrsAux (b : _root_.Address) : Nat → List Ixon.MutConst → List _root_.Address
  | _, [] => []
  | k, m :: rest =>
    Core.projAddr (Core.Specs.Callees.memberProjInfo b k m) :: blockRecurAddrsAux b (k + 1) rest

/-- Projection-record addresses of all members of mutual block `b`, in order. -/
def blockRecurAddrs (b : _root_.Address) (ms : List Ixon.MutConst) : List _root_.Address :=
  blockRecurAddrsAux b 0 ms

private theorem blockRecurAddrsAux_length (b : _root_.Address) (k : Nat) (cur : List Ixon.MutConst) :
    (blockRecurAddrsAux b k cur).length = cur.length := by
  induction cur generalizing k with
  | nil => rfl
  | cons m rest ih => simp [blockRecurAddrsAux, ih (k + 1)]

private theorem blockRecurAddrsAux_getElem (b : _root_.Address) (k : Nat) :
    ∀ (cur : List Ixon.MutConst) (i : Nat) (h1 : i < (blockRecurAddrsAux b k cur).length)
      (h2 : i < cur.length),
      (blockRecurAddrsAux b k cur)[i] =
        Core.projAddr (Core.Specs.Callees.memberProjInfo b (k + i) cur[i]) := by
  intro cur
  induction cur generalizing k with
  | nil => intro i h1; simp [blockRecurAddrsAux] at h1
  | cons m rest ih =>
    intro i h1 h2
    cases i with
    | zero => simp [blockRecurAddrsAux]
    | succ j =>
      simp only [blockRecurAddrsAux, List.getElem_cons_succ]
      rw [ih (k + 1) j (by simpa [blockRecurAddrsAux] using h1) (by simpa using h2)]
      have hadd : k + 1 + j = k + (j + 1) := by omega
      rw [hadd]

theorem blockRecurAddrs_eq_mapIdx (b : _root_.Address) (ms : List Ixon.MutConst) :
    blockRecurAddrs b ms =
      ms.mapIdx fun i m => Core.projAddr (Core.Specs.Callees.memberProjInfo b i m) := by
  apply List.ext_getElem
  · simp [blockRecurAddrs, blockRecurAddrsAux_length]
  · intro i h1 h2
    have hi : i < ms.length := by simpa [blockRecurAddrs, blockRecurAddrsAux_length] using h1
    simp only [blockRecurAddrs, blockRecurAddrsAux_getElem b 0 ms i h1 hi, Nat.zero_add,
      List.getElem_mapIdx]

/-- `Ingress::build_recur_addrs_walk` builds the list of projection addresses for suffix `cur`
starting at index `k ≤ 2^56`. -/
theorem build_recur_addrs_walk_spec {ms : List Ixon.MutConst} {b : Bytes.Address}
    {cur : List Ixon.MutConst} :
    ∀ {k : Nat} {x_all_members x_block_addr x_cur r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      k ≤ 72057594037927936 →
      Core.Specs.Callees.MembersRep h ms x_all_members →
      Bytes.RepAddressRef Core.addrTy h b x_block_addr →
      Core.Specs.Callees.MembersRep h cur x_cur →
      (∀ j m', cur[j]? = some m' → ms[k + j]? = some m') →
      ObsFn W "Ingress::build_recur_addrs_walk"
        [x_all_members, x_block_addr, x_cur, .field (k : F)] h r h' calls →
      Heap.Extends h h' ∧
        ∃ as : List Bytes.Address,
          RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h' as r ∧
          as.map Core.ixAddr = blockRecurAddrsAux (Core.ixAddr b) k cur := by
  induction cur with
  | nil =>
    intro k x_all_members x_block_addr x_cur r h h' calls _ _ _ hcur _ ev
    rcases «Ingress::build_recur_addrs_walk».obs ev with
      ⟨_, he24, hm23, _⟩ | ⟨_, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _⟩
    · rw [he24, hm23]
      exact ⟨Heap.Extends.snoc h _, [], Lib.rep_store_nil h, rfl⟩
    · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hcur ld12
      cases he
  | cons m rest ih =>
    intro k x_all_members x_block_addr x_cur r h h' calls hk hms hb hcur hsuf ev
    rcases «Ingress::build_recur_addrs_walk».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨w36, x_rest, v55, v56, m58, cs66, m94, cs102, v108,
        ld12, he51, hm50, ev68, op143, ev104, _⟩
    · have he := Lib.rep_nil_of_load hcur ld12
      cases he
    · obtain ⟨m', rest', he, _, hrest⟩ := Lib.rep_cons_of_load hcur ld12
      injection he with hm_eq hrest_eq; subst m' rest'
      obtain ⟨ext1, hk_lt, _, mc, a₀, hget_mc, ha₀, ha₀_eq⟩ :=
        projection_addr_spec hms hb ev68
      rw [val_cast_le_u56_ing hk] at hk_lt hget_mc ha₀_eq
      have hmc_eq : mc = m := by
        have h0 := hsuf 0 m rfl
        rw [Nat.add_zero, hget_mc] at h0
        exact Option.some.inj h0
      subst mc
      simp only [evalBinOp, Except.ok.injEq] at op143
      have hv108 : v108 = .field (((k + 1 : Nat) : F)) := by
        rw [← op143]; push_cast; rfl
      rw [hv108] at ev104
      obtain ⟨ext2, as_tl, has_tl, hmap_tl⟩ :=
        ih (by omega) (hms.mono mutShape_heapMono₂ ext1)
          (Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 hb)
          (hrest.mono mutShape_heapMono₂ ext1)
          (fun j m' hj => by
            have hstep := hsuf (j + 1) m' hj
            have hadd : k + 1 + j = k + (j + 1) := by omega
            rwa [hadd])
          ev104
      rw [he51, hm50]
      have ext_fin : Heap.Extends m94
          (m94 ++ [.construct Names.«Lists::Node<&[Field; 32]>» "Cons" [v55, v56]]) :=
        Heap.Extends.snoc m94 _
      have hcons : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy)
          (m94 ++ [.construct Names.«Lists::Node<&[Field; 32]>» "Cons" [v55, v56]])
          (a₀ :: as_tl) (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m94.length) :=
        Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ Core.addrTy)
          (Bytes.repAddressRef_heapMono₂ Core.addrTy ext2 ha₀) has_tl
      refine ⟨(ext1.trans ext2).trans ext_fin, a₀ :: as_tl, hcons, ?_⟩
      simp [blockRecurAddrsAux, ha₀_eq, hmap_tl]

/-- **`Ingress::build_recur_addrs` specification** (discharging
`Core.Specs.Callees.build_recur_addrs`). -/
theorem build_recur_addrs_spec {ms : List Ixon.MutConst} {b : Bytes.Address}
    {x_members x_block_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hms : Core.Specs.Callees.MembersRep h ms x_members)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn W "Ingress::build_recur_addrs" [x_members, x_block_addr] h r h' calls) :
    Heap.Extends h h' ∧
      ∃ as : List Bytes.Address,
        RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h' as r ∧
        as.map Core.ixAddr =
          ms.mapIdx fun i m =>
            Core.projAddr (Core.Specs.Callees.memberProjInfo (Core.ixAddr b) i m) := by
  obtain ⟨cs4, ev6, _⟩ := «Ingress::build_recur_addrs».obs ev
  have ev6' : ObsFn W "Ingress::build_recur_addrs_walk"
      [x_members, x_block_addr, x_members, .field ((0 : Nat) : F)] h r h' cs4 := by
    simpa using ev6
  obtain ⟨ext, as, has, hmap⟩ :=
    build_recur_addrs_walk_spec (Nat.zero_le _) hms hb hms
      (fun j m' hj => by simpa using hj) ev6'
  rw [← blockRecurAddrs_eq_mapIdx]
  exact ⟨ext, as, has, hmap⟩

private theorem repList_core_to_ixon {h : Heap F} {as : List Bytes.Address} {ptr : SourceValue F}
    (rep : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h as ptr) :
    RepList addressListEnum RepIxonAddressRef h (as.map Core.ixAddr) ptr := by
  rw [addressListEnum_eq]
  induction rep with
  | nil cell => exact .nil cell
  | cons cell hhd _ ih => exact .cons cell (core_to_repIxonAddressRef hhd) ih

/-- `Ingress::build_recur_addrs` in `RepIxonAddressRef` form for `Convert::convert_*` callers. -/
theorem build_recur_addrs_ixon_spec {ms : List Ixon.MutConst} {b : Bytes.Address}
    {x_members x_block_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hms : RepList mutConstListEnum RepMutConst h ms x_members)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn W "Ingress::build_recur_addrs" [x_members, x_block_addr] h r h' calls) :
    Heap.Extends h h' ∧
      RepList addressListEnum RepIxonAddressRef h' (blockRecurAddrs (Core.ixAddr b) ms) r := by
  obtain ⟨ext, as, has, hmap⟩ :=
    build_recur_addrs_spec (repList_mutShape_of_repMutConst hms) hb ev
  rw [← blockRecurAddrs_eq_mapIdx] at hmap
  have hix := repList_core_to_ixon has
  rw [hmap] at hix
  exact ⟨ext, hix⟩

/-! ## `Ingress::defn_is_unsafe_ci` and `Ingress::defn_member_recur_addrs` -/

/-- Whether `Ingress::defn_is_unsafe_ci(d.kind, d.safety)` returns `1` (`true`) or `0` (`false`).
Matches `!InLogic (.defn d)` for `.thm` and `.opaq`, and returns `true` for both `.part` and
`.unsaf` `.defn`s (all potentially self-/mutually-recursive definitions). -/
def defnIsUnsafeCI (d : Ixon.Definition) : Bool :=
  match d.kind with
  | .thm => false
  | .opaq => d.safety == .unsaf
  | .defn => d.safety != .safe

/-- Recursive-address table passed to `Convert::convert_definition` for a standalone `.defn` at `a`. -/
def defnRecurAddrs (d : Ixon.Definition) (a : _root_.Address) : List _root_.Address :=
  if defnIsUnsafeCI d then [a] else []

/-- Recursive-address table passed to `Convert::convert_definition` for a `.dPrj` member `d` of
mutual block `blkAddr` with members `ms`. -/
def defnMemberRecurAddrs (d : Ixon.Definition) (blkAddr : _root_.Address)
    (ms : List Ixon.MutConst) : List _root_.Address :=
  if defnIsUnsafeCI d then blockRecurAddrs blkAddr ms else []

/-- `Ingress::defn_is_unsafe_ci` computes `repBoolField (defnIsUnsafeCI d)` without allocation. -/
theorem defn_is_unsafe_ci_spec {d : Ixon.Definition} {r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "Ingress::defn_is_unsafe_ci"
      [repDefKindVal d.kind, repDefSafetyVal d.safety] h r h' calls) :
    r = repBoolField (defnIsUnsafeCI d) ∧ h' = h := by
  rcases «Ingress::defn_is_unsafe_ci».obs ev with
    ⟨hv15, he17, he18, _⟩ |
    ⟨_, hv25, hv41, he43, he44, _⟩ |
    ⟨_, hv25, hne46, he50, he51, _⟩ |
    ⟨_, _, hv58, hv74, he76, he77, _⟩ |
    ⟨_, _, hv58, hne79, he83, he84, _⟩
  · cases hk : d.kind <;> simp [repDefKindVal, hk] at hv15
    simp [defnIsUnsafeCI, hk, repBoolField, he17, he18]
  · cases hk : d.kind <;> simp [repDefKindVal, hk] at hv25
    cases hs : d.safety <;> simp [repDefSafetyVal, hs] at hv41
    simp [defnIsUnsafeCI, hk, hs, repBoolField, he43, he44]
  · cases hk : d.kind <;> simp [repDefKindVal, hk] at hv25
    cases hs : d.safety
    · exact (hne46 [] rfl (by simp [repDefSafetyVal, hs])).elim
    · simp [defnIsUnsafeCI, hk, hs, repBoolField, he50, he51]
    · simp [defnIsUnsafeCI, hk, hs, repBoolField, he50, he51]
  · cases hk : d.kind <;> simp [repDefKindVal, hk] at hv58
    cases hs : d.safety <;> simp [repDefSafetyVal, hs] at hv74
    simp [defnIsUnsafeCI, hk, hs, repBoolField, he76, he77]
  · cases hk : d.kind <;> simp [repDefKindVal, hk] at hv58
    cases hs : d.safety
    · simp [defnIsUnsafeCI, hk, hs, repBoolField, he83, he84]
    · exact (hne79 [] rfl (by simp [repDefSafetyVal, hs])).elim
    · simp [defnIsUnsafeCI, hk, hs, repBoolField, he83, he84]

/-- `Ingress::defn_member_recur_addrs` returns `defnMemberRecurAddrs d (ixAddr b) ms`. -/
theorem defn_member_recur_addrs_spec {d : Ixon.Definition} {ms : List Ixon.MutConst}
    {b : Bytes.Address} {x_d x_members x_block_addr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hd : RepDefinition h d x_d)
    (hms : RepList mutConstListEnum RepMutConst h ms x_members)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn W "Ingress::defn_member_recur_addrs" [x_d, x_members, x_block_addr] h r h' calls) :
    Heap.Extends h h' ∧
      RepList addressListEnum RepIxonAddressRef h'
        (defnMemberRecurAddrs d (Core.ixAddr b) ms) r := by
  obtain ⟨typPtr, valPtr, hd_eq, _, _⟩ := hd
  rcases «Ingress::defn_member_recur_addrs».obs ev with
    ⟨x_kind, x_safety, w17, w18, w19, w20, m52, cs63, hv15, ev65, he90, hm89, _⟩ |
    ⟨x_kind, x_safety, w17, w18, w19, w20, v51, m52, cs63, cs102,
      hv15, ev65, hne95, ev104, _⟩
  · rw [hd_eq] at hv15
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨_, _, hk_eq, hs_eq, _, _, _, _⟩
    subst x_kind x_safety
    obtain ⟨hf0, hm52⟩ := defn_is_unsafe_ci_spec (d := d) ev65
    subst m52
    have hfalse : defnIsUnsafeCI d = false := by
      cases hu : defnIsUnsafeCI d <;> simp [repBoolField, hu] at hf0
      rfl
    rw [he90, hm89]
    have hnil : RepList addressListEnum RepIxonAddressRef
        (h ++ [.construct Names.«Lists::Node<&[Field; 32]>» "Nil" []]) []
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») h.length) := by
      rw [addressListEnum_eq]
      exact Lib.rep_store_nil h
    simpa [defnMemberRecurAddrs, hfalse] using And.intro (Heap.Extends.snoc h _) hnil
  · rw [hd_eq] at hv15
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨_, _, hk_eq, hs_eq, _, _, _, _⟩
    subst x_kind x_safety
    obtain ⟨hv51, hm52⟩ := defn_is_unsafe_ci_spec (d := d) ev65
    subst m52
    have htrue : defnIsUnsafeCI d = true := by
      cases hu : defnIsUnsafeCI d
      · simp [repBoolField, hu] at hv51
        exact (hne95 hv51).elim
      · rfl
    simpa [defnMemberRecurAddrs, htrue] using build_recur_addrs_ixon_spec hms hb ev104

/-! ## Top-level constant ingress (`get_ci_dprj`, `get_ci_iprj`, `get_ci_cprj`, `get_ci_rprj`, `get_ci`) -/

/-- `Ingress::get_ci_dprj` specification: loads parent mutual block `cb` at `ixAddr b`, extracts
member `idx` as `.defn d`, converts `d`, and stores the resulting `KConstantInfo` cell at `r`. -/
theorem get_ci_dprj_spec {b : Bytes.Address} {idx : Nat}
    {x_dprj_addr x_idx x_block_addr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hidx_lt : idx < 18446744073709551616)
    (hx_idx : x_idx = u64Value idx)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn W "Ingress::get_ci_dprj" [x_dprj_addr, x_idx, x_block_addr] h r h' calls) :
    Heap.Extends h h' ∧ idx < 72057594037927936 ∧
      ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
        (d : Ixon.Definition) (blobs : List (_root_.Address × ByteArray)) (v : SourceValue F),
        Hashed calls blkBytes ∧
        Address.blake3Pure blkBytes = Core.ixAddr b ∧
        Ixon.deConstantExact blkBytes = .ok cb ∧
        Ixon.deConstant blkBytes = .ok cb ∧
        cb.info = .muts ms ∧
        ms.toList[idx]? = some (.defn d) ∧
        HashedPairs calls blobs ∧
        loadValue h' r = .ok v ∧
        RawDefnValRep cb.refs.toList (defnMemberRecurAddrs d (Core.ixAddr b) ms.toList)
          cb.univs.toList cb.sharing.toList blobs h' d v := by
  subst x_idx
  obtain ⟨v1, m2, cs12, m24, cs34, x_sharing, x_refs, x_univs, x_binders, x_members,
      m108, cs118, x_d, v158, m159, cs169, v188, m189, cs199,
      v226, m227, cs234, v243, v244, m288, cs296, m308, cs316, v320, m329, cs337,
      ev14, ev36, ev120, ev171, ev201, he230, hm229, ev298, ev339, ev318, ev236, hc348⟩ :=
    «Ingress::get_ci_dprj».obs ev
  have ext0 := ev14.heap_extends
  have hb2 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext0 hb
  obtain ⟨ext1, blkList, cb, hhash_blk, haddr_blk, hexact_blk, hde_blk,
      _, _, _, hbd32, _, cRep⟩ :=
    load_verified_constant_decode hb2 ev36
  obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
  rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
  subst infoVal shPtr rfPtr unPtr bdPtr
  have hmuts : ∃ ms : Array Ixon.MutConst,
      cb.info = .muts ms ∧ RepList mutConstListEnum RepMutConst m24 ms.toList x_members := by
    cases hci : cb.info <;> simp [RepConstantInfo, hci] at hinfo
    obtain ⟨msPtr, hms_eq, hms⟩ := hinfo
    subst msPtr
    exact ⟨_, rfl, hms⟩
  obtain ⟨ms, hcb_info, hms⟩ := hmuts
  rw [← Names.«WordLists::lookup_u64<Ixon::MutConst>».symbol] at ev120
  have hms_inst : RepList (Instance.mk "Lists::Node" [.named "Ixon::MutConst" []]).symbol
      RepMutConst m24 ms.toList x_members := by
    rwa [Names.«Lists::Node<Ixon::MutConst>».symbol]
  obtain ⟨⟨mc, hmc_get, hmc_rep⟩, hm108⟩ := Lib.lookup_u64_spec hidx_lt rfl ev120 hms_inst
  subst m108
  have hdefn : ∃ d : Ixon.Definition, mc = .defn d ∧ RepDefinition m24 d x_d := by
    cases mc with
    | defn d =>
      obtain ⟨dv, hdv_eq, hdv⟩ := hmc_rep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hdv_eq
      rcases hdv_eq with ⟨_, _, rfl⟩
      exact ⟨d, rfl, hdv⟩
    | indc _ => obtain ⟨iv, hiv, _⟩ := hmc_rep; simp at hiv
    | recr _ => obtain ⟨rv, hrv, _⟩ := hmc_rep; simp at hrv
  obtain ⟨d, rfl, hd_rep⟩ := hdefn
  have ext2 := ev171.heap_extends
  have hb159 := Bytes.repAddressRef_heapMono₂ Core.addrTy (ext0.trans (ext1.trans ext2)) hb
  obtain ⟨ext3, hrecs⟩ :=
    defn_member_recur_addrs_spec (hd_rep.mono ext2) (hms.mono repMutConst_heapMono₂ ext2)
      hb159 ev201
  have ext23 := ext2.trans ext3
  obtain ⟨ext4, htbl⟩ := binder_table_spec (hbd.mono repBinderBlock_heapMono₂ ext23) hbd32 ev298
  have ext24 := ext23.trans ext4
  obtain ⟨hidx56, hv320, hm329⟩ :=
    Lib.u64_to_field_spec (Lib.repU64_ofNatLT m288 hidx_lt) ev339
  simp only [UInt64.toNat_ofNatLT] at hidx56 hv320
  subst v320 m329
  obtain ⟨_, _, hm308⟩ := muts_root_offset_spec (hms.mono repMutConst_heapMono₂ ext24) ev318
  subst m308
  obtain ⟨ext5, blobs, hhp, hraw⟩ :=
    convert_definition_spec
      (hd_rep.mono ext24)
      (RepShareVec.mono ext24 hsh)
      (hrf.mono repIxonAddressRef_heapMono₂ ext24)
      (hrecs.mono repIxonAddressRef_heapMono₂ ext4)
      (hun.mono repUnivPtr_heapMono₂ ext24)
      htbl ev236
  rw [he230, hm229]
  have ext_snoc := Heap.Extends.snoc m227 v226
  have ext_all := (((ext0.trans ext1).trans ext24).trans ext5).trans ext_snoc
  refine ⟨ext_all, hidx56, ⟨blkList.toArray⟩, cb, ms, d, blobs, v226,
    Hashed.mono hhash_blk (by rw [hc348]; intro c hc; simp [hc]),
    haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get,
    hhp.sub (by rw [hc348]; intro c hc; simp [hc]),
    loadValue_snoc m227 v226,
    hraw.mono ext_snoc (fun _ hm => hm)⟩

/-- `Ingress::get_ci_iprj` specification under `Bounded calls` (handling both direct calls from
`Core` and subcalls from `Ingress::get_ci`). -/
theorem get_ci_iprj_spec {b : Bytes.Address} {idx : F}
    {x_block_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hbounded : IxVM.Consistency.Bounded calls)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn W "Ingress::get_ci_iprj" [x_block_addr, .field idx] h r h' calls) :
    Heap.Extends h h' ∧ idx.val < 72057594037927936 ∧
      ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
        (ind : Ixon.Inductive) (blobs : List (_root_.Address × ByteArray)) (v : SourceValue F),
        Hashed calls blkBytes ∧
        Address.blake3Pure blkBytes = Core.ixAddr b ∧
        Ixon.deConstantExact blkBytes = .ok cb ∧
        Ixon.deConstant blkBytes = .ok cb ∧
        cb.info = .muts ms ∧
        ms.toList[idx.val]? = some (.indc ind) ∧
        HashedPairs calls blobs ∧
        loadValue h' r = .ok v ∧
        RawInductValRep cb.refs.toList (blockRecurAddrs (Core.ixAddr b) ms.toList)
          cb.univs.toList cb.sharing.toList blobs h' ind (Core.ixAddr b) idx.val v := by
  obtain ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_members,
      m86, cs96, x_ind, v136, m137, cs147, v166, m167, cs174,
      v184, v185, m236, cs244, m256, cs264,
      ev14, ev98, ev149, he170, hm169, ev246, ev266, ev176, hc283⟩ :=
    «Ingress::get_ci_iprj».obs ev
  obtain ⟨ext1, blkList, cb, hhash_blk, haddr_blk, hexact_blk, hde_blk,
      _, _, _, hbd32, _, cRep⟩ :=
    load_verified_constant_decode hb ev14
  obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
  rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
  subst infoVal shPtr rfPtr unPtr bdPtr
  have hmuts : ∃ ms : Array Ixon.MutConst,
      cb.info = .muts ms ∧ RepList mutConstListEnum RepMutConst m2 ms.toList x_members := by
    cases hci : cb.info <;> simp [RepConstantInfo, hci] at hinfo
    obtain ⟨msPtr, hms_eq, hms⟩ := hinfo
    subst msPtr
    exact ⟨_, rfl, hms⟩
  obtain ⟨ms, hcb_info, hms⟩ := hmuts
  obtain ⟨hm86, hidx_lt_ms, mc, hmc_get, hmc_rep⟩ := muts_member_at_spec hms ev98
  subst m86
  have hcall_muts : (⟨"Ingress::muts_member_at", [x_members, .field idx], m2⟩ : Call F) ∈ calls := by
    rw [hc283]; simp
  have hms_len39 : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbounded hcall_muts (by simp) hms
  have hidx56 : idx.val < 72057594037927936 := by omega
  have hindc : ∃ ind : Ixon.Inductive, mc = .indc ind ∧ RepInductive m2 ind x_ind := by
    cases mc with
    | indc ind =>
      obtain ⟨iv, hiv_eq, hiv⟩ := hmc_rep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hiv_eq
      rcases hiv_eq with ⟨_, _, rfl⟩
      exact ⟨ind, rfl, hiv⟩
    | defn _ => obtain ⟨dv, hdv, _⟩ := hmc_rep; simp at hdv
    | recr _ => obtain ⟨rv, hrv, _⟩ := hmc_rep; simp at hrv
  obtain ⟨ind, rfl, hind_rep⟩ := hindc
  have hb2 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 hb
  obtain ⟨ext2, hrecs⟩ := build_recur_addrs_ixon_spec hms hb2 ev149
  obtain ⟨ext3, htbl⟩ := binder_table_spec (hbd.mono repBinderBlock_heapMono₂ ext2) hbd32 ev246
  have ext23 := ext2.trans ext3
  obtain ⟨_, _, hm256⟩ := muts_root_offset_spec (hms.mono repMutConst_heapMono₂ ext23) ev266
  subst m256
  have hbounded174 : IxVM.Consistency.Bounded cs174 :=
    RomBound.bounded_mono hbounded (by rw [hc283]; intro c hc; simp [hc])
  have ev176' : ObsFn W "Convert::convert_inductive"
      [x_ind, x_block_addr, .field ((idx.val : Nat) : F), x_sharing, x_refs, v136,
       x_univs, v184, v185] m236 v166 m167 cs174 := by
    rwa [ZMod.natCast_zmod_val idx]
  obtain ⟨ext4, blobs, hhp, hraw⟩ :=
    convert_inductive_spec hbounded174
      (hind_rep.mono ext23)
      ((core_to_repIxonAddressRef hb2).mono ext23)
      hidx56
      (RepShareVec.mono ext23 hsh)
      (hrf.mono repIxonAddressRef_heapMono₂ ext23)
      (hrecs.mono repIxonAddressRef_heapMono₂ ext3)
      (hun.mono repUnivPtr_heapMono₂ ext23)
      htbl ev176'
  rw [he170, hm169]
  have ext_snoc := Heap.Extends.snoc m167 v166
  refine ⟨(((ext1.trans ext23).trans ext4).trans ext_snoc), hidx56,
    ⟨blkList.toArray⟩, cb, ms, ind, blobs, v166,
    Hashed.mono hhash_blk (by rw [hc283]; intro c hc; simp [hc]),
    haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get,
    hhp.sub (by rw [hc283]; intro c hc; simp [hc]),
    loadValue_snoc m167 v166,
    hraw.mono ext_snoc (fun _ hm => hm)⟩

/-- `Ingress::get_ci_cprj` specification under `Bounded calls` (handling both direct calls from
`Core` and subcalls from `Ingress::get_ci`). -/
theorem get_ci_cprj_spec {b : Bytes.Address} {idx cidx : F}
    {x_block_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hbounded : IxVM.Consistency.Bounded calls)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn W "Ingress::get_ci_cprj" [x_block_addr, .field idx, .field cidx] h r h' calls) :
    Heap.Extends h h' ∧ idx.val < 72057594037927936 ∧ cidx.val < 72057594037927936 ∧
      ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
        (ind : Ixon.Inductive) (ct : Ixon.Constructor)
        (blobs : List (_root_.Address × ByteArray)) (v : SourceValue F),
        Hashed calls blkBytes ∧
        Address.blake3Pure blkBytes = Core.ixAddr b ∧
        Ixon.deConstantExact blkBytes = .ok cb ∧
        Ixon.deConstant blkBytes = .ok cb ∧
        cb.info = .muts ms ∧
        ms.toList[idx.val]? = some (.indc ind) ∧
        ind.ctors.toList[cidx.val]? = some ct ∧
        HashedPairs calls blobs ∧
        loadValue h' r = .ok v ∧
        RawCtorValRep cb.refs.toList (blockRecurAddrs (Core.ixAddr b) ms.toList)
          cb.univs.toList cb.sharing.toList blobs h' ct (Core.ixAddr b) idx.val v := by
  obtain ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_members,
      m86, cs96, w152, w153, w154, w155, w156, x_ctors,
      v187, m188, cs198, v217, m218, cs228, v247, m248, cs255,
      v265, v266, m317, cs325, x342, x350, m352, cs361,
      ev14, ev98, ev200, ev230, he251, hm250, ev327, ev363, op357, op349, ev257, hc381⟩ :=
    «Ingress::get_ci_cprj».obs ev
  obtain ⟨ext1, blkList, cb, hhash_blk, haddr_blk, hexact_blk, hde_blk,
      _, _, _, hbd32, _, cRep⟩ :=
    load_verified_constant_decode hb ev14
  obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
  rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
  subst infoVal shPtr rfPtr unPtr bdPtr
  have hmuts : ∃ ms : Array Ixon.MutConst,
      cb.info = .muts ms ∧ RepList mutConstListEnum RepMutConst m2 ms.toList x_members := by
    cases hci : cb.info <;> simp [RepConstantInfo, hci] at hinfo
    obtain ⟨msPtr, hms_eq, hms⟩ := hinfo
    subst msPtr
    exact ⟨_, rfl, hms⟩
  obtain ⟨ms, hcb_info, hms⟩ := hmuts
  obtain ⟨hm86, hidx_lt_ms, mc, hmc_get, hmc_rep⟩ := muts_member_at_spec hms ev98
  subst m86
  have hcall_muts : (⟨"Ingress::muts_member_at", [x_members, .field idx], m2⟩ : Call F) ∈ calls := by
    rw [hc381]; simp
  have hms_len39 : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbounded hcall_muts (by simp) hms
  have hidx56 : idx.val < 72057594037927936 := by omega
  have hindc : ∃ ind : Ixon.Inductive, mc = .indc ind ∧
      RepList constructorListEnum RepConstructor m2 ind.ctors.toList x_ctors := by
    cases mc with
    | indc ind =>
      obtain ⟨iv, hiv_eq, typPtr, ctorsPtr, hmk, _, hctors⟩ := hmc_rep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hiv_eq
      rcases hiv_eq with ⟨_, _, hiv_mk⟩
      rw [hmk] at hiv_mk
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hiv_mk
      rcases hiv_mk with ⟨_, _, _, _, _, _, _, hct_eq⟩
      subst ctorsPtr
      exact ⟨ind, rfl, hctors⟩
    | defn _ => obtain ⟨dv, hdv, _⟩ := hmc_rep; simp at hdv
    | recr _ => obtain ⟨rv, hrv, _⟩ := hmc_rep; simp at hrv
  obtain ⟨ind, rfl, hctors⟩ := hindc
  obtain ⟨hm188, hcidx_lt_ct, ct, hct_get, hct_rep⟩ := ctor_at_spec hctors ev200
  subst m188
  have hcall_ctor : (⟨"Convert::ctor_at", [x_ctors, .field cidx], m2⟩ : Call F) ∈ calls := by
    rw [hc381]; simp
  have hct_len39 : ind.ctors.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbounded hcall_ctor (by simp) hctors
  have hcidx56 : cidx.val < 72057594037927936 := by omega
  have hb2 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 hb
  obtain ⟨ext2, hrecs⟩ := build_recur_addrs_ixon_spec hms hb2 ev230
  obtain ⟨ext3, htbl⟩ := binder_table_spec (hbd.mono repBinderBlock_heapMono₂ ext2) hbd32 ev327
  have ext23 := ext2.trans ext3
  obtain ⟨_, _, hm352⟩ := muts_root_offset_spec (hms.mono repMutConst_heapMono₂ ext23) ev363
  subst m352
  have ev257' : ObsFn W "Convert::convert_constructor"
      [v187, x_block_addr, .field ((idx.val : Nat) : F), x_sharing, x_refs, v217,
       x_univs, v265, v266] m317 v247 m248 cs255 := by
    rwa [ZMod.natCast_zmod_val idx]
  obtain ⟨ext4, blobs, hhp, hraw⟩ :=
    convert_constructor_spec
      (hct_rep.mono ext23)
      ((core_to_repIxonAddressRef hb2).mono ext23)
      hidx56
      (RepShareVec.mono ext23 hsh)
      (hrf.mono repIxonAddressRef_heapMono₂ ext23)
      (hrecs.mono repIxonAddressRef_heapMono₂ ext3)
      (hun.mono repUnivPtr_heapMono₂ ext23)
      htbl ev257'
  rw [he251, hm250]
  have ext_snoc := Heap.Extends.snoc m248 v247
  refine ⟨(((ext1.trans ext23).trans ext4).trans ext_snoc), hidx56, hcidx56,
    ⟨blkList.toArray⟩, cb, ms, ind, ct, blobs, v247,
    Hashed.mono hhash_blk (by rw [hc381]; intro c hc; simp [hc]),
    haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get, hct_get,
    hhp.sub (by rw [hc381]; intro c hc; simp [hc]),
    loadValue_snoc m248 v247,
    hraw.mono ext_snoc (fun _ hm => hm)⟩

/-- `Ingress::get_ci_rprj` specification under `Bounded calls`. -/
theorem get_ci_rprj_spec {b : Bytes.Address} {idx : F}
    {x_block_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hbounded : IxVM.Consistency.Bounded calls)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn W "Ingress::get_ci_rprj" [x_block_addr, .field idx] h r h' calls) :
    Heap.Extends h h' ∧ idx.val < 72057594037927936 ∧
      ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
        (rc : Ixon.Recursor) (blobs : List (_root_.Address × ByteArray)) (v : SourceValue F),
        Hashed calls blkBytes ∧
        Address.blake3Pure blkBytes = Core.ixAddr b ∧
        Ixon.deConstantExact blkBytes = .ok cb ∧
        Ixon.deConstant blkBytes = .ok cb ∧
        cb.info = .muts ms ∧
        ms.toList[idx.val]? = some (.recr rc) ∧
        HashedPairs calls blobs ∧
        loadValue h' r = .ok v ∧
        RawRecrValRep cb.refs.toList (blockRecurAddrs (Core.ixAddr b) ms.toList)
          cb.univs.toList cb.sharing.toList blobs h' rc (Core.ixAddr b) idx.val v := by
  obtain ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_members,
      m86, cs96, x_r, v136, m137, cs147, v166, m167, cs174,
      v184, v185, m236, cs244, m256, cs264,
      ev14, ev98, ev149, he170, hm169, ev246, ev266, ev176, hc283⟩ :=
    «Ingress::get_ci_rprj».obs ev
  obtain ⟨ext1, blkList, cb, hhash_blk, haddr_blk, hexact_blk, hde_blk,
      _, _, _, hbd32, _, cRep⟩ :=
    load_verified_constant_decode hb ev14
  obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
  rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
  subst infoVal shPtr rfPtr unPtr bdPtr
  have hmuts : ∃ ms : Array Ixon.MutConst,
      cb.info = .muts ms ∧ RepList mutConstListEnum RepMutConst m2 ms.toList x_members := by
    cases hci : cb.info <;> simp [RepConstantInfo, hci] at hinfo
    obtain ⟨msPtr, hms_eq, hms⟩ := hinfo
    subst msPtr
    exact ⟨_, rfl, hms⟩
  obtain ⟨ms, hcb_info, hms⟩ := hmuts
  obtain ⟨hm86, hidx_lt_ms, mc, hmc_get, hmc_rep⟩ := muts_member_at_spec hms ev98
  subst m86
  have hcall_muts : (⟨"Ingress::muts_member_at", [x_members, .field idx], m2⟩ : Call F) ∈ calls := by
    rw [hc283]; simp
  have hms_len39 : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbounded hcall_muts (by simp) hms
  have hidx56 : idx.val < 72057594037927936 := by omega
  have hrecr : ∃ rc : Ixon.Recursor, mc = .recr rc ∧ RepRecursor m2 rc x_r := by
    cases mc with
    | recr rc =>
      obtain ⟨rv, hrv_eq, hrv⟩ := hmc_rep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hrv_eq
      rcases hrv_eq with ⟨_, _, rfl⟩
      exact ⟨rc, rfl, hrv⟩
    | defn _ => obtain ⟨dv, hdv, _⟩ := hmc_rep; simp at hdv
    | indc _ => obtain ⟨iv, hiv, _⟩ := hmc_rep; simp at hiv
  obtain ⟨rc, rfl, hrc_rep⟩ := hrecr
  have hb2 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 hb
  obtain ⟨ext2, hrecs⟩ := build_recur_addrs_ixon_spec hms hb2 ev149
  obtain ⟨ext3, htbl⟩ := binder_table_spec (hbd.mono repBinderBlock_heapMono₂ ext2) hbd32 ev246
  have ext23 := ext2.trans ext3
  obtain ⟨_, _, hm256⟩ := muts_root_offset_spec (hms.mono repMutConst_heapMono₂ ext23) ev266
  subst m256
  have ev176' : ObsFn W "Convert::convert_recursor"
      [x_r, x_block_addr, .field ((idx.val : Nat) : F), x_sharing, x_refs, v136,
       x_univs, v184, v185] m236 v166 m167 cs174 := by
    rwa [ZMod.natCast_zmod_val idx]
  obtain ⟨ext4, blobs, hhp, hraw⟩ :=
    convert_recursor_spec
      (hrc_rep.mono ext23)
      ((core_to_repIxonAddressRef hb2).mono ext23)
      hidx56
      (RepShareVec.mono ext23 hsh)
      (hrf.mono repIxonAddressRef_heapMono₂ ext23)
      (hrecs.mono repIxonAddressRef_heapMono₂ ext3)
      (hun.mono repUnivPtr_heapMono₂ ext23)
      htbl ev176'
  rw [he170, hm169]
  have ext_snoc := Heap.Extends.snoc m167 v166
  refine ⟨(((ext1.trans ext23).trans ext4).trans ext_snoc), hidx56,
    ⟨blkList.toArray⟩, cb, ms, rc, blobs, v166,
    Hashed.mono hhash_blk (by rw [hc283]; intro c hc; simp [hc]),
    haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get,
    hhp.sub (by rw [hc283]; intro c hc; simp [hc]),
    loadValue_snoc m167 v166,
    hraw.mono ext_snoc (fun _ hm => hm)⟩

/-- Exact trace-level outcome of `Ingress::get_ci` on decoded constant `c` at address `a`,
capturing both the heap `KConstantInfo` cell at `r` and (for projection records) the hashed and
decoded parent mutual block `cb`. -/
def GetCIRawResult (calls : List (Call F)) (blobs : List (_root_.Address × ByteArray))
    (h : Heap F) (a : _root_.Address) (c : Ixon.Constant) (r : SourceValue F) : Prop :=
  match c.info with
  | .defn d =>
    ∃ v, loadValue h r = .ok v ∧
      RawDefnValRep c.refs.toList (defnRecurAddrs d a) c.univs.toList c.sharing.toList blobs h d v
  | .axio ax =>
    ∃ v, loadValue h r = .ok v ∧
      RawAxioValRep c.refs.toList [] c.univs.toList c.sharing.toList blobs h ax v
  | .quot q =>
    ∃ v, loadValue h r = .ok v ∧
      RawQuotValRep c.refs.toList [] c.univs.toList c.sharing.toList blobs h q v
  | .recr rc =>
    ∃ v, loadValue h r = .ok v ∧
      RawRecrValRep c.refs.toList [a] c.univs.toList c.sharing.toList blobs h rc a 0 v
  | .dPrj p =>
    p.idx.toNat < 72057594037927936 ∧
    ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (d : Ixon.Definition) (v : SourceValue F),
      Hashed calls blkBytes ∧
      Address.blake3Pure blkBytes = p.block ∧
      Ixon.deConstantExact blkBytes = .ok cb ∧
      Ixon.deConstant blkBytes = .ok cb ∧
      cb.info = .muts ms ∧
      ms.toList[p.idx.toNat]? = some (.defn d) ∧
      loadValue h r = .ok v ∧
      RawDefnValRep cb.refs.toList (defnMemberRecurAddrs d p.block ms.toList)
        cb.univs.toList cb.sharing.toList blobs h d v
  | .iPrj p =>
    p.idx.toNat < 72057594037927936 ∧
    ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (ind : Ixon.Inductive) (v : SourceValue F),
      Hashed calls blkBytes ∧
      Address.blake3Pure blkBytes = p.block ∧
      Ixon.deConstantExact blkBytes = .ok cb ∧
      Ixon.deConstant blkBytes = .ok cb ∧
      cb.info = .muts ms ∧
      ms.toList[p.idx.toNat]? = some (.indc ind) ∧
      loadValue h r = .ok v ∧
      RawInductValRep cb.refs.toList (blockRecurAddrs p.block ms.toList)
        cb.univs.toList cb.sharing.toList blobs h ind p.block p.idx.toNat v
  | .cPrj p =>
    p.idx.toNat < 72057594037927936 ∧ p.cidx.toNat < 72057594037927936 ∧
    ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (ind : Ixon.Inductive) (ct : Ixon.Constructor) (v : SourceValue F),
      Hashed calls blkBytes ∧
      Address.blake3Pure blkBytes = p.block ∧
      Ixon.deConstantExact blkBytes = .ok cb ∧
      Ixon.deConstant blkBytes = .ok cb ∧
      cb.info = .muts ms ∧
      ms.toList[p.idx.toNat]? = some (.indc ind) ∧
      ind.ctors.toList[p.cidx.toNat]? = some ct ∧
      loadValue h r = .ok v ∧
      RawCtorValRep cb.refs.toList (blockRecurAddrs p.block ms.toList)
        cb.univs.toList cb.sharing.toList blobs h ct p.block p.idx.toNat v
  | .rPrj p =>
    p.idx.toNat < 72057594037927936 ∧
    ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (rc : Ixon.Recursor) (v : SourceValue F),
      Hashed calls blkBytes ∧
      Address.blake3Pure blkBytes = p.block ∧
      Ixon.deConstantExact blkBytes = .ok cb ∧
      Ixon.deConstant blkBytes = .ok cb ∧
      cb.info = .muts ms ∧
      ms.toList[p.idx.toNat]? = some (.recr rc) ∧
      loadValue h r = .ok v ∧
      RawRecrValRep cb.refs.toList (blockRecurAddrs p.block ms.toList)
        cb.univs.toList cb.sharing.toList blobs h rc p.block p.idx.toNat v
  | .muts _ => False

/-- **`Ingress::get_ci` full specification**: loads and verifies `rawBytes` at `ixAddr a`, decodes
`c` (`deConstantExact rawBytes = .ok c`), hashes any literal blobs into `blobs`, and allocates the
converted `KConstantInfo` cell at `r` (loading the parent block `cb` when `c` is a projection). -/
theorem get_ci_spec {a : Bytes.Address} {x_addr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hbounded : IxVM.Consistency.Bounded calls)
    (ha : Bytes.RepAddressRef Core.addrTy h a x_addr)
    (ev : ObsFn W "Ingress::get_ci" [x_addr] h r h' calls) :
    Heap.Extends h h' ∧
      ∃ (rawBytes : ByteArray) (c : Ixon.Constant) (blobs : List (_root_.Address × ByteArray)),
        Hashed calls rawBytes ∧
        Address.blake3Pure rawBytes = Core.ixAddr a ∧
        Ixon.deConstantExact rawBytes = .ok c ∧
        Ixon.deConstant rawBytes = .ok c ∧
        ConstantTablesValid c ∧
        HashedPairs calls blobs ∧
        GetCIRawResult calls blobs h' (Core.ixAddr a) c r := by
  rcases «Ingress::get_ci».obs ev with
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, v85, m86, cs96, m116,
      x_kind, x_safety, w139, w140, w141, w142, m174, cs185,
      v215, m216, cs223, v232, m277, cs285,
      ev14, ev98, ev187, hm211, he219, hm218, ev287, ev225, hc302⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, v85, m86, cs96, m116,
      x_kind, x_safety, w139, w140, w141, w142, v173, m174, cs185, m324,
      v336, m337, cs344, v353, m398, cs406,
      ev14, ev98, ev187, hne303, hm310, hm332, he340, hm339, ev408, ev346, hc423⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_axio,
      v437, m438, cs445, v453, m476, m496, cs504,
      ev14, he441, hm440, hm484, ev506, ev447, hc515⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_quot,
      v528, m529, cs536, v544, m567, m587, cs595,
      ev14, he532, hm531, hm575, ev597, ev538, hc606⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_idx, x_block_addr, cs648,
      ev14, ev650, hc675⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_idx, x_block_addr, cs718,
      v722, m731, cs739, ev14, ev741, ev720, hc750⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_idx, x_cidx, x_block_addr, cs798,
      v802, v803, m812, cs820, m832, cs840, ev14, ev822, ev842, ev800, hc851⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_idx, x_block_addr, cs894,
      v898, m907, cs915, ev14, ev917, ev896, hc926⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_recr, m941, m965,
      v977, m978, cs985, v995, m1046, cs1054,
      ev14, hm951, hm973, he981, hm980, ev1056, ev987, hc1071⟩
  · -- `Defn_n0`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal shPtr rfPtr unPtr bdPtr
    let dv := Value.construct "Ixon::Definition" "Mk" [x_kind, x_safety, w139, w140, w141, w142]
    have hdefn : ∃ d : Ixon.Definition, c.info = .defn d ∧ RepDefinition m2 d dv := by
      cases hci : c.info <;> simp [RepConstantInfo, hci] at hinfo
      obtain ⟨dv', hdv_eq, hdv⟩ := hinfo
      subst dv'
      exact ⟨_, rfl, hdv⟩
    obtain ⟨d, hc_info, hd_rep⟩ := hdefn
    obtain ⟨_, _, hd_mk, _, _⟩ := hd_rep
    have hks : x_kind = repDefKindVal d.kind ∧ x_safety = repDefSafetyVal d.safety := by
      simp only [dv, Value.construct.injEq, List.cons.injEq, and_true] at hd_mk
      rcases hd_mk with ⟨_, _, hk_eq, hs_eq, _, _, _, _⟩
      exact ⟨hk_eq, hs_eq⟩
    have ext2 := ev98.heap_extends
    rw [hks.1, hks.2] at ev187
    obtain ⟨hf0, hm174⟩ := defn_is_unsafe_ci_spec (d := d) ev187
    subst m174
    have hfalse : defnIsUnsafeCI d = false := by
      cases hu : defnIsUnsafeCI d <;> simp [repBoolField, hu] at hf0
      rfl
    have ext3 : Heap.Extends m86 m116 := by rw [hm211]; exact Heap.Extends.snoc m86 _
    have hrecs : RepList addressListEnum RepIxonAddressRef m116
        (defnRecurAddrs d (Core.ixAddr a))
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m86.length) := by
      simp only [defnRecurAddrs, hfalse, Bool.false_eq_true, ↓reduceIte]
      rw [hm211, addressListEnum_eq]
      exact Lib.rep_store_nil m86
    have ext23 := ext2.trans ext3
    obtain ⟨ext4, htbl⟩ := binder_table_spec (hbd.mono repBinderBlock_heapMono₂ ext23) hbd32 ev287
    have ext24 := ext23.trans ext4
    obtain ⟨ext5, blobs, hhp, hraw⟩ :=
      convert_definition_spec
        (hd_rep.mono ext24)
        (RepShareVec.mono ext24 hsh)
        (hrf.mono repIxonAddressRef_heapMono₂ ext24)
        (hrecs.mono repIxonAddressRef_heapMono₂ ext4)
        (hun.mono repUnivPtr_heapMono₂ ext24)
        htbl ev225
    rw [he219, hm218]
    have ext_snoc := Heap.Extends.snoc m216 v215
    refine ⟨(((ext1.trans ext24).trans ext5).trans ext_snoc), ⟨rawList.toArray⟩, c, blobs,
      Hashed.mono hhash (by rw [hc302]; intro x hx; simp [hx]),
      haddr, hexact, hde, htables,
      hhp.sub (by rw [hc302]; intro x hx; simp [hx]), ?_⟩
    simp only [GetCIRawResult, hc_info]
    exact ⟨v215, loadValue_snoc m216 v215, hraw.mono ext_snoc (fun _ hm => hm)⟩
  · -- `Defn_other`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal shPtr rfPtr unPtr bdPtr
    let dv := Value.construct "Ixon::Definition" "Mk" [x_kind, x_safety, w139, w140, w141, w142]
    have hdefn : ∃ d : Ixon.Definition, c.info = .defn d ∧ RepDefinition m2 d dv := by
      cases hci : c.info <;> simp [RepConstantInfo, hci] at hinfo
      obtain ⟨dv', hdv_eq, hdv⟩ := hinfo
      subst dv'
      exact ⟨_, rfl, hdv⟩
    obtain ⟨d, hc_info, hd_rep⟩ := hdefn
    obtain ⟨_, _, hd_mk, _, _⟩ := hd_rep
    have hks : x_kind = repDefKindVal d.kind ∧ x_safety = repDefSafetyVal d.safety := by
      simp only [dv, Value.construct.injEq, List.cons.injEq, and_true] at hd_mk
      rcases hd_mk with ⟨_, _, hk_eq, hs_eq, _, _, _, _⟩
      exact ⟨hk_eq, hs_eq⟩
    have ext2 := ev98.heap_extends
    rw [hks.1, hks.2] at ev187
    obtain ⟨hv173, hm174⟩ := defn_is_unsafe_ci_spec (d := d) ev187
    subst m174
    have htrue : defnIsUnsafeCI d = true := by
      cases hu : defnIsUnsafeCI d
      · simp [repBoolField, hu] at hv173
        exact (hne303 hv173).elim
      · rfl
    have ext3a : Heap.Extends m86 m324 := by rw [hm332]; exact Heap.Extends.snoc m86 _
    have ext3b : Heap.Extends m324 m116 := by rw [hm310]; exact Heap.Extends.snoc m324 _
    have ext3 := ext3a.trans ext3b
    have hnil324 : RepList Names.«Lists::Node<&[Field; 32]>» RepIxonAddressRef m324 []
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m86.length) := by
      rw [hm332]; exact Lib.rep_store_nil m86
    have ha324 : RepIxonAddressRef m324 (Core.ixAddr a) x_addr :=
      (core_to_repIxonAddressRef ha).mono ((ext1.trans ext2).trans ext3a)
    have hrecs : RepList addressListEnum RepIxonAddressRef m116
        (defnRecurAddrs d (Core.ixAddr a))
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m324.length) := by
      simp only [defnRecurAddrs, htrue, ↓reduceIte]
      rw [hm310, addressListEnum_eq]
      exact Lib.rep_store_cons repIxonAddressRef_heapMono₂ ha324 hnil324
    have ext23 := ext2.trans ext3
    obtain ⟨ext4, htbl⟩ := binder_table_spec (hbd.mono repBinderBlock_heapMono₂ ext23) hbd32 ev408
    have ext24 := ext23.trans ext4
    obtain ⟨ext5, blobs, hhp, hraw⟩ :=
      convert_definition_spec
        (hd_rep.mono ext24)
        (RepShareVec.mono ext24 hsh)
        (hrf.mono repIxonAddressRef_heapMono₂ ext24)
        (hrecs.mono repIxonAddressRef_heapMono₂ ext4)
        (hun.mono repUnivPtr_heapMono₂ ext24)
        htbl ev346
    rw [he340, hm339]
    have ext_snoc := Heap.Extends.snoc m337 v336
    refine ⟨(((ext1.trans ext24).trans ext5).trans ext_snoc), ⟨rawList.toArray⟩, c, blobs,
      Hashed.mono hhash (by rw [hc423]; intro x hx; simp [hx]),
      haddr, hexact, hde, htables,
      hhp.sub (by rw [hc423]; intro x hx; simp [hx]), ?_⟩
    simp only [GetCIRawResult, hc_info]
    exact ⟨v336, loadValue_snoc m337 v336, hraw.mono ext_snoc (fun _ hm => hm)⟩
  · -- `Axio`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal shPtr rfPtr unPtr bdPtr
    have haxio : ∃ ax : Ixon.Axiom, c.info = .axio ax ∧ RepAxiom m2 ax x_axio := by
      cases hci : c.info <;> simp [RepConstantInfo, hci] at hinfo
      obtain ⟨av, hav_eq, hav⟩ := hinfo
      subst av
      exact ⟨_, rfl, hav⟩
    obtain ⟨ax, hc_info, hax_rep⟩ := haxio
    have ext2 : Heap.Extends m2 m476 := by rw [hm484]; exact Heap.Extends.snoc m2 _
    have hrecs : RepList addressListEnum RepIxonAddressRef m476 []
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m2.length) := by
      rw [hm484, addressListEnum_eq]
      exact Lib.rep_store_nil m2
    obtain ⟨ext3, htbl⟩ := binder_table_spec (hbd.mono repBinderBlock_heapMono₂ ext2) hbd32 ev506
    have ext23 := ext2.trans ext3
    obtain ⟨ext4, blobs, hhp, hraw⟩ :=
      convert_axiom_spec
        (hax_rep.mono ext23)
        (RepShareVec.mono ext23 hsh)
        (hrf.mono repIxonAddressRef_heapMono₂ ext23)
        (hrecs.mono repIxonAddressRef_heapMono₂ ext3)
        (hun.mono repUnivPtr_heapMono₂ ext23)
        htbl ev447
    rw [he441, hm440]
    have ext_snoc := Heap.Extends.snoc m438 v437
    refine ⟨(((ext1.trans ext23).trans ext4).trans ext_snoc), ⟨rawList.toArray⟩, c, blobs,
      Hashed.mono hhash (by rw [hc515]; intro x hx; simp [hx]),
      haddr, hexact, hde, htables,
      hhp.sub (by rw [hc515]; intro x hx; simp [hx]), ?_⟩
    simp only [GetCIRawResult, hc_info]
    exact ⟨v437, loadValue_snoc m438 v437, hraw.mono ext_snoc (fun _ hm => hm)⟩
  · -- `Quot`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal shPtr rfPtr unPtr bdPtr
    have hquot : ∃ q : Ixon.Quotient, c.info = .quot q ∧ RepQuotient m2 q x_quot := by
      cases hci : c.info <;> simp [RepConstantInfo, hci] at hinfo
      obtain ⟨qv, hqv_eq, hqv⟩ := hinfo
      subst qv
      exact ⟨_, rfl, hqv⟩
    obtain ⟨q, hc_info, hq_rep⟩ := hquot
    have ext2 : Heap.Extends m2 m567 := by rw [hm575]; exact Heap.Extends.snoc m2 _
    have hrecs : RepList addressListEnum RepIxonAddressRef m567 []
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m2.length) := by
      rw [hm575, addressListEnum_eq]
      exact Lib.rep_store_nil m2
    obtain ⟨ext3, htbl⟩ := binder_table_spec (hbd.mono repBinderBlock_heapMono₂ ext2) hbd32 ev597
    have ext23 := ext2.trans ext3
    obtain ⟨ext4, blobs, hhp, hraw⟩ :=
      convert_quotient_spec
        (hq_rep.mono ext23)
        (RepShareVec.mono ext23 hsh)
        (hrf.mono repIxonAddressRef_heapMono₂ ext23)
        (hrecs.mono repIxonAddressRef_heapMono₂ ext3)
        (hun.mono repUnivPtr_heapMono₂ ext23)
        htbl ev538
    rw [he532, hm531]
    have ext_snoc := Heap.Extends.snoc m529 v528
    refine ⟨(((ext1.trans ext23).trans ext4).trans ext_snoc), ⟨rawList.toArray⟩, c, blobs,
      Hashed.mono hhash (by rw [hc606]; intro x hx; simp [hx]),
      haddr, hexact, hde, htables,
      hhp.sub (by rw [hc606]; intro x hx; simp [hx]), ?_⟩
    simp only [GetCIRawResult, hc_info]
    exact ⟨v528, loadValue_snoc m529 v528, hraw.mono ext_snoc (fun _ hm => hm)⟩
  · -- `DPrj`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, _, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, _, _, _, _⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    have hdprj : ∃ p : Ixon.DefinitionProj, c.info = .dPrj p ∧
        x_idx = u64Value p.idx.toNat ∧ RepIxonAddressRef m2 p.block x_block_addr := by
      cases hci : c.info <;> simp [RepConstantInfo, hci] at hinfo
      obtain ⟨pv, hpv_eq, blkPtr, hmk, hblk⟩ := hinfo
      subst pv
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hmk
      rcases hmk with ⟨_, _, hidx_eq, hbp_eq⟩
      subst blkPtr
      exact ⟨_, rfl, hidx_eq, hblk⟩
    obtain ⟨p, hc_info, hx_idx, hblk_ix⟩ := hdprj
    obtain ⟨b, hb_eq, hb_rep⟩ := repIxonAddressRef_to_core hblk_ix
    obtain ⟨ext2, hidx56, blkBytes, cb, ms, d, blobs, v,
        hhash_blk, haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get, hhp, hld, hraw⟩ :=
      get_ci_dprj_spec p.idx.toNat_lt hx_idx hb_rep ev650
    rw [hb_eq] at haddr_blk hraw
    refine ⟨ext1.trans ext2, ⟨rawList.toArray⟩, c, blobs,
      Hashed.mono hhash (by rw [hc675]; intro x hx; simp [hx]),
      haddr, hexact, hde, htables,
      hhp.sub (by rw [hc675]; intro x hx; simp [hx]), ?_⟩
    simp only [GetCIRawResult, hc_info]
    exact ⟨hidx56, blkBytes, cb, ms, d, v,
      Hashed.mono hhash_blk (by rw [hc675]; intro x hx; simp [hx]),
      haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get, hld, hraw⟩
  · -- `IPrj`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, _, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, _, _, _, _⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    have hiprj : ∃ p : Ixon.InductiveProj, c.info = .iPrj p ∧
        x_idx = u64Value p.idx.toNat ∧ RepIxonAddressRef m2 p.block x_block_addr := by
      cases hci : c.info <;> simp [RepConstantInfo, hci] at hinfo
      obtain ⟨pv, hpv_eq, blkPtr, hmk, hblk⟩ := hinfo
      subst pv
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hmk
      rcases hmk with ⟨_, _, hidx_eq, hbp_eq⟩
      subst blkPtr
      exact ⟨_, rfl, hidx_eq, hblk⟩
    obtain ⟨p, hc_info, hx_idx, hblk_ix⟩ := hiprj
    subst x_idx
    obtain ⟨hidx56, hv722, hm731⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 p.idx) ev741
    subst v722 m731
    obtain ⟨b, hb_eq, hb_rep⟩ := repIxonAddressRef_to_core hblk_ix
    have hbounded718 : IxVM.Consistency.Bounded cs718 :=
      RomBound.bounded_mono hbounded (by rw [hc750]; intro x hx; simp [hx])
    obtain ⟨ext2, _, blkBytes, cb, ms, ind, blobs, v,
        hhash_blk, haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get, hhp, hld, hraw⟩ :=
      get_ci_iprj_spec hbounded718 hb_rep ev720
    rw [val_cast_u56_ing hidx56] at hmc_get hraw
    rw [hb_eq] at haddr_blk hraw
    refine ⟨ext1.trans ext2, ⟨rawList.toArray⟩, c, blobs,
      Hashed.mono hhash (by rw [hc750]; intro x hx; simp [hx]),
      haddr, hexact, hde, htables,
      hhp.sub (by rw [hc750]; intro x hx; simp [hx]), ?_⟩
    simp only [GetCIRawResult, hc_info]
    exact ⟨hidx56, blkBytes, cb, ms, ind, v,
      Hashed.mono hhash_blk (by rw [hc750]; intro x hx; simp [hx]),
      haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get, hld, hraw⟩
  · -- `CPrj`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, _, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, _, _, _, _⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    have hcprj : ∃ p : Ixon.ConstructorProj, c.info = .cPrj p ∧
        x_idx = u64Value p.idx.toNat ∧ x_cidx = u64Value p.cidx.toNat ∧
        RepIxonAddressRef m2 p.block x_block_addr := by
      cases hci : c.info <;> simp [RepConstantInfo, hci] at hinfo
      obtain ⟨pv, hpv_eq, blkPtr, hmk, hblk⟩ := hinfo
      subst pv
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hmk
      rcases hmk with ⟨_, _, hidx_eq, hcidx_eq, hbp_eq⟩
      subst blkPtr
      exact ⟨_, rfl, hidx_eq, hcidx_eq, hblk⟩
    obtain ⟨p, hc_info, hx_idx, hx_cidx, hblk_ix⟩ := hcprj
    subst x_idx x_cidx
    obtain ⟨hidx56, hv802, hm812⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 p.idx) ev822
    subst v802 m812
    obtain ⟨hcidx56, hv803, hm832⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 p.cidx) ev842
    subst v803 m832
    obtain ⟨b, hb_eq, hb_rep⟩ := repIxonAddressRef_to_core hblk_ix
    have hbounded798 : IxVM.Consistency.Bounded cs798 :=
      RomBound.bounded_mono hbounded (by rw [hc851]; intro x hx; simp [hx])
    obtain ⟨ext2, _, _, blkBytes, cb, ms, ind, ct, blobs, v,
        hhash_blk, haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get, hct_get, hhp, hld, hraw⟩ :=
      get_ci_cprj_spec hbounded798 hb_rep ev800
    rw [val_cast_u56_ing hidx56] at hmc_get hraw
    rw [val_cast_u56_ing hcidx56] at hct_get
    rw [hb_eq] at haddr_blk hraw
    refine ⟨ext1.trans ext2, ⟨rawList.toArray⟩, c, blobs,
      Hashed.mono hhash (by rw [hc851]; intro x hx; simp [hx]),
      haddr, hexact, hde, htables,
      hhp.sub (by rw [hc851]; intro x hx; simp [hx]), ?_⟩
    simp only [GetCIRawResult, hc_info]
    exact ⟨hidx56, hcidx56, blkBytes, cb, ms, ind, ct, v,
      Hashed.mono hhash_blk (by rw [hc851]; intro x hx; simp [hx]),
      haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get, hct_get, hld, hraw⟩
  · -- `RPrj`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, _, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, _, _, _, _⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    have hrprj : ∃ p : Ixon.RecursorProj, c.info = .rPrj p ∧
        x_idx = u64Value p.idx.toNat ∧ RepIxonAddressRef m2 p.block x_block_addr := by
      cases hci : c.info <;> simp [RepConstantInfo, hci] at hinfo
      obtain ⟨pv, hpv_eq, blkPtr, hmk, hblk⟩ := hinfo
      subst pv
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hmk
      rcases hmk with ⟨_, _, hidx_eq, hbp_eq⟩
      subst blkPtr
      exact ⟨_, rfl, hidx_eq, hblk⟩
    obtain ⟨p, hc_info, hx_idx, hblk_ix⟩ := hrprj
    subst x_idx
    obtain ⟨hidx56, hv898, hm907⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 p.idx) ev917
    subst v898 m907
    obtain ⟨b, hb_eq, hb_rep⟩ := repIxonAddressRef_to_core hblk_ix
    have hbounded894 : IxVM.Consistency.Bounded cs894 :=
      RomBound.bounded_mono hbounded (by rw [hc926]; intro x hx; simp [hx])
    obtain ⟨ext2, _, blkBytes, cb, ms, rc, blobs, v,
        hhash_blk, haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get, hhp, hld, hraw⟩ :=
      get_ci_rprj_spec hbounded894 hb_rep ev896
    rw [val_cast_u56_ing hidx56] at hmc_get hraw
    rw [hb_eq] at haddr_blk hraw
    refine ⟨ext1.trans ext2, ⟨rawList.toArray⟩, c, blobs,
      Hashed.mono hhash (by rw [hc926]; intro x hx; simp [hx]),
      haddr, hexact, hde, htables,
      hhp.sub (by rw [hc926]; intro x hx; simp [hx]), ?_⟩
    simp only [GetCIRawResult, hc_info]
    exact ⟨hidx56, blkBytes, cb, ms, rc, v,
      Hashed.mono hhash_blk (by rw [hc926]; intro x hx; simp [hx]),
      haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get, hld, hraw⟩
  · -- `Recr`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal shPtr rfPtr unPtr bdPtr
    have hrecr : ∃ rc : Ixon.Recursor, c.info = .recr rc ∧ RepRecursor m2 rc x_recr := by
      cases hci : c.info <;> simp [RepConstantInfo, hci] at hinfo
      obtain ⟨rv, hrv_eq, hrv⟩ := hinfo
      subst rv
      exact ⟨_, rfl, hrv⟩
    obtain ⟨rc, hc_info, hrc_rep⟩ := hrecr
    have ext2a : Heap.Extends m2 m965 := by rw [hm973]; exact Heap.Extends.snoc m2 _
    have ext2b : Heap.Extends m965 m941 := by rw [hm951]; exact Heap.Extends.snoc m965 _
    have ext2 := ext2a.trans ext2b
    have hnil965 : RepList Names.«Lists::Node<&[Field; 32]>» RepIxonAddressRef m965 []
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m2.length) := by
      rw [hm973]; exact Lib.rep_store_nil m2
    have ha965 : RepIxonAddressRef m965 (Core.ixAddr a) x_addr :=
      (core_to_repIxonAddressRef ha).mono (ext1.trans ext2a)
    have hrecs : RepList addressListEnum RepIxonAddressRef m941 [Core.ixAddr a]
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m965.length) := by
      rw [hm951, addressListEnum_eq]
      exact Lib.rep_store_cons repIxonAddressRef_heapMono₂ ha965 hnil965
    obtain ⟨ext3, htbl⟩ := binder_table_spec (hbd.mono repBinderBlock_heapMono₂ ext2) hbd32 ev1056
    have ext23 := ext2.trans ext3
    have ev987' : ObsFn W "Convert::convert_recursor"
        [x_recr, x_addr, .field ((0 : Nat) : F), x_sharing, x_refs,
         .ptr (.enum Names.«Lists::Node<&[Field; 32]>») m965.length,
         x_univs, v995, .field 0] m1046 v977 m978 cs985 := by
      simpa using ev987
    obtain ⟨ext4, blobs, hhp, hraw⟩ :=
      convert_recursor_spec
        (hrc_rep.mono ext23)
        ((core_to_repIxonAddressRef ha).mono (ext1.trans ext23))
        (by decide)
        (RepShareVec.mono ext23 hsh)
        (hrf.mono repIxonAddressRef_heapMono₂ ext23)
        (hrecs.mono repIxonAddressRef_heapMono₂ ext3)
        (hun.mono repUnivPtr_heapMono₂ ext23)
        htbl ev987'
    rw [he981, hm980]
    have ext_snoc := Heap.Extends.snoc m978 v977
    refine ⟨(((ext1.trans ext23).trans ext4).trans ext_snoc), ⟨rawList.toArray⟩, c, blobs,
      Hashed.mono hhash (by rw [hc1071]; intro x hx; simp [hx]),
      haddr, hexact, hde, htables,
      hhp.sub (by rw [hc1071]; intro x hx; simp [hx]), ?_⟩
    simp only [GetCIRawResult, hc_info]
    exact ⟨v977, loadValue_snoc m978 v977, hraw.mono ext_snoc (fun _ hm => hm)⟩

end IxVM.Refinement.L1
