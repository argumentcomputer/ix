import IxVMRefinement.Core.Registry
import IxVMRefinement.Lib.WordHints
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.L1.Blake3
import IxVMRefinement.Obs.Ingress0
import IxVMRefinement.Obs.KernelCheck9
import IxVMRefinement.Obs.IxonSerialize0
import IxVMRefinement.Obs.IxonSerialize1
import IxVMRefinement.Obs.IxonSerialize2
import IxC.Ixon.Verify.NonrecursiveConstant

/-! # Projection-record serialization and hashing

Step lemmas for the four projection-address functions of `Specs.Callees.Fn`:
* `Blake3::bytes_to_addr`: hashes a represented byte stream (`RepBytes`) under `Good` and stores
  its 32-byte BLAKE3 digest (`Address.blake3Pure`);
* `IxonSerialize::put_constant`: serializes a projection record with empty side tables
  (`ProjConstRep`) in front of a represented byte tail (`Ixon.serConstant`);
* `KernelCheck::projection_addr_ctor`: builds, serializes, and hashes the constructor-projection
  record `(i, j, block)` (`cprjAddr`);
* `Ingress::build_recur_addrs`: builds, serializes, and hashes the member-projection records of a
  mutual block in order (`projAddr (memberProjInfo ...)`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ProjAddrAux

/-! ## Field, word, and `ByteArray` arithmetic helpers -/

theorem val_natCast_small {m : Nat} (hm : m < 9223372036854775808) :
    ZMod.val (m : F) = m :=
  ZMod.val_natCast_of_lt (Nat.lt_of_lt_of_le hm (by decide))

theorem natCast_eq_zero_of_lt {m : Nat} (hm : m < 9223372036854775808)
    (h : (m : F) = 0) : m = 0 := by
  have hv := congrArg ZMod.val h
  rw [val_natCast_small hm, ZMod.val_zero] at hv
  exact hv

theorem add_field_inv {a b : F} {v : SourceValue F}
    (op : evalBinOp .add (.field a : SourceValue F) (.field b) = .ok v) :
    v = .field (a + b) := by
  simp only [evalBinOp, Except.ok.injEq] at op
  exact op.symm

theorem mul_field_inv {a b : F} {v : SourceValue F}
    (op : evalBinOp .mul (.field a : SourceValue F) (.field b) = .ok v) :
    v = .field (a * b) := by
  simp only [evalBinOp, Except.ok.injEq] at op
  exact op.symm

theorem sub_field_inv {a b : F} {v : SourceValue F}
    (op : evalBinOp .sub (.field a : SourceValue F) (.field b) = .ok v) :
    v = .field (a - b) := by
  simp only [evalBinOp, Except.ok.injEq] at op
  exact op.symm

theorem bytes_mk_toList (x : ByteArray) :
    (⟨(x.data.toList ++ []).toArray⟩ : ByteArray) = x := by
  cases x
  simp

@[simp] theorem data_toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  cases a; cases b
  simp

@[simp] theorem data_toList_singleton (b : UInt8) :
    ([b].toByteArray).data.toList = [b] := by
  rfl

@[simp] theorem data_toList_empty :
    ByteArray.empty.data.toList = [] := by
  rfl

theorem repBytes_cons {h h' : Heap F} {b : UInt8} {bs : List UInt8}
    {vb tl r : SourceValue F}
    (hvb : vb = .field (b.toNat : F))
    (htl : RepBytes h bs tl)
    (hh' : h' = h ++ [.construct byteListEnum "Cons" [vb, tl]])
    (hr : r = .ptr (.enum byteListEnum) h.length) :
    RepBytes h' (b :: bs) r := by
  subst hvb hh' hr
  exact Lib.rep_store_cons (fun _ hx => hx) rfl htl

/-! ## `UInt8::raw_add` and `WordLists::length_u64` on empty lists -/

theorem u8_raw_add_spec {a b : Nat} {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (ha : a < 256) (hb : b < 256)
    (ev : ObsFn W "UInt8::raw_add" [.field (a : F), .field (b : F)] h r h' cs) :
    r = .tuple [.field (((a + b) % 256 : Nat) : F), .field (((a + b) / 256 : Nat) : F)] ∧
      h' = h := by
  have hm := ev.erase.map_row Mirrors.«UInt8::raw_add».none
  simp only [mapCall, TagN.rawAdd_row ha hb, Constant.toValue, Value.mapAddress,
    List.map, Option.some.injEq, Prod.mk.injEq] at hm
  exact ⟨hm.1.symm, hm.2.symm⟩

theorem length_u64_nil_spec {α : Type} {t_T : Generic.Ty}
    {R : Heap F → α → SourceValue F → Prop} {x_list r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W (Instance.mk "WordLists::length_u64" [t_T]).symbol [x_list] h r h' calls)
    (hl : RepList (Instance.mk "Lists::Node" [t_T]).symbol R h [] x_list) :
    r = TagN.u64Value 0 ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) (Mirrors.«WordLists::length_u64».lookup t_T)
    (by simp [IxVM.WordLists.length_u64, ControlLower.hasControl]) ev
  simp only [IxVM.WordLists.length_u64] at d0
  obtain ⟨v1, m2, bs3, body4, c5, c6, d7, sel8, d9, rfl⟩ := d0.matchValue_inv
  obtain ⟨p10, d11, ld12⟩ := d7.load_inv
  obtain ⟨l13, rfl, rfl⟩ := d11.var_inv
  simp at l13
  subst l13
  rcases selectArm_cons_inv sel8 with ⟨mt14, rfl⟩ | ⟨-, sel16⟩
  · obtain ⟨vs17, hv18, -, ml19⟩ := matchPattern_construct_inv mt14
    rw [constructorName_named, instanceName_some_one, subst_param_singleton] at hv18
    subst hv18
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml19
    obtain ⟨w, dw, rfl⟩ := d9.repeat_inv
    have hc0 : W.constant "UInt8::BYTE_0" (Generic.Ty.field.subst [("T", t_T)]) =
        .ok (.literal 0) := Obs.Names.c9173999864893739538
    obtain ⟨rfl, rfl, rfl⟩ := dw.global_literal_inv hc0
    exact ⟨rfl, rfl⟩
  · rcases selectArm_cons_inv sel16 with ⟨mt24, rfl⟩ | ⟨-, sel26⟩
    · obtain ⟨vs27, hv28, -, ml29⟩ := matchPattern_construct_inv mt24
      rw [constructorName_named, instanceName_some_one, subst_param_singleton] at hv28
      subst hv28
      obtain ⟨w30, vs32, b33, b34, rfl, mt35, ml36, rfl⟩ := matchListWith_cons_inv ml29
      obtain rfl := matchPattern_wildcard_inv mt35
      obtain ⟨w31, vs37, b38, b39, rfl, mt40, ml41, rfl⟩ := matchListWith_cons_inv ml36
      obtain rfl := matchPattern_bind_inv mt40
      obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml41
      obtain ⟨z, zs, he, -, -⟩ := Lib.rep_cons_of_load hl ld12
      cases he
    · exact (selectArm_nil_inv sel26).elim

/-! ## `IxonSerialize::put_u64_le` and TagN writers -/

theorem toUInt64_shift8 {d : Nat} (hd : d < 18446744073709551616) :
    d.toUInt64 >>> 8 = (d / 256).toUInt64 := by
  apply UInt64.eq_of_toNat_eq
  have hd' : d / 256 < 18446744073709551616 := by omega
  simp [Nat.toUInt64, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd']

theorem toUInt64_lowByte {d : Nat} (hd : d < 18446744073709551616) :
    d.toUInt64.toUInt8.toNat = d % 256 := by
  simp [Nat.toUInt64, UInt64.toUInt8, UInt8.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt hd]

theorem u64Value_shift8 {d : Nat} (hd : d < 18446744073709551616) :
    (.tuple [
      .field ((d / 256 % 256 : Nat) : F),
      .field ((d / 65536 % 256 : Nat) : F),
      .field ((d / 16777216 % 256 : Nat) : F),
      .field ((d / 4294967296 % 256 : Nat) : F),
      .field ((d / 1099511627776 % 256 : Nat) : F),
      .field ((d / 281474976710656 % 256 : Nat) : F),
      .field ((d / 72057594037927936 % 256 : Nat) : F),
      .field 0] : SourceValue F) = TagN.u64Value (d / 256) := by
  have f1 : d / 256 / 256 % 256 = d / 65536 % 256 := by omega
  have f2 : d / 256 / 65536 % 256 = d / 16777216 % 256 := by omega
  have f3 : d / 256 / 16777216 % 256 = d / 4294967296 % 256 := by omega
  have f4 : d / 256 / 4294967296 % 256 = d / 1099511627776 % 256 := by omega
  have f5 : d / 256 / 1099511627776 % 256 = d / 281474976710656 % 256 := by omega
  have f6 : d / 256 / 281474976710656 % 256 = d / 72057594037927936 % 256 := by omega
  have f7 : d / 256 / 72057594037927936 % 256 = 0 := by omega
  simp only [TagN.u64Value, f1, f2, f3, f4, f5, f6, f7, Nat.cast_zero]

theorem put_u64_le_spec :
    ∀ (k : Nat) {d : Nat} {x_rest r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)} {rest : List UInt8},
      k ≤ 8 → d < 18446744073709551616 →
      ObsFn W "IxonSerialize::put_u64_le" [TagN.u64Value d, .field (k : F), x_rest]
        h r h' calls →
      RepBytes h rest x_rest →
      RepBytes h' ((Ixon.Verify.Codec.trimmedBytes d.toUInt64 k).data.toList ++ rest) r := by
  intro k
  induction k with
  | zero =>
    intro d x_rest r h h' calls rest _ _ ev hrest
    cases Obs.«IxonSerialize::put_u64_le».obs ev with
    | n0 _ hr hh _ =>
      subst hr hh
      simpa [Ixon.Verify.Codec.trimmedBytes] using hrest
    | other _ _ _ _ _ _ _ _ _ _ _ _ hne _ _ _ _ _ _ =>
      exact absurd (by simp) hne
  | succ k ih =>
    intro d x_rest r h h' calls rest hk hd ev hrest
    cases Obs.«IxonSerialize::put_u64_le».obs ev with
    | n0 hv _ _ _ =>
      have hk0 := natCast_eq_zero_of_lt (m := k + 1) (by omega) (Value.field.inj hv)
      omega
    | other x_b1 x_b2 x_b3 x_b4 x_b5 x_b6 x_b7 x_b8 v157 m166 cs174 v178 _ hv33 he152 hm151
        op200 ev176 _ =>
      simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hv33
      rcases hv33 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [u64Value_shift8 hd] at ev176
      have hv178 : v178 = .field (k : F) := by
        rw [Lib.sub_one_inv op200]
        push_cast
        ring_nf
      rw [hv178] at ev176
      have hrec := ih (d := d / 256) (by omega) (by omega) ev176 hrest
      have hb1 : (.field ((d % 256 : Nat) : F) : SourceValue F) =
          .field (d.toUInt64.toUInt8.toNat : F) := by
        rw [toUInt64_lowByte hd]
      have hcons := repBytes_cons hb1 hrec hm151 he152
      simpa [Ixon.Verify.Codec.trimmedBytes, toUInt64_shift8 hd] using hcons

theorem put_tagn_wide_c3 {d : Nat} {x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hd : d < 18446744073709551616)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 3, TagN.u64Value d, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      (((195 : UInt8) :: (Ixon.Verify.Codec.trimmedBytes d.toUInt64 8).data.toList) ++ rest) r := by
  cases Obs.«IxonSerialize::put_tagn_wide».obs ev with
  | n0_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n0_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n2_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n2_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n3 _ _ _ _ _ _ _ _ v1080 v1081 m1083 _ v1094 m1111 _ _ _ _ _ _ he1076 hm1075 op1108 ev1093
      ev1121 _ =>
    have hv1094 : v1094 = .field 195 := by
      rw [add_field_inv op1108]; norm_num
    rw [hv1094] at ev1093
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev1093
    have hle := put_u64_le_spec 8 (by omega) hd ev1121 hrest
    have hb : (.field 195 : SourceValue F) = .field ((195 : UInt8).toNat : F) := by norm_num
    simpa using repBytes_cons hb hle hm1075 he1076

theorem put_tagn_wide_c2 {d : Nat} {x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hd : d < 18446744073709551616)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 2, TagN.u64Value d, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((if d < 4294967296 then
          (194 : UInt8) :: (Ixon.Verify.Codec.trimmedBytes d.toUInt64 4).data.toList
        else
          (195 : UInt8) ::
            (Ixon.Verify.Codec.trimmedBytes (d - 4294967296).toUInt64 8).data.toList) ++ rest) r := by
  cases Obs.«IxonSerialize::put_tagn_wide».obs ev with
  | n0_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n0_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne _ _ _ _ _ _ _ =>
    exact absurd rfl hne
  | n2_n0 _ _ _ _ x_d4 x_d5 x_d6 x_d7 m758 x766 y767 m768 x774 y775 m776 x782 y783 m784 _ _ _ _
      v858 v859 m861 _ v872 m889 _ hv11 _ _ _ ev795 ev809 op789 ev823 op781 ev837 op773 he854
      hm853 op886 ev871 ev899 _ =>
    have hv11' := hv11
    simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨-, -, -, -, rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev795
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev809
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev823
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev837
    have hx774 := add_field_inv op789
    subst hx774
    have hx766 := add_field_inv op781
    subst hx766
    have hsumF := Value.field.inj (add_field_inv op773).symm
    have hsum0 : d / 4294967296 % 256 + d / 1099511627776 % 256 +
        d / 281474976710656 % 256 + d / 72057594037927936 % 256 = 0 := by
      apply natCast_eq_zero_of_lt (by omega)
      push_cast
      exact hsumF
    have hd_lt : d < 4294967296 := by
      have := Lib.leBytes8_bytes hd
      unfold Lib.leBytes8 at this
      omega
    rw [ite_eq_left hd_lt]
    have hv872 : v872 = .field 194 := by rw [add_field_inv op886]; norm_num
    rw [hv872] at ev871
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev871
    have hle := put_u64_le_spec 4 (by omega) hd ev899 hrest
    have hb : (.field 194 : SourceValue F) = .field ((194 : UInt8).toNat : F) := by norm_num
    simpa using repBytes_cons hb hle hm853 he854
  | n2_other _ _ _ _ x_d4 x_d5 x_d6 x_d7 v757 m758 x766 y767 m768 x774 y775 m776 x782 y783 m784
      _ _ _ _ m929 _ x_next w1018 _ hv11 _ _ _ ev795 ev809 op789 ev823 op781 ev837 op773 hne924
      ev941 ev1034 _ =>
    have hv11' := hv11
    simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨-, -, -, -, rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev795
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev809
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev823
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev837
    have hx774 := add_field_inv op789
    subst hx774
    have hx766 := add_field_inv op781
    subst hx766
    have hv757 := add_field_inv op773
    subst hv757
    have hd_ge : ¬ d < 4294967296 := by
      intro hlt
      apply hne924
      have h0 : d / 4294967296 % 256 = 0 ∧ d / 1099511627776 % 256 = 0 ∧
          d / 281474976710656 % 256 = 0 ∧ d / 72057594037927936 % 256 = 0 := by omega
      rcases h0 with ⟨e1, e2, e3, e4⟩
      simp [e1, e2, e3, e4]
    rw [ite_eq_right hd_ge]
    let subVal : Nat := Lib.leBytes8 0 0 0 0 255 255 255 255
    have hsub_val : subVal = 18446744069414584320 := by decide
    have hsub_lt : subVal < 18446744073709551616 := by rw [hsub_val]; omega
    have hsub_tup : (.tuple [.field 0, .field 0, .field 0, .field 0,
        .field 255, .field 255, .field 255, .field 255] : SourceValue F) =
        TagN.u64Value subVal := by
      simpa [subVal] using (Lib.u64Value_leBytes8 (F := F)
        (b0 := 0) (b1 := 0) (b2 := 0) (b3 := 0) (b4 := 255) (b5 := 255) (b6 := 255) (b7 := 255)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
    rw [hsub_tup] at ev941
    have hd_rep := Lib.repU64_ofNatLT h hd
    have hsub_rep := Lib.repU64_ofNatLT h hsub_lt
    obtain ⟨hadd, rfl⟩ := Lib.u64_add_spec hd_rep hsub_rep ev941
    simp only [Value.tuple.injEq, List.cons.injEq, and_true, UInt64.toNat_ofNatLT] at hadd
    rcases hadd with ⟨hx_next, -⟩
    have hmod : (d + subVal) % 18446744073709551616 = d - 4294967296 := by
      rw [hsub_val]; omega
    rw [hmod] at hx_next
    subst hx_next
    exact put_tagn_wide_c3 (by omega) ev1034 hrest

theorem put_tagn_wide_c1 {d : Nat} {x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hd : d < 18446744073709551616)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 1, TagN.u64Value d, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((if d < 16777216 then
          (193 : UInt8) :: (Ixon.Verify.Codec.trimmedBytes d.toUInt64 3).data.toList
        else if d - 16777216 < 4294967296 then
          (194 : UInt8) ::
            (Ixon.Verify.Codec.trimmedBytes (d - 16777216).toUInt64 4).data.toList
        else
          (195 : UInt8) ::
            (Ixon.Verify.Codec.trimmedBytes (d - 16777216 - 4294967296).toUInt64 8).data.toList) ++
        rest) r := by
  cases Obs.«IxonSerialize::put_tagn_wide».obs ev with
  | n0_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n0_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    have := Value.field.inj hv; norm_num at this
  | n2_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd rfl hne
  | n2_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd rfl hne
  | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne _ _ _ _ _ _ _ _ =>
    exact absurd rfl hne
  | n1_n0 _ _ _ x_d3 x_d4 x_d5 x_d6 x_d7 m421 x429 y430 m431 x437 y438 m439 x445 y446 m447 x453
      y454 m455 _ _ _ _ _ v543 v544 m546 _ v557 m574 _ hv11 _ _ ev466 ev480 op460 ev494 op452
      ev508 op444 ev522 op436 he539 hm538 op571 ev556 ev584 _ =>
    have hv11' := hv11
    simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨-, -, -, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev466
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev480
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev494
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev508
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev522
    have hx445 := add_field_inv op460; subst hx445
    have hx437 := add_field_inv op452; subst hx437
    have hx429 := add_field_inv op444; subst hx429
    have hsumF := Value.field.inj (add_field_inv op436).symm
    have hsum0 : d / 16777216 % 256 + d / 4294967296 % 256 + d / 1099511627776 % 256 +
        d / 281474976710656 % 256 + d / 72057594037927936 % 256 = 0 := by
      apply natCast_eq_zero_of_lt (by omega)
      push_cast
      exact hsumF
    have hd_lt : d < 16777216 := by
      have := Lib.leBytes8_bytes hd
      unfold Lib.leBytes8 at this
      omega
    rw [ite_eq_left hd_lt]
    have hv557 : v557 = .field 193 := by rw [add_field_inv op571]; norm_num
    rw [hv557] at ev556
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev556
    have hle := put_u64_le_spec 3 (by omega) hd ev584 hrest
    have hb : (.field 193 : SourceValue F) = .field ((193 : UInt8).toNat : F) := by norm_num
    simpa using repBytes_cons hb hle hm538 he539
  | n1_other _ _ _ x_d3 x_d4 x_d5 x_d6 x_d7 v420 m421 x429 y430 m431 x437 y438 m439 x445 y446
      m447 x453 y454 m455 _ _ _ _ _ m614 _ x_next w703 _ hv11 _ _ ev466 ev480 op460 ev494 op452
      ev508 op444 ev522 op436 hne609 ev626 ev719 _ =>
    have hv11' := hv11
    simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨-, -, -, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev466
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev480
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev494
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev508
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev522
    have hx445 := add_field_inv op460; subst hx445
    have hx437 := add_field_inv op452; subst hx437
    have hx429 := add_field_inv op444; subst hx429
    have hv420 := add_field_inv op436; subst hv420
    have hd_ge : ¬ d < 16777216 := by
      intro hlt
      apply hne609
      have h0 : d / 16777216 % 256 = 0 ∧ d / 4294967296 % 256 = 0 ∧
          d / 1099511627776 % 256 = 0 ∧ d / 281474976710656 % 256 = 0 ∧
          d / 72057594037927936 % 256 = 0 := by omega
      rcases h0 with ⟨e1, e2, e3, e4, e5⟩
      simp [e1, e2, e3, e4, e5]
    rw [ite_eq_right hd_ge]
    let subVal : Nat := Lib.leBytes8 0 0 0 255 255 255 255 255
    have hsub_val : subVal = 18446744073692774400 := by decide
    have hsub_lt : subVal < 18446744073709551616 := by rw [hsub_val]; omega
    have hsub_tup : (.tuple [.field 0, .field 0, .field 0, .field 255,
        .field 255, .field 255, .field 255, .field 255] : SourceValue F) =
        TagN.u64Value subVal := by
      simpa [subVal] using (Lib.u64Value_leBytes8 (F := F)
        (b0 := 0) (b1 := 0) (b2 := 0) (b3 := 255) (b4 := 255) (b5 := 255) (b6 := 255) (b7 := 255)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
    rw [hsub_tup] at ev626
    have hd_rep := Lib.repU64_ofNatLT h hd
    have hsub_rep := Lib.repU64_ofNatLT h hsub_lt
    obtain ⟨hadd, rfl⟩ := Lib.u64_add_spec hd_rep hsub_rep ev626
    simp only [Value.tuple.injEq, List.cons.injEq, and_true, UInt64.toNat_ofNatLT] at hadd
    rcases hadd with ⟨hx_next, -⟩
    have hmod : (d + subVal) % 18446744073709551616 = d - 16777216 := by
      rw [hsub_val]; omega
    rw [hmod] at hx_next
    subst hx_next
    exact put_tagn_wide_c2 (by omega) ev719 hrest

theorem put_tagn_wide_c0 {d : Nat} {x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hd : d < 18446744073709551616)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 0, TagN.u64Value d, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((if d < 65536 then
          (192 : UInt8) :: (Ixon.Verify.Codec.trimmedBytes d.toUInt64 2).data.toList
        else if d - 65536 < 16777216 then
          (193 : UInt8) ::
            (Ixon.Verify.Codec.trimmedBytes (d - 65536).toUInt64 3).data.toList
        else if d - 65536 - 16777216 < 4294967296 then
          (194 : UInt8) ::
            (Ixon.Verify.Codec.trimmedBytes (d - 65536 - 16777216).toUInt64 4).data.toList
        else
          (195 : UInt8) ::
            (Ixon.Verify.Codec.trimmedBytes
              (d - 65536 - 16777216 - 4294967296).toUInt64 8).data.toList) ++ rest) r := by
  cases Obs.«IxonSerialize::put_tagn_wide».obs ev with
  | n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd rfl hne
  | n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd rfl hne
  | n2_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd rfl hne
  | n2_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd rfl hne
  | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hne _ _ _ _ _ _ _ _ _ =>
    exact absurd rfl hne
  | n0_n0 _ _ x_d2 x_d3 x_d4 x_d5 x_d6 x_d7 m70 x78 y79 m80 x86 y87 m88 x94 y95 m96 x102 y103
      m104 x110 y111 m112 _ _ _ _ _ _ v214 v215 m217 _ m237 _ hv11 _ ev123 ev137 op117 ev151
      op109 ev165 op101 ev179 op93 ev193 op85 he210 hm209 ev227 ev247 _ =>
    have hv11' := hv11
    simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨-, -, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev123
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev137
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev151
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev165
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev179
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev193
    have hx102 := add_field_inv op117; subst hx102
    have hx94 := add_field_inv op109; subst hx94
    have hx86 := add_field_inv op101; subst hx86
    have hx78 := add_field_inv op93; subst hx78
    have hsumF := Value.field.inj (add_field_inv op85).symm
    have hsum0 : d / 65536 % 256 + d / 16777216 % 256 + d / 4294967296 % 256 +
        d / 1099511627776 % 256 + d / 281474976710656 % 256 +
        d / 72057594037927936 % 256 = 0 := by
      apply natCast_eq_zero_of_lt (by omega)
      push_cast
      exact hsumF
    have hd_lt : d < 65536 := by
      have := Lib.leBytes8_bytes hd
      unfold Lib.leBytes8 at this
      omega
    rw [ite_eq_left hd_lt]
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev227
    have hle := put_u64_le_spec 2 (by omega) hd ev247 hrest
    have hb : (.field 192 : SourceValue F) = .field ((192 : UInt8).toNat : F) := by norm_num
    simpa using repBytes_cons hb hle hm209 he210
  | n0_other _ _ x_d2 x_d3 x_d4 x_d5 x_d6 x_d7 v69 m70 x78 y79 m80 x86 y87 m88 x94 y95 m96
      x102 y103 m104 x110 y111 m112 _ _ _ _ _ _ m277 _ x_next w366 _ hv11 _ ev123 ev137 op117
      ev151 op109 ev165 op101 ev179 op93 ev193 op85 hne272 ev289 ev382 _ =>
    have hv11' := hv11
    simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨-, -, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev123
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev137
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev151
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev165
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev179
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev193
    have hx102 := add_field_inv op117; subst hx102
    have hx94 := add_field_inv op109; subst hx94
    have hx86 := add_field_inv op101; subst hx86
    have hx78 := add_field_inv op93; subst hx78
    have hv69 := add_field_inv op85; subst hv69
    have hd_ge : ¬ d < 65536 := by
      intro hlt
      apply hne272
      have h0 : d / 65536 % 256 = 0 ∧ d / 16777216 % 256 = 0 ∧ d / 4294967296 % 256 = 0 ∧
          d / 1099511627776 % 256 = 0 ∧ d / 281474976710656 % 256 = 0 ∧
          d / 72057594037927936 % 256 = 0 := by omega
      rcases h0 with ⟨e1, e2, e3, e4, e5, e6⟩
      simp [e1, e2, e3, e4, e5, e6]
    rw [ite_eq_right hd_ge]
    let subVal : Nat := Lib.leBytes8 0 0 255 255 255 255 255 255
    have hsub_val : subVal = 18446744073709486080 := by decide
    have hsub_lt : subVal < 18446744073709551616 := by rw [hsub_val]; omega
    have hsub_tup : (.tuple [.field 0, .field 0, .field 255, .field 255,
        .field 255, .field 255, .field 255, .field 255] : SourceValue F) =
        TagN.u64Value subVal := by
      simpa [subVal] using (Lib.u64Value_leBytes8 (F := F)
        (b0 := 0) (b1 := 0) (b2 := 255) (b3 := 255) (b4 := 255) (b5 := 255) (b6 := 255) (b7 := 255)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
    rw [hsub_tup] at ev289
    have hd_rep := Lib.repU64_ofNatLT h hd
    have hsub_rep := Lib.repU64_ofNatLT h hsub_lt
    obtain ⟨hadd, rfl⟩ := Lib.u64_add_spec hd_rep hsub_rep ev289
    simp only [Value.tuple.injEq, List.cons.injEq, and_true, UInt64.toNat_ofNatLT] at hadd
    rcases hadd with ⟨hx_next, -⟩
    have hmod : (d + subVal) % 18446744073709551616 = d - 65536 := by
      rw [hsub_val]; omega
    rw [hmod] at hx_next
    subst hx_next
    exact put_tagn_wide_c1 (by omega) ev382 hrest

theorem put_tagn_tail_zero_spec {w : UInt64} {x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hw128 : ¬ w.toNat < 128)
    (ev : ObsFn W "IxonSerialize::put_tagn_tail"
      [.field 0, .field 64, TagN.u64Value w.toNat, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((Ixon.Verify.Codec.tag0Bytes w).data.toList ++ rest) r := by
  have hw_lt := Lib.u64_toNat_lt w
  let subVal : Nat := Lib.leBytes8 128 191 255 255 255 255 255 255
  have hsub_val : subVal = 18446744073709535104 := by decide
  have hsub_lt : subVal < 18446744073709551616 := by rw [hsub_val]; omega
  have hsub_tup : (.tuple [.field 128, .field 191, .field 255, .field 255,
      .field 255, .field 255, .field 255, .field 255] : SourceValue F) =
      TagN.u64Value subVal := by
    simpa [subVal] using (Lib.u64Value_leBytes8 (F := F)
      (b0 := 128) (b1 := 191) (b2 := 255) (b3 := 255) (b4 := 255) (b5 := 255) (b6 := 255) (b7 := 255)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
  cases Obs.«IxonSerialize::put_tagn_tail».obs ev with
  | n0 m2 _ v32 v33 m41 _ v52 y60 m77 _ v88 x_d x_at_least_r2 m154 _ m181 _ v194 v195 m197 _
      v208 y226 x_lo x_no_borrow v255 x263 m265 x271 y272 m273 _ v285 _ v318 m321 _ v332 x339
      y348 m367 op74 op66 ev51 op102 ev87 ev14 ev167 pr217 ev207 op240 op232 ev193 pr294 ev284
      ev301 op278 op270 he314 hm313 op363 op354 op346 ev331 hm375 _ =>
    have hy60 : y60 = .field 128 := by rw [mul_field_inv op74]; norm_num
    subst hy60
    have hv52 : v52 = .field 128 := by rw [sub_field_inv op66]; norm_num
    subst hv52
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev51
    have hv88 : v88 = .field 191 := by rw [sub_field_inv op102]; norm_num
    subst hv88
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev87
    rw [hsub_tup] at ev14
    have hw_rep := Lib.repU64_ofNatLT h hw_lt
    have hsub_rep := Lib.repU64_ofNatLT h hsub_lt
    obtain ⟨hadd, rfl⟩ := Lib.u64_add_spec hw_rep hsub_rep ev14
    simp only [Value.tuple.injEq, List.cons.injEq, and_true, UInt64.toNat_ofNatLT] at hadd
    rcases hadd with ⟨-, hcarry⟩
    subst hcarry
    obtain ⟨hcF, rfl⟩ := Lib.u8_to_field_spec ev167
    have hdiv0 : (w.toNat + subVal) / 18446744073709551616 = 0 :=
      natCast_eq_zero_of_lt (by rw [hsub_val]; omega) (Value.field.inj hcF)
    have hw_r2 : w.toNat < 16512 := by rw [hsub_val] at hdiv0; omega
    have hp0 : projectValue (TagN.u64Value w.toNat : SourceValue F) 0 =
        .ok (.field ((w.toNat % 256 : Nat) : F)) := rfl
    have hv208 := Except.ok.inj (hp0.symm.trans pr217)
    subst hv208
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev207
    have hy226 : y226 = .field 128 := by rw [mul_field_inv op240]; norm_num
    subst hy226
    have hv195 : v195 = .field ((128 : Nat) : F) := by rw [sub_field_inv op232]; norm_num
    subst hv195
    obtain ⟨hraw, rfl⟩ := u8_raw_add_spec (a := w.toNat % 256) (b := 128) (by omega) (by omega) ev193
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hraw
    rcases hraw with ⟨rfl, rfl⟩
    have hp1 : projectValue (TagN.u64Value w.toNat : SourceValue F) 1 =
        .ok (.field ((w.toNat / 256 % 256 : Nat) : F)) := rfl
    have hv285 := Except.ok.inj (hp1.symm.trans pr294)
    subst hv285
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev284
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev301
    have hx263 := add_field_inv op278; subst hx263
    have hv255 := sub_field_inv op270; subst hv255
    have hy348 : y348 = .field 128 := by rw [mul_field_inv op363]; norm_num
    subst hy348
    have hx339 : x339 = .field 128 := by rw [add_field_inv op354]; norm_num
    subst hx339
    have hv332 := add_field_inv op346; subst hv332
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev331
    have hhi_arith : w.toNat / 256 % 256 + (w.toNat % 256 + 128) / 256 =
        1 + (w.toNat - 128) / 256 := by omega
    have hlo_arith : (w.toNat % 256 + 128) % 256 = (w.toNat - 128) % 256 := by omega
    have hlo_b : (.field (((w.toNat % 256 + 128) % 256 : Nat) : F) : SourceValue F) =
        .field ((((w.toNat - 128) % 256).toUInt8).toNat : F) := by
      rw [hlo_arith]
      simp [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (show (w.toNat - 128) % 256 < 256 by omega)]
    have hhi_b : (.field (128 + (((w.toNat / 256 % 256 : Nat) : F) +
        (((w.toNat % 256 + 128) / 256 : Nat) : F) - 1)) : SourceValue F) =
        .field (((Ixon.tagNHeader 0 0 (128 + (w.toNat - 128) / 256)).toNat) : F) := by
      have hdr_eq : (Ixon.tagNHeader 0 0 (128 + (w.toNat - 128) / 256)).toNat =
          128 + (w.toNat - 128) / 256 := by
        simp [Ixon.tagNHeader, Nat.toUInt8, UInt8.toNat_ofNat',
          Nat.mod_eq_of_lt (show 128 + (w.toNat - 128) / 256 < 256 by omega)]
      rw [hdr_eq]
      congr 1
      have hcast : (((w.toNat / 256 % 256 : Nat) : F) +
          (((w.toNat % 256 + 128) / 256 : Nat) : F) - 1) =
          (((w.toNat - 128) / 256 : Nat) : F) := by
        have := congrArg (Nat.cast (R := F)) hhi_arith
        push_cast at this
        linear_combination this
      rw [hcast]
      push_cast
      ring
    have hstep1 := repBytes_cons hlo_b hrest hm375 rfl
    have hstep2 := repBytes_cons hhi_b hstep1 hm313 he314
    have he1 : Ixon.tagNEnd1 0 = 128 := rfl
    have he2 : Ixon.tagNEnd2 0 = 16512 := rfl
    simpa [Ixon.Verify.Codec.tag0Bytes, Ixon.Verify.Codec.tagNBytes, he1, he2, hw128, hw_r2]
      using hstep2
  | n1 m2 _ v32 v33 m41 _ v52 y60 m77 _ v88 x_d x_at_least_r2 m154 _ _ v407 y418 op74 op66 ev51
      op102 ev87 ev14 ev167 op433 op424 ev406 _ =>
    have hy60 : y60 = .field 128 := by rw [mul_field_inv op74]; norm_num
    subst hy60
    have hv52 : v52 = .field 128 := by rw [sub_field_inv op66]; norm_num
    subst hv52
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev51
    have hv88 : v88 = .field 191 := by rw [sub_field_inv op102]; norm_num
    subst hv88
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev87
    rw [hsub_tup] at ev14
    have hw_rep := Lib.repU64_ofNatLT h hw_lt
    have hsub_rep := Lib.repU64_ofNatLT h hsub_lt
    obtain ⟨hadd, rfl⟩ := Lib.u64_add_spec hw_rep hsub_rep ev14
    simp only [Value.tuple.injEq, List.cons.injEq, and_true, UInt64.toNat_ofNatLT] at hadd
    rcases hadd with ⟨hx_d, hcarry⟩
    subst hcarry
    obtain ⟨hcF, rfl⟩ := Lib.u8_to_field_spec ev167
    have hdiv1 : (w.toNat + subVal) / 18446744073709551616 = 1 := by
      have hne0 : (w.toNat + subVal) / 18446744073709551616 ≠ 0 := by
        intro h0
        rw [h0] at hcF
        exact zero_ne_one (Value.field.inj hcF)
      rw [hsub_val] at hne0 ⊢
      omega
    have hw_ge2 : ¬ w.toNat < 16512 := by rw [hsub_val] at hdiv1; omega
    have hmod : (w.toNat + subVal) % 18446744073709551616 = w.toNat - 16512 := by
      rw [hsub_val]; omega
    rw [hmod] at hx_d
    subst hx_d
    have hy418 : y418 = .field 192 := by rw [mul_field_inv op433]; norm_num
    subst hy418
    have hv407 : v407 = .field 192 := by rw [add_field_inv op424]; norm_num
    subst hv407
    have hwide := put_tagn_wide_c0 (d := w.toNat - 16512) (by omega) ev406 hrest
    have he1 : Ixon.tagNEnd1 0 = 128 := rfl
    have he2 : Ixon.tagNEnd2 0 = 16512 := rfl
    have he3 : Ixon.tagNEnd3 0 = 82048 := rfl
    have he4 : Ixon.tagNEnd4 0 = 16859264 := rfl
    have he5 : Ixon.tagNEnd5 0 = 4311826560 := rfl
    have hh0 : Ixon.tagNHeader 0 0 (2 ^ (8 - 0 - 1) + 2 ^ (8 - 0 - 2)) = (192 : UInt8) := rfl
    have hh1 : Ixon.tagNHeader 0 0 (2 ^ (8 - 0 - 1) + 2 ^ (8 - 0 - 2) + 1) = (193 : UInt8) := rfl
    have hh2 : Ixon.tagNHeader 0 0 (2 ^ (8 - 0 - 1) + 2 ^ (8 - 0 - 2) + 2) = (194 : UInt8) := rfl
    have hh3 : Ixon.tagNHeader 0 0 (2 ^ (8 - 0 - 1) + 2 ^ (8 - 0 - 2) + 3) = (195 : UInt8) := rfl
    by_cases h3 : w.toNat < 82048
    · have hd3 : w.toNat - 16512 < 65536 := by omega
      simpa [Ixon.Verify.Codec.tag0Bytes, Ixon.Verify.Codec.tagNBytes,
        he1, he2, he3, hw128, hw_ge2, h3, hd3, hh0] using hwide
    · have hd3 : ¬ w.toNat - 16512 < 65536 := by omega
      have hs3 : w.toNat - 16512 - 65536 = w.toNat - 82048 := by omega
      by_cases h4 : w.toNat < 16859264
      · have hd4 : w.toNat - 82048 < 16777216 := by omega
        simpa [Ixon.Verify.Codec.tag0Bytes, Ixon.Verify.Codec.tagNBytes,
          he1, he2, he3, he4, hw128, hw_ge2, h3, hd3, hs3, h4, hd4, hh1] using hwide
      · have hd4 : ¬ w.toNat - 82048 < 16777216 := by omega
        have hs4 : w.toNat - 82048 - 16777216 = w.toNat - 16859264 := by omega
        by_cases h5 : w.toNat < 4311826560
        · have hd5 : w.toNat - 16859264 < 4294967296 := by omega
          simpa [Ixon.Verify.Codec.tag0Bytes, Ixon.Verify.Codec.tagNBytes,
            he1, he2, he3, he4, he5, hw128, hw_ge2, h3, hd3, hs3, h4, hd4, hs4, h5, hd5, hh2]
            using hwide
        · have hd5 : ¬ w.toNat - 16859264 < 4294967296 := by omega
          have hs5 : w.toNat - 16859264 - 4294967296 = w.toNat - 4311826560 := by omega
          simpa [Ixon.Verify.Codec.tag0Bytes, Ixon.Verify.Codec.tagNBytes,
            he1, he2, he3, he4, he5, hw128, hw_ge2, h3, hd3, hs3, h4, hd4, hs4, h5, hd5, hs5, hh3]
            using hwide

theorem put_tagn0_spec {w : UInt64} {x_v x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hw : RepU64 h w x_v)
    (ev : ObsFn W "IxonSerialize::put_tagn0" [x_v, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((Ixon.Verify.Codec.tag0Bytes w).data.toList ++ rest) r := by
  obtain rfl := Lib.repU64_eq hw
  have hw_lt := Lib.u64_toNat_lt w
  cases Obs.«IxonSerialize::put_tagn0».obs ev with
  | n0_n1 x_v0 x_v1 x_v2 x_v3 x_v4 x_v5 x_v6 x_v7 m54 x62 y63 m64 x70 y71 m72 x78 y79 m80 x86 y87
      m88 x94 y95 m96 x102 y103 m104 _ _ _ _ _ _ _ m213 _ hv11 ev115 ev129 op109 ev143 op101 ev157
      op93 ev171 op85 ev185 op77 ev199 op69 ev226 he250 hm249 _ =>
    simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    rcases hv11 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev115
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev129
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev143
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev157
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev171
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev185
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev199
    have hx94 := add_field_inv op109; subst hx94
    have hx86 := add_field_inv op101; subst hx86
    have hx78 := add_field_inv op93; subst hx78
    have hx70 := add_field_inv op85; subst hx70
    have hx62 := add_field_inv op77; subst hx62
    have hsumF := Value.field.inj (add_field_inv op69).symm
    have hsum0 : w.toNat / 256 % 256 + w.toNat / 65536 % 256 + w.toNat / 16777216 % 256 +
        w.toNat / 4294967296 % 256 + w.toNat / 1099511627776 % 256 +
        w.toNat / 281474976710656 % 256 + w.toNat / 72057594037927936 % 256 = 0 := by
      apply natCast_eq_zero_of_lt (by omega)
      push_cast
      exact hsumF
    have hw256 : w.toNat < 256 := by
      have := Lib.leBytes8_bytes hw_lt
      unfold Lib.leBytes8 at this
      omega
    have hv0_rep : RepU8 h w.toUInt8 (.field ((w.toNat % 256 : Nat) : F)) := by
      show (.field ((w.toNat % 256 : Nat) : F) : SourceValue F) = .field (w.toUInt8.toNat : F)
      simp [UInt64.toUInt8, UInt8.toNat_ofNat']
    have h128_rep : RepU8 h (128 : UInt8) (.field 128) := by
      show (.field 128 : SourceValue F) = .field ((128 : UInt8).toNat : F)
      norm_num
    obtain ⟨hltF, rfl⟩ := Lib.u8_less_than_spec hv0_rep h128_rep ev226
    have hw_toUInt8 : w.toUInt8.toNat = w.toNat := by
      simp [UInt64.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hw256]
    have hw128 : w.toNat < 128 := by
      by_contra hge
      have hge' : ¬ w.toUInt8.toNat < (128 : UInt8).toNat := by
        rw [hw_toUInt8]; change ¬ w.toNat < 128; exact hge
      rw [ite_eq_right hge'] at hltF
      exact one_ne_zero (Value.field.inj hltF)
    have he1 : Ixon.tagNEnd1 0 = 128 := rfl
    have hhdr : Ixon.tagNHeader 0 0 w.toNat = w.toUInt8 := by
      apply UInt8.eq_of_toNat_eq
      rw [hw_toUInt8]
      simp [Ixon.tagNHeader, Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hw256]
    have hcons := repBytes_cons hv0_rep hrest hm249 he250
    simpa [Ixon.Verify.Codec.tag0Bytes, Ixon.Verify.Codec.tagNBytes, he1, hw128, hhdr] using hcons
  | n0_n0 x_v0 x_v1 x_v2 x_v3 x_v4 x_v5 x_v6 x_v7 m54 x62 y63 m64 x70 y71 m72 x78 y79 m80 x86 y87
      m88 x94 y95 m96 x102 y103 m104 _ _ _ _ _ _ _ m213 _ _ hv11 ev115 ev129 op109 ev143 op101
      ev157 op93 ev171 op85 ev185 op77 ev199 op69 ev226 ev281 _ =>
    have hv11' := hv11
    simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev115
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev129
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev143
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev157
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev171
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev185
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev199
    have hx94 := add_field_inv op109; subst hx94
    have hx86 := add_field_inv op101; subst hx86
    have hx78 := add_field_inv op93; subst hx78
    have hx70 := add_field_inv op85; subst hx70
    have hx62 := add_field_inv op77; subst hx62
    have hsumF := Value.field.inj (add_field_inv op69).symm
    have hsum0 : w.toNat / 256 % 256 + w.toNat / 65536 % 256 + w.toNat / 16777216 % 256 +
        w.toNat / 4294967296 % 256 + w.toNat / 1099511627776 % 256 +
        w.toNat / 281474976710656 % 256 + w.toNat / 72057594037927936 % 256 = 0 := by
      apply natCast_eq_zero_of_lt (by omega)
      push_cast
      exact hsumF
    have hw256 : w.toNat < 256 := by
      have := Lib.leBytes8_bytes hw_lt
      unfold Lib.leBytes8 at this
      omega
    have hv0_rep : RepU8 h w.toUInt8 (.field ((w.toNat % 256 : Nat) : F)) := by
      show (.field ((w.toNat % 256 : Nat) : F) : SourceValue F) = .field (w.toUInt8.toNat : F)
      simp [UInt64.toUInt8, UInt8.toNat_ofNat']
    have h128_rep : RepU8 h (128 : UInt8) (.field 128) := by
      show (.field 128 : SourceValue F) = .field ((128 : UInt8).toNat : F)
      norm_num
    obtain ⟨hltF, rfl⟩ := Lib.u8_less_than_spec hv0_rep h128_rep ev226
    have hw_toUInt8 : w.toUInt8.toNat = w.toNat := by
      simp [UInt64.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hw256]
    have hw128 : ¬ w.toNat < 128 := by
      intro hlt
      have hlt' : w.toUInt8.toNat < (128 : UInt8).toNat := by
        rw [hw_toUInt8]; exact hlt
      rw [ite_eq_left hlt'] at hltF
      exact zero_ne_one (Value.field.inj hltF)
    exact put_tagn_tail_zero_spec hw128 ev281 hrest
  | other x_v0 x_v1 x_v2 x_v3 x_v4 x_v5 x_v6 x_v7 v53 m54 x62 y63 m64 x70 y71 m72 x78 y79 m80
      x86 y87 m88 x94 y95 m96 x102 y103 m104 _ _ _ _ _ _ _ _ hv11 ev115 ev129 op109 ev143 op101
      ev157 op93 ev171 op85 ev185 op77 ev199 op69 hne314 ev323 _ =>
    have hv11' := hv11
    simp only [TagN.u64Value, Value.tuple.injEq, List.cons.injEq, and_true] at hv11'
    rcases hv11' with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev115
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev129
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev143
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev157
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev171
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev185
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev199
    have hx94 := add_field_inv op109; subst hx94
    have hx86 := add_field_inv op101; subst hx86
    have hx78 := add_field_inv op93; subst hx78
    have hx70 := add_field_inv op85; subst hx70
    have hx62 := add_field_inv op77; subst hx62
    have hv53 := add_field_inv op69; subst hv53
    have hw128 : ¬ w.toNat < 128 := by
      intro hlt
      apply hne314
      have h0 : w.toNat / 256 % 256 = 0 ∧ w.toNat / 65536 % 256 = 0 ∧
          w.toNat / 16777216 % 256 = 0 ∧ w.toNat / 4294967296 % 256 = 0 ∧
          w.toNat / 1099511627776 % 256 = 0 ∧ w.toNat / 281474976710656 % 256 = 0 ∧
          w.toNat / 72057594037927936 % 256 = 0 := by omega
      rcases h0 with ⟨e1, e2, e3, e4, e5, e6, e7⟩
      simp [e1, e2, e3, e4, e5, e6, e7]
    exact put_tagn_tail_zero_spec hw128 ev323 hrest

theorem put_tagn4_const_small {k : Nat} {x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hk : k < 8)
    (ev : ObsFn W "IxonSerialize::put_tagn4"
      [.field 13,
       .tuple [.field (k : F), .field 0, .field 0, .field 0, .field 0, .field 0, .field 0, .field 0],
       x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((Ixon.Verify.Codec.tag4Bytes Ixon.Constant.FLAG k.toUInt64).data.toList ++ rest) r := by
  have hk_rep : ∀ m : Heap F, RepU8 m k.toUInt8 (.field (k : F)) := by
    intro m
    show (.field (k : F) : SourceValue F) = .field (k.toUInt8.toNat : F)
    simp [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (show k < 256 by omega)]
  have h8_rep : ∀ m : Heap F, RepU8 m (8 : UInt8) (.field 8) := by
    intro m
    show (.field 8 : SourceValue F) = .field ((8 : UInt8).toNat : F)
    norm_num
  cases Obs.«IxonSerialize::put_tagn4».obs ev with
  | n0_n0 x_v0 x_v1 x_v2 x_v3 x_v4 x_v5 x_v6 x_v7 m54 x62 y63 m64 x70 y71 m72 x78 y79 m80 x86 y87
      m88 x94 y95 m96 x102 y103 m104 _ _ _ _ _ _ _ m213 _ _ _ hv11 ev115 ev129 op109 ev143 op101
      ev157 op93 ev171 op85 ev185 op77 ev199 op69 ev226 _ _ _ =>
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    rcases hv11 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨hltF, -⟩ := Lib.u8_less_than_spec (hk_rep m54) (h8_rep m54) ev226
    have hk8 : k.toUInt8.toNat < (8 : UInt8).toNat := by
      simp [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (show k < 256 by omega), hk]
    rw [ite_eq_left hk8] at hltF
    exact absurd (Value.field.inj hltF) zero_ne_one
  | other x_v0 x_v1 x_v2 x_v3 x_v4 x_v5 x_v6 x_v7 v53 m54 x62 y63 m64 x70 y71 m72 x78 y79 m80
      x86 y87 m88 x94 y95 m96 x102 y103 m104 _ _ _ _ _ _ _ _ _ hv11 ev115 ev129 op109 ev143 op101
      ev157 op93 ev171 op85 ev185 op77 ev199 op69 hne366 _ _ _ =>
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    rcases hv11 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev115
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev129
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev143
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev157
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev171
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev185
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev199
    have hx94 := add_field_inv op109; subst hx94
    have hx86 := add_field_inv op101; subst hx86
    have hx78 := add_field_inv op93; subst hx78
    have hx70 := add_field_inv op85; subst hx70
    have hx62 := add_field_inv op77; subst hx62
    have hv53 := add_field_inv op69; subst hv53
    exact absurd (by simp) hne366
  | n0_n1 x_v0 x_v1 x_v2 x_v3 x_v4 x_v5 x_v6 x_v7 m54 x62 y63 m64 x70 y71 m72 x78 y79 m80 x86 y87
      m88 x94 y95 m96 x102 y103 m104 _ _ _ _ _ _ _ m213 _ v254 m257 _ v268 m270 x275 y276 _ hv11
      ev115 ev129 op109 ev143 op101 ev157 op93 ev171 op85 ev185 op77 ev199 _ ev226 he250 hm249
      op290 ev297 op282 ev267 _ =>
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv11
    rcases hv11 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨-, rfl⟩ := Lib.u8_to_field_spec ev115
    obtain ⟨-, rfl⟩ := Lib.u8_to_field_spec ev129
    obtain ⟨-, rfl⟩ := Lib.u8_to_field_spec ev143
    obtain ⟨-, rfl⟩ := Lib.u8_to_field_spec ev157
    obtain ⟨-, rfl⟩ := Lib.u8_to_field_spec ev171
    obtain ⟨-, rfl⟩ := Lib.u8_to_field_spec ev185
    obtain ⟨-, rfl⟩ := Lib.u8_to_field_spec ev199
    obtain ⟨-, rfl⟩ := Lib.u8_less_than_spec (hk_rep h) (h8_rep h) ev226
    have hx275 : x275 = .field 208 := by rw [mul_field_inv op290]; norm_num
    subst hx275
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev297
    have hv268 := add_field_inv op282; subst hv268
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev267
    have hk_u64 : k.toUInt64.toNat = k := by
      simp [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show k < 18446744073709551616 by omega)]
    have he1 : Ixon.tagNEnd1 4 = 8 := rfl
    have hhdr : (.field (208 + (k : F)) : SourceValue F) =
        .field ((Ixon.tagNHeader 4 Ixon.Constant.FLAG k).toNat : F) := by
      have hflag : Ixon.Constant.FLAG = (13 : UInt8) := rfl
      have hval : (Ixon.tagNHeader 4 Ixon.Constant.FLAG k).toNat = 208 + k := by
        rw [hflag]
        simp [Ixon.tagNHeader, Nat.toUInt8, UInt8.toNat_ofNat',
          Nat.mod_eq_of_lt (show 13 * 16 + k < 256 by omega)]
        omega
      rw [hval]
      push_cast
      ring
    have hcons := repBytes_cons hhdr hrest hm249 he250
    simpa [Ixon.Verify.Codec.tag4Bytes, Ixon.Verify.Codec.tagNBytes, hk_u64, he1, hk] using hcons

/-! ## `put_address`, empty side tables, and `put_constant` -/

theorem proj_addrCell (b : Bytes.Address) (i : Nat) (hi : i < 32) {v : SourceValue F}
    (hp : projectValue (.tuple (Lib.addrCell F b)) i = .ok v) :
    v = .field (b[i].toNat : F) := by
  have e : projectValue (Value.tuple (Lib.addrCell F b) : SourceValue F) i =
      .ok (.field (b[i].toNat : F)) := by
    interval_cases i <;> rfl
  exact Except.ok.inj (e.symm.trans hp)

theorem put_address_spec {b : Bytes.Address} {x_a x_rest r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)} {rest : List UInt8}
    (ha : RepAddr h b x_a)
    (ev : ObsFn W "IxonSerialize::put_address" [x_a, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((ixAddr b).hash.data.toList ++ rest) r := by
  rcases Obs.«IxonSerialize::put_address».obs ev with
    ⟨v1, m14, v28, m48, v62, m82, v96, m116, v130, m150, v164, m184, v198, m218, v232, m252,
      v266, m286, v300, m320, v334, m354, v368, m388, v402, m422, v436, m456, v470, m490, v504,
      m524, v538, m558, v572, m592, v606, m626, v640, m660, v674, m694, v708, m728, v742, m762,
      v776, m796, v810, m830, v844, m864, v878, m898, v912, m932, v946, m966, v980, m1000, v1014,
      m1034, v1048, v1075, ld11, hm24, pr38, hm58, pr72, hm92, pr106, hm126, pr140, hm160, pr174,
      hm194, pr208, hm228, pr242, hm262, pr276, hm296, pr310, hm330, pr344, hm364, pr378, hm398,
      pr412, hm432, pr446, hm466, pr480, hm500, pr514, hm534, pr548, hm568, pr582, hm602, pr616,
      hm636, pr650, hm670, pr684, hm704, pr718, hm738, pr752, hm772, pr786, hm806, pr820, hm840,
      pr854, hm874, pr888, hm908, pr922, hm942, pr956, hm976, pr990, hm1010, pr1024, hm1044,
      pr1058, he1071, hm1070, pr1085, -⟩
  have hv1 := Lib.load_addr ha v1 ld11
  subst hv1
  have s31 := repBytes_cons (proj_addrCell b 31 (by omega) pr38) hrest hm24 rfl
  have s30 := repBytes_cons (proj_addrCell b 30 (by omega) pr72) s31 hm58 rfl
  have s29 := repBytes_cons (proj_addrCell b 29 (by omega) pr106) s30 hm92 rfl
  have s28 := repBytes_cons (proj_addrCell b 28 (by omega) pr140) s29 hm126 rfl
  have s27 := repBytes_cons (proj_addrCell b 27 (by omega) pr174) s28 hm160 rfl
  have s26 := repBytes_cons (proj_addrCell b 26 (by omega) pr208) s27 hm194 rfl
  have s25 := repBytes_cons (proj_addrCell b 25 (by omega) pr242) s26 hm228 rfl
  have s24 := repBytes_cons (proj_addrCell b 24 (by omega) pr276) s25 hm262 rfl
  have s23 := repBytes_cons (proj_addrCell b 23 (by omega) pr310) s24 hm296 rfl
  have s22 := repBytes_cons (proj_addrCell b 22 (by omega) pr344) s23 hm330 rfl
  have s21 := repBytes_cons (proj_addrCell b 21 (by omega) pr378) s22 hm364 rfl
  have s20 := repBytes_cons (proj_addrCell b 20 (by omega) pr412) s21 hm398 rfl
  have s19 := repBytes_cons (proj_addrCell b 19 (by omega) pr446) s20 hm432 rfl
  have s18 := repBytes_cons (proj_addrCell b 18 (by omega) pr480) s19 hm466 rfl
  have s17 := repBytes_cons (proj_addrCell b 17 (by omega) pr514) s18 hm500 rfl
  have s16 := repBytes_cons (proj_addrCell b 16 (by omega) pr548) s17 hm534 rfl
  have s15 := repBytes_cons (proj_addrCell b 15 (by omega) pr582) s16 hm568 rfl
  have s14 := repBytes_cons (proj_addrCell b 14 (by omega) pr616) s15 hm602 rfl
  have s13 := repBytes_cons (proj_addrCell b 13 (by omega) pr650) s14 hm636 rfl
  have s12 := repBytes_cons (proj_addrCell b 12 (by omega) pr684) s13 hm670 rfl
  have s11 := repBytes_cons (proj_addrCell b 11 (by omega) pr718) s12 hm704 rfl
  have s10 := repBytes_cons (proj_addrCell b 10 (by omega) pr752) s11 hm738 rfl
  have s9  := repBytes_cons (proj_addrCell b 9  (by omega) pr786) s10 hm772 rfl
  have s8  := repBytes_cons (proj_addrCell b 8  (by omega) pr820) s9  hm806 rfl
  have s7  := repBytes_cons (proj_addrCell b 7  (by omega) pr854) s8  hm840 rfl
  have s6  := repBytes_cons (proj_addrCell b 6  (by omega) pr888) s7  hm874 rfl
  have s5  := repBytes_cons (proj_addrCell b 5  (by omega) pr922) s6  hm908 rfl
  have s4  := repBytes_cons (proj_addrCell b 4  (by omega) pr956) s5  hm942 rfl
  have s3  := repBytes_cons (proj_addrCell b 3  (by omega) pr990) s4  hm976 rfl
  have s2  := repBytes_cons (proj_addrCell b 2  (by omega) pr1024) s3 hm1010 rfl
  have s1  := repBytes_cons (proj_addrCell b 1  (by omega) pr1058) s2 hm1044 rfl
  have s0  := repBytes_cons (proj_addrCell b 0  (by omega) pr1085) s1 hm1070 he1071
  have hhash : (ixAddr b).hash.data.toList = b.toList := by
    simp [ixAddr]
  rw [hhash, Lib.vec32_toList b]
  exact s0

theorem put_sharing_nil_spec {x_list x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hl : RepList Specs.Callees.ixExprListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (ev : ObsFn W "IxonSerialize::put_sharing" [x_list, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((Ixon.Verify.Codec.tag0Bytes 0).data.toList ++ rest) r := by
  rcases Obs.«IxonSerialize::put_sharing».obs ev with ⟨v1, m2, _, _, v30, m39, _, ev14, ev49, ev28, -⟩
  rw [← Obs.Names.«WordLists::length_u64<&Ixon::Expr>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Expr" [])]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Obs.Names.«Lists::Node<&Ixon::Expr>».symbol]
  obtain ⟨rfl, rfl⟩ := length_u64_nil_spec ev14 hl'
  cases Obs.«IxonSerialize::put_expr_list».obs ev49 with
  | Nil _ rfl rfl _ =>
    exact put_tagn0_spec (Lib.repU64_ofNatLT h (m := 0) (by omega)) ev28 hrest
  | Cons _ _ _ _ _ _ _ ld12 _ _ _ _ =>
    obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hl ld12
    cases he

theorem put_refs_nil_spec {x_list x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hl : RepList addrListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (ev : ObsFn W "IxonSerialize::put_refs" [x_list, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((Ixon.Verify.Codec.tag0Bytes 0).data.toList ++ rest) r := by
  rcases Obs.«IxonSerialize::put_refs».obs ev with ⟨v1, m2, _, _, v30, m39, _, ev14, ev49, ev28, -⟩
  rw [← Obs.Names.«WordLists::length_u64<&[Field; 32]>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Obs.Names.«Lists::Node<&[Field; 32]>».symbol]
  obtain ⟨rfl, rfl⟩ := length_u64_nil_spec ev14 hl'
  cases Obs.«IxonSerialize::put_address_list».obs ev49 with
  | Nil _ rfl rfl _ =>
    exact put_tagn0_spec (Lib.repU64_ofNatLT h (m := 0) (by omega)) ev28 hrest
  | Cons _ _ _ _ _ _ ld12 _ _ _ =>
    obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hl ld12
    cases he

theorem put_univs_nil_spec {x_list x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hl : RepList Specs.Callees.ixUnivListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (ev : ObsFn W "IxonSerialize::put_univs" [x_list, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((Ixon.Verify.Codec.tag0Bytes 0).data.toList ++ rest) r := by
  rcases Obs.«IxonSerialize::put_univs».obs ev with ⟨v1, m2, _, _, v30, m39, _, ev14, ev49, ev28, -⟩
  rw [← Obs.Names.«WordLists::length_u64<&Ixon::Univ>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Univ" [])]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Obs.Names.«Lists::Node<&Ixon::Univ>».symbol]
  obtain ⟨rfl, rfl⟩ := length_u64_nil_spec ev14 hl'
  cases Obs.«IxonSerialize::put_univ_list».obs ev49 with
  | Nil _ rfl rfl _ =>
    exact put_tagn0_spec (Lib.repU64_ofNatLT h (m := 0) (by omega)) ev28 hrest
  | Cons _ _ _ _ _ _ _ ld12 _ _ _ _ =>
    obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hl ld12
    cases he

theorem put_binders_nil_spec {x_list x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hl : RepList Specs.Callees.ixBinderListEnum (fun _ (_ : Unit) _ => True) h [] x_list)
    (ev : ObsFn W "IxonSerialize::put_binders" [x_list, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((Ixon.Verify.Codec.tag0Bytes 0).data.toList ++ rest) r := by
  rcases Obs.«IxonSerialize::put_binders».obs ev with
    ⟨v1, m2, _, _, v30, m39, _, ev14, ev49, ev28, -⟩
  rw [← Obs.Names.«WordLists::length_u64<Ixon::BinderBlock>».symbol] at ev14
  have hl' : RepList (Instance.mk "Lists::Node" [.named "Ixon::BinderBlock" []]).symbol
      (fun _ (_ : Unit) _ => True) h [] x_list := by
    rwa [Obs.Names.«Lists::Node<Ixon::BinderBlock>».symbol]
  obtain ⟨rfl, rfl⟩ := length_u64_nil_spec ev14 hl'
  cases Obs.«IxonSerialize::put_binder_block_list».obs ev49 with
  | Nil _ rfl rfl _ =>
    exact put_tagn0_spec (Lib.repU64_ofNatLT h (m := 0) (by omega)) ev28 hrest
  | Cons _ _ _ _ _ _ ld12 _ _ _ =>
    obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hl ld12
    cases he

theorem put_cprj_info_spec {p : Ixon.ConstructorProj} {vi vj bp x_rest r : SourceValue F}
    {b : Bytes.Address} {h h' : Heap F} {calls : List (Call F)} {rest : List UInt8}
    (hvi : RepU64 h p.idx vi) (hvj : RepU64 h p.cidx vj)
    (hb : RepAddr h b bp) (hblk : ixAddr b = p.block)
    (ev : ObsFn W "IxonSerialize::put_constant_info"
      [.construct "Ixon::ConstantInfo" "CPrj"
        [.construct "Ixon::ConstructorProj" "Mk" [vi, vj, bp]], x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((Ixon.Verify.Codec.NonrecursiveConstant.constructorProjBytes p).data.toList ++ rest) r := by
  cases Obs.«IxonSerialize::put_constant_info».obs ev with
  | Defn _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Recr _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Axio _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Quot _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | RPrj _ _ _ _ _ _ hne _ _ _ => exact absurd rfl (hne _ rfl)
  | IPrj _ _ _ _ _ _ hne _ _ _ _ => exact absurd rfl (hne _ rfl)
  | DPrj _ _ _ _ _ _ hne _ _ _ _ _ => exact absurd rfl (hne _ rfl)
  | CPrj x_prj _ _ _ _ _ hv155 ev167 _ =>
    injection hv155 with _ _ hx
    injection hx with hx _
    subst hx
    rcases Obs.«IxonSerialize::put_constructor_proj».obs ev167 with
      ⟨x_idx, x_cidx, x_block, _, v39, m48, _, v60, m69, _, hv15, ev79, ev58, ev37, -⟩
    injection hv15 with _ _ hargs
    injection hargs with rfl hargs
    injection hargs with rfl hargs
    injection hargs with rfl _
    have s1 := put_address_spec hb ev79 hrest
    have hvj' : RepU64 m69 p.cidx vj :=
      U64.repU64_heapMono₂ ev79.heap_extends hvj
    have s2 := put_tagn0_spec hvj' ev58 s1
    have hvi' : RepU64 m48 p.idx vi :=
      U64.repU64_heapMono₂ (ev79.heap_extends.trans ev58.heap_extends) hvi
    have s3 := put_tagn0_spec hvi' ev37 s2
    subst hblk
    simpa [Ixon.Verify.Codec.NonrecursiveConstant.constructorProjBytes, List.append_assoc]
      using s3

theorem put_rprj_info_spec {p : Ixon.RecursorProj} {vi bp x_rest r : SourceValue F}
    {b : Bytes.Address} {h h' : Heap F} {calls : List (Call F)} {rest : List UInt8}
    (hvi : RepU64 h p.idx vi) (hb : RepAddr h b bp) (hblk : ixAddr b = p.block)
    (ev : ObsFn W "IxonSerialize::put_constant_info"
      [.construct "Ixon::ConstantInfo" "RPrj"
        [.construct "Ixon::RecursorProj" "Mk" [vi, bp]], x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((Ixon.Verify.Codec.NonrecursiveConstant.recursorProjBytes p).data.toList ++ rest) r := by
  cases Obs.«IxonSerialize::put_constant_info».obs ev with
  | Defn _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Recr _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Axio _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Quot _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | CPrj _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | IPrj _ _ _ _ _ _ _ hne _ _ _ => exact absurd rfl (hne _ rfl)
  | DPrj _ _ _ _ _ _ _ hne _ _ _ _ => exact absurd rfl (hne _ rfl)
  | RPrj x_prj _ _ _ _ _ _ hv190 ev202 _ =>
    injection hv190 with _ _ hx
    injection hx with hx _
    subst hx
    rcases Obs.«IxonSerialize::put_recursor_proj».obs ev202 with
      ⟨x_idx, x_block, _, v34, m43, _, hv15, ev53, ev32, -⟩
    injection hv15 with _ _ hargs
    injection hargs with rfl hargs
    injection hargs with rfl _
    have s1 := put_address_spec hb ev53 hrest
    have hvi' : RepU64 m43 p.idx vi := U64.repU64_heapMono₂ ev53.heap_extends hvi
    have s2 := put_tagn0_spec hvi' ev32 s1
    subst hblk
    simpa [Ixon.Verify.Codec.NonrecursiveConstant.recursorProjBytes, List.append_assoc]
      using s2

theorem put_iprj_info_spec {p : Ixon.InductiveProj} {vi bp x_rest r : SourceValue F}
    {b : Bytes.Address} {h h' : Heap F} {calls : List (Call F)} {rest : List UInt8}
    (hvi : RepU64 h p.idx vi) (hb : RepAddr h b bp) (hblk : ixAddr b = p.block)
    (ev : ObsFn W "IxonSerialize::put_constant_info"
      [.construct "Ixon::ConstantInfo" "IPrj"
        [.construct "Ixon::InductiveProj" "Mk" [vi, bp]], x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((Ixon.Verify.Codec.NonrecursiveConstant.inductiveProjBytes p).data.toList ++ rest) r := by
  cases Obs.«IxonSerialize::put_constant_info».obs ev with
  | Defn _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Recr _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Axio _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Quot _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | CPrj _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | RPrj _ _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | DPrj _ _ _ _ _ _ _ _ hne _ _ _ => exact absurd rfl (hne _ rfl)
  | IPrj x_prj _ _ _ _ _ _ _ hv225 ev237 _ =>
    injection hv225 with _ _ hx
    injection hx with hx _
    subst hx
    rcases Obs.«IxonSerialize::put_inductive_proj».obs ev237 with
      ⟨x_idx, x_block, _, v34, m43, _, hv15, ev53, ev32, -⟩
    injection hv15 with _ _ hargs
    injection hargs with rfl hargs
    injection hargs with rfl _
    have s1 := put_address_spec hb ev53 hrest
    have hvi' : RepU64 m43 p.idx vi := U64.repU64_heapMono₂ ev53.heap_extends hvi
    have s2 := put_tagn0_spec hvi' ev32 s1
    subst hblk
    simpa [Ixon.Verify.Codec.NonrecursiveConstant.inductiveProjBytes, List.append_assoc]
      using s2

theorem put_dprj_info_spec {p : Ixon.DefinitionProj} {vi bp x_rest r : SourceValue F}
    {b : Bytes.Address} {h h' : Heap F} {calls : List (Call F)} {rest : List UInt8}
    (hvi : RepU64 h p.idx vi) (hb : RepAddr h b bp) (hblk : ixAddr b = p.block)
    (ev : ObsFn W "IxonSerialize::put_constant_info"
      [.construct "Ixon::ConstantInfo" "DPrj"
        [.construct "Ixon::DefinitionProj" "Mk" [vi, bp]], x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((Ixon.Verify.Codec.NonrecursiveConstant.definitionProjBytes p).data.toList ++ rest) r := by
  cases Obs.«IxonSerialize::put_constant_info».obs ev with
  | Defn _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Recr _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Axio _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | Quot _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | CPrj _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | RPrj _ _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | IPrj _ _ _ _ _ _ _ _ hv _ _ => injection hv with _ hc _; exact absurd hc (by decide)
  | DPrj x_prj _ _ _ _ _ _ _ _ hv260 ev272 _ =>
    injection hv260 with _ _ hx
    injection hx with hx _
    subst hx
    rcases Obs.«IxonSerialize::put_definition_proj».obs ev272 with
      ⟨x_idx, x_block, _, v34, m43, _, hv15, ev53, ev32, -⟩
    injection hv15 with _ _ hargs
    injection hargs with rfl hargs
    injection hargs with rfl _
    have s1 := put_address_spec hb ev53 hrest
    have hvi' : RepU64 m43 p.idx vi := U64.repU64_heapMono₂ ev53.heap_extends hvi
    have s2 := put_tagn0_spec hvi' ev32 s1
    subst hblk
    simpa [Ixon.Verify.Codec.NonrecursiveConstant.definitionProjBytes, List.append_assoc]
      using s2

theorem empty_tables_wf (info : Ixon.ConstantInfo)
    (hinfo : Ixon.Verify.Codec.NonrecursiveConstant.NonrecursiveInfoWireWF info) :
    Ixon.Verify.Codec.NonrecursiveConstant.NonrecursiveConstantWireWF
      ⟨info, #[], #[], #[], #[]⟩ where
  info := hinfo
  sharingCount := by change 0 < UInt64.size; decide
  sharingEntries := by simp
  refsCount := by change 0 < UInt64.size; decide
  refsEntries := by simp
  univsCount := by change 0 < UInt64.size; decide
  univsEntries := by simp
  binders := Ixon.bindersWireWF_empty

theorem addressWireWF_ixAddr (b : Bytes.Address) :
    Ixon.Verify.Codec.ConstantTables.AddressWireWF (ixAddr b) := by
  show (ixAddr b).hash.size = 32
  simp [ixAddr]

theorem serConstant_empty_tables_eq (info : Ixon.ConstantInfo)
    (hinfo : Ixon.Verify.Codec.NonrecursiveConstant.NonrecursiveInfoWireWF info) :
    (Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩).data.toList =
      (Ixon.Verify.Codec.NonrecursiveConstant.nonrecursiveInfoBytes info).data.toList ++
        (Ixon.Verify.Codec.tag0Bytes 0).data.toList ++
        (Ixon.Verify.Codec.tag0Bytes 0).data.toList ++
        (Ixon.Verify.Codec.tag0Bytes 0).data.toList ++
        (Ixon.Verify.Codec.tag0Bytes 0).data.toList := by
  unfold Ixon.serConstant
  rw [(Ixon.Verify.Codec.NonrecursiveConstant.putConstant_writes_nonrecursive
    ⟨info, #[], #[], #[], #[]⟩ (empty_tables_wf info hinfo)).runPut]
  simp [Ixon.Verify.Codec.NonrecursiveConstant.nonrecursiveConstantBytes,
    Ixon.Verify.Codec.ConstantTables.bindersBytes,
    Ixon.Verify.Codec.ConstantTables.listBytes, List.append_assoc]

theorem put_empty_tables_spec
    {x_sh x_rf x_un x_bd x_rest v99 v78 v57 v42 : SourceValue F}
    {h m108 m87 m66 m43 : Heap F} {c1 c2 c3 c4 : List (Call F)} {rest : List UInt8}
    (hp1 : RepList Specs.Callees.ixExprListEnum (fun _ (_ : Unit) _ => True) h [] x_sh)
    (hp2 : RepList addrListEnum (fun _ (_ : Unit) _ => True) h [] x_rf)
    (hp3 : RepList Specs.Callees.ixUnivListEnum (fun _ (_ : Unit) _ => True) h [] x_un)
    (hp4 : RepList Specs.Callees.ixBinderListEnum (fun _ (_ : Unit) _ => True) h [] x_bd)
    (ev_bd : ObsFn W "IxonSerialize::put_binders" [x_bd, x_rest] h v99 m108 c1)
    (ev_un : ObsFn W "IxonSerialize::put_univs" [x_un, v99] m108 v78 m87 c2)
    (ev_rf : ObsFn W "IxonSerialize::put_refs" [x_rf, v78] m87 v57 m66 c3)
    (ev_sh : ObsFn W "IxonSerialize::put_sharing" [x_sh, v57] m66 v42 m43 c4)
    (hrest : RepBytes h rest x_rest) :
    Heap.Extends h m43 ∧
      RepBytes m43
        ((Ixon.Verify.Codec.tag0Bytes 0).data.toList ++
          (Ixon.Verify.Codec.tag0Bytes 0).data.toList ++
          (Ixon.Verify.Codec.tag0Bytes 0).data.toList ++
          (Ixon.Verify.Codec.tag0Bytes 0).data.toList ++ rest) v42 := by
  have e1 := ev_bd.heap_extends
  have e2 := ev_un.heap_extends
  have e3 := ev_rf.heap_extends
  have e4 := ev_sh.heap_extends
  have s_bd := put_binders_nil_spec hp4 ev_bd hrest
  have s_un := put_univs_nil_spec (RepLinkedList.mono (fun _ hx => hx) e1 hp3) ev_un s_bd
  have s_rf := put_refs_nil_spec
    (RepLinkedList.mono (fun _ hx => hx) (e1.trans e2) hp2) ev_rf s_un
  have s_sh := put_sharing_nil_spec
    (RepLinkedList.mono (fun _ hx => hx) (e1.trans (e2.trans e3)) hp1) ev_sh s_rf
  refine ⟨e1.trans (e2.trans (e3.trans e4)), ?_⟩
  simpa [List.append_assoc] using s_sh

end ProjAddrAux

/-! ## Exported step lemmas -/

/-- `Blake3::bytes_to_addr`: hashes a represented byte list under `Good` and returns a pointer
to its 32-byte BLAKE3 digest. -/
theorem bytes_to_addr_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Blake3::bytes_to_addr" args h r h' calls) :
    ∀ bp (bytes : List UInt8), args = [bp] → Good c calls → RepBytes h bytes bp →
      ∃ a : Bytes.Address, RepAddr h' a r ∧ ixAddr a = Address.blake3Pure ⟨bytes.toArray⟩ := by
  intro bp bytes hargs good hbytes
  subst hargs
  have hstream : L1.Stream h bytes bp := by
    change Bytes.RepByteStream byteStreamEnum h bytes bp
    have e : (byteStreamEnum : String) = byteListEnum := rfl
    rw [e]
    exact hbytes
  obtain ⟨v1, m2, cs12, v23, m24, cs31, ev14, he27, hm26, ev33, hc42⟩ :=
    Obs.«Blake3::bytes_to_addr».obs ev
  obtain ⟨-, rfl⟩ := L1.hash_spec hstream ev14
  obtain ⟨rfl, hm24⟩ := L1.digest_bytes_spec ev33
  subst m24
  have hcall : (⟨"Blake3::hash", [bp], h⟩ : Call F) ∈ calls := by
    rw [hc42]; simp
  have hlen : bytes.length < 2 ^ 39 :=
    RomBound.bounded_length_lt good.2 hcall (by simp) hbytes
  have hnat : Blake3.Pure.NativeInput bytes := by
    show bytes.length < 2 ^ 64
    omega
  let d : Bytes.Address := Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel bytes)
  have hd_eq : d = Blake3.Pure.digest bytes :=
    Aiur.Library.Blake3.hash_model_spec bytes hnat
  have hty : (L1.digestV d).type = addrTy := by
    simp [L1.digestV, L1.bv, addrTy, Value.type, List.map_map]
  refine ⟨d, ?_, ?_⟩
  · refine ⟨m2.length, L1.digestV d, ?_, ?_, ?_⟩
    · rw [he27, hty]
    · rw [hm26]; simp
    · simp [L1.digestV, L1.bv]
  · rw [hd_eq, L1.blake3Pure_eq]
    rfl

/-- `IxonSerialize::put_constant`: serializes a projection record with empty side tables
(`ProjConstRep`) in front of `rest`. -/
theorem put_constant_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "IxonSerialize::put_constant" args h r h' calls) :
    Specs.Callees.put_constant c args h r h' calls := by
  intro cv tl info rest hargs hcv hrest
  subst hargs
  rcases hcv with ⟨iv, p1, p2, p3, p4, rfl, hinfo, hp1, hp2, hp3, hp4⟩
  cases info with
  | defn _ | recr _ | axio _ | quot _ | muts _ =>
    simp [Specs.Callees.ProjInfoRep] at hinfo
  | cPrj p =>
    rcases hinfo with ⟨vi, vj, bp, b, rfl, hvi, hvj, hb, hblk⟩
    cases Obs.«IxonSerialize::put_constant».obs ev with
    | Muts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Defn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Recr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Axio _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Quot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | RPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | IPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | DPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | CPrj x_sh x_rf x_un x_bd v42 m43 _ v57 m66 _ v78 m87 _ v99 m108 _ w664 _ v678 m750 _
        hv15 ev118 ev97 ev76 ev55 ev760 ev675 _ =>
      injection hv15 with _ _ hm; injection hm with hi hm
      injection hm with rfl hm; injection hm with rfl hm
      injection hm with rfl hm; injection hm with rfl _
      injection hi with _ _ hw; injection hw with hw _; subst hw
      obtain ⟨etab, stab⟩ :=
        ProjAddrAux.put_empty_tables_spec hp1 hp2 hp3 hp4 ev118 ev97 ev76 ev55 hrest
      have sinfo := ProjAddrAux.put_cprj_info_spec
        (U64.repU64_heapMono₂ etab hvi) (U64.repU64_heapMono₂ etab hvj)
        (Bytes.repAddressRef_heapMono₂ addrTy etab hb) hblk ev760 stab
      have stag := ProjAddrAux.put_tagn4_const_small (k := 4) (by omega) ev675 sinfo
      have hwf : Ixon.Verify.Codec.NonrecursiveConstant.NonrecursiveInfoWireWF (.cPrj p) :=
        .cPrj (hblk ▸ ProjAddrAux.addressWireWF_ixAddr b)
      rw [ProjAddrAux.serConstant_empty_tables_eq (.cPrj p) hwf]
      simpa [Ixon.Verify.Codec.NonrecursiveConstant.nonrecursiveInfoBytes,
        Ixon.ConstantInfo.CONST_CPRJ, List.append_assoc] using stag
  | rPrj p =>
    rcases hinfo with ⟨vi, bp, b, rfl, hvi, hb, hblk⟩
    cases Obs.«IxonSerialize::put_constant».obs ev with
    | Muts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Defn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Recr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Axio _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Quot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | CPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | IPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | DPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | RPrj x_sh x_rf x_un x_bd v42 m43 _ v57 m66 _ v78 m87 _ v99 m108 _ w785 _ v799 m871 _
        hv15 ev118 ev97 ev76 ev55 ev881 ev796 _ =>
      injection hv15 with _ _ hm; injection hm with hi hm
      injection hm with rfl hm; injection hm with rfl hm
      injection hm with rfl hm; injection hm with rfl _
      injection hi with _ _ hw; injection hw with hw _; subst hw
      obtain ⟨etab, stab⟩ :=
        ProjAddrAux.put_empty_tables_spec hp1 hp2 hp3 hp4 ev118 ev97 ev76 ev55 hrest
      have sinfo := ProjAddrAux.put_rprj_info_spec
        (U64.repU64_heapMono₂ etab hvi)
        (Bytes.repAddressRef_heapMono₂ addrTy etab hb) hblk ev881 stab
      have stag := ProjAddrAux.put_tagn4_const_small (k := 5) (by omega) ev796 sinfo
      have hwf : Ixon.Verify.Codec.NonrecursiveConstant.NonrecursiveInfoWireWF (.rPrj p) :=
        .rPrj (hblk ▸ ProjAddrAux.addressWireWF_ixAddr b)
      rw [ProjAddrAux.serConstant_empty_tables_eq (.rPrj p) hwf]
      simpa [Ixon.Verify.Codec.NonrecursiveConstant.nonrecursiveInfoBytes,
        Ixon.ConstantInfo.CONST_RPRJ, List.append_assoc] using stag
  | iPrj p =>
    rcases hinfo with ⟨vi, bp, b, rfl, hvi, hb, hblk⟩
    cases Obs.«IxonSerialize::put_constant».obs ev with
    | Muts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Defn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Recr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Axio _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Quot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | CPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | RPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | DPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | IPrj x_sh x_rf x_un x_bd v42 m43 _ v57 m66 _ v78 m87 _ v99 m108 _ w906 _ v920 m992 _
        hv15 ev118 ev97 ev76 ev55 ev1002 ev917 _ =>
      injection hv15 with _ _ hm; injection hm with hi hm
      injection hm with rfl hm; injection hm with rfl hm
      injection hm with rfl hm; injection hm with rfl _
      injection hi with _ _ hw; injection hw with hw _; subst hw
      obtain ⟨etab, stab⟩ :=
        ProjAddrAux.put_empty_tables_spec hp1 hp2 hp3 hp4 ev118 ev97 ev76 ev55 hrest
      have sinfo := ProjAddrAux.put_iprj_info_spec
        (U64.repU64_heapMono₂ etab hvi)
        (Bytes.repAddressRef_heapMono₂ addrTy etab hb) hblk ev1002 stab
      have stag := ProjAddrAux.put_tagn4_const_small (k := 6) (by omega) ev917 sinfo
      have hwf : Ixon.Verify.Codec.NonrecursiveConstant.NonrecursiveInfoWireWF (.iPrj p) :=
        .iPrj (hblk ▸ ProjAddrAux.addressWireWF_ixAddr b)
      rw [ProjAddrAux.serConstant_empty_tables_eq (.iPrj p) hwf]
      simpa [Ixon.Verify.Codec.NonrecursiveConstant.nonrecursiveInfoBytes,
        Ixon.ConstantInfo.CONST_IPRJ, List.append_assoc] using stag
  | dPrj p =>
    rcases hinfo with ⟨vi, bp, b, rfl, hvi, hb, hblk⟩
    cases Obs.«IxonSerialize::put_constant».obs ev with
    | Muts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Defn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Recr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Axio _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | Quot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | CPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | RPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | IPrj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ =>
      injection hv with _ _ h; injection h with h _; injection h with _ hc _; exact absurd hc (by decide)
    | DPrj x_sh x_rf x_un x_bd v42 m43 _ v57 m66 _ v78 m87 _ v99 m108 _ w1027 _ v1041 m1113 _
        hv15 ev118 ev97 ev76 ev55 ev1123 ev1038 _ =>
      injection hv15 with _ _ hm; injection hm with hi hm
      injection hm with rfl hm; injection hm with rfl hm
      injection hm with rfl hm; injection hm with rfl _
      injection hi with _ _ hw; injection hw with hw _; subst hw
      obtain ⟨etab, stab⟩ :=
        ProjAddrAux.put_empty_tables_spec hp1 hp2 hp3 hp4 ev118 ev97 ev76 ev55 hrest
      have sinfo := ProjAddrAux.put_dprj_info_spec
        (U64.repU64_heapMono₂ etab hvi)
        (Bytes.repAddressRef_heapMono₂ addrTy etab hb) hblk ev1123 stab
      have stag := ProjAddrAux.put_tagn4_const_small (k := 7) (by omega) ev1038 sinfo
      have hwf : Ixon.Verify.Codec.NonrecursiveConstant.NonrecursiveInfoWireWF (.dPrj p) :=
        .dPrj (hblk ▸ ProjAddrAux.addressWireWF_ixAddr b)
      rw [ProjAddrAux.serConstant_empty_tables_eq (.dPrj p) hwf]
      simpa [Ixon.Verify.Codec.NonrecursiveConstant.nonrecursiveInfoBytes,
        Ixon.ConstantInfo.CONST_DPRJ, List.append_assoc] using stag

/-- `KernelCheck::projection_addr_ctor`: builds, serializes, and hashes the constructor-projection
record `(i, j, block)` (`cprjAddr`). -/
theorem projection_addr_ctor_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::projection_addr_ctor" args h r h' calls) :
    Specs.Callees.projection_addr_ctor c args h r h' calls := by
  intro i j bp b hargs good hb
  subst hargs
  obtain ⟨v1, m2, cs12, v23, m24, cs34, m114, m127, m140, m153, v165, m166, cs176, m189, cs204,
    ev14, ev36, hm122, hm135, hm148, hm161, hm197, ev178, ev206, hc215⟩ :=
    Obs.«KernelCheck::projection_addr_ctor».obs ev
  obtain ⟨ni, hni, hxi, rfl, hm2⟩ := Lib.u64_from_field_spec ev14
  obtain ⟨nj, hnj, hxj, rfl, hm24⟩ := Lib.u64_from_field_spec ev36
  injection hxi with hxi
  injection hxj with hxj
  have hvali : ZMod.val i = ni := by
    rw [hxi]; exact ProjAddrAux.val_natCast_small (by omega)
  have hvalj : ZMod.val j = nj := by
    rw [hxj]; exact ProjAddrAux.val_natCast_small (by omega)
  have e1 : Heap.Extends m24 m114 := by rw [hm122]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends m114 m127 := by rw [hm135]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends m127 m140 := by rw [hm148]; exact Heap.Extends.snoc _ _
  have e4 : Heap.Extends m140 m153 := by rw [hm161]; exact Heap.Extends.snoc _ _
  have e5 : Heap.Extends m153 m189 := by rw [hm197]; exact Heap.Extends.snoc _ _
  have E : Heap.Extends h m189 := by
    rw [← hm2, ← hm24]
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
  have c1 : m189[m24.length]? = some (.construct Specs.Callees.ixExprListEnum "Nil" []) :=
    (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm122]; simp)
  have c2 : m189[m114.length]? = some (.construct addrListEnum "Nil" []) :=
    (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm135]; simp)
  have c3 : m189[m127.length]? = some (.construct Specs.Callees.ixUnivListEnum "Nil" []) :=
    (e4.trans e5).getElem?_eq (by rw [hm148]; simp)
  have c4 : m189[m140.length]? = some (.construct Specs.Callees.ixBinderListEnum "Nil" []) :=
    e5.getElem?_eq (by rw [hm161]; simp)
  have c5 : m189[m153.length]? = some (.construct byteListEnum "Nil" []) := by
    rw [hm197]; simp
  have hrepi : RepU64 m189 (ZMod.val i).toUInt64 (TagN.u64Value ni) := by
    rw [hvali]
    have e := Lib.repU64_ofNatLT m189 (m := ni) (by omega)
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hrepj : RepU64 m189 (ZMod.val j).toUInt64 (TagN.u64Value nj) := by
    rw [hvalj]
    have e := Lib.repU64_ofNatLT m189 (m := nj) (by omega)
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hinfo : Specs.Callees.ProjInfoRep m189
      (.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩)
      (.construct "Ixon::ConstantInfo" "CPrj"
        [.construct "Ixon::ConstructorProj" "Mk" [TagN.u64Value ni, TagN.u64Value nj, bp]]) := by
    simp only [Specs.Callees.ProjInfoRep]
    exact ⟨TagN.u64Value ni, TagN.u64Value nj, bp, b, rfl, hrepi, hrepj,
      Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
  have hbytes := put_constant_step c ev178 _ _
    (.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩) [] rfl
    ⟨_, _, _, _, _, rfl, hinfo, RepLinkedList.nil c1, RepLinkedList.nil c2,
      RepLinkedList.nil c3, RepLinkedList.nil c4⟩
    (RepLinkedList.nil c5)
  have hgood_bta : Good c cs204 :=
    good.sub (by rw [hc215]; intro x hx; simp [hx])
  obtain ⟨a, ha, haddr⟩ := bytes_to_addr_step c ev206 v165 _ rfl hgood_bta hbytes
  refine ⟨a, ha, ?_⟩
  rw [haddr, ProjAddrAux.bytes_mk_toList]
  rfl

/-! ## `Ingress::muts_member_at`, `Ingress::projection_addr`, and `Ingress::build_recur_addrs` -/

namespace ProjAddrAux

theorem muts_member_at_spec :
    ∀ (k : Nat) {ms : List Ixon.MutConst} {lp r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)},
      (hk : k < ms.length) → ms.length < 2 ^ 39 →
      Specs.Callees.MembersRep h ms lp →
      ObsFn W "Ingress::muts_member_at" [lp, .field (k : F)] h r h' calls →
      Specs.Callees.MutShape h ms[k] r ∧ h' = h := by
  intro k
  induction k with
  | zero =>
    intro ms lp r h h' calls hk _ hms ev
    cases Obs.«Ingress::muts_member_at».obs ev with
    | n0 x_m x_rest ld12 _ rfl rfl _ =>
      obtain ⟨z, zs, he, hz, -⟩ := Lib.rep_cons_of_load hms ld12
      subst he
      exact ⟨hz, rfl⟩
    | other _ _ _ _ _ hne48 _ _ _ =>
      exact absurd (by simp) hne48
  | succ k ih =>
    intro ms lp r h h' calls hk hlen hms ev
    cases Obs.«Ingress::muts_member_at».obs ev with
    | n0 _ _ _ hv43 _ _ _ =>
      have hk0 := natCast_eq_zero_of_lt (m := k + 1) (by omega) (Value.field.inj hv43)
      omega
    | other x_m x_rest cs55 v59 ld12 _ op80 ev57 _ =>
      obtain ⟨z, zs, he, -, hzs⟩ := Lib.rep_cons_of_load hms ld12
      subst he
      have hv59 : v59 = .field (k : F) := by
        rw [Lib.sub_one_inv op80]
        push_cast
        ring_nf
      rw [hv59] at ev57
      simp only [List.length_cons] at hk hlen
      exact ih (by omega) (by omega) hzs ev57

theorem projection_addr_spec (c : Ctx) {ms : List Ixon.MutConst} {b : Bytes.Address}
    {i : Nat} {lp bp r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hi : i < ms.length) (hlen : ms.length < 2 ^ 39)
    (good : Good c calls)
    (hms : Specs.Callees.MembersRep h ms lp)
    (hb : RepAddr h b bp)
    (ev : ObsFn W "Ingress::projection_addr" [lp, bp, .field (i : F)] h r h' calls) :
    ∃ a : Bytes.Address, RepAddr h' a r ∧
      ixAddr a = projAddr (Specs.Callees.memberProjInfo (ixAddr b) i ms[i]) := by
  obtain ⟨v1, m2, cs12, v31, m32, cs42, v198, m199, cs201, m231, m244, m257, m270, v282, m283,
    cs293, m306, cs321, ev14, ev44, sg206, hm239, hm252, hm265, hm278, hm314, ev295, ev323,
    hc332⟩ := Obs.«Ingress::projection_addr».obs ev
  obtain ⟨hmem, rfl⟩ := muts_member_at_spec i hi hlen hms ev14
  obtain ⟨ni, hni, hxi, rfl, rfl⟩ := Lib.u64_from_field_spec ev44
  injection hxi with hxi
  have hni_eq : ni = i := by
    have hv := congrArg ZMod.val hxi
    rw [val_natCast_small (by omega), val_natCast_small (by omega)] at hv
    exact hv.symm
  subst hni_eq
  have e1 : Heap.Extends m199 m231 := by rw [hm239]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends m231 m244 := by rw [hm252]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends m244 m257 := by rw [hm265]; exact Heap.Extends.snoc _ _
  have e4 : Heap.Extends m257 m270 := by rw [hm278]; exact Heap.Extends.snoc _ _
  have e5 : Heap.Extends m270 m306 := by rw [hm314]; exact Heap.Extends.snoc _ _
  have c1 : m306[m199.length]? = some (.construct Specs.Callees.ixExprListEnum "Nil" []) :=
    (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm239]; simp)
  have c2 : m306[m231.length]? = some (.construct addrListEnum "Nil" []) :=
    (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm252]; simp)
  have c3 : m306[m244.length]? = some (.construct Specs.Callees.ixUnivListEnum "Nil" []) :=
    (e4.trans e5).getElem?_eq (by rw [hm265]; simp)
  have c4 : m306[m257.length]? = some (.construct Specs.Callees.ixBinderListEnum "Nil" []) :=
    e5.getElem?_eq (by rw [hm278]; simp)
  have c5 : m306[m270.length]? = some (.construct byteListEnum "Nil" []) := by
    rw [hm314]; simp
  have hrepi : RepU64 m306 i.toUInt64 (TagN.u64Value i) := by
    have e := Lib.repU64_ofNatLT m306 (m := i) (by omega)
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hseg : m199 = h ∧
      Specs.Callees.ProjInfoRep m306
        (Specs.Callees.memberProjInfo (ixAddr b) i ms[i]) v198 := by
    rcases hmem with ⟨x, hmc⟩
    cases hmi : ms[i] with
    | defn d =>
      rw [hmi, Specs.Callees.mutCtor] at hmc
      cases sg206 with
      | Defn _ _ rfl rfl _ =>
        have E : Heap.Extends m199 m306 := e1.trans (e2.trans (e3.trans (e4.trans e5)))
        refine ⟨rfl, ?_⟩
        simp only [Specs.Callees.memberProjInfo, Specs.Callees.ProjInfoRep]
        exact ⟨TagN.u64Value i, bp, b, rfl, hrepi, Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
      | Indc _ _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
      | Recr _ _ _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
    | indc d =>
      rw [hmi, Specs.Callees.mutCtor] at hmc
      cases sg206 with
      | Defn _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
      | Indc _ _ _ rfl rfl _ =>
        have E : Heap.Extends m199 m306 := e1.trans (e2.trans (e3.trans (e4.trans e5)))
        refine ⟨rfl, ?_⟩
        simp only [Specs.Callees.memberProjInfo, Specs.Callees.ProjInfoRep]
        exact ⟨TagN.u64Value i, bp, b, rfl, hrepi, Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
      | Recr _ _ _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
    | recr d =>
      rw [hmi, Specs.Callees.mutCtor] at hmc
      cases sg206 with
      | Defn _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
      | Indc _ _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
      | Recr _ _ _ _ rfl rfl _ =>
        have E : Heap.Extends m199 m306 := e1.trans (e2.trans (e3.trans (e4.trans e5)))
        refine ⟨rfl, ?_⟩
        simp only [Specs.Callees.memberProjInfo, Specs.Callees.ProjInfoRep]
        exact ⟨TagN.u64Value i, bp, b, rfl, hrepi, Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
  have hbytes := put_constant_step c ev295 _ _
    (Specs.Callees.memberProjInfo (ixAddr b) i ms[i]) [] rfl
    ⟨_, _, _, _, _, rfl, hseg.2, RepLinkedList.nil c1, RepLinkedList.nil c2,
      RepLinkedList.nil c3, RepLinkedList.nil c4⟩
    (RepLinkedList.nil c5)
  have hgood_bta : Good c cs321 :=
    good.sub (by rw [hc332]; intro x hx; simp [hx])
  obtain ⟨a, ha, haddr⟩ := bytes_to_addr_step c ev323 v282 _ rfl hgood_bta hbytes
  refine ⟨a, ha, ?_⟩
  rw [haddr, bytes_mk_toList]
  rfl

theorem drop_succ_of_drop_cons {α : Type} :
    ∀ (xs : List α) (i : Nat) {x : α} {rest : List α},
      xs.drop i = x :: rest →
        ∃ (hi : i < xs.length), xs[i] = x ∧ xs.drop (i + 1) = rest := by
  intro xs
  induction xs with
  | nil =>
    intro i x rest h
    simp at h
  | cons y ys ih =>
    intro i x rest h
    cases i with
    | zero =>
      simp only [List.drop_zero, List.cons.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨by simp, rfl, rfl⟩
    | succ k =>
      simp only [List.drop_succ_cons] at h
      obtain ⟨hk, hget, hdrop⟩ := ih k h
      exact ⟨by simp [hk], hget, hdrop⟩

theorem mapIdx_cons_eq {α β : Type} (f : Nat → α → β) (x : α) (xs : List α) :
    (x :: xs).mapIdx f = f 0 x :: xs.mapIdx (fun k y => f (k + 1) y) := by
  apply List.ext_getElem?
  intro n
  cases n with
  | zero => simp [List.getElem?_mapIdx]
  | succ k => simp [List.getElem?_mapIdx]

theorem build_recur_addrs_walk_spec (c : Ctx) {ms : List Ixon.MutConst} {b : Bytes.Address}
    {lp bp : SourceValue F} (hlen : ms.length < 2 ^ 39) :
    ∀ (cur : List Ixon.MutConst) {i : Nat} {cur_p r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)},
      ms.drop i = cur →
      Good c calls →
      Specs.Callees.MembersRep h ms lp →
      RepAddr h b bp →
      Specs.Callees.MembersRep h cur cur_p →
      ObsFn W "Ingress::build_recur_addrs_walk" [lp, bp, cur_p, .field (i : F)] h r h' calls →
      ∃ as : List Bytes.Address, RepList addrListEnum RepAddr h' as r ∧
        as.map ixAddr =
          cur.mapIdx fun k m => projAddr (Specs.Callees.memberProjInfo (ixAddr b) (i + k) m) := by
  intro cur
  induction cur with
  | nil =>
    intro i cur_p r h h' calls _ _ _ _ hcur ev
    cases Obs.«Ingress::build_recur_addrs_walk».obs ev with
    | Nil _ he24 hm23 _ =>
      subst he24 hm23
      exact ⟨[], Lib.rep_store_nil h, rfl⟩
    | Cons _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ _ =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hcur ld12
      cases he
  | cons m rest ih =>
    intro i cur_p r h h' calls hdrop good hms hb hcur ev
    cases Obs.«Ingress::build_recur_addrs_walk».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hcur ld12
    | Cons w36 x_rest v55 v56 m58 cs66 m94 cs102 v108 ld12 he51 hm50 ev68 op143 ev104 hc145 =>
      obtain ⟨z, zs, he, -, hrest_rep⟩ := Lib.rep_cons_of_load hcur ld12
      injection he with rfl rfl
      obtain ⟨hi, hmi, hdrop'⟩ := drop_succ_of_drop_cons ms i hdrop
      have hgood1 : Good c cs66 := good.sub (by rw [hc145]; intro x hx; simp [hx])
      have hgood2 : Good c cs102 := good.sub (by rw [hc145]; intro x hx; simp [hx])
      obtain ⟨a, ha, ha_addr⟩ := projection_addr_spec c hi hlen hgood1 hms hb ev68
      rw [hmi] at ha_addr
      have ext1 := ev68.heap_extends
      have hms' : Specs.Callees.MembersRep m58 ms lp :=
        RepLinkedList.mono (fun _ hx => hx) ext1 hms
      have hb' : RepAddr m58 b bp := Bytes.repAddressRef_heapMono₂ addrTy ext1 hb
      have hrest_rep' : Specs.Callees.MembersRep m58 rest x_rest :=
        RepLinkedList.mono (fun _ hx => hx) ext1 hrest_rep
      have hv108 : v108 = .field ((i + 1 : Nat) : F) := by
        rw [add_field_inv op143]
        push_cast
        rfl
      rw [hv108] at ev104
      obtain ⟨as_tail, has_tail, hmap_tail⟩ :=
        ih hdrop' hgood2 hms' hb' hrest_rep' ev104
      have ha' : RepAddr m94 a v55 := Bytes.repAddressRef_heapMono₂ addrTy ev104.heap_extends ha
      subst he51 hm50
      refine ⟨a :: as_tail,
        Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy) ha' has_tail, ?_⟩
      rw [List.map_cons, ha_addr, hmap_tail, mapIdx_cons_eq]
      simp only [Nat.add_zero]
      congr 1
      apply List.ext_getElem?
      intro k
      simp only [List.getElem?_mapIdx]
      cases rest[k]? with
      | none => rfl
      | some mk =>
        simp only [Option.map_some, Option.some.injEq]
        rw [show i + 1 + k = i + (k + 1) by omega]

end ProjAddrAux

/-- `Ingress::build_recur_addrs`: builds, serializes, and hashes the projection records of a
mutual block's members in order. -/
theorem build_recur_addrs_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Ingress::build_recur_addrs" args h r h' calls) :
    Specs.Callees.build_recur_addrs c args h r h' calls := by
  intro lp bp ms b hargs good hms hb
  subst hargs
  obtain ⟨cs4, ev6, hc38⟩ := Obs.«Ingress::build_recur_addrs».obs ev
  have hcall : (⟨"Ingress::build_recur_addrs_walk", [lp, bp, lp, .field 0], h⟩ : Call F) ∈ calls := by
    rw [hc38]; simp
  have hlen : ms.length < 2 ^ 39 :=
    RomBound.bounded_length_lt good.2 hcall (by simp) hms
  have hgood4 : Good c cs4 := good.sub (by rw [hc38]; intro x hx; simp [hx])
  have ev6' : ObsFn W "Ingress::build_recur_addrs_walk" [lp, bp, lp, .field ((0 : Nat) : F)]
      h r h' cs4 := by
    simpa using ev6
  obtain ⟨as, has, hmap⟩ :=
    ProjAddrAux.build_recur_addrs_walk_spec c hlen ms (i := 0) (by simp) hgood4 hms hb hms ev6'
  refine ⟨as, has, ?_⟩
  simpa using hmap

end IxVM.Refinement.Core
