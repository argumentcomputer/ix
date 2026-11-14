import IxVMRefinement.Core.Registry
import IxVMRefinement.Lib.WordHints
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.Obs.IxonSerialize0

/-! # TagN and little-endian `UInt64` writers (`IxonSerialize0`)

Auxiliary refinement lemmas for `IxonSerialize::put_u64_le`, `put_tagn_wide`,
`put_tagn_tail`, `put_tagn0`, and `put_tagn4` used by projection-record serialization. -/

namespace IxVM.Refinement.Core.ProjAddrAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

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

theorem div_mod_zero {d p : Nat} (h : d < p) : d / p % 256 = 0 := by
  rw [Nat.div_eq_of_lt h]
  rfl

theorem sum_eq_zero_4 {a b c e : Nat}
    (ha : a < 256) (hb : b < 256) (hc : c < 256) (he : e < 256)
    (h : ((a + b + c + e : Nat) : F) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  have h0 := natCast_eq_zero_of_lt (by omega) h
  omega

theorem sum_eq_zero_5 {a b c e f : Nat}
    (ha : a < 256) (hb : b < 256) (hc : c < 256) (he : e < 256) (hf : f < 256)
    (h : ((a + b + c + e + f : Nat) : F) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 ∧ f = 0 := by
  have h0 := natCast_eq_zero_of_lt (by omega) h
  omega

theorem sum_eq_zero_6 {a b c e f g : Nat}
    (ha : a < 256) (hb : b < 256) (hc : c < 256) (he : e < 256) (hf : f < 256) (hg : g < 256)
    (h : ((a + b + c + e + f + g : Nat) : F) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 := by
  have h0 := natCast_eq_zero_of_lt (by omega) h
  omega

theorem sum_eq_zero_7 {a b c e f g k : Nat}
    (ha : a < 256) (hb : b < 256) (hc : c < 256) (he : e < 256) (hf : f < 256)
    (hg : g < 256) (hk : k < 256)
    (h : ((a + b + c + e + f + g + k : Nat) : F) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ k = 0 := by
  have h0 := natCast_eq_zero_of_lt (by omega) h
  omega

theorem leBytes8_lt_256 {b0 : Nat} (hb0 : b0 < 256) :
    Lib.leBytes8 b0 0 0 0 0 0 0 0 < 256 := by
  simpa [Lib.leBytes8] using hb0

theorem leBytes8_lt_65536 {b0 b1 : Nat} (hb0 : b0 < 256) (hb1 : b1 < 256) :
    Lib.leBytes8 b0 b1 0 0 0 0 0 0 < 65536 := by
  simp only [Lib.leBytes8, Nat.mul_zero, Nat.add_zero]
  omega

theorem leBytes8_lt_16777216 {b0 b1 b2 : Nat}
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) :
    Lib.leBytes8 b0 b1 b2 0 0 0 0 0 < 16777216 := by
  simp only [Lib.leBytes8, Nat.mul_zero, Nat.add_zero]
  omega

theorem leBytes8_lt_4294967296 {b0 b1 b2 b3 : Nat}
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256) :
    Lib.leBytes8 b0 b1 b2 b3 0 0 0 0 < 4294967296 := by
  simp only [Lib.leBytes8, Nat.mul_zero, Nat.add_zero]
  omega

theorem wrap_sub_mod {d K S M : Nat} (hKS : K + S = M) (hd : d < M) (hge : ¬ d < K) :
    (d + S) % M = d - K := by
  have heq : d + S = (d - K) + M := by omega
  rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem wrap_div_zero {w K S M : Nat} (hKS : K + S = M) (hdiv : (w + S) / M = 0) :
    w < K := by
  by_contra hge
  have hgeM : M ≤ w + S := by omega
  have hpos : 0 < (w + S) / M := Nat.div_pos hgeM (by omega)
  omega

theorem wrap_div_lt_two {w S M : Nat} (hw : w < M) (hS : S < M) :
    (w + S) / M < 2 := by
  have hlt : w + S < 2 * M := by omega
  exact (Nat.div_lt_iff_lt_mul (by omega)).mpr hlt

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
  have hd' : d / 256 < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hd
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
  have f1 : d / 256 / 256 % 256 = d / 65536 % 256 := by rw [Nat.div_div_eq_div_mul]
  have f2 : d / 256 / 65536 % 256 = d / 16777216 % 256 := by rw [Nat.div_div_eq_div_mul]
  have f3 : d / 256 / 16777216 % 256 = d / 4294967296 % 256 := by rw [Nat.div_div_eq_div_mul]
  have f4 : d / 256 / 4294967296 % 256 = d / 1099511627776 % 256 := by rw [Nat.div_div_eq_div_mul]
  have f5 : d / 256 / 1099511627776 % 256 = d / 281474976710656 % 256 := by rw [Nat.div_div_eq_div_mul]
  have f6 : d / 256 / 281474976710656 % 256 = d / 72057594037927936 % 256 := by rw [Nat.div_div_eq_div_mul]
  have f7 : d / 256 / 72057594037927936 % 256 = 0 := by
    rw [Nat.div_div_eq_div_mul]
    change d / 18446744073709551616 % 256 = 0
    rw [Nat.div_eq_of_lt hd]
  simp only [TagN.u64Value, f1, f2, f3, f4, f5, f6, f7, Nat.cast_zero]

/-! ## Pure byte-slice models of `Ixon.putU64TrimmedLEAux` and `Ixon.putTagN` -/

def Writes (putm : Ixon.PutM Unit) (bytes : ByteArray) : Prop :=
  ∀ before, putm.run before = ((), before ++ bytes)

theorem Writes.pure : Writes (pure () : Ixon.PutM Unit) ByteArray.empty := by
  intro before
  change (StateT.pure () : Ixon.PutM Unit) before = _
  simp only [ByteArray.append_empty]
  rfl

theorem Writes.bind {leftM rightM : Ixon.PutM Unit} {left right : ByteArray}
    (hleft : Writes leftM left) (hright : Writes rightM right) :
    Writes (leftM >>= fun _ => rightM) (left ++ right) := by
  intro before
  change StateT.bind leftM (fun _ => rightM) before = _
  have hl := hleft before
  change leftM before = ((), before ++ left) at hl
  have hr := hright (before ++ left)
  change rightM (before ++ left) = ((), (before ++ left) ++ right) at hr
  rw [StateT.bind, hl]
  change rightM (before ++ left) = _
  rw [hr]
  simp [ByteArray.append_assoc]

theorem Writes.runPut {putm : Ixon.PutM Unit} {bytes : ByteArray}
    (h : Writes putm bytes) : Ixon.runPut putm = bytes := by
  rw [Ixon.runPut, h ByteArray.empty]
  simp

theorem putU8_writes (byte : UInt8) :
    Writes (Ixon.putU8 byte) [byte].toByteArray := by
  intro before
  simp only [Ixon.putU8, StateT.run]
  change StateT.modifyGet _ before = _
  simp [StateT.modifyGet]
  change ((), before.push byte) = _
  rfl

theorem putBytes_writes (bytes : ByteArray) :
    Writes (Ixon.putBytes bytes) bytes := by
  intro before
  simp only [Ixon.putBytes, StateT.run]
  change StateT.modifyGet _ before = _
  simp [StateT.modifyGet]
  rfl

def trimmedBytes : UInt64 → Nat → ByteArray
  | _, 0 => ByteArray.empty
  | x, len + 1 => [x.toUInt8].toByteArray ++ trimmedBytes (x >>> 8) len

theorem putU64TrimmedLEAux_writes (x : UInt64) (len : Nat) :
    Writes (Ixon.putU64TrimmedLEAux x len) (trimmedBytes x len) := by
  induction len generalizing x with
  | zero =>
    simpa [Ixon.putU64TrimmedLEAux, trimmedBytes] using Writes.pure
  | succ len ih =>
    simpa [Ixon.putU64TrimmedLEAux, trimmedBytes] using
      (putU8_writes x.toUInt8).bind (ih (x >>> 8))

def tagNBytes (f : Nat) (flag : UInt8) (value : UInt64) : ByteArray :=
  let v := value.toNat
  let lead := 2 ^ (8 - f - 1)
  let mbit := 2 ^ (8 - f - 2)
  if v < Ixon.tagNEnd1 f then
    [Ixon.tagNHeader f flag v].toByteArray
  else if v < Ixon.tagNEnd2 f then
    [Ixon.tagNHeader f flag (lead + (v - Ixon.tagNEnd1 f) / 256)].toByteArray ++
      [((v - Ixon.tagNEnd1 f) % 256).toUInt8].toByteArray
  else if v < Ixon.tagNEnd3 f then
    [Ixon.tagNHeader f flag (lead + mbit)].toByteArray ++
      trimmedBytes (v - Ixon.tagNEnd2 f).toUInt64 2
  else if v < Ixon.tagNEnd4 f then
    [Ixon.tagNHeader f flag (lead + mbit + 1)].toByteArray ++
      trimmedBytes (v - Ixon.tagNEnd3 f).toUInt64 3
  else if v < Ixon.tagNEnd5 f then
    [Ixon.tagNHeader f flag (lead + mbit + 2)].toByteArray ++
      trimmedBytes (v - Ixon.tagNEnd4 f).toUInt64 4
  else
    [Ixon.tagNHeader f flag (lead + mbit + 3)].toByteArray ++
      trimmedBytes (v - Ixon.tagNEnd5 f).toUInt64 8

def tag0Bytes (value : UInt64) : ByteArray := tagNBytes 0 0 value

def tag4Bytes (flag : UInt8) (value : UInt64) : ByteArray := tagNBytes 4 flag value

theorem putTagN_writes (f : Nat) (flag : UInt8) (value : UInt64) :
    Writes (Ixon.putTagN f flag value) (tagNBytes f flag value) := by
  unfold Ixon.putTagN tagNBytes
  simp only
  by_cases h1 : value.toNat < Ixon.tagNEnd1 f
  · simp only [h1, ↓reduceIte]
    exact putU8_writes _
  by_cases h2 : value.toNat < Ixon.tagNEnd2 f
  · simp only [h1, h2, ↓reduceIte]
    exact (putU8_writes _).bind (putU8_writes _)
  by_cases h3 : value.toNat < Ixon.tagNEnd3 f
  · simp only [h1, h2, h3, ↓reduceIte]
    exact (putU8_writes _).bind (putU64TrimmedLEAux_writes _ _)
  by_cases h4 : value.toNat < Ixon.tagNEnd4 f
  · simp only [h1, h2, h3, h4, ↓reduceIte]
    exact (putU8_writes _).bind (putU64TrimmedLEAux_writes _ _)
  by_cases h5 : value.toNat < Ixon.tagNEnd5 f
  · simp only [h1, h2, h3, h4, h5, ↓reduceIte]
    exact (putU8_writes _).bind (putU64TrimmedLEAux_writes _ _)
  · simp only [h1, h2, h3, h4, h5, ↓reduceIte]
    exact (putU8_writes _).bind (putU64TrimmedLEAux_writes _ _)

theorem put_u64_le_spec :
    ∀ (k : Nat) {d : Nat} {x_rest r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)} {rest : List UInt8},
      k ≤ 8 → d < 18446744073709551616 →
      ObsFn W "IxonSerialize::put_u64_le" [TagN.u64Value d, .field (k : F), x_rest]
        h r h' calls →
      RepBytes h rest x_rest →
      RepBytes h' ((trimmedBytes d.toUInt64 k).data.toList ++ rest) r := by
  intro k
  induction k with
  | zero =>
    intro d x_rest r h h' calls rest _ _ ev hrest
    cases Obs.«IxonSerialize::put_u64_le».obs ev with
    | n0 _ hr hh _ =>
      subst hr hh
      simpa [trimmedBytes] using hrest
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
      have hrec := ih (d := d / 256) (by omega) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hd)
        ev176 hrest
      have hb1 : (.field ((d % 256 : Nat) : F) : SourceValue F) =
          .field (d.toUInt64.toUInt8.toNat : F) := by
        rw [toUInt64_lowByte hd]
      have hcons := repBytes_cons hb1 hrec hm151 he152
      simpa [trimmedBytes, toUInt64_shift8 hd] using hcons

theorem put_tagn_wide_c3 {d : Nat} {x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hd : d < 18446744073709551616)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 3, TagN.u64Value d, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      (((195 : UInt8) :: (trimmedBytes d.toUInt64 8).data.toList) ++ rest) r := by
  cases Obs.«IxonSerialize::put_tagn_wide».obs ev with
  | n0_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
  | n0_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
  | n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
  | n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
  | n2_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
  | n2_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
  | n3 _ _ _ _ _ _ _ _ v1080 v1081 m1083 _ v1094 m1111 _ _ _ _ _ _ he1076 hm1075 op1108 ev1093
      ev1121 _ =>
    have hv1094 : v1094 = .field 195 := by
      rw [add_field_inv op1108]; congr 1; decide
    rw [hv1094] at ev1093
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev1093
    have hle := put_u64_le_spec 8 (by omega) hd ev1121 hrest
    have hb : (.field 195 : SourceValue F) = .field ((195 : UInt8).toNat : F) := by
      simp only [show (195 : UInt8).toNat = 195 from rfl, Nat.cast_ofNat]
    rw [List.cons_append]
    exact repBytes_cons hb hle hm1075 he1076

theorem put_tagn_wide_c2 {d : Nat} {x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hd : d < 18446744073709551616)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 2, TagN.u64Value d, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((if d < 4294967296 then
          (194 : UInt8) :: (trimmedBytes d.toUInt64 4).data.toList
        else
          (195 : UInt8) ::
            (trimmedBytes (d - 4294967296).toUInt64 8).data.toList) ++ rest) r := by
  cases Obs.«IxonSerialize::put_tagn_wide».obs ev with
  | n0_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
  | n0_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
  | n1_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
  | n1_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
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
    rcases sum_eq_zero_4 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (by push_cast; exact hsumF) with
      ⟨e4, e5, e6, e7⟩
    have hd_lt : d < 4294967296 := by
      have hb := Lib.leBytes8_bytes hd
      rw [e4, e5, e6, e7] at hb
      rw [← hb]
      exact leBytes8_lt_4294967296 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    rw [ite_eq_left hd_lt]
    have hv872 : v872 = .field 194 := by rw [add_field_inv op886]; congr 1; decide
    rw [hv872] at ev871
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev871
    have hle := put_u64_le_spec 4 (by omega) hd ev899 hrest
    have hb : (.field 194 : SourceValue F) = .field ((194 : UInt8).toNat : F) := by
      simp only [show (194 : UInt8).toNat = 194 from rfl, Nat.cast_ofNat]
    rw [List.cons_append]
    exact repBytes_cons hb hle hm853 he854
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
      have e1 : d / 4294967296 % 256 = 0 := div_mod_zero hlt
      have e2 : d / 1099511627776 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e3 : d / 281474976710656 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e4 : d / 72057594037927936 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      simp [e1, e2, e3, e4]
    rw [ite_eq_right hd_ge]
    let subVal : Nat := Lib.leBytes8 0 0 0 0 255 255 255 255
    have hsub_val : subVal = 18446744069414584320 := by decide
    have hsub_lt : subVal < 18446744073709551616 := by rw [hsub_val]; decide
    have hsub_tup : (.tuple [.field 0, .field 0, .field 0, .field 0,
        .field 255, .field 255, .field 255, .field 255] : SourceValue F) =
        TagN.u64Value subVal := by
      simpa [subVal] using (Lib.u64Value_leBytes8 (F := F)
        (b0 := 0) (b1 := 0) (b2 := 0) (b3 := 0) (b4 := 255) (b5 := 255) (b6 := 255) (b7 := 255)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    rw [hsub_tup] at ev941
    have hd_rep := Lib.repU64_ofNatLT h hd
    have hsub_rep := Lib.repU64_ofNatLT h hsub_lt
    obtain ⟨hadd, rfl⟩ := Lib.u64_add_spec hd_rep hsub_rep ev941
    simp only [Value.tuple.injEq, List.cons.injEq, and_true, UInt64.toNat_ofNatLT] at hadd
    rcases hadd with ⟨hx_next, -⟩
    have hmod : (d + subVal) % 18446744073709551616 = d - 4294967296 := by
      rw [hsub_val]
      exact wrap_sub_mod (by decide) hd hd_ge
    rw [hmod] at hx_next
    subst hx_next
    exact put_tagn_wide_c3 (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hd) ev1034 hrest

theorem put_tagn_wide_c1 {d : Nat} {x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hd : d < 18446744073709551616)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 1, TagN.u64Value d, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((if d < 16777216 then
          (193 : UInt8) :: (trimmedBytes d.toUInt64 3).data.toList
        else if d - 16777216 < 4294967296 then
          (194 : UInt8) ::
            (trimmedBytes (d - 16777216).toUInt64 4).data.toList
        else
          (195 : UInt8) ::
            (trimmedBytes (d - 16777216 - 4294967296).toUInt64 8).data.toList) ++
        rest) r := by
  cases Obs.«IxonSerialize::put_tagn_wide».obs ev with
  | n0_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
  | n0_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact absurd (Value.field.inj hv) (by decide)
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
    rcases sum_eq_zero_5 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (by push_cast; exact hsumF) with ⟨e3, e4, e5, e6, e7⟩
    have hd_lt : d < 16777216 := by
      have hb := Lib.leBytes8_bytes hd
      rw [e3, e4, e5, e6, e7] at hb
      rw [← hb]
      exact leBytes8_lt_16777216 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide))
    rw [ite_eq_left hd_lt]
    have hv557 : v557 = .field 193 := by rw [add_field_inv op571]; congr 1; decide
    rw [hv557] at ev556
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev556
    have hle := put_u64_le_spec 3 (by omega) hd ev584 hrest
    have hb : (.field 193 : SourceValue F) = .field ((193 : UInt8).toNat : F) := by
      simp only [show (193 : UInt8).toNat = 193 from rfl, Nat.cast_ofNat]
    rw [List.cons_append]
    exact repBytes_cons hb hle hm538 he539
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
      have e1 : d / 16777216 % 256 = 0 := div_mod_zero hlt
      have e2 : d / 4294967296 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e3 : d / 1099511627776 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e4 : d / 281474976710656 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e5 : d / 72057594037927936 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      simp [e1, e2, e3, e4, e5]
    rw [ite_eq_right hd_ge]
    let subVal : Nat := Lib.leBytes8 0 0 0 255 255 255 255 255
    have hsub_val : subVal = 18446744073692774400 := by decide
    have hsub_lt : subVal < 18446744073709551616 := by rw [hsub_val]; decide
    have hsub_tup : (.tuple [.field 0, .field 0, .field 0, .field 255,
        .field 255, .field 255, .field 255, .field 255] : SourceValue F) =
        TagN.u64Value subVal := by
      simpa [subVal] using (Lib.u64Value_leBytes8 (F := F)
        (b0 := 0) (b1 := 0) (b2 := 0) (b3 := 255) (b4 := 255) (b5 := 255) (b6 := 255) (b7 := 255)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    rw [hsub_tup] at ev626
    have hd_rep := Lib.repU64_ofNatLT h hd
    have hsub_rep := Lib.repU64_ofNatLT h hsub_lt
    obtain ⟨hadd, rfl⟩ := Lib.u64_add_spec hd_rep hsub_rep ev626
    simp only [Value.tuple.injEq, List.cons.injEq, and_true, UInt64.toNat_ofNatLT] at hadd
    rcases hadd with ⟨hx_next, -⟩
    have hmod : (d + subVal) % 18446744073709551616 = d - 16777216 := by
      rw [hsub_val]
      exact wrap_sub_mod (by decide) hd hd_ge
    rw [hmod] at hx_next
    subst hx_next
    exact put_tagn_wide_c2 (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hd) ev719 hrest

theorem put_tagn_wide_c0 {d : Nat} {x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hd : d < 18446744073709551616)
    (ev : ObsFn W "IxonSerialize::put_tagn_wide"
      [.field 192, .field 0, TagN.u64Value d, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h'
      ((if d < 65536 then
          (192 : UInt8) :: (trimmedBytes d.toUInt64 2).data.toList
        else if d - 65536 < 16777216 then
          (193 : UInt8) ::
            (trimmedBytes (d - 65536).toUInt64 3).data.toList
        else if d - 65536 - 16777216 < 4294967296 then
          (194 : UInt8) ::
            (trimmedBytes (d - 65536 - 16777216).toUInt64 4).data.toList
        else
          (195 : UInt8) ::
            (trimmedBytes
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
    rcases sum_eq_zero_6 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide)) (by push_cast; exact hsumF) with
      ⟨e2, e3, e4, e5, e6, e7⟩
    have hd_lt : d < 65536 := by
      have hb := Lib.leBytes8_bytes hd
      rw [e2, e3, e4, e5, e6, e7] at hb
      rw [← hb]
      exact leBytes8_lt_65536 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    rw [ite_eq_left hd_lt]
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev227
    have hle := put_u64_le_spec 2 (by omega) hd ev247 hrest
    have hb : (.field 192 : SourceValue F) = .field ((192 : UInt8).toNat : F) := by
      simp only [show (192 : UInt8).toNat = 192 from rfl, Nat.cast_ofNat]
    rw [List.cons_append]
    exact repBytes_cons hb hle hm209 he210
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
      have e1 : d / 65536 % 256 = 0 := div_mod_zero hlt
      have e2 : d / 16777216 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e3 : d / 4294967296 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e4 : d / 1099511627776 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e5 : d / 281474976710656 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e6 : d / 72057594037927936 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      simp [e1, e2, e3, e4, e5, e6]
    rw [ite_eq_right hd_ge]
    let subVal : Nat := Lib.leBytes8 0 0 255 255 255 255 255 255
    have hsub_val : subVal = 18446744073709486080 := by decide
    have hsub_lt : subVal < 18446744073709551616 := by rw [hsub_val]; decide
    have hsub_tup : (.tuple [.field 0, .field 0, .field 255, .field 255,
        .field 255, .field 255, .field 255, .field 255] : SourceValue F) =
        TagN.u64Value subVal := by
      simpa [subVal] using (Lib.u64Value_leBytes8 (F := F)
        (b0 := 0) (b1 := 0) (b2 := 255) (b3 := 255) (b4 := 255) (b5 := 255) (b6 := 255) (b7 := 255)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    rw [hsub_tup] at ev289
    have hd_rep := Lib.repU64_ofNatLT h hd
    have hsub_rep := Lib.repU64_ofNatLT h hsub_lt
    obtain ⟨hadd, rfl⟩ := Lib.u64_add_spec hd_rep hsub_rep ev289
    simp only [Value.tuple.injEq, List.cons.injEq, and_true, UInt64.toNat_ofNatLT] at hadd
    rcases hadd with ⟨hx_next, -⟩
    have hmod : (d + subVal) % 18446744073709551616 = d - 65536 := by
      rw [hsub_val]
      exact wrap_sub_mod (by decide) hd hd_ge
    rw [hmod] at hx_next
    subst hx_next
    exact put_tagn_wide_c1 (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hd) ev382 hrest

theorem put_tagn_tail_zero_spec {w : UInt64} {x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hw128 : ¬ w.toNat < 128)
    (ev : ObsFn W "IxonSerialize::put_tagn_tail"
      [.field 0, .field 64, TagN.u64Value w.toNat, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((tag0Bytes w).data.toList ++ rest) r := by
  have hw_lt := Lib.u64_toNat_lt w
  let subVal : Nat := Lib.leBytes8 128 191 255 255 255 255 255 255
  have hsub_val : subVal = 18446744073709535104 := by decide
  have hsub_lt : subVal < 18446744073709551616 := by rw [hsub_val]; decide
  have hsub_tup : (.tuple [.field 128, .field 191, .field 255, .field 255,
      .field 255, .field 255, .field 255, .field 255] : SourceValue F) =
      TagN.u64Value subVal := by
    simpa [subVal] using (Lib.u64Value_leBytes8 (F := F)
      (b0 := 128) (b1 := 191) (b2 := 255) (b3 := 255) (b4 := 255) (b5 := 255) (b6 := 255) (b7 := 255)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).symm
  cases Obs.«IxonSerialize::put_tagn_tail».obs ev with
  | n0 m2 _ v32 v33 m41 _ v52 y60 m77 _ v88 x_d x_at_least_r2 m154 _ m181 _ v194 v195 m197 _
      v208 y226 x_lo x_no_borrow v255 x263 m265 x271 y272 m273 _ v285 _ v318 m321 _ v332 x339
      y348 m367 op74 op66 ev51 op102 ev87 ev14 ev167 pr217 ev207 op240 op232 ev193 pr294 ev284
      ev301 op278 op270 he314 hm313 op363 op354 op346 ev331 hm375 _ =>
    have hy60 : y60 = .field 128 := by rw [mul_field_inv op74]; congr 1; decide
    subst hy60
    have hv52 : v52 = .field 128 := by rw [sub_field_inv op66]; congr 1; decide
    subst hv52
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev51
    have hv88 : v88 = .field 191 := by rw [sub_field_inv op102]; congr 1; decide
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
    have hlt2 := wrap_div_lt_two hw_lt hsub_lt
    have hdiv0 : (w.toNat + subVal) / 18446744073709551616 = 0 :=
      natCast_eq_zero_of_lt (Nat.lt_trans hlt2 (by decide)) (Value.field.inj hcF)
    have hw_r2 : w.toNat < 16512 := by
      rw [hsub_val] at hdiv0
      exact wrap_div_zero (by decide) hdiv0
    have hp0 : projectValue (TagN.u64Value w.toNat : SourceValue F) 0 =
        .ok (.field ((w.toNat % 256 : Nat) : F)) := rfl
    have hv208 := Except.ok.inj (hp0.symm.trans pr217)
    subst hv208
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev207
    have hy226 : y226 = .field 128 := by rw [mul_field_inv op240]; congr 1; decide
    subst hy226
    have hv195 : v195 = .field ((128 : Nat) : F) := by rw [sub_field_inv op232]; congr 1; decide
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
    have hy348 : y348 = .field 128 := by rw [mul_field_inv op363]; congr 1; decide
    subst hy348
    have hx339 : x339 = .field 128 := by rw [add_field_inv op354]; congr 1; decide
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
    have hbytes : (tag0Bytes w).data.toList =
        Ixon.tagNHeader 0 0 (128 + (w.toNat - 128) / 256) ::
          [((w.toNat - 128) % 256).toUInt8] := by
      unfold tag0Bytes tagNBytes
      dsimp only []
      rw [he1, if_neg hw128, he2, if_pos hw_r2]
      have hp2 : 2 ^ (8 - 0 - 1) = 128 := rfl
      rw [hp2, data_toList_append, data_toList_singleton, data_toList_singleton]
      rfl
    rw [hbytes, List.cons_append, List.singleton_append]
    exact hstep2
  | n1 m2 _ v32 v33 m41 _ v52 y60 m77 _ v88 x_d x_at_least_r2 m154 _ _ v407 y418 op74 op66 ev51
      op102 ev87 ev14 ev167 op433 op424 ev406 _ =>
    have hy60 : y60 = .field 128 := by rw [mul_field_inv op74]; congr 1; decide
    subst hy60
    have hv52 : v52 = .field 128 := by rw [sub_field_inv op66]; congr 1; decide
    subst hv52
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev51
    have hv88 : v88 = .field 191 := by rw [sub_field_inv op102]; congr 1; decide
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
    have hw_ge2 : ¬ w.toNat < 16512 := by
      intro hlt
      have hsum_lt : w.toNat + subVal < 18446744073709551616 := by
        rw [hsub_val]
        have : w.toNat + 18446744073709535104 < 16512 + 18446744073709535104 :=
          Nat.add_lt_add_right hlt _
        exact Nat.lt_of_lt_of_eq this (by decide)
      have h0 : (w.toNat + subVal) / 18446744073709551616 = 0 := Nat.div_eq_of_lt hsum_lt
      rw [h0] at hcF
      exact absurd (Value.field.inj hcF) (by decide)
    have hmod : (w.toNat + subVal) % 18446744073709551616 = w.toNat - 16512 := by
      rw [hsub_val]
      exact wrap_sub_mod (by decide) hw_lt hw_ge2
    rw [hmod] at hx_d
    subst hx_d
    have hy418 : y418 = .field 192 := by rw [mul_field_inv op433]; congr 1; decide
    subst hy418
    have hv407 : v407 = .field 192 := by rw [add_field_inv op424]; congr 1; decide
    subst hv407
    have hwide := put_tagn_wide_c0 (d := w.toNat - 16512)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hw_lt) ev406 hrest
    have he1 : Ixon.tagNEnd1 0 = 128 := rfl
    have he2 : Ixon.tagNEnd2 0 = 16512 := rfl
    have he3 : Ixon.tagNEnd3 0 = 82048 := rfl
    have he4 : Ixon.tagNEnd4 0 = 16859264 := rfl
    have he5 : Ixon.tagNEnd5 0 = 4311826560 := rfl
    have hh0 : Ixon.tagNHeader 0 0 (2 ^ (8 - 0 - 1) + 2 ^ (8 - 0 - 2)) = (192 : UInt8) := rfl
    have hh1 : Ixon.tagNHeader 0 0 (2 ^ (8 - 0 - 1) + 2 ^ (8 - 0 - 2) + 1) = (193 : UInt8) := rfl
    have hh2 : Ixon.tagNHeader 0 0 (2 ^ (8 - 0 - 1) + 2 ^ (8 - 0 - 2) + 2) = (194 : UInt8) := rfl
    have hh3 : Ixon.tagNHeader 0 0 (2 ^ (8 - 0 - 1) + 2 ^ (8 - 0 - 2) + 3) = (195 : UInt8) := rfl
    have hbytes : (tag0Bytes w).data.toList =
        (if w.toNat - 16512 < 65536 then
          (192 : UInt8) :: (trimmedBytes (w.toNat - 16512).toUInt64 2).data.toList
        else if w.toNat - 16512 - 65536 < 16777216 then
          (193 : UInt8) :: (trimmedBytes (w.toNat - 16512 - 65536).toUInt64 3).data.toList
        else if w.toNat - 16512 - 65536 - 16777216 < 4294967296 then
          (194 : UInt8) ::
            (trimmedBytes (w.toNat - 16512 - 65536 - 16777216).toUInt64 4).data.toList
        else
          (195 : UInt8) ::
            (trimmedBytes
              (w.toNat - 16512 - 65536 - 16777216 - 4294967296).toUInt64 8).data.toList) := by
      unfold tag0Bytes tagNBytes
      dsimp only []
      rw [he1, if_neg hw128, he2, if_neg hw_ge2, he3, he4, he5, hh0, hh1, hh2, hh3]
      by_cases h3 : w.toNat < 82048
      · have hd3 : w.toNat - 16512 < 65536 := by omega
        rw [if_pos h3, if_pos hd3, data_toList_append, data_toList_singleton]
        rfl
      · have hd3 : ¬ w.toNat - 16512 < 65536 := by omega
        have hs3 : w.toNat - 16512 - 65536 = w.toNat - 82048 := by omega
        rw [if_neg h3, if_neg hd3, hs3]
        by_cases h4 : w.toNat < 16859264
        · have hd4 : w.toNat - 82048 < 16777216 := by omega
          rw [if_pos h4, if_pos hd4, data_toList_append, data_toList_singleton]
          rfl
        · have hd4 : ¬ w.toNat - 82048 < 16777216 := by omega
          have hs4 : w.toNat - 82048 - 16777216 = w.toNat - 16859264 := by omega
          rw [if_neg h4, if_neg hd4, hs4]
          by_cases h5 : w.toNat < 4311826560
          · have hd5 : w.toNat - 16859264 < 4294967296 := by omega
            rw [if_pos h5, if_pos hd5, data_toList_append, data_toList_singleton]
            rfl
          · have hd5 : ¬ w.toNat - 16859264 < 4294967296 := by omega
            have hs5 : w.toNat - 16859264 - 4294967296 = w.toNat - 4311826560 := by omega
            rw [if_neg h5, if_neg hd5, hs5, data_toList_append, data_toList_singleton]
            rfl
    rw [hbytes]
    exact hwide

theorem put_tagn0_spec {w : UInt64} {x_v x_rest r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} {rest : List UInt8}
    (hw : RepU64 h w x_v)
    (ev : ObsFn W "IxonSerialize::put_tagn0" [x_v, x_rest] h r h' calls)
    (hrest : RepBytes h rest x_rest) :
    RepBytes h' ((tag0Bytes w).data.toList ++ rest) r := by
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
    rcases sum_eq_zero_7 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (by push_cast; exact hsumF) with
      ⟨e1, e2, e3, e4, e5, e6, e7⟩
    have hw256 : w.toNat < 256 := by
      have hb := Lib.leBytes8_bytes hw_lt
      rw [e1, e2, e3, e4, e5, e6, e7] at hb
      rw [← hb]
      exact leBytes8_lt_256 (Nat.mod_lt _ (by decide))
    have hv0_rep : RepU8 h w.toUInt8 (.field ((w.toNat % 256 : Nat) : F)) := by
      show (.field ((w.toNat % 256 : Nat) : F) : SourceValue F) = .field (w.toUInt8.toNat : F)
      simp [UInt64.toUInt8, UInt8.toNat_ofNat']
    have h128_rep : RepU8 h (128 : UInt8) (.field 128) := by
      show (.field 128 : SourceValue F) = .field ((128 : UInt8).toNat : F)
      simp only [show (128 : UInt8).toNat = 128 from rfl, Nat.cast_ofNat]
    obtain ⟨hltF, rfl⟩ := Lib.u8_less_than_spec hv0_rep h128_rep ev226
    have hw_toUInt8 : w.toUInt8.toNat = w.toNat := by
      simp [UInt64.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hw256]
    have hw128 : w.toNat < 128 := by
      by_contra hge
      have hge' : ¬ w.toUInt8.toNat < (128 : UInt8).toNat := by
        rw [hw_toUInt8]; change ¬ w.toNat < 128; exact hge
      rw [ite_eq_right hge'] at hltF
      exact absurd (Value.field.inj hltF) (by decide)
    have he1 : Ixon.tagNEnd1 0 = 128 := rfl
    have hhdr : Ixon.tagNHeader 0 0 w.toNat = w.toUInt8 := by
      apply UInt8.eq_of_toNat_eq
      rw [hw_toUInt8]
      simp [Ixon.tagNHeader, Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hw256]
    have hcons := repBytes_cons hv0_rep hrest hm249 he250
    have hbytes : (tag0Bytes w).data.toList = [w.toUInt8] := by
      unfold tag0Bytes tagNBytes
      dsimp only []
      rw [he1, if_pos hw128, hhdr, data_toList_singleton]
    rw [hbytes, List.singleton_append]
    exact hcons
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
    rcases sum_eq_zero_7 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (by push_cast; exact hsumF) with
      ⟨e1, e2, e3, e4, e5, e6, e7⟩
    have hw256 : w.toNat < 256 := by
      have hb := Lib.leBytes8_bytes hw_lt
      rw [e1, e2, e3, e4, e5, e6, e7] at hb
      rw [← hb]
      exact leBytes8_lt_256 (Nat.mod_lt _ (by decide))
    have hv0_rep : RepU8 h w.toUInt8 (.field ((w.toNat % 256 : Nat) : F)) := by
      show (.field ((w.toNat % 256 : Nat) : F) : SourceValue F) = .field (w.toUInt8.toNat : F)
      simp [UInt64.toUInt8, UInt8.toNat_ofNat']
    have h128_rep : RepU8 h (128 : UInt8) (.field 128) := by
      show (.field 128 : SourceValue F) = .field ((128 : UInt8).toNat : F)
      simp only [show (128 : UInt8).toNat = 128 from rfl, Nat.cast_ofNat]
    obtain ⟨hltF, rfl⟩ := Lib.u8_less_than_spec hv0_rep h128_rep ev226
    have hw_toUInt8 : w.toUInt8.toNat = w.toNat := by
      simp [UInt64.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hw256]
    have hw128 : ¬ w.toNat < 128 := by
      intro hlt
      have hlt' : w.toUInt8.toNat < (128 : UInt8).toNat := by
        rw [hw_toUInt8]; exact hlt
      rw [ite_eq_left hlt'] at hltF
      exact absurd (Value.field.inj hltF) (by decide)
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
      have h256 : w.toNat < 256 := Nat.lt_trans hlt (by decide)
      have e1 : w.toNat / 256 % 256 = 0 := div_mod_zero h256
      have e2 : w.toNat / 65536 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e3 : w.toNat / 16777216 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e4 : w.toNat / 4294967296 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e5 : w.toNat / 1099511627776 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e6 : w.toNat / 281474976710656 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
      have e7 : w.toNat / 72057594037927936 % 256 = 0 := div_mod_zero (Nat.lt_trans hlt (by decide))
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
      ((tag4Bytes Ixon.Constant.FLAG k.toUInt64).data.toList ++ rest) r := by
  have hk_rep : ∀ m : Heap F, RepU8 m k.toUInt8 (.field (k : F)) := by
    intro m
    show (.field (k : F) : SourceValue F) = .field (k.toUInt8.toNat : F)
    simp [Nat.toUInt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (show k < 256 by omega)]
  have h8_rep : ∀ m : Heap F, RepU8 m (8 : UInt8) (.field 8) := by
    intro m
    show (.field 8 : SourceValue F) = .field ((8 : UInt8).toNat : F)
    simp only [show (8 : UInt8).toNat = 8 from rfl, Nat.cast_ofNat]
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
    exact absurd (Value.field.inj hltF) (by decide)
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
    have hx275 : x275 = .field 208 := by rw [mul_field_inv op290]; congr 1; decide
    subst hx275
    obtain ⟨rfl, rfl⟩ := Lib.u8_to_field_spec ev297
    have hv268 := add_field_inv op282; subst hv268
    obtain ⟨rfl, rfl, -⟩ := Lib.u8_from_field_spec ev267
    have hk_u64 : k.toUInt64.toNat = k := by
      simp [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hk (by decide))]
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
    have hbytes : (tag4Bytes Ixon.Constant.FLAG k.toUInt64).data.toList =
        [Ixon.tagNHeader 4 Ixon.Constant.FLAG k] := by
      unfold tag4Bytes tagNBytes
      dsimp only []
      rw [hk_u64, he1, if_pos hk, data_toList_singleton]
    rw [hbytes, List.singleton_append]
    exact hcons

end IxVM.Refinement.Core.ProjAddrAux
